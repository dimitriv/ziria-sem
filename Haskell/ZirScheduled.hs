module Main where

import System.Random
import System.IO ( hSetBuffering
                 , BufferMode( LineBuffering )
                 , stdout
                 ) 
import Control.Concurrent
import Control.Concurrent.STM
import Control.Concurrent.STM.TChan

-----------------------------------------------------------------
-- Alternative #2 "stateless" Ziria semantics
--
-- See the comments in 'ZirPar.hs' for more details.  The main
-- difference from that implementation is that in this file, the
-- dataflow graph is unfolded independently of the scheduling policy
-- used to execute the graph, which makes it possible to play around
-- with multiple different schedules (but so far there's only one).
--
-- Also, 'zrepeat' is no longer implemented in the usual way, as
-- 'zrepeat z = zbind z (\_ -> zrepeat z)', but now as a loop in the
-- scheduler.
--
-- BUILD:
--   ghc --make ZirSchedule.hs -threaded -o main
--   ./main +RTS -Nm -RTS
-- where 'm' is the number of cores you want to use.
--
-----------------------------------------------------------------

data Handles = Handles (TChan ()) (TChan ())

-- The dataflow graph

data Graph =
    Leaf Handles
  | Bind Graph Graph 
  | Pipe Graph Graph
  | Repeat Graph

-- Used to register the threads that are forked as the dataflow graph
-- is unfolded

type Children = MVar [MVar ()]

newtype Zir a b v 
  = Zir { unZir :: -- Special parameters:
                   Children -- A handle to a global list of forked threads

                   -- Main parameters:
                -> TChan a -- Input channel
                -> TChan b -- Output channel
                -> TChan v -- Control channel
                   
                   -- Producing a representation of the dataflow graph 
                -> IO Graph
        }

wrap :: MVar [MVar ()] -> String -> IO a -> IO Graph
wrap children name f
  = do { scheduler_chan <- newTChanIO
         -- TODO: Better than creating a new signaling channel here
         -- may be to use the current control channel instead.
       ; done_chan <- newTChanIO
       ; forkChild children name
         $ forever
         $ block_on scheduler_chan (\_ ->
             do { identify name f
                ; signal_on done_chan
                })
       ; return $ Leaf (Handles scheduler_chan done_chan)
       }

ztake :: Zir a b a
ztake = Zir go
  where go children as bs ctl
          = wrap children "take" $ copy_one as ctl

zemit :: TChan b -> Zir a b ()
zemit bs = Zir go
  where go children as bs' ctl
          = wrap children "emit" $ copy_one bs bs' >> signal_on ctl

zbind :: Zir a b v1 -> (TChan v1 -> Zir a b v2) -> Zir a b v2
zbind z1 f = Zir go
  where go children as bs ctl
          = do { z1_done <- newTChanIO
               ; g1 <- unZir z1 children as bs z1_done
               ; g2 <- unZir (f z1_done) children as bs ctl
               ; return $ Bind g1 g2
               }

zpipe :: Zir a b v -> Zir b c v -> Zir a c v
zpipe z1 z2 = Zir go
  where go children as cs ctl
          = do { bs <- newTChanIO
               ; g1 <- unZir z1 children as bs ctl
               ; g2 <- unZir z2 children bs cs ctl
               ; return $ Pipe g1 g2
               }

zrepeat :: Zir a b v -> Zir a b ()
zrepeat (Zir f) = Zir go 
  where go children as bs ctl
          = do { ctl' <- newTChanIO
               ; g <- f children as bs ctl'
               ; return $ Repeat g
               }

zmap :: (TChan a -> TChan b) -> Zir a b ()
zmap f = zrepeat $ zbind ztake (\ch -> zemit (f ch))


-----------------------------------------------------------------
--
-- Scheduling
--
-----------------------------------------------------------------

schedule :: Children -> TChan () -> [Graph] -> IO (TChan ())
schedule _ ch [] = return ch
schedule children ch (g : gs)
  = case g of
      Leaf (Handles start_chan done_chan) ->
        do { signal_on start_chan
           ; schedule children done_chan gs
           }
      Bind g1 g2 ->
        do { g1_done <- schedule children ch [g1]
           ; block_on g1_done (\_ -> schedule children ch $ g2 : gs)
           }
      Pipe g1 g2 ->
        do { forkChild children "pipe-left"  (schedule children ch [g1])
           ; forkChild children "pipe-right" (schedule children ch [g2])
           ; schedule children ch gs
           }
      Repeat g1  ->
        do { g1_done <- schedule children ch [g1]
           ; block_on g1_done (\_ -> schedule children ch $ gs ++ [g])
           }

test_zir :: Show b => Zir a b v -> [a] -> IO ()
test_zir z as
  = do { in_chan <- newTChanIO
       ; out_chan <- newTChanIO
       ; ctl_chan <- newTChanIO
       ; done_chan <- newTChanIO                     
       ; children <- newMVar []
       ; write_to in_chan as
       ; g <- unZir z children in_chan out_chan ctl_chan
       ; forkChild children "printer" $ forever $ print_one out_chan
       ; schedule children done_chan [g]
       ; waitForChildren children
       }
  where write_to ch [] = return ()
        write_to ch (v : vs)
          = do { atomically $ writeTChan ch v
               ; write_to ch vs
               }

test
  = zrepeat (zbind ztake (\_ -> zbind ztake zemit))

main =
  do { hSetBuffering stdout LineBuffering
     ; test_zir test [1..25]
     }  

-----------------------------------------------------------------
--
-- Auxiliary functions for programming concurrency
--
-----------------------------------------------------------------

debug = False

identify :: String -> IO a -> IO a 
identify prefix f
  = do { tid <- myThreadId
       ; if debug then putStrLn $ show tid ++ ": " ++ prefix ++ " start"
         else return ()
       ; a <- f 
       ; if debug then putStrLn $ show tid ++ ": " ++ prefix ++ " end"
         else return ()
       ; return a
       }

signal_on :: TChan () -> IO ()
signal_on ch = atomically $ writeTChan ch ()

forever :: IO a -> IO a
forever a = a >> forever a

block_on :: TChan v -> (v ->  IO a) -> IO a
block_on ch f
  = do { v <- atomically $ readTChan ch
       ; f v
       }

copy_one :: TChan a -> TChan a -> IO ()
copy_one ch_in ch_out
  = block_on ch_in (\a -> atomically (writeTChan ch_out a))

print_one :: Show a => TChan a -> IO ()
print_one ch = block_on ch (\v -> putStrLn $ show v)

forkChild :: MVar [MVar ()] -> String -> IO a -> IO ThreadId
forkChild children name f
  = do { mvar <- newEmptyMVar
       ; cs <- takeMVar children         
       ; putMVar children (mvar : cs)
       ; tid <- forkFinally f (\_ -> putMVar mvar ())
       ; if debug then putStrLn $ "forked " ++ name ++ ": " ++ show tid
         else return ()
       ; return tid
       }

waitForChildren :: MVar [MVar ()] -> IO ()
waitForChildren children
  = do { cs <- takeMVar children
       ; case cs of
           [] -> return ()
           (c : cs') ->
             do { putMVar children cs'
                ; takeMVar c
                ; waitForChildren children
                }
       }
