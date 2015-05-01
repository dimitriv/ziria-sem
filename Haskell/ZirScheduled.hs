{-# LANGUAGE RankNTypes
           , StandaloneDeriving
           , GADTs
  #-}

module Main where

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

instance Show (TChan a) where
  show _ = "<chan>"  

data Handles where
  Handles :: TChan () -- Start chan
          -> TChan ()  -- Done chan
          -> Handles

deriving instance Show Handles

-- The dataflow graph

data Graph =
    TakeLeaf Handles
  | EmitLeaf Handles
  | Bind Graph Graph 
  | Pipe Graph Graph
  | Repeat Graph
  deriving Show    

-- Used to register the threads that are forked as the dataflow graph
-- is unfolded

type Children = MVar [MVar ()]

newtype Zir a b v = Zir { unZir :: -- Special parameters:
                                   Children -- A handle to a global list of forked threads

                                   -- Main parameters: 
                                -> TChan a  -- Input channel
                                -> TChan b  -- Output channel
                                -> TChan v  -- Control channel

                                   -- Producing a representation of the dataflow graph 
                                -> IO Graph
                        }

ztake :: Zir a b a
ztake = Zir go
  where go children as bs ctl
          = do { start_chan <- newTChanIO
               ; done_chan  <- newTChanIO
               ; forkChild children
                 $ forever 
                 $ block_on start_chan (\_ ->
                     do { copy_one as ctl
                        ; signal_on done_chan
                        })
               ; return $ TakeLeaf (Handles start_chan done_chan)
               }

zemit :: TChan b -> Zir a b ()
zemit bs_in = Zir go
  where go children as bs ctl
          = do { start_chan <- newTChanIO
               ; done_chan  <- newTChanIO
               ; forkChild children
                 $ forever
                 $ block_on start_chan (\_ ->
                     do { copy_one bs_in bs
                        ; signal_on ctl
                        ; signal_on done_chan
                        })
               ; return $ EmitLeaf (Handles start_chan done_chan)
               }        

{-
'zbind z1 (\v -> z2)' is modeled as the dataflow graph that looks
like:
              |-------|
         /----|   z1  |----\
        /     |_______|     \
 a ----/          |          \-----> b
       \          | v        / 
        \     |---v---|     /
         \____|   z2  |____/
              |_______|

where 'a' and 'b' are streams of input/output values and 'v' is the
(private) control channel between 'z1' and 'z2'. 'z2' blocks until the
control channel 'v' is nonempty.
-}

zbind :: Zir a b v1 -> (TChan v1 -> Zir a b v2) -> Zir a b v2
zbind z1 f = Zir go
  where go children as bs ctl
          = do { -- A private control channel between 'z1' and 'f'
                 z1_done <- newTChanIO 
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
               ; return $ Repeat (Pipe g1 g2)
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

-- Schedules operate on focused graphs:

data ZipNode =
    BindLeft  Graph
  | BindRight Graph
  | PipeLeft  Graph
  | PipeRight Graph
  | RepeatNode 
  deriving Show    

data Zip = Zip { graph :: Graph
               , path  :: [ZipNode]
               }
         deriving Show

up_from :: Zip -> Zip
up_from z = case (graph z, path z) of
  (_, []) -> z
  (g, BindLeft g' : ns) -> Zip (Bind g g') ns
  (g, BindRight g' : ns) -> Zip (Bind g' g) ns
  (g, PipeLeft g' : ns) -> Zip (Pipe g g') ns
  (g, PipeRight g' : ns) -> Zip (Pipe g' g) ns
  (g, RepeatNode : ns) -> Zip (Repeat g) ns    

left_of :: Zip -> Zip
left_of z = case graph z of
  TakeLeaf {} -> z
  EmitLeaf {} -> z  
  Bind g1 g2 -> z { graph = g1, path = BindLeft g2 : path z }
  Pipe g1 g2 -> z { graph = g1, path = PipeLeft g2 : path z }
  Repeat g -> z { graph = g, path = RepeatNode : path z }

right_of :: Zip -> Zip
right_of z = case graph z of
  TakeLeaf {} -> z
  EmitLeaf {} -> z  
  Bind g1 g2 -> z { graph = g2, path = BindRight g1 : path z }
  Pipe g1 g2 -> z { graph = g2, path = PipeRight g1 : path z }
  Repeat g -> z { graph = g, path = RepeatNode : path z }  

zip_of_graph :: Graph -> Zip
zip_of_graph g = Zip g []

-- One particular (static) scheduling policy:

tick_tock :: Zip -> (Zip -> IO ()) -> IO ()
tick_tock z kont
  = case graph z of
      TakeLeaf (Handles start_chan done_chan) ->
        do { schedule_leaf start_chan done_chan
           ; kont z
           }
      EmitLeaf (Handles start_chan done_chan) ->
        do { schedule_leaf start_chan done_chan
           ; kont z
           } 
      Bind _ _ -> 
        do { tick_tock (left_of z) (\z1 ->
               tick_tock (right_of $ up_from z1) (\z2 ->
                 kont (up_from z2)))                                                   
           }
      Pipe _ _ -> 
        do { tick_tock (left_of z) (\z1 ->
               tick_tock (right_of $ up_from z1) (\z2 ->
                 kont (up_from z2)))
           }
      Repeat _ -> 
        do { tick_tock (left_of z) (\z1 ->
               do { kont (up_from z1)
                  ; tick_tock (up_from z1) (\_ -> return ())
                  })
           }
  where schedule_leaf start_chan done_chan
          = do { signal_on start_chan
               ; return ()
               ; atomically $ readTChan done_chan
               }

test_zir :: Show b => (Zip -> IO ()) -> Zir a b v -> [a] -> IO ()
test_zir schedule z as
  = do { in_chan <- newTChanIO
       ; out_chan <- newTChanIO
       ; ctl_chan <- newTChanIO
       ; children <- newMVar []
       ; write_to in_chan as
       ; g <- unZir z children in_chan out_chan ctl_chan
       ; forkChild children $ forever $ print_one out_chan              
       ; schedule $ zip_of_graph g
       ; waitForChildren children
       }
  where write_to ch [] = return ()
        write_to ch (v : vs)
          = do { atomically $ writeTChan ch v
               ; write_to ch vs
               }
test
  = zrepeat
    (zbind ztake
     (\_ -> zbind ztake
     (\v -> zemit v)))
    `zpipe`
    zrepeat
    (zbind ztake zemit)
    `zpipe`
    zrepeat
    (zbind ztake zemit)
    `zpipe`
    zrepeat
    (zbind ztake zemit)
    `zpipe`
    zrepeat
    (zbind ztake zemit)
    `zpipe`
    zrepeat
    (zbind ztake zemit)
    `zpipe`
    zrepeat
    (zbind ztake zemit)
    `zpipe`
    zrepeat
    (zbind ztake zemit)
    `zpipe`
    zrepeat
    (zbind ztake zemit)

main = test_zir (flip tick_tock (\_ -> return ())) test [1..20]

-----------------------------------------------------------------
--
-- Auxiliary functions for programming concurrency
--
-----------------------------------------------------------------

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
  = block_on ch_in (\a -> atomically $ writeTChan ch_out a)

print_one ch
  = do { mv <- atomically $ tryReadTChan ch
       ; case mv of
           Nothing -> return ()
           Just v  -> putStrLn (show v)
       }

forkChild :: MVar [MVar ()] -> IO () -> IO ThreadId
forkChild children f
  = do { mvar <- newEmptyMVar
       ; cs <- takeMVar children         
       ; putMVar children (mvar : cs)
       ; forkFinally f (\_ -> putMVar mvar ())
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
