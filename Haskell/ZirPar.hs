module ZirPar where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Concurrent.STM.TChan

copy_one :: TChan a -> TChan a -> STM ()
copy_one ch_in ch_out
  = do { ma <- tryReadTChan ch_in
       ; case ma of
           Nothing -> return ()
           Just a -> writeTChan ch_out a
       }

forever :: IO a -> IO a
forever a = a >> forever a

block_on :: TChan v1 -> (v1 ->  Zir a b v2) -> Zir a b v2
block_on ch f = Zir go
  where go as bs ctl 
          = do { ma <- atomically $ tryReadTChan ch
               ; case ma of
                   Nothing -> unZir (block_on ch f) as bs ctl
                   Just a  -> unZir (f a) as bs ctl
               }

mux :: TChan v -> TChan a -> TChan a -> TChan a -> IO ()
mux ctl_chan in_chan1 in_chan2 out_chan
  = do { behave_as_chan2 <-
            atomically
            $ do { in_chan1_flushed <- isEmptyTChan in_chan1
                 ; ctl_chan_empty   <- isEmptyTChan ctl_chan
                 ; return $ in_chan1_flushed && not ctl_chan_empty
                 }
       ; atomically
         $ if behave_as_chan2 then copy_one in_chan2 out_chan
           else copy_one in_chan1 out_chan
       }

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

test_mux
  = do { in_chan1 <- newTChanIO
       ; in_chan2 <- newTChanIO
       ; ctl_chan <- newTChanIO
       ; out_chan <- newTChanIO
       ; children <- newMVar []
       ; forkChild children
         $ atomically $ do { writeTChan in_chan1 3; writeTChan ctl_chan () }
       ; forkChild children $ atomically (writeTChan in_chan2 4)
       ; forkChild children $ forever $ mux ctl_chan in_chan1 in_chan2 out_chan
       ; forkChild children $ forever $ print_one out_chan
       ; waitForChildren children
       }

dup :: TChan a -> STM (TChan a,TChan a)
dup as
  = do { as' <- cloneTChan as
       ; return (as,as')
       }

newtype Zir a b v = Zir { unZir :: TChan a -> TChan b -> TChan v -> IO () }

ztake :: Zir a b a
ztake = Zir go
  where go as bs ctl = atomically (copy_one as ctl) >> return ()

zemit :: b -> Zir a b ()
zemit b = Zir go
  where go as bs ctl
          = atomically 
            $ do { writeTChan bs b
                 ; writeTChan ctl ()
                 }

zbind :: Zir a b v1 -> (v1 -> Zir a b v2) -> Zir a b v2
zbind z1 f = Zir go
  where go as bs ctl
          = do { bs1 <- newTChanIO
               ; bs2 <- newTChanIO
               ; new_ctl <- newTChanIO
               ; (z1_done,mux_switch) <- atomically $ dup new_ctl
               ; children <- newMVar []
               ; forkChild children $ unZir z1 as bs1 z1_done
               ; forkChild children $ unZir (block_on z1_done f) as bs2 ctl
               ; forkChild children $ mux mux_switch bs1 bs2 bs
               ; waitForChildren children
               }

zpipe :: Zir a b v -> Zir b c v -> Zir a c v
zpipe z1 z2 = Zir go
  where go as cs ctl
          = do { bs <- newTChanIO
               ; children <- newMVar []
               ; forkChild children $ unZir z1 as bs ctl
               ; forkChild children $ unZir z2 bs cs ctl
               ; waitForChildren children
               }

zrepeat :: Zir a b v -> Zir a b v
zrepeat z@(Zir f) = Zir go
  where go as bs ctl = forever $ f as bs ctl
        
zmap f = zrepeat $ zbind ztake (\v -> zemit (f v))

test_zir :: Show b => Zir a b v -> [a] -> IO ()
test_zir z as 
  = do { in_chan <- newTChanIO
       ; out_chan <- newTChanIO
       ; ctl_chan <- newTChanIO
       ; children <- newMVar []
       ; write_to in_chan as
       ; forkChild children $ unZir z in_chan out_chan ctl_chan
       ; forkChild children $ forever $ print_one out_chan
       ; waitForChildren children
       }
  where write_to ch [] = return ()
        write_to ch (v : vs)
          = do { atomically $ writeTChan ch v
               ; write_to ch vs
               }

zinc = zmap (+ 1)

test_bind = test_zir zinc [1,2,3]

zid = zmap id

zplus2 = zid `zpipe` zid

test_pipe = test_zir zplus2 [1,2,3]

zsum2
  = zrepeat
    $ zbind ztake (\v1 ->
        zbind ztake (\v2 ->
          zemit (v1 + v2)))

test_zsum2 = test_zir zsum2 [23,10]
