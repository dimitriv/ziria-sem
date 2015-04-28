module ZirPar where

import Control.Concurrent.STM
import Control.Concurrent.STM.TChan

rw :: TChan a -> TChan a -> STM ()
rw ch_in ch_out
  = do { ma <- tryReadTChan ch_in
       ; case ma of
           Nothing -> return ()
           Just a -> writeTChan ch_out a
       }
    
forever :: STM u -> STM u
forever f = f >> forever f

mux :: TChan v -> TChan a -> TChan a -> TChan a -> STM ()
mux ctl as1 as2 out_chan = go ctl as1 as2 out_chan
  where go ctl as1 as2 out_chan
          = do { mswitch  <- tryReadTChan ctl
               ; case mswitch of
                   Nothing -> rw as1 out_chan 
                   Just _  -> rw as2 out_chan 
               }
                      
dup :: TChan a -> STM (TChan a,TChan a)
dup as
  = do { as' <- cloneTChan as
       ; return (as,as')
       }

newtype Zir a b v = Zir { unZir :: TChan a -> TChan b -> TChan v -> STM () }

ztake :: Zir a b a
ztake = Zir go
  where go as bs ctl = rw as ctl >> return ()

zemit :: b -> Zir a b ()
zemit b = Zir go
  where go as bs ctl
          = do { writeTChan bs b
               ; writeTChan ctl ()
               }

zbind :: Zir a b v1 -> (v1 -> Zir a b v2) -> Zir a b v2
zbind z1 f = Zir go
  where go as bs ctl
          = do { let (as1,as2) = (as,as)
               ; bs1 <- newTChan
               ; bs2 <- newTChan
               ; priv_ctl <- newTChan
               ; (z2_start,mux_switch) <- dup priv_ctl
               ; unZir z1 as1 bs1 z2_start
               ; go2 z2_start as2 bs2 ctl
               ; mux mux_switch bs1 bs2 bs
               }
        go2 start as0 bs0 ctl0
          = do { mv1 <- tryReadTChan start
               ; case mv1 of
                   Nothing -> return ()
                   Just v1 -> unZir (f v1) as0 bs0 ctl0
               }

zpipe :: Zir a b v -> Zir b c v -> Zir a c v
zpipe z1 z2 = Zir go
  where go as cs ctl
          = do { bs <- newTChan 
               ; unZir z1 as bs ctl
               ; unZir z2 bs cs ctl
               }
    
test_emit_take
  = do { a0 <- newTChan
       ; a <- newTChan
       ; b <- newTChan
       ; c0 <- newTChan              
       ; c <- newTChan
       ; unZir (zemit 2) a0 a c0
       ; unZir ztake a b c
       ; tryReadTChan c
       }

test_mux
  = do { in_chan1 <- newTChan
       ; in_chan2 <- newTChan
       ; ctl_chan <- newTChan
       ; out_chan <- newTChan                     
       ; writeTChan in_chan1 1
       ; mux in_chan1 in_chan2 ctl_chan out_chan
       ; tryReadTChan out_chan
       }

zmap f = zbind ztake (\v -> zemit (f v))

zinc = zmap (+ 1)

zdouble = zinc `zpipe` zinc

test_bind
  = do { in_chan <- newTChan
       ; out_chan <- newTChan
       ; ctl_chan <- newTChan
       ; writeTChan in_chan 1
       ; unZir zinc in_chan out_chan ctl_chan
       ; tryReadTChan out_chan
       }

test_pipe
  = do { in_chan <- newTChan
       ; out_chan <- newTChan
       ; ctl_chan <- newTChan
       ; writeTChan in_chan 1
       ; unZir zdouble in_chan out_chan ctl_chan
       ; tryReadTChan out_chan
       }

zsum
  = zbind ztake (\v1 ->
      zbind ztake (\v2 ->
        zemit (v1 + v2)))

test_sum
  = do { in_chan <- newTChan
       ; out_chan <- newTChan
       ; ctl_chan <- newTChan
       ; writeTChan in_chan 20
       ; writeTChan in_chan 22
       ; unZir zsum in_chan out_chan ctl_chan
       ; tryReadTChan out_chan
       }

zsum_and_square
  = zbind ztake (\v1 ->
      zbind ztake (\v2 ->
        zemit (v1 + v2)
        `zpipe` zbind ztake (\v3 -> zemit (v3 * v3))))

test_sum_and_square
  = do { in_chan <- newTChan
       ; out_chan <- newTChan
       ; ctl_chan <- newTChan
       ; writeTChan in_chan 20
       ; writeTChan in_chan 22
       ; unZir zsum_and_square in_chan out_chan ctl_chan
       ; tryReadTChan out_chan
       }


