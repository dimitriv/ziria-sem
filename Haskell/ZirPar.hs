module Main where

import System.IO ( hSetBuffering
                 , BufferMode( LineBuffering )
                 , stdout
		 ) 

import Control.Concurrent
import Control.Concurrent.STM
import Control.Concurrent.STM.TChan

-----------------------------------------------------------------
-- An alternative "stateless" Ziria semantics
--
-- The main idea is to make a distinction, on the one hand, between
-- (a) the graph of a Ziria computation, which is just a static
-- description of the program's dataflow, together with some
-- control-flow constraints, and (b) the execution model, which is a
-- particular (dynamic) scheduling strategy for executing the nodes of
-- (a).
-- 
-- Below is a draft implementation of (a) in which all nodes in the
-- dataflow graph run concurrently. I think it's possible to view the
-- previous tick-process execution model as a particular dynamic
-- scheduling policy applied to this "soup-of-nodes".  Note that,
-- while I use the term "dataflow graph", there is actually some
-- control flow hidden inside the implementation of `zbind', in the
-- form of a set of control-flow constraints: When we `zbind z1 f',
-- 'f' must block on the private control channel between `z1' and
-- itself before proceeding.
--
-- NOTE that the soup-of-nodes model has the same problems (wrt.
-- parallel pipe-in-bind, etc.) as the tick-process model. See the
-- comment near 'test_pipe_in_bind' below for more discussion.  This
-- file might be a good place to explore possible solutions, but I
-- haven't yet done so.
--
-----------------------------------------------------------------

-- Used to register the threads that are forked as the dataflow graph
-- is unfolded
type Children = MVar [MVar ()]

newtype Zir a b v = Zir { unZir :: -- Special parameter:
                                   Children -- A handle to a global list of forked threads

                                   -- Main parameters: 
                                -> TChan a  -- Input channel
                                -> TChan b  -- Output channel
                                -> TChan v  -- Control channel

                                   -- Producing an IO action
                                -> IO ()
                        }

ztake :: Zir a b a
ztake = Zir (\_ as _ ctl -> copy_one as ctl)

zemit :: b -> Zir a b ()
zemit b = Zir (\_ _ bs ctl -> atomically $ writeTChan bs b >> writeTChan ctl ())

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

zbind :: Zir a b v1 -> (v1 -> Zir a b v2) -> Zir a b v2
zbind z1 f = Zir go
  where go children as bs ctl
          = do { -- A private control channel between 'z1' and 'f'
                 z1_done <- newTChanIO 
               ; unZir z1 children as bs z1_done
                 -- Fork a new thread to block until z1 sends a control value...
               ; forkChild children $ unZir (block_on z1_done f) children as bs ctl
                 -- No need to join here, we're just unfolding the graph...
               ; return ()
               }

zpipe :: Zir a b v -> Zir b c v -> Zir a c v
zpipe z1 z2 = Zir go
  where go children as cs ctl
          = do { bs <- newTChanIO
               ; unZir z1 children as bs ctl
               ; unZir z2 children bs cs ctl
               ; return ()
               }

zrepeat :: Zir a b v -> Zir a b ()
zrepeat z = zbind z (\_ -> zrepeat z)
        
zmap f = zrepeat $ zbind ztake (\v -> zemit (f v))

test_zir :: Show b => Zir a b v -> [a] -> IO ()
test_zir z as 
  = do { in_chan <- newTChanIO
       ; out_chan <- newTChanIO
       ; ctl_chan <- newTChanIO
       ; children <- newMVar []
       ; write_to in_chan as
       ; forkChild children $ forever $ print_one out_chan         
       ; unZir z children in_chan out_chan ctl_chan
       ; waitForChildren children
       }
  where write_to ch [] = return ()
        write_to ch (v : vs)
          = do { atomically $ writeTChan ch v
               ; write_to ch vs
               }

zinc = zmap (+ 1)
zsum = zrepeat $ zbind ztake (\v1 -> zbind ztake (\v2 -> zemit (v1 + v2)))

-- Tests may not terminate; zmap, etc., produces nodes that zrepeat.
test_bind  = test_zir zinc [1..10]
test_pipe  = test_zir ((zpipe zinc zinc) `zpipe` (zpipe zinc zinc)) [1..10]
test_zsum  = test_zir zsum [1..10]

main =
  do { hSetBuffering stdout LineBuffering
     ; test_zir ((zinc `zpipe` zinc) `zpipe` zsum `zpipe` (zinc `zpipe` zinc)) [1..10]
     }

-- The following program may produce result '4 5' (though I haven't
-- yet observed it) due to a pipe-bind race condition (I think the
-- same one that makes an appearance in parpipe-in-bind in the
-- tick-process execution model):

-- When (zemit 0) sends () on the private control channel sitting
-- between (zemit 0 `zpipe` zemit 5) and (zemit 4), it does not
-- synchronize with (zemit 5), which therefore continues to execute,
-- possibly writing 5 to the output channel after (zemit 4) has
-- written 4. My feeling is that pipe-in-bind is a general problem,
-- even with the tick-process model, and probably orthogonal to the
-- particular choice of execution model.
--
-- It's possible to prevent the race condition from occurring by
-- introducing extra synchronizations (before (zemit 5) does anything
-- observable, e.g., writing 5 to the output channel, make it check
-- that (zemit 0) hasn't yet signalled). However, the extra
-- synchronizations probably incur a performance pernalty.
--
-- ALSO: none of what's done in this file deals with the related
-- mismatched-inputs problem, in which one component reads more from
-- the input stream than it should have, causing a later-bound
-- component from skipping some of its inputs.
test_pipe_in_bind
  = test_zir (zbind (zemit 0 `zpipe` zemit 5) (\_ -> zemit 4)) [1..5]


-----------------------------------------------------------------
--
-- Auxiliary functions for programming concurrency
--
-----------------------------------------------------------------

copy_one :: TChan a -> TChan a -> IO ()
copy_one ch_in ch_out
  = do { a <- atomically $ readTChan ch_in
       ; atomically $ writeTChan ch_out a
       }

forever :: IO a -> IO a
forever a = a >> forever a

block_on :: TChan v1 -> (v1 ->  Zir a b v2) -> Zir a b v2
block_on ch f = Zir go
  where go children as bs ctl 
          = do { v <- atomically $ readTChan ch
               ; unZir (f v) children as bs ctl
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
