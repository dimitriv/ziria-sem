{-# LANGUAGE GADTs, 
    TypeSynonymInstances, RankNTypes, ScopedTypeVariables #-}
module ZirStepper ( testC ) where 

import Control.Applicative
import Control.Monad

{- 
   Ziria combinators but this time they are step-based, with only a
   top-level loop in 'run'. No recursive functions during construction of
   a pipeline.

-}

data ZirS s i o v 
  = Yield s o  
  | Skip s
  | Done v             
  | NeedInput (i -> s)

cast :: (s -> s') -> ZirS s i o v -> ZirS s' i o v
cast f (Done v) = Done v
cast f (Yield s o) = Yield (f s) o
cast f (NeedInput g) = NeedInput (f . g)

data SZir i o v = forall s. SZir s (s -> ZirS s i o v)

zemit :: o -> SZir i o ()
{-# INLINE zemit #-}
zemit x = SZir True aux 
  where aux True  = Yield False x 
        aux False = Done () 

ztake :: SZir i o i
ztake = SZir Nothing aux
  where aux Nothing  = NeedInput Just
        aux (Just i) = Done i

zreturn :: v -> SZir i o v
{-# INLINE zreturn #-}
zreturn v = SZir () (\() -> Done v)

zbind (SZir s1 step1) f = SZir sinit step 
  where sinit = Left s1       
        s2step (SZir s2 step2) 
           = cast (\x -> Right (SZir x step2)) (step2 s2) 
        step (Left s1) = 
           case step1 s1 of 
             Skip s1' -> Skip (Left s1')
             Done v -> s2step (f v)
             Yield s1' o -> Yield (Left s1') o
             NeedInput h -> NeedInput (\i -> Left (h i))
        step (Right sec) = s2step sec

zpipe :: SZir i m v -> SZir m o v -> SZir i o v
{-# INLINE zpipe #-}
zpipe (SZir s1 step1) (SZir s2 step2) = 
   let sinit = (s1,s2)
       step (s1,s2) = 
         case step2 s2 of
           Skip s2' -> Skip (s1,s2')
           Done v -> Done v
           Yield s2' o  -> Yield (s1,s2') o
           NeedInput g2 -> case step1 s1 of
             Skip s1' -> Skip (s1',s2)
             Done v -> Done v
             Yield s1' m -> Skip (s1', g2 m)
             NeedInput g1 -> NeedInput (\i -> (g1 i, s2))
   in SZir sinit step

zrepeat p = zbind p (\() -> zrepeat p)
testC = zbind ztake zemit

-- A single recursive function
run :: Show o => [i] -> SZir i o v -> ([o], v)
run ins (SZir s step) = loop [] ins (step s)
  where 
    loop acc ins (Done v)          = (reverse acc, v)
    loop acc ins (Yield s' o)      = loop (o : acc) ins (step s') 
    loop acc ins (Skip s')         = loop acc ins (step s')
    loop acc (i:ins) (NeedInput g) = loop acc ins (step (g i))
    loop acc [] (NeedInput g)
      = error $ "Need more inputs! Outputs were: " ++ show (reverse acc)

