{-# LANGUAGE GADTs, TypeSynonymInstances, RankNTypes, ScopedTypeVariables #-}
module ZirBasic where 
import Control.Applicative
import Control.Monad

{- A basic implementation of the Ziria combinators based on a recursive type -}
data Zir i o v = Yield (Zir i o v) o
               | Done v 
               | NeedInput (i -> Zir i o v)

zemit :: o -> Zir i o ()
{-# INLINE zemit #-}
zemit     = Yield (Done ())

ztake :: Zir i o i
{-# INLINE ztake #-}
ztake     = NeedInput Done

zreturn :: v -> Zir i o v
{-# INLINE zreturn #-}
zreturn   = Done

zpipe :: forall i o m v. Zir i m v -> Zir m o v -> Zir i o v
{-# INLINE zpipe #-}
zpipe az1 az2 = go2 az1 az2 
  where go2 :: Zir i m v -> Zir m o v -> Zir i o v
        go2 z1 (Done v) = Done v
        go2 z1 (Yield z2' o) = Yield (z1 `zpipe` z2') o
        go2 z1 (NeedInput g) = go1 g z1     -- Go upstream!

        go1 :: (m -> Zir m o v) -> Zir i m v -> Zir i o v
        go1 g (Done v) = Done v
        go1 g (Yield z1' m) = go2 z1' (g m) -- Push downstream!
        go1 g (NeedInput proc1) = NeedInput (go1 g . proc1)


zbind :: Zir i o v -> (v -> Zir i o w) -> Zir i o w
{-# INLINE zbind #-}
zbind (Done v) f       = f v
zbind (Yield z1' o ) f = Yield (zbind z1' f) o
zbind (NeedInput g) f  = NeedInput (\i -> zbind (g i) f)


zrepeat :: Zir i o () -> Zir i o a
{-# INLINE zrepeat #-}
zrepeat p = zbind p (\() -> zrepeat p)

zmap :: (i -> o) -> Zir i o a
zmap f = zrepeat $ do { x <- ztake ; zemit (f x) }
  -- = zrepeat (NeedInput \i -> (Yield (Done ()) (f i)))
  -- = NeedInput (\i -> zbind (Yield (Done ()) (f i)) (\_ -> zmap f))
  -- = NeedInput (\i -> Yield (zbind (Done ()) (\_ -> zmap f)) (f i)
  -- = NeedInput (\i -> Yield (zmap f) (f i)

zfilter :: (i -> Bool) -> Zir i i a
zfilter f = zrepeat $ 
  do x <- ztake
     if f x then zemit x else zreturn ()


instance Monad (Zir i o) where
   return = zreturn
   (>>=)  = zbind

-- Boilerplate
instance Functor (Zir i o) where fmap = liftM
instance Applicative (Zir i o) where 
    pure  = return
    (<*>) = ap


testC = do x <- ztake 
           zemit x
      -- = zbind (ztake) (\x -> zemit x)
      -- = zbind (NeedInput Done) (\x -> Yield x (Done ()))
      -- = NeedInput (\i -> zbind (Done i) (\x -> Yield x (Done ())))
      -- = NeedInput (Yield (Done ()))

testB = do zemit 3
           zemit 4

testD = zemit 3

testA = zrepeat $ do x <- ztake
                     zemit x
      -- = zbind (NeedInput (Yield (Done ()))) (\_ -> testA)
      -- = NeedInput (\i -> zbind (Yield (Done ()) i) (\_ -> testA))
      -- = NeedInput (\i -> Yield (zbind (Done ()) (\_ -> testA)) i)
      -- = NeedInput (\i -> Yield testA i)

main :: IO ()
main = return ()

