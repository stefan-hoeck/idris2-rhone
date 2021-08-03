module Data.MSF

import Control.Arrow
import Control.Category
import Control.Monad.Either

%default total

public export
(*) : Type -> Type -> Type
(*) = Pair

public export
(+) : Type -> Type -> Type
(+) = Either

public export
data MSF : (m : Type -> Type) -> (i : Type) -> (o : Type) -> Type where
  Id        :  MSF m i i
  Const     :  o -> MSF m i o
  Arr       :  (i -> o) -> MSF m i o
  Lifted    :  (i -> m o) -> MSF m i o
  Seq       :  MSF m i x -> MSF m x o -> MSF m i o
  Par       :  MSF m i1 o1 -> MSF m i2 o2 -> MSF m (i1 * i2) (o1 * o2)
  Fan       :  MSF m i o1 -> MSF m i o2 -> MSF m i (o1 * o2)
  Choice    :  MSF m i1 o1 -> MSF m i2 o2 -> MSF m (i1 + i2) (o1 + o2)
  Loop      :  s -> MSF m (i, s) (o, s) -> MSF m i o

  Morph     :  Monad m1
            => (forall c . (a1 -> m1 (b1, c)) -> (a2 -> m2 (b2, c)))
            -> MSF m1 a1 b1
            -> MSF m2 a2 b2

  RunEither :  MSF (EitherT e m) i o
            -> (e -> (o, MSF (EitherT e m) i o))
            -> MSF m i o

--------------------------------------------------------------------------------
--          Lifting Primitives
--------------------------------------------------------------------------------

||| Mapping streaming function
export %inline
const : o -> MSF m i o
const = Const

export %inline
arr : (i -> o) -> MSF m i o
arr = Arr

||| Effectful mapping
export %inline
arrM : (i -> m o) -> MSF m i o
arrM = Lifted

export %inline
withSideEffect : Functor m => (o -> m a) -> MSF m o o
withSideEffect f = Lifted (\o => f o $> o)

export %inline
elementwise : (o1 -> o2) -> MSF m i o1 -> MSF m i o2
elementwise f sf = Seq sf $ arr f

export %inline
elementwise2 : (o1 -> o2 -> o3) -> MSF m i o1 -> MSF m i o2 -> MSF m i o3
elementwise2 f sf1 sf2 = Seq (Fan sf1 sf2) $ arr (uncurry f)

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export %inline
Category (MSF m) where
  id      = Id
  bc . ab = Seq ab bc

export %inline
Arrow (MSF m) where
  arrow     = arr
  first sf  = Par sf Id
  second sf = Par Id sf
  (***)     = Par
  (&&&)     = Fan

export %inline
ArrowChoice (MSF m) where
  left  = (`Choice` Id)
  right = Choice Id
  (+++) = Choice

export %inline
Functor (MSF m i) where
  map f = (>>> arr f)

export %inline
Applicative (MSF m i) where
  pure = Const
  (<*>) = elementwise2 apply

export %inline
Semigroup o => Semigroup (MSF m i o) where
  (<+>) = elementwise2 (<+>)

export %inline
Monoid o => Monoid (MSF m i o) where
  neutral = Const neutral

export %inline
Num o => Num (MSF m i o) where
  fromInteger = Const . fromInteger
  (+) = elementwise2 (+)
  (*) = elementwise2 (*)

export %inline
Neg o => Neg (MSF m i o) where
  (-)  = elementwise2 (-)
  negate = elementwise negate

export %inline
Integral o => Integral (MSF m i o) where
  mod = elementwise2 mod
  div = elementwise2 div

export %inline
Fractional o => Fractional (MSF m i o) where
  (/)  = elementwise2 (/)

--------------------------------------------------------------------------------
--          Loops and Stateful computations
--------------------------------------------------------------------------------

export %inline
feedback : s -> MSF m (i * s) (o * s) -> MSF m i o
feedback = Loop

||| Delay a signal by one sample
export %inline
iPre : o -> MSF m o o
iPre v = feedback v (arr $ \(new,delayed) => (delayed,new))

--------------------------------------------------------------------------------
--          Switching
--------------------------------------------------------------------------------

export %inline
runEither :  MSF (EitherT e m) i o
          -> (e -> (o, MSF (EitherT e m) i o))
          -> MSF m i o
runEither = RunEither

--------------------------------------------------------------------------------
--          Monad Morphisms
--------------------------------------------------------------------------------

export %inline
morph : Monad m1 => (f : forall c . m1 c -> m2 c) -> MSF m1 i o -> MSF m2 i o
morph f = Morph (f .)

export %inline
morphGS :  Monad m1
        => (forall c . (a1 -> m1 (b1, c)) -> (a2 -> m2 (b2, c)))
        -> MSF m1 a1 b1
        -> MSF m2 a2 b2
morphGS = Morph

--------------------------------------------------------------------------------
--          Single step evaluation
--------------------------------------------------------------------------------

export
step : Monad m => i -> MSF m i o -> m (o, MSF m i o)
step _ c@(Const x)  = pure (x, c)
step v Id           = pure (v, Id)
step v c@(Arr f)    = pure (f v, c)
step v c@(Lifted f) = (,c) <$> f v

step v (Seq sf1 sf2) = do
  (vx,sf1') <- step v  sf1
  (vo,sf2') <- step vx sf2
  pure (vo, Seq sf1' sf2')

step (v1,v2) (Par sf1 sf2)  = do
  (o1,sf1') <- step v1 sf1
  (o2,sf2') <- step v2 sf2
  pure ((o1,o2), Par sf1' sf2')

step v (Fan sf1 sf2)  = do
  (o1,sf1') <- step v sf1
  (o2,sf2') <- step v sf2
  pure ((o1,o2), Fan sf1' sf2')

step (Left i1) (Choice sf1 sf2)  = do
  (o1,sf1') <- step i1 sf1
  pure (Left o1, Choice sf1' sf2)

step (Right i2) (Choice sf1 sf2)  = do
  (o2,sf2') <- step i2 sf2
  pure (Right o2, Choice sf1 sf2')

step v (Loop s sf) = do
  ((o,s2), sf2) <- step (v,s) sf
  pure (o, Loop s2 sf2)

step v (Morph f msf) = do
  (o, msf2) <- f (`step` msf) v
  pure (o, Morph f msf2)

step i (RunEither sf f) = do
  Left e <- runEitherT (step i sf)
    | Right (o, sf2) => pure (o, RunEither sf2 f)
  let (o, sf2) = f e
  pure (o, RunEither sf2 f)
