module Data.MSF

import Control.Arrow
import Control.Category
import Control.Monad.Either

import Data.Event
import Data.Maybe
import Data.VectorSpace

%default total

||| Operator alias for `Pair`
public export
(*) : Type -> Type -> Type
(*) = Pair

||| Operator alias for `Either`
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
  SeqE      :  MSF m i (Event x) -> MSF m x (Event o) -> MSF m i (Event o)
  Par       :  MSF m i1 o1 -> MSF m i2 o2 -> MSF m (i1 * i2) (o1 * o2)
  Fan       :  MSF m i o1 -> MSF m i o2 -> MSF m i (o1 * o2)
  Choice    :  MSF m i1 o1 -> MSF m i2 o2 -> MSF m (i1 + i2) (o1 + o2)
  Loop      :  s -> MSF m (i, s) (o, s) -> MSF m i o

  Switch    :  MSF m i (o, Event e)
            -> (e -> o -> (o,MSF m i (o, Event e)))
            -> MSF m i o

  Morph     :  Monad m1
            => (forall c . (a1 -> m1 (b1, c)) -> (a2 -> m2 (b2, c)))
            -> MSF m1 a1 b1
            -> MSF m2 a2 b2

--------------------------------------------------------------------------------
--          Lifting Primitives
--------------------------------------------------------------------------------

infixr 1 >>^, ^>>

||| Constant streaming function
export %inline
const : o -> MSF m i o
const = Const

||| Mapping streaming function
export %inline
arr : (i -> o) -> MSF m i o
arr = Arr

||| Effectful mapping
export %inline
arrM : (i -> m o) -> MSF m i o
arrM = Lifted

export %inline
withSideEffect : Functor m => (o -> m ()) -> MSF m o o
withSideEffect f = Lifted (\o => f o $> o)

||| Alias for `map`
export %inline
elementwise : (o1 -> o2) -> MSF m i o1 -> MSF m i o2
elementwise f sf = Seq sf $ arr f

||| Applies a binary function to the outputs of two
||| streaming functions.
export %inline
elementwise2 : (o1 -> o2 -> o3) -> MSF m i o1 -> MSF m i o2 -> MSF m i o3
elementwise2 f sf1 sf2 = Seq (Fan sf1 sf2) $ arr (uncurry f)

||| `sf >>^ f` is an alias for `sf >>> arr f`.
export %inline
(>>^) : MSF m i o -> (o -> o2) -> MSF m i o2
sf >>^ f = Seq sf $ arr f

||| `f ^>> sf` is an alias for `arr f >>> sf`.
export %inline
(^>>) : (i -> i2) -> MSF m i2 o -> MSF m i o
f ^>> sf = Seq (arr f) sf

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
  (-)    = elementwise2 (-)
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

||| Applies a function to the input and an accumulator,
||| outputting the updated accumulator.
export
accumulateWith : (i -> o -> o) -> o -> MSF m i o
accumulateWith f ini = feedback ini (arr g)
  where g : (i,o) -> (o,o)
        g (inp,acc) = let acc' = f inp acc in (acc',acc')

||| Counts the number of scans of the signal function.
export
count : Num n => MSF m i n
count = 1 >>> accumulateWith (+) 0

||| Sums the inputs, starting from an initial vector.
export
sumFrom : VectorSpace v => v -> MSF m v v
sumFrom = accumulateWith (^+^)

||| Sums the inputs, starting from zero.
export
sumS : VectorSpace v => MSF m v v
sumS = sumFrom zeroVector

||| Accumulate the inputs, starting from an initial value.
export
appendFrom : Semigroup v => v -> MSF m v v
appendFrom = accumulateWith (<+>)

||| Accumulate the inputs, starting from `neutral`
export
append : Monoid n => MSF m n n
append = appendFrom neutral

||| Applies a transfer function to the input and an accumulator,
||| returning the updated accumulator and output.
export
mealy : (i -> s -> (o, s)) -> s -> MSF m i o
mealy f s0 = feedback s0 $ arr (uncurry f)

export
unfold : (s -> (o, s)) -> s -> MSF m i o
unfold f ini = feedback ini (arr $ f . snd)

||| Generate outputs using a step-wise generation function and an initial
||| value. Version of 'unfold' in which the output and the new accumulator
||| are the same.
export
repeatedly : (o -> o) -> o -> MSF m i o
repeatedly f = unfold $ dup . f

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

step v (SeqE sf1 sf2) = do
  (Ev vx,sf1') <- step v  sf1 | (NoEv, sf1') => pure (NoEv, SeqE sf1' sf2)
  (vo,sf2') <- step vx sf2
  pure (vo, SeqE sf1' sf2')

-- todo: Change this back to a pattern match on
-- `p`, once #1974 has been fixed.
step p (Par sf1 sf2)  = do
  (o1,sf1') <- step (fst p) sf1
  (o2,sf2') <- step (snd p) sf2
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

step i (Switch sf f) = do
  ((o,Ev e),_) <- step i sf
    | ((o,NoEv),sf2) => pure (o, Switch sf2 f)
  let (o2,sf2) = f e o
  pure (o2, Switch sf2 f)
