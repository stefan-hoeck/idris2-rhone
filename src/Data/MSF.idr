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

||| A monadic streaming function (`MSF`) is used to
||| provide streams of input values of type `i` to
||| output values of type `o` in a monadic context `m`.
|||
||| The [dunai](TODO: link-to-dunai) library implements
||| them as `data MSF m i o = MSF (i -> m (o, MSF m i o))`
||| but this most general for does not go well with
||| the Idris totality checker.
|||
||| It is therefore implemented as a set of primitive
||| constructors, some of which are truly primitives,
||| some of which are there for reasons of efficiency.
||| In later version of this library, the `MSF` might
||| no longer be publicly exportet, so client code should
||| use the provided combinators instaed of using the
||| data constructors directly.
|||
||| `MSF` objects can be stepwise evaluated by invoking
||| function `step`.
public export
data MSF : (m : Type -> Type) -> (i : Type) -> (o : Type) -> Type where

  ||| The identity streaming function
  Id        :  MSF m i i
  
  ||| The constant streaming function
  Const     :  o -> MSF m i o

  ||| Lifts a pure function to a streaming function
  Arr       :  (i -> o) -> MSF m i o

  ||| Lifts an effectful computation
  Lifted    :  (i -> m o) -> MSF m i o

  ||| Sequencing of streaming functions
  Seq       :  MSF m i x -> MSF m x o -> MSF m i o

  ||| Sequencing of partial streaming functions
  SeqE      :  MSF m i (Event x) -> MSF m x (Event o) -> MSF m i (Event o)

  ||| Parallel combination of streaming functions
  Par       :  MSF m i1 o1 -> MSF m i2 o2 -> MSF m (i1 * i2) (o1 * o2)

  ||| Fanning out input over two streaming functions
  Fan       :  MSF m i o1 -> MSF m i o2 -> MSF m i (o1 * o2)

  ||| Choose an streaming function depending on the input type
  Choice    :  MSF m i1 o1 -> MSF m i2 o2 -> MSF m (i1 + i2) (o1 + o2)

  ||| Feedback loops
  Loop      :  s -> MSF m (i, s) (o, s) -> MSF m i o

  ||| Single time switiching: Upon the first event,
  ||| the second streaming function is calculated
  ||| evaluated immediately and used henceforth.
  Switch    :  MSF m i (o, Event e) -> (e -> MSF m i o) -> MSF m i o

  ||| Single time delayed switiching: Upon the first event,
  ||| the second streaming function is generated but the
  ||| former output is returned. The freshly 
  ||| generated streaming function is used in all future
  ||| evaluation steps.
  |||
  ||| It is safe to use this in arbitrary recursive calls.
  DSwitch   :  MSF m i (o, Event e) -> Inf (e -> MSF m i o) -> MSF m i o

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

||| Runs the given effectful computation on each input,
||| passing on the unmodified input afterwards.
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

export
firstArg : MSF m (x,i) o -> x -> MSF m i o
firstArg sf vx = Seq (Fan (Const vx) Id) sf

export
secondArg : MSF m (i,x) o -> x -> MSF m i o
secondArg sf vx = Seq (Fan Id (Const vx)) sf

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

export
observeWith : MSF m o () -> MSF m o o
observeWith h = (h &&& id) >>^ snd

--------------------------------------------------------------------------------
--          Event Streams
--------------------------------------------------------------------------------

export %inline
never : MSF m i (Event o)
never = const NoEv

export %inline
always : o -> MSF m i (Event o)
always = const . Ev

export %inline
once : o -> MSF m i (Event o)
once vo = DSwitch (const (Ev vo, Ev never)) id

export
when : (i -> Maybe o) -> MSF m i (Event o)
when f = arr (maybeToEvent . f)

export
filter : (i -> Bool) -> MSF m i (Event i)
filter f = when $ \x => toMaybe (f x) x

export
is : Eq i => i -> MSF m i (Event i)
is v = filter (v ==)

export
ifLeft : MSF m (Either a b) (Event a)
ifLeft = arr $ either Ev (const NoEv)

export
ifRight : MSF m (Either a b) (Event b)
ifRight = arr $ either (const NoEv) Ev

export
ifJust : MSF m (Maybe a) (Event a)
ifJust = arr maybeToEvent

export
ifNothing : MSF m (Maybe a) (Event ())
ifNothing = arr $ maybe (Ev ()) (const NoEv)

export %inline
unionWith : (o -> o -> o)
          -> MSF m i (Event o)
          -> MSF m i (Event o)
          -> MSF m i (Event o)
unionWith f = elementwise2 (unionWith f)

export %inline
unionL :  MSF m i (Event o)
       -> MSF m i (Event o)
       -> MSF m i (Event o)
unionL = elementwise2 unionL

export %inline
unionR :  MSF m i (Event o)
       -> MSF m i (Event o)
       -> MSF m i (Event o)
unionR = elementwise2 unionR

export %inline
union :  Semigroup o
      => MSF m i (Event o)
      -> MSF m i (Event o)
      -> MSF m i (Event o)
union = unionWith (<+>)

export %inline
(<|>) :   MSF m i (Event o)
       -> MSF m i (Event o)
       -> MSF m i (Event o)
(<|>) = unionL

infixr 1 ??>, ?>>, >-

export %inline
(??>) : MSF m i (Event x) -> MSF m x (Event o) -> MSF m i (Event o)
(??>) = SeqE

export %inline
(?>>) : MSF m i (Event x) -> MSF m x o -> MSF m i (Event o)
(?>>) y z = y ??> (z >>^ Ev)

export %inline
(>-) : MSF m i (Event x) -> MSF m x () -> MSF m i ()
(>-) y z = Seq (y ?>> z) $ const ()

export
onWith : (o -> e -> x) -> MSF m i o -> MSF m i (Event e) -> MSF m i (Event x)
onWith f = elementwise2 (map . f)

export
on : MSF m i o -> MSF m i (Event e) -> MSF m i (Event o)
on = onWith const

export
eventOn : MSF m i (Event o) -> MSF m i (Event e) -> MSF m i (Event o)
eventOn sf e = (sf `on` e) >>^ join

export
leftOn : MSF m i (Either o1 o2) -> MSF m i (Event e) -> MSF m i (Event o1)
leftOn sf = eventOn $ sf >>> ifLeft

export
rightOn : MSF m i (Either o1 o2) -> MSF m i (Event e) -> MSF m i (Event o2)
rightOn sf = eventOn $ sf >>> ifRight

export
justOn : MSF m i (Maybe o) -> MSF m i (Event e) -> MSF m i (Event o)
justOn sf = eventOn $ sf >>> ifJust

export
nothingOn : MSF m i (Maybe o) -> MSF m i (Event e) -> MSF m i (Event ())
nothingOn sf = eventOn $ sf >>> ifNothing

--------------------------------------------------------------------------------
--          Loops and Stateful computations
--------------------------------------------------------------------------------

||| Feedback loops: Given an initial state value,
||| we can feedback the result of each evaluation
||| step and us it as the new state for the next step.
export %inline
feedback : s -> MSF m (i * s) (o * s) -> MSF m i o
feedback = Loop

||| Delay a stream by one sample.
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

export
stepper : o -> MSF m (Event o) o
stepper = accumulateWith (\e,vo => fromEvent vo e) 

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

||| Unfolds a function over an initial state
||| value.
export
unfold : (s -> (o, s)) -> s -> MSF m i o
unfold f ini = feedback ini (arr $ f . snd)

||| Generates output using a step-wise generation function and an initial
||| value. Version of 'unfold' in which the output and the new accumulator
||| are the same.
export
repeatedly : (o -> o) -> o -> MSF m i o
repeatedly f = unfold $ dup . f

--------------------------------------------------------------------------------
--          Switches
--------------------------------------------------------------------------------

export %inline
switch : MSF m i (o, Event e) -> (e -> MSF m i o) -> MSF m i o
switch = Switch

export %inline
dSwitch : MSF m i (o, Event e) -> Inf (e -> MSF m i o) -> MSF m i o
dSwitch = DSwitch

export
drSwitch : MSF m i o -> MSF m (i, Event $ MSF m i o) o
drSwitch io = dSwitch (first io) drSwitch

export
resetOn : MSF m i o -> MSF m i (Event ()) -> MSF m i o
resetOn sf ev = Fan Id (ev >>^ ($> sf)) >>> drSwitch sf

export
switchOn : (a -> MSF m i o) -> MSF m i (Event a) -> a -> MSF m i o
switchOn f ev va = Fan Id (ev >>^ map f) >>> drSwitch (f va)

export
switchOnM :  Applicative m
          => (a -> m (MSF m i o))
          -> MSF m i (Event a)
          -> MSF m i o
          -> MSF m i o
switchOnM f ev sf0 = Fan Id (ev >>> arrM (traverse f)) >>> drSwitch sf0

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
  step i $ f e

step i (DSwitch sf f) = do
  ((o,Ev e),_) <- step i sf
    | ((o,NoEv),sf2) => pure (o, DSwitch sf2 f)
  pure (o, f e)
