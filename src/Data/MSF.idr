module Data.MSF

import Control.Monad.Identity
import Data.List.Elem
import Data.Maybe
import Data.VectorSpace
import public Data.SOP

%default total

mutual
  public export
  data MSFList :  (m : Type -> Type)
               -> (is : List Type)
               -> (os : List Type)
               -> Type where
    Nil  : MSFList m [] []
    (::) :  (sf : MSF m i o)
         -> (sfs : MSFList m is os)
         -> MSFList m (i :: is) (o :: os) 

  namespace FanList
    public export
    data FanList :  (m : Type -> Type)
                 -> (i : Type)
                 -> (os : List Type)
                 -> Type where
      Nil  : FanList m i Nil
      (::) :  (sf : MSF m i o)
           -> (sfs : FanList m i os)
           -> FanList m i (o :: os)

  namespace CollectList
    public export
    data CollectList :  (m  : Type -> Type)
                     -> (is : List Type)
                     -> (o  : Type)
                 -> Type where
      Nil  : CollectList m Nil o
      (::) :  (sf : MSF m i o)
           -> (sfs : CollectList m is o)
           -> CollectList m (i :: is) o

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
  
    ||| Parallel combination of streaming functions
    Par       :  MSFList m is os -> MSF m (NP I is) (NP I os)
  
    ||| Broadcasting a value to a list of signal functions
    ||| all taking the same input
    Fan       :  FanList m i os -> MSF m i (NP I os)
  
    ||| Choose an streaming function depending on the input
    Choice    :  MSFList m is os -> MSF m (NS I is) (NS I os)
  
    ||| Choose an streaming function depending on the input
    Collect   :  CollectList m is o -> MSF m (NS I is) o
  
    ||| Feedback loops
    Loop      :  s -> MSF m (i, s) (o, s) -> MSF m i o
  
  --   ||| Single time switiching: Upon the first event,
  --   ||| the second streaming function is calculated
  --   ||| evaluated immediately and used henceforth.
  --   Switch    :  MSF m i (o, Event e) -> (e -> MSF m i o) -> MSF m i o
  -- 
  --   ||| Single time delayed switiching: Upon the first event,
  --   ||| the second streaming function is generated but the
  --   ||| former output is returned. The freshly 
  --   ||| generated streaming function is used in all future
  --   ||| evaluation steps.
  --   |||
  --   ||| It is safe to use this in arbitrary recursive calls.
  --   DSwitch   :  MSF m i (o, Event e) -> Inf (e -> MSF m i o) -> MSF m i o
  -- 
  --   Morph     :  Monad m1
  --             => (forall c . (a1 -> m1 (b1, c)) -> (a2 -> m2 (b2, c)))
  --             -> MSF m1 a1 b1
  --             -> MSF m2 a2 b2

--------------------------------------------------------------------------------
--          Lifting Primitives
--------------------------------------------------------------------------------

||| Constant streaming function
export %inline
id : MSF m i i
id = Id

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

--------------------------------------------------------------------------------
--          Sequencing MSFs
--------------------------------------------------------------------------------

infixr 1 >>^, ^>>, >>>

||| Sequencing of monadic streaming functions
export %inline
(>>>) : MSF m i x -> MSF m x o -> MSF m i o
(>>>) = Seq

||| `sf >>^ f` is an alias for `sf >>> arr f`.
export %inline
(>>^) : MSF m i o -> (o -> o2) -> MSF m i o2
sf >>^ f = Seq sf $ arr f

||| `f ^>> sf` is an alias for `arr f >>> sf`.
export %inline
(^>>) : (i -> i2) -> MSF m i2 o -> MSF m i o
f ^>> sf = Seq (arr f) sf

--------------------------------------------------------------------------------
--          Paralellising MSFs
--------------------------------------------------------------------------------

||| Runs a bundle of MSFs in parallel. This is
||| a generalization of `(***)` from `Control.Arrow`.
export %inline
par : MSFList m is os -> MSF m (NP I is) (NP I os) 
par = Par

||| Broadcasts an input value across a list of MSFs,
||| all of which must accept the same type of input.
||| This is a generalization of `(&&&)` from `Control.Arrow`.
export %inline
fan : FanList m i os -> MSF m i (NP I os) 
fan = Fan

||| Like `fan` but discard the results.
||| This is mainly useful for broadcasting to data sinks
||| (streaming functions that do not produce any interesting
||| out put).
|||
||| TODO: Should we require a proof here that `os` is a list
|||       of `Unit`?
export %inline
fan_ : FanList m i os -> MSF m i ()
fan_ sfs = Fan sfs >>> Const ()

export %inline
elementwise2 : (o1 -> o2 -> o3) -> MSF m i o1 -> MSF m i o2 -> MSF m i o3
elementwise2 f x y = Fan [x,y] >>> Arr (\[a,b] => f a b)

export
firstArg : MSF m (NP I [x,i]) o -> x -> MSF m i o
firstArg sf vx = Fan [Const vx, Id] >>> sf

export
secondArg : MSF m (NP I [i,x]) o -> x -> MSF m i o
secondArg sf vx = Fan [Id, Const vx] >>> sf

--------------------------------------------------------------------------------
--          Selecting MSFs
--------------------------------------------------------------------------------

||| Choose a streaming function to run depending the input value
||| This is a generalization of `(+++)` from `Control.Arrow`.
export %inline
choice : MSFList m is os -> MSF m (NS I is) (NS I os) 
choice = Choice

||| Choose a streaming function from a list of function yielding
||| all the same output.
||| This is a generalization of `(\|/)` from `Control.Arrow`.
export %inline
collect : CollectList m is o -> MSF m (NS I is) o
collect = Collect

export
either :  MSF m i1 o1
       -> MSF m i2 o2
       -> MSF m (Either i1 i2) (Either o1 o2)
either sf1 sf2 =   either Z (S . Z)
               ^>> choice [sf1,sf2]
               >>^ collapseNS . hapNS [Left,Right]

export
maybe :  MSF m i1 o1
      -> MSF m () ()
      -> MSF m (Maybe i1) (Maybe o1)
maybe sf1 sf2 =   maybe (S $ Z ()) Z
              ^>> choice [sf1,sf2]
              >>^ collapseNS . hapNS [Just, const Nothing]

export
ifLeft : MSF m i o -> MSF m (Either i a) (Either o a)
ifLeft sf = either sf id

export
ifRight : MSF m i o -> MSF m (Either a i) (Either a o)
ifRight sf = either id sf

export
ifJust : MSF m a b -> MSF m (Maybe a) (Maybe b)
ifJust sf = maybe sf id

export
ifNothing : MSF m () () -> MSF m (Maybe a) (Maybe a)
ifNothing sf = maybe id sf

export
ifTrue : (f : i -> Bool) -> MSF m i o -> MSF m i (Maybe o)
ifTrue f sf = (\vi => toMaybe (f vi) vi) ^>> ifJust sf

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

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
  negate = map negate

export %inline
Integral o => Integral (MSF m i o) where
  mod = elementwise2 mod
  div = elementwise2 div

export %inline
Fractional o => Fractional (MSF m i o) where
  (/)  = elementwise2 (/)

--------------------------------------------------------------------------------
--          Observing MSFs
--------------------------------------------------------------------------------

public export
fst : NP I [a,b] -> a
fst [va,_] = va

public export
snd : NP I [a,b] -> b
snd [_,vb] = vb

export
observeWith : MSF m o () -> MSF m o o
observeWith h = Fan [h, id] >>^ snd

-- --------------------------------------------------------------------------------
-- --          Event Streams
-- --------------------------------------------------------------------------------
-- 
-- export %inline
-- never : MSF m i (Event o)
-- never = const NoEv
-- 
-- export %inline
-- always : o -> MSF m i (Event o)
-- always = const . Ev
-- 
-- export %inline
-- once : o -> MSF m i (Event o)
-- once vo = DSwitch (const (Ev vo, Ev never)) id
-- 
-- export
-- when : (i -> Maybe o) -> MSF m i (Event o)
-- when f = arr (maybeToEvent . f)
-- 
-- export
-- filter : (i -> Bool) -> MSF m i (Event i)
-- filter f = when $ \x => toMaybe (f x) x
-- 
-- export
-- is : Eq i => i -> MSF m i (Event i)
-- is v = filter (v ==)
-- 
-- export
-- ifLeft : MSF m (Either a b) (Event a)
-- ifLeft = arr $ either Ev (const NoEv)
-- 
-- export
-- ifRight : MSF m (Either a b) (Event b)
-- ifRight = arr $ either (const NoEv) Ev
-- 
-- export
-- ifJust : MSF m (Maybe a) (Event a)
-- ifJust = arr maybeToEvent
-- 
-- export
-- ifNothing : MSF m (Maybe a) (Event ())
-- ifNothing = arr $ maybe (Ev ()) (const NoEv)
-- 
-- export %inline
-- unionWith : (o -> o -> o)
--           -> MSF m i (Event o)
--           -> MSF m i (Event o)
--           -> MSF m i (Event o)
-- unionWith f = elementwise2 (unionWith f)
-- 
-- export %inline
-- unionL :  MSF m i (Event o)
--        -> MSF m i (Event o)
--        -> MSF m i (Event o)
-- unionL = elementwise2 unionL
-- 
-- export %inline
-- unionR :  MSF m i (Event o)
--        -> MSF m i (Event o)
--        -> MSF m i (Event o)
-- unionR = elementwise2 unionR
-- 
-- export %inline
-- union :  Semigroup o
--       => MSF m i (Event o)
--       -> MSF m i (Event o)
--       -> MSF m i (Event o)
-- union = unionWith (<+>)
-- 
-- export %inline
-- (<|>) :   MSF m i (Event o)
--        -> MSF m i (Event o)
--        -> MSF m i (Event o)
-- (<|>) = unionL
-- 
-- infixr 1 ??>, ?>>, >-
-- 
-- export %inline
-- (??>) : MSF m i (Event x) -> MSF m x (Event o) -> MSF m i (Event o)
-- (??>) = SeqE
-- 
-- export %inline
-- (?>>) : MSF m i (Event x) -> MSF m x o -> MSF m i (Event o)
-- (?>>) y z = y ??> (z >>^ Ev)
-- 
-- export %inline
-- (>-) : MSF m i (Event x) -> MSF m x () -> MSF m i ()
-- (>-) y z = Seq (y ?>> z) $ const ()
-- 
-- export
-- onWith : (o -> e -> x) -> MSF m i o -> MSF m i (Event e) -> MSF m i (Event x)
-- onWith f = elementwise2 (map . f)
-- 
-- export
-- on : MSF m i o -> MSF m i (Event e) -> MSF m i (Event o)
-- on = onWith const
-- 
-- export
-- eventOn : MSF m i (Event o) -> MSF m i (Event e) -> MSF m i (Event o)
-- eventOn sf e = (sf `on` e) >>^ join
-- 
-- export
-- leftOn : MSF m i (Either o1 o2) -> MSF m i (Event e) -> MSF m i (Event o1)
-- leftOn sf = eventOn $ sf >>> ifLeft
-- 
-- export
-- rightOn : MSF m i (Either o1 o2) -> MSF m i (Event e) -> MSF m i (Event o2)
-- rightOn sf = eventOn $ sf >>> ifRight
-- 
-- export
-- justOn : MSF m i (Maybe o) -> MSF m i (Event e) -> MSF m i (Event o)
-- justOn sf = eventOn $ sf >>> ifJust
-- 
-- export
-- nothingOn : MSF m i (Maybe o) -> MSF m i (Event e) -> MSF m i (Event ())
-- nothingOn sf = eventOn $ sf >>> ifNothing
-- 
--------------------------------------------------------------------------------
--          Loops and Stateful computations
--------------------------------------------------------------------------------

||| Feedback loops: Given an initial state value,
||| we can feedback the result of each evaluation
||| step and us it as the new state for the next step.
export %inline
feedback : s -> MSF m (i, s) (o, s) -> MSF m i o
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

-- export
-- stepper : o -> MSF m (Event o) o
-- stepper = accumulateWith (\e,vo => fromEvent vo e) 

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

-- --------------------------------------------------------------------------------
-- --          Switches
-- --------------------------------------------------------------------------------
-- 
-- export %inline
-- switch : MSF m i (o, Event e) -> (e -> MSF m i o) -> MSF m i o
-- switch = Switch
-- 
-- export %inline
-- dSwitch : MSF m i (o, Event e) -> Inf (e -> MSF m i o) -> MSF m i o
-- dSwitch = DSwitch
-- 
-- export
-- drSwitch : MSF m i o -> MSF m (i, Event $ MSF m i o) o
-- drSwitch io = dSwitch (first io) drSwitch
-- 
-- export
-- resetOn : MSF m i o -> MSF m i (Event ()) -> MSF m i o
-- resetOn sf ev = Fan Id (ev >>^ ($> sf)) >>> drSwitch sf
-- 
-- export
-- switchOn : (a -> MSF m i o) -> MSF m i (Event a) -> a -> MSF m i o
-- switchOn f ev va = Fan Id (ev >>^ map f) >>> drSwitch (f va)
-- 
-- export
-- switchOnM :  Applicative m
--           => (a -> m (MSF m i o))
--           -> MSF m i (Event a)
--           -> MSF m i o
--           -> MSF m i o
-- switchOnM f ev sf0 = Fan Id (ev >>> arrM (traverse f)) >>> drSwitch sf0
-- 
-- --------------------------------------------------------------------------------
-- --          Monad Morphisms
-- --------------------------------------------------------------------------------
-- 
-- export %inline
-- morph : Monad m1 => (f : forall c . m1 c -> m2 c) -> MSF m1 i o -> MSF m2 i o
-- morph f = Morph (f .)
-- 
-- export %inline
-- morphGS :  Monad m1
--         => (forall c . (a1 -> m1 (b1, c)) -> (a2 -> m2 (b2, c)))
--         -> MSF m1 a1 b1
--         -> MSF m2 a2 b2
-- morphGS = Morph
-- 
--------------------------------------------------------------------------------
--          Single step evaluation
--------------------------------------------------------------------------------

mutual
  export
  stepPar :  Monad m
          => MSFList m is os
          -> NP I is
          -> m (NP I os, MSFList m is os)
  stepPar []          []          = pure ([],[])
  stepPar (sf :: sfs) (vi :: vis) = do
    (vo, sf2)   <- step    sf  vi
    (vos, sfs2) <- stepPar sfs vis
    pure (vo :: vos, sf2 :: sfs2)

  export
  stepFan :  Monad m
          => FanList m i os
          -> i
          -> m (NP I os, FanList m i os)
  stepFan []          _  = pure ([],[])
  stepFan (sf :: sfs) vi = do
    (vo, sf2)   <- step    sf  vi
    (vos, sfs2) <- stepFan sfs vi
    pure (vo :: vos, sf2 :: sfs2)

  export
  stepChoice :  Monad m
             => MSFList m is os
             -> NS I is
             -> m (NS I os, MSFList m is os)
  stepChoice (sf :: sfs) (Z vi) = do
    (vo, sf2) <- step sf vi
    pure (Z vo, sf2 :: sfs)

  stepChoice (sf :: sfs) (S y) = do
    (vo, sfs2) <- stepChoice sfs y
    pure (S vo, sf :: sfs2)

  export
  stepCollect :  Monad m
              => CollectList m is o
              -> NS I is
              -> m (o, CollectList m is o)
  stepCollect (sf :: sfs) (Z vi) = do
    (vo, sf2) <- step sf vi
    pure (vo, sf2 :: sfs)

  stepCollect (sf :: sfs) (S y) = do
    (vo, sfs2) <- stepCollect sfs y
    pure (vo, sf :: sfs2)

  export
  step : Monad m => MSF m i o -> i -> m (o, MSF m i o)
  step c@(Const x)  _ = pure (x, c)
  step Id           v = pure (v, Id)
  step c@(Arr f)    v = pure (f v, c)
  step c@(Lifted f) v = (,c) <$> f v

  step (Seq sf1 sf2) v = do
    (vx,sf1') <- step sf1 v
    (vo,sf2') <- step sf2 vx
    pure (vo, Seq sf1' sf2')

  step (Par sfs) v = mapSnd Par <$> stepPar sfs v

  step (Fan sfs) v = mapSnd Fan <$> stepFan sfs v

  step (Choice sfs) v = mapSnd Choice <$> stepChoice sfs v

  step (Collect sfs) v = mapSnd Collect <$> stepCollect sfs v

  step (Loop s sf) v = do
    ((o,s2), sf2) <- step sf (v,s)
    pure (o, Loop s2 sf2)
  
-- step v (Morph f msf) = do
--   (o, msf2) <- f (`step` msf) v
--   pure (o, Morph f msf2)
-- 
-- step i (Switch sf f) = do
--   ((o,Ev e),_) <- step i sf
--     | ((o,NoEv),sf2) => pure (o, Switch sf2 f)
--   step i $ f e
-- 
-- step i (DSwitch sf f) = do
--   ((o,Ev e),_) <- step i sf
--     | ((o,NoEv),sf2) => pure (o, DSwitch sf2 f)
--   pure (o, f e)

--------------------------------------------------------------------------------
--          Running MSFs
--------------------------------------------------------------------------------

export
embed : Monad m => List i -> MSF m i o -> m (List o)
embed [] _          = pure []
embed (vi :: is) sf = do
  (vo,sf2) <- step sf vi
  os       <- embed is sf2
  pure $ vo :: os

export
embedI : List i -> MSF Identity i o -> List o
embedI is = runIdentity . embed is
