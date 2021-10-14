||| Various utility combinators
module Data.MSF.Util

import Data.MSF.Core
import Data.MSF.Event
import Data.SOP

--------------------------------------------------------------------------------
--          Sequencing Utilities
--------------------------------------------------------------------------------

infixr 1 >>^, ^>>, >>!, !>>

||| Reverse sequenceing of MSFs
export %inline
(.) : MSF m x o -> MSF m i x -> MSF m i o
sf2 . sf1 = Seq sf1 sf2

||| Sequencing of an MSF and a pure function
export %inline
(>>^) : MSF m i o -> (o -> o2) -> MSF m i o2
sf >>^ f = sf >>> arr f

||| Sequencing of a pure function and an MSF
export %inline
(^>>) : (i -> i2) -> MSF m i2 o -> MSF m i o
f ^>> sf = arr f >>> sf

||| Sequencing of an MSF and an effectful computation
export %inline
(>>!) : MSF m i o -> (o -> m o2) -> MSF m i o2
sf >>! f = sf >>> arrM f

||| Sequencing of an effectful computation and an MSF
export %inline
(!>>) : (i -> m i2) -> MSF m i2 o -> MSF m i o
f !>> sf = arrM f >>> sf

--------------------------------------------------------------------------------
--          Paralellising Utilities
--------------------------------------------------------------------------------

||| Like `fan` but discards the results.
||| This is mainly useful for broadcasting to data sinks
||| (streaming functions that do not produce any interesting
||| out put).
|||
||| TODO: Should we require a proof here that `os` is a list
|||       of `Unit`?
export %inline
fan_ : FanList m i os -> MSF m i ()
fan_ sfs = Fan sfs >>> Const ()

||| Extract the first argument from an MSF taking a pair
||| of input values.
export
firstArg : MSF m (NP I [x,i]) o -> x -> MSF m i o
firstArg sf vx = fan [const vx, id] >>> sf

||| Extract the second argument from an MSF taking a pair
||| of input values.
export
secondArg : MSF m (NP I [i,x]) o -> x -> MSF m i o
secondArg sf vx = fan [id, const vx] >>> sf

||| Extract the first value of an n-ary product
export
hd : MSF m (NP I (i :: t)) i
hd = arr hd

||| Extract the tail of an n-ary product
export
tl : MSF m (NP I (i :: t)) (NP I t)
tl = arr tl

||| Extract the second value of an n-ary product
export
snd : MSF m (NP I (i :: i2 :: t)) i2
snd = arr $ \(_ :: v :: _) => v

--------------------------------------------------------------------------------
--          Selecting Utilities
--------------------------------------------------------------------------------

||| Convert an `Either` input to a binary sum, which
||| can then be sequenced with a call to `choice` or `collect`.
export
either : MSF m (Either i1 i2) (NS I [i1,i2])
either = arr $ either Z (S . Z)

||| Run the given MSF only if the input is a `Left`.
export
ifLeft : Monoid o => MSF m i o -> MSF m (Either i a) o
ifLeft sf = either >>> collect [sf, const neutral]

||| Run the given MSF only if the input is a `Right`.
export
ifRight : Monoid o => MSF m i o -> MSF m (Either a i) o
ifRight sf = either >>> collect [const neutral, sf]

||| Convert an `Maybe` input to a binary sum, which
||| can then be sequenced with a call to `choice` or `collect`.
export
maybe :  MSF m (Maybe i) (NS I [i,()])
maybe = arr $ maybe (S $ Z ()) Z

||| Run the given MSF only if the input is a `Just`.
export
ifJust : Monoid o => MSF m i o -> MSF m (Maybe i) o
ifJust sf = maybe >>> collect [sf, const neutral]

||| Run the given MSF only if the input is a `Nothing`.
export
ifNothing : Monoid o => MSF m () o -> MSF m (Maybe i) o
ifNothing sf = maybe >>> collect [const neutral, sf]

||| Convert an input to a binary sum, depending on whether
||| the given predicate returns `True` or `False`. The result
||| can then be sequenced with a call to `choice` or `collect`.
export
bool : (f : i -> Bool) -> MSF m i (NS I [i,i])
bool f = arr $ \vi => if f vi then Z vi else (S $ Z vi)

||| Run the given MSF only if the predicate holds for the input.
export
ifTrue : Monoid o => (f : i -> Bool) -> MSF m i o -> MSF m i o
ifTrue f sf = bool f >>> collect [sf, const neutral]

||| Run the given MSF only if the predicate does not hold for the input.
export
ifFalse : Monoid o => (f : i -> Bool) -> MSF m i o -> MSF m i o
ifFalse f sf = bool f >>> collect [const neutral, sf]

--------------------------------------------------------------------------------
--          Looping Utilities
--------------------------------------------------------------------------------

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

||| Counts the number of scans of the signal function.
export
count : Num n => MSF m i n
count = const 1 >>> accumulateWith (+) 0

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
--          Observing Streaming Functions
--------------------------------------------------------------------------------

||| Observe input values through the given MSF, discarding
||| its output.
export
observeWith : MSF m i o -> MSF m i i
observeWith sf = fan [id,sf] >>> hd

||| Run the given effectful computation on each input.
export %inline
withEffect : (i -> m ()) -> MSF m i i
withEffect = observeWith . arrM

||| Run the given monadic action on each input.
export %inline
runEffect : m () -> MSF m i i
runEffect = withEffect . const

--------------------------------------------------------------------------------
--          Event Streams
--------------------------------------------------------------------------------

||| The empty event stream that never fires an event
export
never : MSF m i (Event o)
never = const NoEv

||| Convert an event stream to a streaming function
||| holding the value of the last event fired starting
||| from the given initial value.
export
hold : o -> MSF m (Event o) o
hold = accumulateWith (\ev,v => fromEvent v ev)

||| Fire the given event exactly once on the first
||| evaluation step.
export
once : o -> MSF m i (Event o)
once v = DSwitch (const $ Left ((),Ev v)) (const never)

||| Fire an event whenever the given predicate holds.
export
when : (i -> Bool) -> MSF m i (Event i)
when f = arr $ \vi => toEvent (f vi) vi

||| Like `when` but discard the input.
export
when_ : (i -> Bool) -> MSF m i (Event ())
when_ f = arr $ \vi => toEvent (f vi) ()

||| Fire an event if the input is a `Left`.
export
whenLeft : MSF m (Either a b) (Event a)
whenLeft = arr $ either Ev (const NoEv)

||| Fire an event if the input is a `Right`.
export
whenRight : MSF m (Either a b) (Event b)
whenRight = arr $ either (const NoEv) Ev

||| Fire an event if the input is a `Just`.
export
whenJust : MSF m (Maybe a) (Event a)
whenJust = arr maybeToEvent

||| Fire an event if the input is a `Nothing`.
export
whenNothing : MSF m (Maybe a) (Event ())
whenNothing = arr $ maybe (Ev ()) (const NoEv)

||| Convert an `Event` input to a binary sum, which
||| can then be sequenced with a call to `choice` or `collect`.
export
event :  MSF m (Event i) (NS I [i,()])
event = arr $ event (S $ Z ()) Z

||| Run the given MSF only if the input fired an event.
export
ifEvent : Monoid o => MSF m i o -> MSF m (Event i) o
ifEvent sf = event >>> collect [sf, const neutral]

||| Run the given MSF only if the input fired no event.
export
ifNoEvent : Monoid o => MSF m () o -> MSF m (Event i) o
ifNoEvent sf = event >>> collect [const neutral, sf]

||| Fire an event whenever the input value changed.
||| Always fires on first input.
export
onChange : Eq i => MSF m i (Event i)
onChange = mealy accum  NoEv
  where accum : i -> Event i -> (Event i, Event i)
        accum v old =
          let ev = Ev v
           in if ev == old then (NoEv, old) else (ev,ev)

||| Left-biased union of event streams: Fires an event
||| whenever either of the event streams fires an event.
||| In case of simultaneous events, the one from the
||| left event stream is used.
export
(<|>) : MSF m i (Event o) -> MSF m i (Event o) -> MSF m i (Event o)
(<|>) = elementwise2 (\e1,e2 => e1 <|> e2)

||| Fires the first input as an event whenever the
||| second input fires.
export
onEvent : MSF m (NP I [a, Event e]) (Event a)
onEvent = arr $ \case [va,e] => e $> va

||| Combines the first input with the event fired by the
||| second input.
export
onEventWith : (a -> e -> b) -> MSF m (NP I [a, Event e]) (Event b)
onEventWith f = arr $ \case [va,e] => f va <$> e

||| Combines an input event stream with a stream function
||| holding an `Either` trying to extract a `Left` whenever
||| an event is fired.
export
leftOnEvent : MSF m (NP I [Either a b, Event e]) (Event a)
leftOnEvent = arr $ \case [Left va,e] => e $> va
                          _           => NoEv

||| Combines an input event stream with a stream function
||| holding an `Either` trying to extract a `Right` whenever
||| an event is fired.
export
rightOnEvent : MSF m (NP I [Either a b, Event e]) (Event b)
rightOnEvent = arr $ \case [Right vb,e] => e $> vb
                           _            => NoEv

||| Combines an input event stream with a stream function
||| holding a `Maybe` trying to extract the value from a `Just` whenever
||| an event is fired.
export
justOnEvent : MSF m (NP I [Maybe a, Event e]) (Event a)
justOnEvent = arr $ \case [Just va,e] => e $> va
                          _           => NoEv
