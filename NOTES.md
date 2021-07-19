I'm working through Neil Scoulthorpe's dissertation,
taking some notes on the go.

## FRP

Signals: `Signal a` is semantically a continuous function over time:
`Time -> a`, where `Time` the non-negatie real numbers (often `Double`
in implementations).

Signal functions are functions over signals:
`SF a b` is semantically equal to `Signal a -> Signal b`.

Descrete time signals are signals whose domain is an at most
countable set of points in time. Single-kinded FRP implementations
make no distinction between continuous-time and descrete-time
signals (the latter being treated as continous-time signals with
an optional return type), while multi-kinded FRP treat the two
as separate entities.

Structural dynamism allows dynamic reconfigurations of reactive
networks. This is typically done through one or more
switching combinators. At the moment of switching, the subordinate
signal is removed from the network and replaced by the
residual signal. Since in general the residual signal is not known
until the moment of switching, it is not at once clear over
what range of time the residual signal is defined: From the system
start time or from the time it was switched in.
The former can lead to space and time leaks if the residual
signal as to retroactively be computed from all former inputs
(which have to be kept in memory until then). Therefore, many
FRP implementations with first class signals choose the
second approach. This results in the concept of
signal generators: `StartTime -> Signal a`.

### Classic FRP (CFRP)

Distinguishes between Behaviors (continuous-time signals) and Events
(discrete-time signals). In many implementations, these are actually
signal generators: `StartTime -> SampleTime -> a`.
An event produces a finite and time-ordered list up to the
sample time: `Event a = StartTime -> SampleTime -> List [(Time,a)]`.

Switching (the following switchings on the first occurence of `Event b`
(remember that events are time-ordered lists of pairs):

```idris
untilB : Behavior a -> Event b -> (b -> Behavior a) -> Behavior a
untilB f [] _ = f
untilB f ((te,e) :: _) g = \t0,t1 => g e te t1
```

Compare this to the following

```idris
untilB' : Behavior a -> Event b -> (b -> Behavior a) -> Behavior a
untilB' f [] _ = f
untilB' f ((_,e) :: _) g = \t0,t1 => g e t0 t1
```

The definitions of bouncing balls are not repeated here but
are well worth the read.

Sometimes it is necessary to retain signals (instead of
restarting them after switching). This is explained with the
`resetBall` example and the `runningIn` types of combinators.

```idris
resetBall : Event Ball -> (Ball -> Behavior Ball) -> Ball -> Behavior Ball
resetBall e f b = untilB (f b) e (resetBall e f)
```

The problem with the above is, that `resetBall` does not only
reset the `Behavior` but also the `Event` resetting the
ball. This is not necessarily, what's desired.
We could use `untilB'`, but this would not start the
behavior at time 0.

```idris
runningInBB : Behavior a -> (Behavior a -> Behavior b) -> Behavior b
runningInBB ba f = \t0 = f (\_ => ba t0) t0
```

### Unary FRP (UFRP)

In Yampa, the main abstraction is `SF A B`, a function from
`Signal a` to `Signal b`.

```idris
advance : Time -> Signal a -> Signal a
advance t0 s = \t => s (t + t0) 

switch : SF A (B, Event C) -> (Event C -> SF A B) -> SF A B
switch sf mk = \s,t => let (b,ev) = sf s t
                        in case dropWhile ((< 0) . fst) ev of
                             []          => b
                             (c,tc) :: _ => mk c (advance tc s) (tc - t)
```

Thus, every signal function lives in its own local time
frame.

## N-ary FRP

### Multi-kinded signals
Single-kinded FRP implementations treat events as a special
kind of signal, which does not respect the semantic model.
Also, some operations need to be done different for
the different kinds of signals. In addition, from interaction with
events, many continuous-time signals are piecewise constants.
Goal: Clear type-level distinction between continuous signals,
event signals, and step signals (piecewise constant continuous
time signal).
