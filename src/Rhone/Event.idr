module Rhone.Event

%default total

||| A data type isomorphic to `Maybe` for representing
||| descrete signals (event occurences)
public export
data Event a = NoEvent | Ev a

public export
Eq a => Eq (Event a) where
  NoEvent == NoEvent = True
  Ev a1   == Ev a2   = a1 == a2
  _       == _       = False

public export
Ord a => Ord (Event a) where
  compare NoEvent NoEvent = EQ
  compare NoEvent _       = LT
  compare _       NoEvent = GT
  compare (Ev a1) (Ev a2) = compare a1 a2

export
Show a => Show (Event a) where
  showPrec d NoEvent  = "NoEvent"
  showPrec d (Ev x)   = showCon d "Ev" (showArg x)

public export
Functor Event where
  map f (Ev x) = Ev (f x)
  map f NoEvent  = NoEvent

public export
Applicative Event where
  pure = Ev

  Ev f <*> Ev a = Ev (f a)
  _    <*> _    = NoEvent

public export
Alternative Event where
  empty = NoEvent

  (Ev x)  <|> _ = Ev x
  NoEvent <|> v = v

public export
Monad Event where
  NoEvent  >>= k = NoEvent
  (Ev x)   >>= k = k x

public export
Foldable Event where
  foldr _ z NoEvent = z
  foldr f z (Ev x)  = f x z
  null NoEvent      = True
  null (Ev _)       = False

public export
Traversable Event where
  traverse f NoEvent = pure NoEvent
  traverse f (Ev x)  = Ev <$> f x

public export
Semigroup a => Semigroup (Event a) where
  a <+> b = [| a <+> b |]

public export
Monoid a => Monoid (Event a) where
  neutral = Ev neutral
