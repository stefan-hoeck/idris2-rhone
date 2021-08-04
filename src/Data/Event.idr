module Data.Event

%default total

public export
data Event : (a : Type) -> Type where
  NoEv : Event a
  Ev   : (v : a) -> Event a

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
maybeToEvent : Maybe a -> Event a
maybeToEvent Nothing  = NoEv
maybeToEvent (Just x) = Ev x

public export
eventToMaybe : Event a -> Maybe a
eventToMaybe NoEv   = Nothing
eventToMaybe (Ev v) = Just v

public export
fromEvent : Lazy a -> Event a -> a
fromEvent x NoEv   = x
fromEvent _ (Ev v) = v

public export
event : Lazy b -> Lazy (a -> b) -> Event a -> b
event v _ NoEv   = v
event _ f (Ev x) = f x

--------------------------------------------------------------------------------
--          Interface Implementations
--------------------------------------------------------------------------------

public export
Eq a => Eq (Event a) where
  NoEv == NoEv = True
  Ev x == Ev y = x == y
  _    == _    = False

public export
Ord a => Ord (Event a) where
  compare NoEv   NoEv   = EQ
  compare NoEv   (Ev _) = LT
  compare (Ev _) NoEv   = GT
  compare (Ev x) (Ev y) = compare x y

public export
Functor Event where
  map _ NoEv   = NoEv
  map f (Ev a) = Ev $ f a

public export
Applicative Event where
  pure = Ev
  Ev f <*> Ev a = Ev $ f a
  _    <*> _    = NoEv

public export
Monad Event where
  NoEv >>= _ = NoEv
  Ev a >>= f = f a

public export
Foldable Event where
  foldr _ v NoEv   = v
  foldr f v (Ev a) = f a v

  foldl _ v NoEv   = v
  foldl f v (Ev a) = f v a

  foldMap _ NoEv   = neutral
  foldMap f (Ev a) = f a

  null NoEv   = True
  null (Ev a) = False

public export
Traversable Event where
  traverse _ NoEv   = pure NoEv
  traverse f (Ev a) = Ev <$> f a

public export
Alternative Event where
  empty = NoEv

  NoEv <|> e = e
  e    <|> _ = e

public export
Semigroup a => Semigroup (Event a) where
  Ev a <+> Ev b = Ev $ a <+> b
  _    <+> _    = NoEv

public export
Monoid a => Monoid (Event a) where
  neutral = Ev neutral
