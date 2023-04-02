module Data.MSF.Event

import public Data.List.Elem
import public Data.List.Quantifiers

%default total

--------------------------------------------------------------------------------
--          n-ary  sums
--------------------------------------------------------------------------------

public export
0 HSum : List Type -> Type
HSum = Any Prelude.id

||| Wrap a value in an n-ary sum
public export
inject : Elem k ks => f k -> Any f ks
inject @{Here}    x = Here x
inject @{There _} x = There $ inject x

--------------------------------------------------------------------------------
--          Event
--------------------------------------------------------------------------------

||| A data type isomorphic to `Maybe` used to signal
||| occurences of discrete events.
public export
data Event : (a : Type) -> Type where
  NoEv : Event a
  Ev   : (v : a) -> Event a

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Try to extract a value from an n-ary sum.
public export
project : (0 k : _) -> Elem k ks => Any f ks -> Event (f k)
project _ @{Here}    (Here p)  = Ev p
project v @{There _} (There p) = project v p
project _            _         = NoEv

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
toEvent : Bool -> Lazy a -> Event a
toEvent False _  = NoEv
toEvent True  va = Ev va

public export
event : Lazy b -> Lazy (a -> b) -> Event a -> b
event v _ NoEv   = v
event _ f (Ev x) = f x

public export
unionL : Event a -> Event a -> Event a
unionL (Ev x) _ = Ev x
unionL _      y = y

public export
unionR : Event a -> Event a -> Event a
unionR _ (Ev y) = Ev y
unionR x _      = x

public export
unionWith : (a -> a -> a) -> Event a -> Event a -> Event a
unionWith f (Ev x) (Ev y) = Ev $ f x y
unionWith _ x      y      = unionL x y

public export
filter : (a -> Bool) -> Event a -> Event a
filter f NoEv    = NoEv
filter f (Ev va) = if f va then Ev va else NoEv

--------------------------------------------------------------------------------
--          Interface Implementations
--------------------------------------------------------------------------------

export
Show a => Show (Event a) where
  showPrec p NoEv   = "NoEv"
  showPrec p (Ev v) = showCon p "Ev" $ showArg v

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

public export %inline
Traversable Event where
  traverse _ NoEv   = pure NoEv
  traverse f (Ev a) = Ev <$> f a

public export %inline
Alternative Event where
  empty = NoEv
  x <|> y = unionL x y

public export %inline
Semigroup a => Semigroup (Event a) where
  (<+>) = unionWith (<+>)

public export %inline
Semigroup a => Monoid (Event a) where
  neutral = NoEv

--------------------------------------------------------------------------------
--          More Utilities
--------------------------------------------------------------------------------

public export
mapMaybe : (a -> Maybe b) -> Event a -> Event b
mapMaybe f ev = ev >>= maybeToEvent . f
