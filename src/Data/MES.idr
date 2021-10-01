module Data.MES

import Control.Arrow
import Control.Category
import Control.Monad.Either

import Data.Event
import Data.Maybe
import Data.MSF
import Data.VectorSpace

%default total

public export
record MES (m : Type -> Type) (i,o : Type) where
  constructor MkMES
  sf : MSF m i (Event o)

export %inline
never : MES m i o
never = MkMES $ const NoEv

export %inline
const : o -> MES m i o
const = MkMES . const . Ev

export
when : (i -> Maybe o) -> MES m i o
when f = MkMES $ arr (maybeToEvent . f)

export
unionWith : (o -> o -> o) -> MES m i o -> MES m i o -> MES m i o
unionWith f (MkMES sf1) (MkMES sf2) = MkMES $ unionWith f <$> sf1 <*> sf2

export
unionL : MES m i o -> MES m i o -> MES m i o
unionL (MkMES sf1) (MkMES sf2) = MkMES $ unionL <$> sf1 <*> sf2

export
unionR : MES m i o -> MES m i o -> MES m i o
unionR (MkMES sf1) (MkMES sf2) = MkMES $ unionR <$> sf1 <*> sf2

export
union : Semigroup o => MES m i o -> MES m i o -> MES m i o
union = unionWith (<+>)

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Category (MES m) where
  id      = MkMES $ arr pure
  bc . ab = MkMES $ SeqE ab.sf bc.sf

export %inline
Semigroup o => Semigroup (MES m i o) where
  (<+>) = union

export %inline
Semigroup o => Monoid (MES m i o) where
  neutral = never

export
Functor (MES m i) where
  map f (MkMES sf) = MkMES $ map f <$> sf

export
Applicative (MES m i) where
  pure = const
  MkMES f <*> MkMES a = MkMES [| f <*> a |]

export %inline
Alternative (MES m i) where
  empty   = never
  a <|> b = unionL a b

infixr 1 >>?, ?>>

export %inline
(>>?) : MSF m i x -> MES m x o -> MES m i o
(>>?) y (MkMES z) = MkMES $ y >>> z

export %inline
(?>>) : MES m i x -> MSF m x o -> MES m i o
(?>>) y z = y >>> MkMES (z >>^ Ev)

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

export
onWith : (o -> e -> x) -> MSF m i o -> MES m i e -> MES m i x
onWith f io (MkMES ev) = MkMES $ io &&& ev >>^ (\(vo,ve) => f vo <$> ve)

export
on : MSF m i o -> MES m i () -> MES m i o
on = onWith const
