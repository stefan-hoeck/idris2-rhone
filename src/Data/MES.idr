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

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Category (MES m) where
  id      = MkMES $ arr pure
  bc . ab = MkMES $ SeqE ab.sf bc.sf
