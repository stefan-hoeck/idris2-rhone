module Test.Basics

import Control.Monad.Identity
import Data.MSF
import Data.SOP
import Hedgehog

export
embed : Monad m => List i  -> MSF m i o -> m (List o)
embed [] _          = pure []
embed (vi :: is) sf = do
  (vo,sf2) <- step vi sf
  os       <- embed is sf2
  pure $ vo :: os

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

smallInt : Gen Integer
smallInt = integer (linear 0 1000)

smallInts : Gen (List Integer)
smallInts = list (linear 0 30) smallInt

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

prop_const : Property
prop_const = property $ do
  [n,ns] <- forAll $ np [smallInt, smallInts]
  runIdentity (embed ns $ const n) === map (const n) ns

--------------------------------------------------------------------------------
--          props
--------------------------------------------------------------------------------

export
props : Group
props = MkGroup "basic properties"
          [("prop_const", prop_const)
          ]
