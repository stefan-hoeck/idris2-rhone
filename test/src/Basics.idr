module Basics

import Control.Monad.Identity
import Data.List
import Data.MSF
import Data.SOP
import Hedgehog

%default total

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
  embedI ns (const n) === map (const n) ns

prop_arrId : Property
prop_arrId = property $ do
  ns <- forAll smallInts
  embedI ns (arr id) === ns

prop_arr : Property
prop_arr = property $ do
  [n,ns] <- forAll $ np [smallInt, smallInts]
  embedI ns (arr (*n)) === map (*n) ns

prop_elementwise : Property
prop_elementwise = property $ do
  [n1,n2,ns] <- forAll $ np [smallInt,smallInt,smallInts]
  embedI ns (map (*n1) (arr (+n2))) ===
    map (\n => n1 * (n + n2)) ns

prop_elementwise2 : Property
prop_elementwise2 = property $ do
  [n1,n2,ns] <- forAll $ np [smallInt,smallInt,smallInts]
  embedI ns [| arr (+n1) * arr (+n2) |] ===
  zipWith (*) (map (+n1) ns) (map (+n2) ns)

prop_once : Property
prop_once = property $ do
  [n1,n2,ns] <- forAll $ np [smallInt,smallInt,smallInts]
  embedI (n2 :: ns) (once n1) === Ev n1 :: (ns $> NoEv)

prop_onceOrId : Property
prop_onceOrId = property $ do
  [n1,n2,ns] <- forAll $ np [smallInt,smallInt,smallInts]
  embedI (map Ev $ n2 :: ns) (once n1 <|> id) === Ev n1 :: map Ev ns

prop_idOrOnce : Property
prop_idOrOnce = property $ do
  [n1,n2,ns] <- forAll $ np [smallInt,smallInt,smallInts]
  embedI (map Ev $ n2 :: ns) (id <|> once n1) === Ev n2 :: map Ev ns
  embedI (NoEv :: map Ev ns) (id <|> once n1) === Ev n1 :: map Ev ns

--------------------------------------------------------------------------------
--          props
--------------------------------------------------------------------------------

export
props : Group
props =
  MkGroup
    "basic properties"
    [ ("prop_const", prop_const)
    , ("prop_arrId", prop_arrId)
    , ("prop_arr", prop_arr)
    , ("prop_elementwise", prop_elementwise)
    , ("prop_elementwise2", prop_elementwise2)
    , ("prop_once", prop_once)
    , ("idOrOnce", prop_idOrOnce)
    ]
