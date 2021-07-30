module Rhone.Scan

import Rhone.Types

||| Stateful event accumulation
export
sscanPrim : (c -> a -> Maybe (b,c)) -> c -> b -> SF (E a) (S b) Cau
sscanPrim f vc vb = mkSFTimeless run (vb,vc)
  where run : (b,c) -> Maybe a -> ((b,c),b)
        run (sb,sc) ma = maybe ((sb,sc),sb) (\p => (p, fst p)) (ma >>= f sc)

||| Stateful event accumulation
export
sscan : (b -> a -> b) -> b -> SF (E a) (S b) Cau
sscan f vb = mkSFTimeless run vb
  where run : b -> Maybe a -> (b,b)
        run sb ma = maybe (sb,sb) (dup . f sb) ma
