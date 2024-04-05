module Data.VectorSpace

import Data.Vect

export infixr 9 *^
export infixl 9 ^/
export infixl 6 ^+^, ^-^
export infix 7 `dot`

public export
interface VectorSpace v where
  ||| Vector with no magnitude (unit for addition).
  zeroVector : v

  ||| Multiplication by a scalar.
  (*^) : Double -> v -> v

  ||| Division by a scalar.
  (^/) : v -> Double -> v

  ||| Vector addition
  (^+^) : v -> v -> v

  ||| Vector subtraction
  (^-^) : v -> v -> v

  ||| Vector negation. Addition with a negated vector should
  ||| be same as subtraction.
  negateVector : v -> v
  negateVector v = zeroVector ^-^ v

  ||| Dot product (also known as scalar or inner product).
  ||| For two vectors, mathematically represented as a = a1,a2,...,an and b = b1,b2,...,bn,
  ||| the dot product is a . b = a1*b1 + a2*b2 + ... + an*bn.
  dot : v -> v -> Double

  ||| Vector's norm (also known as magnitude).
  ||| For a vector represented mathematically
  ||| as a = a1,a2,...,an, the norm is the square root of a1^2 + a2^2 + ... + an^2.
  norm : v -> Double
  norm v = sqrt $ dot v v

  ||| Return a vector with the same origin and orientation (angle),
  ||| but such that the norm is one (the unit for multiplication by a scalar).
  normalize : v -> v
  normalize v = let n = norm v in if n == 0 then v else v ^/ n

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
VectorSpace Double where
  zeroVector = 0.0
  (^-^) = (-)
  (^+^) = (+)
  (^/)  = (/)
  (*^)  = (*)
  dot   = (*)

public export
{n : _} -> VectorSpace (Vect n Double) where
  zeroVector = replicate n 0.0
  (^-^)   = zipWith (-)
  (^+^)   = zipWith (+)
  v ^/ s  = map (/ s) v
  s *^ v  = map (* s) v
  dot a b = sum $ zipWith (*) a b
