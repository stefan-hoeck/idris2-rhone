module Control.Applicative.Syntax

--------------------------------------------------------------------------------
--          mapN etc
--------------------------------------------------------------------------------

public export
map2 : Functor f => Functor g => (a -> b) -> (f . g) a -> (f . g) b
map2 = map . map

public export
map3 :
  Functor f => Functor g => Functor h =>
  (a -> b) -> (f . g . h) a -> (f . g . h) b
map3 = map . map . map

public export
map4 :
  Functor f => Functor g => Functor h => Functor i =>
  (a -> b) -> (f . g . h . i) a -> (f . g . h . i) b
map4 = map . map . map . map

export infixr 4 <$$>, <$$$>, <$$$$>
export infixl 3 <**>, <***>, <****>

public export
(<$$>) : Functor f => Functor g => (a -> b) -> (f . g) a -> (f . g) b
(<$$>) = map . map

public export
(<$$$>) :  Functor f => Functor g => Functor h
        => (a -> b) -> (f . g . h) a -> (f . g . h) b
(<$$$>) = map . map . map

public export
(<$$$$>) :  Functor f => Functor g => Functor h => Functor i
         => (a -> b) -> (f . g . h . i) a -> (f . g . h . i) b
(<$$$$>) = map . map . map . map

public export
(<**>) :  Applicative f => Applicative g
       => (f . g) (a -> b) -> (f . g) a -> (f . g) b
x <**> y = [| x <*> y |]

public export
(<***>) :
  Applicative f => Applicative g => Applicative h =>
  (f . g . h) (a -> b) -> (f . g . h) a -> (f . g . h) b
x <***> y = [| x <**> y |]

public export
(<****>) :
  Applicative f => Applicative g => Applicative h => Applicative i =>
  (f . g . h . i) (a -> b) -> (f . g . h . i) a -> (f . g . h . i) b
x <****> y = [| x <***> y |]

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
record Comp2 (f,g : Type -> Type) (a : Type) where
  constructor C2
  c2 : f (g a)

public export
Functor f => Functor g => Functor (Comp2 f g) where
  map f (C2 v) = C2 $ map2 f v

public export
Applicative f => Applicative g => Applicative (Comp2 f g) where
  pure = C2 . pure . pure
  C2 vf <*> C2 va = C2 $ [| vf <*> va |]

public export
Foldable f => Foldable g => Foldable (Comp2 f g) where
  foldr fun acc (C2 v) =
    foldr (flip $ foldr fun) acc v
  foldl fun acc (C2 v) =
    foldl (foldl fun) acc v

public export
Traversable f => Traversable g => Traversable (Comp2 f g) where
  traverse fun = map C2 . (traverse . traverse) fun . c2
