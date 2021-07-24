module Rhone.Types

import public Data.Fuel
import public Data.Nat
import public Data.Vect

import Rhone.Event

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

-- Proof that the sum of two positive naturals is again
-- a positive natural
addSucc : IsSucc a -> IsSucc b -> IsSucc (a + b)
addSucc ItIsSucc ItIsSucc = ItIsSucc

--------------------------------------------------------------------------------
--          Time
--------------------------------------------------------------------------------

public export
record Time where
  constructor MkTime
  value : Integer

namespace Time
  public export
  fromInteger : (v : Integer) -> Time
  fromInteger = MkTime

||| To avert rounding errors, we use integers
||| instead of floating point numbers for time. A time span is therefore
||| a strictly positive integer.
|||
||| The semantics of an integral time span of course
||| depend on the use case and sampling rate.
public export
record TimeSpan where
  constructor MkTimeSpan
  value    : Nat
  0 isSucc : IsSucc value

namespace TimeSpan
  public export
  fromInteger : (v : Integer) -> {auto 0 prf : IsSucc (fromInteger v)} -> TimeSpan
  fromInteger v = MkTimeSpan (fromInteger v) prf

public export
Semigroup TimeSpan where
  (MkTimeSpan v1 s1 <+> MkTimeSpan v2 s2) = MkTimeSpan (v1 + v2) (addSucc s1 s2)

public export
timeSpan : Time -> Time -> Maybe TimeSpan
timeSpan (MkTime a) (MkTime b) =
  let n = integerToNat (b - a)
   in case isItSucc n of
        (Yes prf)   => Just $ MkTimeSpan n prf
        (No contra) => Nothing

--------------------------------------------------------------------------------
--          Signal Vectors
--------------------------------------------------------------------------------

||| Describes the value stored at a single position in a signal vector.
|||
||| A signal is either continuous (`C`), a countable list of
||| discrete events (`E`), or a step signal (`S`), which is constant
||| except for a countable number of changes.
public export
data SVDesc : Type where
  E : Type -> SVDesc
  C : Type -> SVDesc
  S : Type -> SVDesc
  P : SVDesc -> SVDesc -> SVDesc

||| Calculates the type of a value representing a signal vector
public export
Sample : SVDesc -> Type
Sample (E x)   = Maybe x
Sample (C x)   = x
Sample (S x)   = x
Sample (P x y) = (Sample x, Sample y)

public export
data Kind = KE | KC | KS

--------------------------------------------------------------------------------
--          Lifting Functions
--------------------------------------------------------------------------------

public export
data Liftable : Kind -> SVDesc -> Type where
  LE  : (x : Type) -> Liftable KE (E x)
  LC  : (x : Type) -> Liftable KC (C x)
  LS  : (x : Type) -> Liftable KS (S x)
  PE  : (x : Type) -> Liftable k d -> Liftable KE (P (E x) d)
  PS  : (x : Type) -> Liftable k d -> Liftable k (P (S x) d)
  PCE : (x : Type) -> Liftable KE d -> Liftable KE (P (C x) d)
  PCC : (x : Type) -> Liftable KC d -> Liftable KC (P (C x) d)
  PCS : (x : Type) -> Liftable KS d -> Liftable KC (P (C x) d)

public export
Fun : Liftable k d -> Type -> Type
Fun (LE x)    res = x -> res
Fun (LC x)    res = x -> res
Fun (LS x)    res = x -> res
Fun (PE x y)  res = x -> Fun y res
Fun (PS x y)  res = x -> Fun y res
Fun (PCE x y) res = x -> Fun y res
Fun (PCC x y) res = x -> Fun y res
Fun (PCS x y) res = x -> Fun y res

applyS : (l : Liftable KS d) -> Fun l t -> Sample d -> t
applyS (LS _)   f v     = f v
applyS (PS _ r) f (v,w) = applyS r (f v) w

applyC : (l : Liftable KC d) -> Fun l t -> Sample d -> t
applyC (LC  _)   f v      = f v
applyC (PS  _ r) f (v, w) = applyC r (f v) w
applyC (PCC _ r) f (v, w) = applyC r (f v) w
applyC (PCS _ r) f (v, w) = applyS r (f v) w

applyE : (l : Liftable k d) -> Fun l t -> Sample d -> Maybe t 
applyE (LE _)    f v            = f <$> v
applyE (LC _)    f v            = Just $ f v
applyE (LS _)    f v            = Just $ f v
applyE (PS _  r) f (v, w)       = applyE r (f v) w
applyE (PCE _ r) f (v, w)       = applyE r (f v) w
applyE (PCC _ r) f (v, w)       = applyE r (f v) w
applyE (PCS _ r) f (v, w)       = applyE r (f v) w
applyE (PE _  r) f (Nothing, w) = Nothing
applyE (PE _  r) f (Just v,  w) = applyE r (f v) w

--------------------------------------------------------------------------------
--          Initialisation
--------------------------------------------------------------------------------

public export
data Initialization = Ini | Uni

--------------------------------------------------------------------------------
--          Causality
--------------------------------------------------------------------------------

public export
data Causality = Cau | Dec

public export
or : Causality -> Causality -> Causality
or Cau c = c
or Dec _ = Dec

public export
and : Causality -> Causality -> Causality
and Dec c = c
and Cau _ = Cau

--------------------------------------------------------------------------------
--          Signal Functions
--------------------------------------------------------------------------------

public export
data Node : (input : SVDesc) -> (output : SVDesc) -> Causality -> Type where
  CNode :  {0 st : Type}
        -> (run : TimeSpan -> st -> Sample input -> (st, Sample output))
        -> (state : st)
        -> Node input output Cau

  DNode :  {0 st : Type}
        -> (run : TimeSpan -> st -> Sample input -> (st, Sample output))
        -> (state : st)
        -> Node input output Dec

public export
stepNode : TimeSpan -> Node i o Cau -> Sample i -> (Node i o Cau, Sample o)
stepNode t (CNode run st) i = let (st2,o) = run t st i in (CNode run st2, o)

||| Function over signal vectors.
|||
||| This is the core data type describing a reactive network.
||| While its constructors are publicly available, values of
||| this type should in general be created through (a combination of)
||| the many combinators provided by this library.
|||
||| The data type is indexed over the types of values stored in the
||| input signal vector and the types of values stored in the
|||
||| Note, that for reasons of efficiency, this data type
||| has more data constructors than strictly necessary.
public export
data SF_ :  (ini    : Initialization)
         -> (input  : SVDesc)
         -> (output : SVDesc)
         -> (cau    : Causality)
         -> Type where

   ||| The identity signal function
   Id     : SF_ ini i i Cau

   ||| The identity signal function
   First  : SF_ ini (P as bs) as Cau

   ||| The identity signal function
   Second : SF_ ini (P as bs) bs Cau

   ||| The constant signal function.
   Const  : Sample o -> SF_ ini i o Dec

   ||| Stateless signal function, independent of time.
   Arr    : (f : Sample i -> Sample o) -> SF_ ini i o Cau

   ||| Sequential combination of signal functions
   Seq    :  (c1,c2 : Causality)
          -> SF_ ini i x c1
          -> SF_ ini x o c2
          -> SF_ ini i o (c1 `or` c2)

   ||| Fanning out of signal functions
   Fan    :  (c1,c2 : Causality) 
          -> SF_ ini as bs c1
          -> SF_ ini as cs c2
          -> SF_ ini as (P bs cs) (c1 `and` c2)

   ||| Parallel combination of signal functions
   Par    :  (c1,c2 : Causality) 
          -> SF_ ini as cs c1
          -> SF_ ini bs ds c2
          -> SF_ ini (P as bs) (P cs ds) (c1 `and` c2)

   ||| Primitive stateful uninitialized causal signal function.
   UCPrim  : (Sample i -> (Node i o Cau, Sample o)) -> SF_ Uni i o Cau

   ||| Primitive stateful uninitialized decoupled signal function.
   UDPrim  : (Sample i -> Node i o Dec) -> Sample o -> SF_ Uni i o Dec

   ||| Primitive stateful initialized signal function.
   IPrim   :  Node i o cau -> SF_ Ini i o cau

   RSwitch :  (c1,c2 : Causality)
           -> SF_ ini i (P o $ E e) c1
           -> (e -> SF_ Uni i (P o $ E e) c2)
           -> SF_ ini i o (c1 `and` c2)

   Freezer :  SF_ ini i o cau -> SF_ ini i (P o . C $ SF_ Uni i o cau) cau

   Weaken : SF_ ini i o c -> SF_ ini i o Cau

public export
SF : (input : SVDesc) -> (output : SVDesc) -> Causality -> Type
SF = SF_ Uni

-- --------------------------------------------------------------------------------
-- --          Routing Primitives
-- --------------------------------------------------------------------------------
-- 
-- infixr 1 >>>, ^>>, >>^
-- infixr 3 ***, &&&
-- 
-- public export %inline
-- id : SF as as
-- id = Id
-- 
-- public export %inline
-- fst : SF (P as bs) as
-- fst = First
-- 
-- public export %inline
-- snd : SF (P as bs) bs
-- snd = Second
-- 
-- public export %inline
-- (>>>) : SF as bs -> SF bs cs -> SF as cs
-- (>>>) = Seq
-- 
-- public export %inline
-- (&&&) : SF as bs -> SF as cs -> SF as (P bs cs)
-- (&&&) = Fan
-- 
-- public export %inline
-- (***) : SF as cs -> SF bs ds -> SF (P as bs) (P cs ds) 
-- (***) = Par
-- 
-- public export %inline
-- rswitch : SF as (P bs $ E e) -> (e -> SF as (P bs $ E e)) -> SF as bs
-- rswitch = RSwitch
-- 
-- public export %inline
-- freeze : SF as bs -> SF as (P bs . C $ SF as bs)
-- freeze = Freezer
-- 
-- --------------------------------------------------------------------------------
-- --          Utilities
-- --------------------------------------------------------------------------------
-- 
-- export
-- mkSF :  (TimeSpan -> st -> Sample i -> (st, Sample o))
--      -> (Sample i -> (st, Sample o))
--      -> SF i o
-- mkSF f g = UPrim $ mapFst (MkNode f) . g
-- 
-- export
-- mkSFSource : (TimeSpan -> st -> (st, Sample o)) -> st -> Sample o -> SF i o
-- mkSFSource f st o = mkSF (\dt,s,_ => f dt s) (const (st,o))
-- 
-- export
-- mkSFTimeless : (st -> Sample i -> (st, Sample o)) -> st -> SF i o
-- mkSFTimeless f s = mkSF (const f) (f s)
-- 
-- export
-- mkSFStateless : (Sample i -> Sample o) -> SF i o
-- mkSFStateless = Arr
-- 
-- export
-- const : o -> SF i (S o)
-- const = Const
-- 
-- export
-- never : SF i (E o)
-- never = Const Nothing
-- 
-- export
-- now : SF i (E ())
-- now = mkSFSource (\_,_ => ((),Nothing)) () (Just ())
-- 
-- export
-- notYet : SF (E a) (E a)
-- notYet = mkSF (\_,_,v => ((),v)) (const ((),Nothing))
-- 
-- export
-- filterE : (a -> Bool) -> SF (E a) (E a)
-- filterE f = Arr $ \case Just x  => if f x then Nothing else Just x
--                         Nothing => Nothing
-- 
-- export
-- hold : a -> SF (E a) (S a)
-- hold v = mkSFTimeless (\s => dup . fromMaybe s) v
-- 
-- export
-- edge : SF (S Bool) (E ())
-- edge = mkSFTimeless run True
--   where run : Bool -> Bool -> (Bool,Maybe ())
--         run True False = (False,Just ())
--         run _    b     = (b, Nothing)
-- 
-- export
-- when : (a -> Bool) -> SF (C a) (E a)
-- when p = mkSFTimeless run True
--   where run : Bool -> a -> (Bool,Maybe a)
--         run True  y = (p y, Nothing)
--         run False y = 
--           let b = p y
--            in (b, if b then Just y else Nothing)
-- 
-- --------------------------------------------------------------------------------
-- --          Lifting Functions
-- --------------------------------------------------------------------------------
-- 
-- export
-- liftS : {auto l : Liftable KS i} -> Fun l o -> SF i (S o)
-- liftS f = mkSFStateless (applyS l f)
-- 
-- export
-- liftC : {auto l : Liftable KC i} -> Fun l o -> SF i (C o)
-- liftC f = mkSFStateless (applyC l f)
-- 
-- export
-- liftE : {auto l : Liftable KE i} -> Fun l o -> SF i (E o)
-- liftE f = mkSFStateless (applyE l f)

--------------------------------------------------------------------------------
--          Evaluation
--------------------------------------------------------------------------------

weakenSwitch :  {c1,c2 : Causality}
             -> SF_ Ini i o (c2 `and` c2)
             -> SF_ Ini i o (c1 `and` c2)
weakenSwitch {c1 = Dec} {c2 = Dec} sf = sf
weakenSwitch {c1 = Dec} {c2 = Cau} sf = sf
weakenSwitch {c1 = Cau} {c2 = _}   sf = Weaken sf

export
step0 : SF_ Uni i o c -> Sample i -> (SF_ Ini i o c, Sample o)
step0 Id i          = (Id, i)
step0 (Weaken sf) i = let (sf2,o) = step0 sf i in (Weaken sf2, o)
step0 First (x, _)  = (First, x)
step0 Second (_, y) = (Second, y)
step0 (Const x) _   = (Const x, x)
step0 (Arr f) i     = (Arr f, f i)
step0 (Seq c1 c2 ix xo) i = 
  let (ix2,x) = step0 ix i
      (xo2,o) = step0 xo x
   in (Seq c1 c2 ix2 xo2, o)

step0 (Fan c1 c2 asbs ascs) as = 
  let (asbs2,bs) = step0 asbs as
      (ascs2,cs) = step0 ascs as
   in (Fan c1 c2 asbs2 ascs2, (bs,cs))

step0 (Par c1 c2 ascs bsds) (as,bs) = 
  let (ascs2,cs) = step0 ascs as
      (bsds2,ds) = step0 bsds bs
   in (Par c1 c2 ascs2 bsds2, (cs,ds))

step0 (UCPrim f) i = let (node,o) = f i in (IPrim node, o)
step0 (UDPrim f o) i = (IPrim (f i), o)
step0 (RSwitch c1 c2 sf f) i = case step0 sf i of
  (sf2, (o, Nothing)) => (RSwitch c1 c2 sf2 f, o)
  (_  , (o, Just e))  => let (sf2,(o,_)) = step0 (f e) i
                          in (weakenSwitch $ RSwitch c2 c2 sf2 f, o)

step0 (Freezer sf) i =
  let (sf2,o) = step0 sf i
   in (Freezer sf2, (o, sf))

export
dstep0 : SF_ Uni i o Dec -> (Sample i -> SF_ Ini i o Dec, Sample o)
dstep0 (Const v) = (\_ => Const v, v)
dstep0 (Seq Dec c2 isxs xsos) =
  let (fisxs, xs) = dstep0 isxs
      (sfxsos, os) = step0 xsos xs
   in (\is => Seq Dec c2 (fisxs is) sfxsos, os)

dstep0 (Seq Cau Dec isxs xsos) =
  let (fxsos, os) = dstep0 xsos
   in (\is => let (sfisxs,xs) = step0 isxs is
               in Seq Cau Dec sfisxs (fxsos xs)
      , os)

dstep0 (Fan Dec Dec asbs ascs) =
  let (fasbs,bs) = dstep0 asbs
      (fascs,cs) = dstep0 ascs
   in (\as => Fan Dec Dec (fasbs as) (fascs as), (bs,cs))

dstep0 (Par Dec Dec ascs bsds) =
  let (fascs,cs) = dstep0 ascs
      (fbsds,ds) = dstep0 bsds
   in (\(as,bs) => Par Dec Dec (fascs as) (fbsds bs), (cs,ds))

dstep0 (UDPrim f o) = (\i => IPrim (f i), o)

dstep0 (Freezer sf) =
  let (f,o) = dstep0 sf
   in (\x => Freezer (f x), (o, sf))

dstep0 (RSwitch Dec Dec sf f) = case dstep0 sf of
  (mksf , (o, Nothing)) => (\i => RSwitch Dec Dec (mksf i) f, o)
  (_ , (o, Just e))  => let (mksf,(o,_)) = dstep0 (f e)
                         in (\i => RSwitch Dec Dec (mksf i) f, o)

dstep0 (Seq Cau Cau _ _) impossible
dstep0 (Fan Cau _ _ _) impossible
dstep0 (Fan Dec Cau _ _) impossible
dstep0 (Par Dec Cau _ _) impossible
dstep0 (Par Cau _ _ _) impossible
dstep0 (RSwitch Cau _ _ _) impossible
dstep0 (RSwitch Dec Cau _ _) impossible

-- export
-- step : TimeSpan -> SF_ Ini i o -> Sample i -> (SF_ Ini i o, Sample o)
-- step _ Id i          = (Id, i)
-- step _ First (x, _)  = (First, x)
-- step _ Second (_, y) = (Second, y)
-- step _ (Const x) _   = (Const x, x)
-- step _ (Arr f) i     = (Arr f, f i)
-- step t (Seq ix xo) i = 
--   let (ix2,x) = step t ix i
--       (xo2,o) = step t xo x
--    in (Seq ix2 xo2, o)
-- 
-- step t (Fan asbs ascs) as = 
--   let (asbs2,bs) = step t asbs as
--       (ascs2,cs) = step t ascs as
--    in (Fan asbs2 ascs2, (bs,cs))
-- 
-- step t (Par ascs bsds) (as,bs) = 
--   let (ascs2,cs) = step t ascs as
--       (bsds2,ds) = step t bsds bs
--    in (Par ascs2 bsds2, (cs,ds))
-- 
-- step t (IPrim n) i = let (n2,o) = stepNode t n i in (IPrim n2, o)
-- 
-- step t (RSwitch sf f) i = case step t sf i of
--   (sf2, (o, Nothing)) => (RSwitch sf2 f, o)
--   (_  , (o, Just e))  => let (sf2,(o,_)) = step0 (f e) i
--                           in (RSwitch sf2 f, o)
-- 
-- step t (Freezer sf) i =
--   let (sf2,o) = step t sf i
--    in (Freezer sf2, (o, freeze sf))
--   where freeze : SF_ Ini as bs -> SF_ Uni as bs
--         freeze Id            = Id
--         freeze First         = First
--         freeze Second        = Second
--         freeze (Const x)     = Const x
--         freeze (Arr f)       = Arr f
--         freeze (Seq x y)     = Seq (freeze x) (freeze y)
--         freeze (Fan x y)     = Fan (freeze x) (freeze y)
--         freeze (Par x y)     = Par (freeze x) (freeze y)
--         freeze (RSwitch x f) = RSwitch (freeze x) f
--         freeze (Freezer x)   = Freezer (freeze x)
--         freeze (IPrim n)     = UPrim (stepNode t n)
-- 
-- --------------------------------------------------------------------------------
-- --          Running Signal Functions
-- --------------------------------------------------------------------------------
-- 
-- export
-- runSF :  SF i o
--       -> IO (Sample i)
--       -> (Sample o -> IO ())
--       -> IO Time
--       -> Fuel
--       -> IO ()
-- runSF sf getI putO time fuel = do
--   (sf', o0) <- step0 sf <$> getI
--   putO o0
--   runSF' sf' 0 fuel
--   where runSF' : SF_ Ini i o -> Time -> Fuel -> IO ()
--         runSF' sf' t Dry      = pure ()
--         runSF' sf' t (More f) = do
--           t1 <- time
--           Just dt <- pure (timeSpan t1 t)
--             | Nothing => putStrLn "Time just went backwards"
--           (sf2, o2) <- step dt sf' <$> getI
--           putO o2
--           runSF' sf2 t1 f
