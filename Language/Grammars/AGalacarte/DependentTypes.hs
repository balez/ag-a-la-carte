-- * Header
{- GHC version 7.8.3
Author: Florent Balestrieri
-}
-- ** Ghc options
{-# LANGUAGE
      MultiParamTypeClasses
    , FlexibleContexts
    , TypeOperators
    , UndecidableInstances
    , OverlappingInstances
    , NoMonomorphismRestriction
    , GADTs
    , TypeFamilies
    , FlexibleInstances
    , LambdaCase
    , RankNTypes
    , EmptyCase
    , RecordWildCards
    , ConstraintKinds
    , PolyKinds
    , DataKinds
 #-}

-- ** Module
module Language.Grammars.AGalacarte.DependentTypes where
-- ** Import
import Language.Grammars.AGalacarte.Prelude
import Language.Grammars.AGalacarte.Proxy
import Language.Grammars.AGalacarte.Predicates
import GHC.Exts (Constraint)

-- * Dependent types
-- *** Existential
-- data Exist t where
--   Exist :: t x -> Exist t
-- *** Dependent sum
data DSum a b where
  DSum :: a x -> b x -> DSum a b
-- *** Type natural
data Nat = Zero | Succ Nat
type N0 = Zero
type N1 = Succ N0
type N2 = Succ N1
type N3 = Succ N2
type N4 = Succ N3
type N5 = Succ N4
type N6 = Succ N5
type N7 = Succ N6
type N8 = Succ N7
type N9 = Succ N8

data TNat (n :: Nat) where
  TZero :: TNat Zero
  TSucc :: TNat n -> TNat (Succ n)

class IsNat n where
  is_nat :: P n -> TNat n
instance IsNat Zero where
  is_nat _ = TZero
instance IsNat n => IsNat (Succ n) where
  is_nat p = TSucc $ is_nat $ predP p

-- **** Proxies
predP :: P (Succ n) -> P n
succP :: P n -> P (Succ n)

predP  = const P
succP  = const P

n0 :: P Zero
n0 = P
n1 = succP n0
n2 = succP n1
n3 = succP n2
n4 = succP n3
n5 = succP n4
n6 = succP n5
n7 = succP n6
n8 = succP n7
n9 = succP n8

-- ***** lemmas

succ_fun :: a :~: b -> Succ a :~: Succ b
succ_fun Refl = Refl

-- **** Plus

type family (+) a b where
  Zero + b = b
  Succ a + b = Succ (a + b)
data PlusRel a b c where
  PlusZero :: PlusRel Zero b b
  PlusSucc :: PlusRel a b c -> PlusRel (Succ a) b (Succ c)

plus_zero_right :: TNat a -> (a + Zero) :~: a
plus_zero_right TZero = Refl
plus_zero_right (TSucc a) = case plus_zero_right a of Refl -> Refl

plus_succ_right :: TNat a -> TNat b -> (a + Succ b) :~: Succ (a + b)
plus_succ_right TZero b = Refl
plus_succ_right (TSucc a) b = case plus_succ_right a b of Refl -> Refl

plus_sym :: TNat a -> TNat b -> (a + b) :~: (b + a)
plus_sym a TZero = plus_zero_right a
plus_sym a (TSucc b) = plus_succ_right a b
                      `equal_trans` succ_fun (plus_sym a b)

-- **** Less than
data Leq a b where
  LeqZ :: Leq Zero b
  LeqS :: Leq a b -> Leq (Succ a) (Succ b)

class a :<=: b where
  leq :: a :# b :# N -> Leq a b
instance Zero :<=: b where
  leq _ = LeqZ
instance (a :<=: b) => Succ a :<=: Succ b where
  leq (a :# b :# N) = LeqS $ leq $ predP a :# predP b :# N

type a :<: b = Succ a :<=: b

leq_refl :: TNat a -> Leq a a
leq_refl TZero = LeqZ
leq_refl (TSucc a) = LeqS (leq_refl a)

leq_antisym :: Leq a b -> Leq b a -> a :~: b
leq_antisym LeqZ LeqZ = Refl
-- leq_antisym LeqZ (LeqS b) = impossible
-- leq_antisym (LeqS a) LeqZ = impossible
leq_antisym (LeqS a) (LeqS b) =
  succ_fun $ leq_antisym a b

leq_trans :: Leq a b -> Leq b c -> Leq a c
leq_trans LeqZ _ = LeqZ
--leq_trans (LeqS a) LeqZ = impossible
leq_trans (LeqS a) (LeqS b)  = LeqS $ leq_trans a b

leq_succ_right :: Leq a b -> Leq a (Succ b)
leq_succ_right LeqZ = LeqZ
leq_succ_right (LeqS q) = LeqS (leq_succ_right q)

leq_pred :: Leq (Succ a) (Succ b) -> Leq a b
leq_pred = error "leq_pred"

leq_contradiction :: Leq a b -> Leq (Succ b) a -> x
--leq_contradiction LeqZ LeqZ = impossible
--leq_contradiction LeqZ (LeqS b) = impossible
--leq_contradiction (LeqS a) LeqZ = impossible
leq_contradiction (LeqS a) (LeqS b) = leq_contradiction a b

-- ***** Equal or right succ
data Leq2 a b where
  LeqRefl :: Leq2 a a
  LeqLess :: Leq2 a b -> Leq2 a (Succ b)

leq_to_leq2 :: Leq a b -> TNat b -> Leq2 a b
leq_to_leq2 LeqZ b = leq2_zero b
leq_to_leq2 (LeqS a) (TSucc b) = leq2_succ $ leq_to_leq2 a b

leq2_zero :: TNat b -> Leq2 Zero b
leq2_zero TZero = LeqRefl
leq2_zero (TSucc b) = LeqLess (leq2_zero b)

leq2_succ :: Leq2 a b -> Leq2 (Succ a) (Succ b)
leq2_succ = \case
  LeqRefl -> LeqRefl
  LeqLess q -> LeqLess (leq2_succ q)

leq2_to_leq :: TNat a -> Leq2 a b -> Leq a b
leq2_to_leq a LeqRefl = leq_refl a
leq2_to_leq a (LeqLess q) = leq_succ_right $ leq2_to_leq a q

-- ***** Equal or left succ
data Leq3 a b where
  LeqRefl3 :: Leq3 a a
  LeqLess3 :: Leq3 (Succ a) b -> Leq3 a b

leq3_succ :: Leq3 a b -> Leq3 (Succ a) (Succ b) 
leq3_succ LeqRefl3 = LeqRefl3
leq3_succ (LeqLess3 q) = LeqLess3 $ leq3_succ q

leq3_pred :: Leq3 (Succ a) (Succ b) -> Leq3 a b
leq3_pred LeqRefl3 = LeqRefl3
leq3_pred (LeqLess3 q) = LeqLess3 $ leq3_pred q

leq3_zero :: TNat n -> Leq3 Zero n
leq3_zero TZero = LeqRefl3
leq3_zero (TSucc n) = LeqLess3 $ leq3_succ (leq3_zero n)

leq_to_leq3 :: Leq a b -> TNat b -> Leq3 a b
leq_to_leq3 LeqZ b = leq3_zero b
leq_to_leq3 (LeqS a) (TSucc b) = leq3_succ $ leq_to_leq3 a b

leq3_to_leq :: Leq3 a b -> Leq a b
leq3_to_leq = error "leq3_to_leq"

-- **** lemmas
lt_one :: (n :<: Succ Zero) => TNat n -> n :~: Zero
lt_one n = case leq $ indexP (TSucc n) :# n1 :# N of
  LeqS LeqZ -> Refl

lt_zero :: (n :<: Zero) => TNat n -> a
lt_zero n = case leq $ indexP (TSucc n) :# n0 :# N of {}

-- *** Type tuples
-- **** Proxies
fstP :: P '(a,b) -> P a
sndP :: P '(a,b) -> P b
fstP _ = P
sndP _ = P

-- *** Type Lists
{- with DataKinds, we can use type lists like '[] and (a ': b), and '[a,b,c]
of kind [k] -}

-- **** TList
data TList t where
  TNil :: TList '[]
  TCons :: P t -> TList ts -> TList (t ': ts)

singleT x = TCons x TNil

class IsList l where
  is_list :: P l -> TList l

instance IsList '[] where
  is_list _ = TNil
instance IsList t => IsList (h ': t) where
  is_list p = headP p `TCons` is_list (tailP p)

-- **** Proxies

headP :: P (h ': t) -> P h
tailP :: P (h ': t) -> P t
dropP :: P (a :++ b) -> P a -> P b

nilP :: P '[]
consP :: P h -> P t -> P (h ': t)
singleP :: P x -> P '[x]
appendP :: P a -> P b -> P (a :++ b)
snocP :: P h -> P t -> P (t :++ '[h])

headP _ = P
tailP _ = P
dropP = cst2 P

nilP = P
consP = cst2 P
singleP = const P
appendP = cst2 P
snocP = cst2 P

-- **** Length
type family Len ts where
  Len '[] = Zero
  Len (t ': ts) = Succ (Len ts)

len :: TList ts -> TNat (Len ts)
len TNil = TZero
len (TCons t ts) = TSucc (len ts)

lenP :: P ts -> P (Len ts)
lenP _ = P

-- **** Type list indexing
type family ListAt (ts :: [k]) (n :: Nat) where
  ListAt (t ': ts) Zero = t
  ListAt (t ': ts) (Succ n) = ListAt ts n

-- **** Map
type family TMap f ts where
  TMap f '[] = '[]
  TMap f (t ': ts) = f t ': TMap f ts

map_is_list :: P f -> TList ts -> TList (TMap f ts)
map_is_list f = \case
  TNil -> TNil
  TCons t ts -> TCons P $ map_is_list f ts

map_is_listP :: IsList ts => P f -> P ts -> TList (TMap f ts)
map_is_listP f ts = map_is_list f (is_list ts)

map_preserve_length :: P f -> TList ts -> Len (TMap f ts) :~: Len ts
map_preserve_length f = \case
  TNil -> Refl
  TCons t ts -> case map_preserve_length f ts of Refl -> Refl

map_preserve_lengthP :: IsList ts => P f -> P ts -> Len (TMap f ts) :~: Len ts
map_preserve_lengthP f t = map_preserve_length f (is_list t)

-- **** FromTo
{- the problem with this definition, is that the patterns overlap -}

-- b not included
type family FromTo a b where
  FromTo a a = '[]
  FromTo a b = a ': FromTo (Succ a) b

-- **** Interval
--  [a, a+1, ... a+n -1]
type family Interval len init where
  Interval Zero a = '[]
  Interval (Succ n) a = a ': Interval n (Succ a)

-- A relation representing the type family Interval
data IntervalRel len init interval where
  IntervalZero :: IntervalRel Zero a '[]
  IntervalSucc :: IntervalRel n (Succ a) i ->
                  IntervalRel (Succ n) a (a ': i)

-- the function is embedded in the relation
interval_rel ::
  (Interval n a ~ i) =>
  TNat n ->
  a :# i :# N ->
  IntervalRel n a i
interval_rel TZero _ = IntervalZero
interval_rel (TSucc n) (a :# i :# N) =
  IntervalSucc $ interval_rel n (succP a :# tailP i :# N)

--  the relation is embedded in the function.
interval_fun :: IntervalRel n a i -> Interval n a :~: i
interval_fun = \case
  IntervalZero -> Refl
  IntervalSucc i -> case interval_fun i of Refl -> Refl

interval_is_list :: TNat n -> P a -> TList (Interval n a)
interval_is_list TZero _ = TNil
interval_is_list (TSucc n) a = TCons a $ interval_is_list n (succP a)

-- **** Range
type Range ts = Interval (Len ts) Zero
rangeP :: P ts -> P (Range ts)
rangeP = const P

range_is_list :: TList ts -> TList (Range ts)
range_is_list t = interval_is_list (len t) n0
range_is_listP = range_is_list . is_list

-- **** Append
-- Type families can be of any kind!
infixr 2 :++
type family (a :++ b) where
  (x ': a) :++ b = x ': (a :++ b)
  '[] :++ b = b

appendT :: TList a -> TList b -> TList (a :++ b)
appendT TNil b = b
appendT (TCons x a) b = TCons x $ appendT a b

-- ***** append_nil
append_nil :: TList a -> (a :++ '[]) :~: a
append_nil TNil = Refl
append_nil (TCons t ts) = case append_nil ts of Refl -> Refl

-- ***** append_snoc ::
type Snoc xs y = xs :++ '[y]
append_snoc ::
  TList xs ->
  y :# ys :# N ->
  (Snoc xs y :++ ys) :~: (xs :++ (y ': ys))
append_snoc = undefined

-- **** Prefix

class IsPrefix a b where
  is_prefix :: a :# b :# N -> Prefix a b
instance IsPrefix '[] b where
  is_prefix _ = Prefix P
instance IsPrefix a b => IsPrefix (x ': a) (x ': b)  where
  is_prefix (a :# b :# N) =
    case is_prefix (tailP a :# tailP b :# N) of
      Prefix p -> Prefix p

data Prefix a b where
  Prefix :: (b ~ (a :++ x)) => P x -> Prefix a b

-- **** Suffix

class IsSuffix a b where
  is_suffix :: a :# b :# N -> Suffix a b
instance IsSuffix b b where
  is_suffix _ = Suffix nilP
instance IsSuffix a b => IsSuffix a (x ': b)  where
  is_suffix (a :# b :# N) =
    case is_suffix (a :# tailP b :# N) of
      Suffix p -> Suffix (consP P p)

data Suffix a b where
  Suffix :: (b ~ (x :++ a)) => P x -> Suffix a b

-- **** Pred
type family Pred ts where
  Pred '[] = Empty
  Pred (t ': ts) = Equal t :\/ Pred ts

-- ***** Elem
-- A proof that a type is inside a type list.
data Elem n ns where
  ElemHead :: Elem n (n ': ns)
  ElemTail :: Elem n ns -> Elem n (m ': ns) -- it can also match Elem n (n ': ns)

split_elem :: TList a -> P b -> Elem x (a :++ x ': b)
split_elem a b = case a of
  TNil -> ElemHead
  TCons x a' -> ElemTail $ split_elem a' b

-- from the proof Elem n ns, we compute a proof in the
-- interpretation (Pred ns) n
elemP :: Elem n ns -> Pred ns n
elemP = \case
  ElemHead -> DisjLeft Refl
  ElemTail p -> DisjRight (elemP p)

-- ****** Membership class
class n :<- ns where
  is_elem :: Elem n ns

instance n :<- (n ': ns) where
  is_elem = ElemHead
instance (n :<- ns) => n :<- (m ': ns) where
  is_elem = ElemTail is_elem


-- *** Sums (variants)
data Sum ts where
  InjL :: t -> Sum (t ': ts)
  InjR :: Sum ts -> Sum (t ': ts)

-- **** Union of predicates
data Any ts x where
  AnyL :: x t -> Any (t ': ts) x
  AnyR :: Any ts x -> Any (t ': ts) x

-- *** Constraint quantification
{- Using type lists we can universally quantify constraints
   over a finite set. Note I do the same again with type family
   "Rules" later.
  This is usefully kind-polymorphic. We use it both with
  [*] and [Nat] for instance.
-}

type family Forall ts c :: Constraint where
  Forall '[] c = ()
  Forall (t ': ts) c = (c t, Forall ts c)

-- **** Existential
-- how can we infer that like Forall?
class Exist ts c where
  exist :: Any ts (Dict2 c)
  
