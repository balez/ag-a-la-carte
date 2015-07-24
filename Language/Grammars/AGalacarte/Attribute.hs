-- * Header
{- GHC version 7.8.3
Author: Florent Balestrieri
-}
-- ** Ghc options
{-# LANGUAGE
      MultiParamTypeClasses
    , FlexibleContexts
    , FlexibleInstances
    , TypeOperators
    , NoMonomorphismRestriction
    , GADTs
    , TypeFamilies
    , OverlappingInstances
    , LambdaCase
    , RankNTypes
    , ConstraintKinds
    , PolyKinds
    , DataKinds
 #-}
-- ** Module
module Language.Grammars.AGalacarte.Attribute where
-- ** Import
import Language.Grammars.AGalacarte.Prelude
import Language.Grammars.AGalacarte.Proxy
import Language.Grammars.AGalacarte.Predicates
import Language.Grammars.AGalacarte.DependentTypes
import Language.Grammars.AGalacarte.Indexed
import Language.Grammars.AGalacarte.IndexedContainer

import GHC.Exts (Constraint)

-- * Attribute
-- ** Attribute declaration
{- an attribute is declared with a label type "l",
a sort : inherited(I) or synthesized(S)
a type which is a bifunctor
and a range which must be a valid range predicate.
-}

class (Bifunctor l)
      => Attribute (l :: *) where
  type Mode l :: I_S
  type Type l (a :: [*]) -- list of attribute labels
              (c :: [*] -> * -> *) -- container
              (n :: *) -- non-terminal
  type Domain l :: Dom [*]

type SynAttr l = (Attribute l, Mode l ~ S)
type InhAttr l = (Attribute l, Mode l ~ I)

domainP :: Attribute l => P l -> P (Domain l)
domainP _ = P

-- ** Modes of attribute computation
data I_S = I | S
type family I_S_Dual (t :: I_S) where
  I_S_Dual I = S
  I_S_Dual S = I

type Inherited = I
type Synthesized = S

synthesizedP :: P S
synthesizedP = P

inheritedP :: P I
inheritedP = P

-- ** Domains
{- The domain of definition of an attribute
is either a (finite) list of non-terminals or or the whole set of types.
this data declaration is only meant to be used with kinds:
the kind of the domain is "Dom [*]".
-}
data Dom list = Over list | Everywhere

type family DomPred (d :: Dom [*]) where
  DomPred Everywhere = Unit
  DomPred (Over p) = Pred p

-- ** Bifunctor
newtype Type' n c a l = Type {fromType :: Type l a c n}

{- the type of an attribute must be a bifunctor with respect
   to the attribute record -}
class Bifunctor l where
  bimap :: (Container c) =>    
    l :# c :# n :#N ->
    Rec r' :~~~> Rec r ->
    Rec r :~~~> Rec r' ->
    Type l r c n -> Type l r' c n
bimap' :: (Bifunctor l, Container c) =>
  Rec r' :~~~> Rec r ->
  Rec r :~~~> Rec r' ->
  Type' n c r l -> Type' n c r' l
bimap' f t = res $ \ p -> Type . bimap p f t . fromType
  where res :: Cont (Type' n c r l -> Type' n c r' l)
                    (l :# c :# n :#N)
        res = ($ proxies)

instance (Bifunctor l, RecBifunctor ls)
         => RecBifunctor (l ': ls) where
  rmap from to (a :& as) = bimap_attr from to a :& rmap from to as

-- ** Family over a predicate
{- "Fam t p n" is only defined on "n" such that "p n" is inhabited.
For those values it is always equal to t.
"p" should be of the form
t1 :- t2 ... :- tn :- Empty
or Unit
the class "IsDomain p" embodies this condition.
-}

-- every attribute can be defined using this family
type family Fam (p :: Dom [*]) n where
  Fam Everywhere n = Type' n
  Fam (Over '[]) n = Const3 ()
  Fam (Over (n ': p)) n = Type' n
  Fam (Over (m ': p)) n = Fam (Over p) n

type FamDefined p n = Fam p n ~ Type' n
type FamTrivial p n = Fam p n ~ Const3 ()
type FamDefinedT p n = Fam p n :~: Type' n

-- *** Case analysis
-- **** FamCase gadt
data FamCase p n where
  FamEverywhere :: FamCase Everywhere n
  FamEmpty :: FamCase (Over '[]) n
  FamEqual :: FamCase (Over (n ': p)) n
  FamDisj :: (Fam (Over (m ': p)) n ~ Fam (Over p) n) =>
    FamCase (Over p) n -> FamCase (Over (m ': p)) n

-- **** FameCaseOf class
class FamCaseOf p n where
  fam_caseofP :: (p :# n :#N) -> FamCase p n
fam_caseof :: FamCaseOf p n => FamCase p n
fam_caseof = fam_caseofP proxies
instance FamCaseOf Everywhere n where
  fam_caseofP _ = FamEverywhere
instance FamCaseOf (Over (n ': p)) n where
  fam_caseofP _ = FamEqual
instance (Fam (Over (m ': p)) n ~ Fam (Over p) n, FamCaseOf (Over p) n)
         => FamCaseOf (Over (m ': p)) n where
  fam_caseofP _ = FamDisj $ fam_caseofP proxies
instance FamCaseOf (Over '[]) n where
  fam_caseofP _ = FamEmpty

-- **** Fam defined or trivial

data FamDefOrTriv d n where
  FamDef :: FamDefined d n => FamDefOrTriv d n
  FamTriv :: FamTrivial d n => FamDefOrTriv d n

is_fam_def_or_triv ::
  FamCase d n ->
  FamDefOrTriv d n
is_fam_def_or_triv = \case
  FamEmpty -> FamTriv
  FamEverywhere -> FamDef
  FamEqual -> FamDef
  FamDisj c -> cons_fam_def_or_triv $ is_fam_def_or_triv c

cons_fam_def_or_triv ::
  (Fam (Over (t ': d)) n ~ Fam (Over d) n) =>
  FamDefOrTriv (Over d) n ->
  FamDefOrTriv (Over (t ': d)) n
cons_fam_def_or_triv = \case
  FamDef -> FamDef
  FamTriv -> FamTriv

-- ** attr
-- *** FamNCase
type FamNCase r n c a l = (FamCase r n, Fam r n c a l)

fam2famNcase :: FamCaseOf p n => Fam p n c a l -> FamNCase p n c a l
fam2famNcase x = (fam_caseof, x)

-- *** Attr
-- constraints
type AttrTrivial l n = (Attribute l, FamTrivial (Domain l) n)
type AttrDefined l n = (Attribute l, FamDefined (Domain l) n)
type AttrCaseOf l n = (Attribute l, FamCaseOf (Domain l) n)

attr_caseof :: AttrCaseOf l n => P l -> AttrCase l n
attr_caseof l = fam_caseofP (domainP l :# proxies)

-- types
type AttrFamNCase l a c n = FamNCase (Domain l) n c a l
type AttrCase l = FamCase (Domain l)
type AttrFam l = Fam (Domain l)
type AttrDefinedT l n = FamDefinedT (Domain l) n

data Attr l (a :: [*]) c s n where
  Attr :: Attribute l => AttrFamNCase l a c n -> Attr l a c (Mode l) n
  AttrDual :: Attribute l => Attr l a c (I_S_Dual (Mode l)) n

fromAttr :: (Attribute l) =>
  Attr l a c s n -> AttrFamNCase l a c n
fromAttr (Attr x) = x

-- restricted type
fromDefined :: (AttrDefined l n) =>
  Attr l a c s n -> Type l a c n
fromDefined = fromType . snd . fromAttr

-- *** inject only def
attr ::
  ( AttrCaseOf l n
  , AttrDefined l n
  ) =>
  Type l a c n -> Attr l a c (Mode l) n
attr x = Attr $ fam2famNcase (Type x)

-- *** inject only triv
attrTrivial ::
  ( AttrCaseOf l n
  , AttrTrivial l n
  ) =>
  Attr l a c (Mode l) n
attrTrivial = Attr $ fam2famNcase $ Const3 ()

-- *** injection: def or triv
{- Inject an attribute type in an attribute only if the
   attribute is defined for that index.
-}

inj_attr ::
  (AttrCaseOf l n) =>
  (AttrDefined l n => Type l a d n) ->
  Attr l a d (Mode l) n
inj_attr t =
  res $ \p -> case is_fam_def_or_triv $ fam_caseofP p of
    FamDef -> attr t
    FamTriv -> attrTrivial
  where
    res = ($ proxies) :: Cont (Attr l a d (Mode l) n) (Domain l :# n :#N)

-- *** Bimap

bimap_famNCase :: (Bifunctor l, Container c) =>
  Rec r' :~~~> Rec r -> Rec r :~~~> Rec r' ->
  FamNCase d n c r l -> FamNCase d n c r' l
bimap_famNCase f t = \case
  (FamEmpty, Const3 ()) -> (FamEmpty, Const3 ())
  (FamEverywhere, x) -> (FamEverywhere, bimap' f t x)
  (FamEqual, x) -> (FamEqual, bimap' f t x)
  (FamDisj c, x) -> case bimap_famNCase f t (c,x) of
    (c',x') -> (FamDisj c', x')

bimap_attr :: (Bifunctor l, Container c) =>
  Rec r' :~~~> Rec r -> Rec r :~~~> Rec r' ->
  Attr l r c x n -> Attr l r' c x n
bimap_attr f t = \case
  Attr x -> Attr $ bimap_famNCase f t x
  AttrDual -> AttrDual

-- ** Coercion

class (Domain l ~ Domain l') => Coerce l l' where
  coerce :: l :# l' :# a :# c :# n :#N ->
    Type l a c n -> Type l' a c n

coerce' :: Coerce l l' => Type' n c a l -> Type' n c a l'
coerce' = res $ \ p (Type x) -> (Type $ coerce p x)
  where res :: Cont (Type' n c a l -> Type' n c a l')
                    (l :# l' :# a :# c :# n :#N)
        res = ($ proxies)

map_fam ::
  FamCase d n ->
  (Type' n c a l -> Type' n c a l') ->
  Fam d n c a l -> Fam d n c a l'
map_fam c m x = case c of
  FamEmpty -> Const3 ()
  FamEverywhere -> m x
  FamEqual -> m x
  FamDisj c -> map_fam c m x

coerceAttrFamNCase :: Coerce l l' =>
  AttrFamNCase l a c n -> AttrFamNCase l' a c n
coerceAttrFamNCase (c,x) = (c, map_fam c coerce' x)

coerceAttr ::
  ( Coerce l l'
  , Attribute l'
  , Mode l ~ Mode l'
  ) =>
  l :# l' :#N -> Attr l a c s n -> Attr l' a c s n
coerceAttr _ = \case
  Attr x -> Attr $ coerceAttrFamNCase x
  AttrDual -> AttrDual

-- the two coercions must be inverses of each other.
type Exchange l l' = (Coerce l l', Coerce l' l)

-- ** Getters
-- We can make recursive constraints synonyms!
type family UseT a (x :: I_S) (ls :: [*]) :: Constraint where
  UseT a x '[] = ()
  UseT a x (l ': ls) = (Attribute l, a :=> l, UseT a x ls)
type UseI a i = UseT a I i
type UseS a s = UseT a S s
type Use a i s = (UseI a i, UseS a s)

type GetAttr ls l s c n = (ls :=> l, AttrDefined l n, Container c)

getP :: (GetAttr ls l s c n) => P l -> Rec ls c s n -> Type l ls c n
get :: (GetAttr ls l s c n) => l -> Rec ls c s n -> Type l ls c n

getP l = fromDefined . getAttrP l
get = getP . proxy

infixr 9 !
(!) = get

-- * Attribute Records
-- ** Record morphisms
type f :~~~> g = forall c (s :: I_S) (n :: *) .
  (Container c) => f c s n -> g c s n

type f :~~~~> g = forall (a ::[*]) . f a :~~~> g a

-- ** Record constructors
-- "l" and "r" are lists of attribute labels.
data RecF (l :: [*]) (a :: [*]) (c :: [*] -> * -> *) (s :: I_S) (n :: *) where
  (:&) :: Attr h a c s n -> RecF t a c s n -> RecF (h ': t) a c s n
  X :: RecF '[] a c s n

-- All record fields should be RecBifunctors to allow the renaming operation.
class RecBifunctor f where
  rmap :: Rec r' :~~~> Rec r  -> Rec r :~~~> Rec r' -> RecF f r :~~~> RecF f r'

instance RecBifunctor '[] where
  rmap from to X = X

-- ** Projections
{- Consider this class closed: there shouldn't be more instances
-}
class ls :=> l where
  getF :: RecF ls :~~~~> Attr l
instance (l ': ls) :=> l where
  getF (head :& _) = head
instance (ls :=> l) => (j ': ls) :=> l where
  getF (_ :& tail) = getF tail

-- ** Appending two records
class AppendRecF a b where
  append :: Arr2_4 (RecF a) (RecF b) (RecF (a :++ b))
instance (AppendRecF b c) => AppendRecF (a ': b) c where
  append (a :& b) c = a :& append b c
instance AppendRecF '[] b where
  append ~X = id

-- ** Fixpoint
{- type label for inherited and synthesized attributes
   Gadt implementing two mutual record types
   it's a sort of fixpoint. We can understand it better when
   we use record functor directly.
-}

data Rec
  (a :: [*])
  (c :: [*] -> * -> *)
  (s :: I_S)
  n
 where
  InhRec :: RecF a a c I n -> Rec a c I n
  SynRec :: RecF a a c S n -> Rec a c S n

mapRec ::
  (RecF f f :~~~> RecF f' f') ->
  Rec f :~~~> Rec f'
mapRec m = \case
  InhRec x -> InhRec $ m x
  SynRec x -> SynRec $ m x

getRec :: (ls :=> l) => Rec ls :~~~> Attr l ls
getRec = \case
  InhRec r -> getF r
  SynRec r -> getF r

getAttrP :: (ls :=> l) => P l -> Rec ls :~~~> Attr l ls
getAttrP _ = getRec
getAttr = getAttrP . proxy

-- ** Modify

type family Rename l l' r where
  Rename l l' '[] = '[]
  Rename l l' (l ': r) = l' ': r
  Rename l l' (h ': r) = h ': Rename l l' r

{- Applying a function on a field and preserving the rest of the tuple.
Only the first element of that type is modified.
We use that to rename a field of a record in ~renameInh1~

If we change attribute "l" to "l'" then the record "r" changes to "r'"
-}
-- no user defined instances allowed
class (r :=> l, r' ~ Rename l l' r) => Modify l l' r r' where
  modify ::
    (Attr l :~~~~> Attr l') ->
    RecF r :~~~~> RecF r'

instance Modify a b (a ': r) (b ': r) where
  modify f (a :& r) = f a :& r
instance ( Modify a b r r'
         , Rename a b (c ': r) ~ (c ': r')
         ) =>
         Modify a b (c ': r) (c ': r') where
  modify f (c :& r) = c :& modify f r

type ModifyBothWays f f' r r' =
  ( Modify f f' r r'
  , Modify f' f r' r)

-- ** Modify a fixedpoint record

modifyRec ::
  ( ModifyBothWays l l' r r'
  , RecBifunctor r
  , RecBifunctor r'
  ) =>
  Attr l' :~~~~> Attr l ->
  Attr l :~~~~> Attr l' ->
  Rec r :~~~> Rec r'
modifyRec from to =
    mapRec $ rmap (modifyRec to from)
                   (modifyRec from to) . modify to
