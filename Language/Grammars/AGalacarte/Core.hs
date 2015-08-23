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
    , UndecidableInstances
    , OverlappingInstances
    , NoMonomorphismRestriction
    , GADTs
    , TypeFamilies
    , LambdaCase
    , RankNTypes
    , EmptyCase
    , RecordWildCards
    , ConstraintKinds
    , PolyKinds
    , DataKinds
 #-}
-- ** Module
module Language.Grammars.AGalacarte.Core where
-- ** Import
import Language.Grammars.AGalacarte.Prelude
import Language.Grammars.AGalacarte.Proxy
import Language.Grammars.AGalacarte.DependentTypes
import Language.Grammars.AGalacarte.Indexed
import Language.Grammars.AGalacarte.IndexedContainer
import Language.Grammars.AGalacarte.Product
import Language.Grammars.AGalacarte.Attribute

import Control.Applicative (liftA2)

-- * Attribute Grammars
-- ** Fragments
{- Local attributes
   for a node whose children are at positions "pos"
   the attribute of the node is of type "node"
   the attribute of its children is of type "child"

NOTE: with memoised containers, there is no need for a
datatype LocAttrs (we can use pairs), but here, since (pos
:-> child) is higher rank, we would need impredicative types
to use a pair instead of LocAttrs.
-}

data LocAttrs child_index node_type child_type n =
  LocAttrs (node_type n) (Prod child_index child_type)

mapLocAttrs :: (n :-> n') -> (c :-> c') ->
  LocAttrs p n c :-> LocAttrs p n' c'
mapLocAttrs nf cf (LocAttrs n pc) = LocAttrs (nf n) (cf `pmap` pc)

{- to be used with an indexed type like (Rec af)
-}
mapLocAttrs2 :: (a :--> a') ->
  LocAttrs p (a i) (a s) :-> LocAttrs p (a' i) (a' s)
mapLocAttrs2 m = mapLocAttrs m m

type IFrag c a af n = forall p.
  c p n -> LocAttrs p (Rec a c I) (Rec a c S) n
        -> LocAttrs p (RecF af a c S) (RecF af a c I) n

-- "r" is the index of the root type
data Frag c l l' r = Frag
 { frule :: forall n . IFrag c l l' n
 , froot :: Rec l c S r -> RecF l' l c I r
 }

-- ** AG
type AGRule c i s r n = forall p.
  c p n -> LocAttrs p i s n -> LocAttrs p s i n

{- A complete attribute grammar -}
data AG c i s r = AG
 { grule :: forall n . AGRule c i s r n
 , groot :: s r -> i r
 }
type AG' c a r = AG c (Rec a c I) (Rec a c S) r

-- Universal AG: can be run on any type of the family
newtype UAG c i s = UAG {fromIAG :: forall r . AG c i s r}

ag :: Frag c a a r -> AG' c a r
ag Frag{..} = AG
  { grule = \c a -> mapLocAttrs SynRec InhRec $ frule c a
  , groot = InhRec . froot
  }

algAG ::
  AG c i s r -> Alg c (IFun i s)
algAG (AG{..}) (c :- pf) = IFun $ \i ->
   let LocAttrs s pi
         = grule c $ LocAttrs i $ pf `papp` pi
    in s

runAG :: AG c i s r -> Expr c r -> s r
runAG g@(AG{..}) t = s
 where
  s = cata (algAG g) t `appIFun` groot s

-- ** Gluing Fragments
{- we can combine two fragments if their parameters are the same
each of them must define distinct attributes.
The projection for the attributes are automatically defined for tuples.
We must ensure that the tuples have only attributes on the first components.
(right parenthesizing).

The order in which we glue fragment doesn't matter.  The
attribute list would be equal up a permutation, and running
the AG would be equivalent up to observations.
-}

glue :: (AppendRecF f1 f2) =>
  Frag c a f1 r ->
  Frag c a f2 r ->
  Frag c a (f1 :++ f2) r
glue (Frag g1 r1) (Frag g2 r2) = Frag
 { frule = \ c i_ss ->
    let LocAttrs s1 i1 = g1 c i_ss
        LocAttrs s2 i2 = g2 c i_ss
     in LocAttrs (append s1 s2) (plift2 append i1 i2)
 , froot = \s -> r1 s `append` r2 s
 }

-- ** Syn and Inh rules
-- *** Proxies for rule parameters
rule_container   = p1
rule_record      = p2
rule_aspect      = p3
rule_label       = p4
rule_constructor = p5
rule_child       = p6 -- only irule
rule_childdom    = child_dom . rule_constructor
rule_index       = constr_index . rule_constructor

-- *** Attribute Projections
-- **** label ! child
type ProjPos d v a = forall l n m .
  ( IsNat m
  , ListAt v m ~ n
  , GetAttr a l S d n
  ) =>
  l -> P m -> Type l a d n

projPos :: Prod p (Rec a d S) -> ProjPos d p a
projPos s l p = get l (pget p s)

-- **** child ! label
{- We provide a flipped version of children attribute projection
 because some users might prefer the syntax child ! attribute
rather than the symmetric.
-}
type FlippedProjPos d v a = forall l n m .
  ( IsNat m
  , ListAt v m ~ n
  , GetAttr a l S d n
  ) =>
  P m -> l -> Type l a d n

unflipProjPos :: (a :# d :# p :#N) -> FlippedProjPos d p a -> ProjPos d p a
unflipProjPos _ (!) l p = p ! l

flipProjPos :: (a :# d :# p :#N) -> ProjPos d p a -> FlippedProjPos d p a
flipProjPos _ (!) p l = l ! p

-- ***** Using rule proxies
flipP x = (rule_record x :# rule_container x :# rule_childdom x :#N)
flipProjPosP x = flipProjPos $ flipP x -- eta expansion is necessary
unflipProjPosP x = unflipProjPos $ flipP x

-- **** getInherited label
type ProjInh d a n = forall l .
  (GetAttr a l I d n) => l -> Type l a d n

projInh :: Rec a d I n -> ProjInh d a n
projInh i l = get l i

-- *** SRule

-- **** Methods types: SynV, SynC
type SynV c d a l =
  Rec a d I (Index c) ->
  c ->
  Prod (ChildDom c) (Rec a d S) ->
  (Type l a d (Index c))

-- curried!
type SynC c d a l =
  Rec a d I (Index c) ->
  c ->
  Curry (ChildDom c) (Rec a d S)
        (Type l a d (Index c))

-- **** Contexts
{- We want "Constructor c" and "SynAttr t" in the class
context because we want the user to be warned when they
haven't defined an instance for their attributes, without
those constraint, the error would shows up later and would be
much harder to understand than a missing instance.

If we put the other constraints in the context of the method rather
than the class, that's because we don't want to have to write
them all the time when defining an instance.
-}

type SRuleCtxt l c =
  ( Constructor c
  , SynAttr l)

type SRuleMethodCtxt l c d a =
  ( GetAttr a l S d (Index c)
  , c :< d)

-- **** SRule
class SRuleCtxt l c => SRule d a (g :: *) l c where
  srule :: SRuleMethodCtxt l c d a => d :# a :# g :# l :# c :#N -> SynC c d a l
  srulev :: SRuleMethodCtxt l c d a => d :# a :# g :# l :# c :#N -> SynV c d a l

  srule x i c = prod_curry $ srulev x i c
  srulev x i c = prod_uncurry $ srule x i c

-- useful to call a rule from another namespace
with_namespace ::
  d :# a :# g :# l :# c :#N ->
  g' ->
  d :# a :# g' :# l :# c :#N
with_namespace = cst2 proxies

-- when a namespace is parameterised with another namespace
with_super :: d :# a :# g s :# l :# c :#N ->
              d :# a :# s :# l :# c :#N
with_super = const proxies

-- **** Choosing between defined and trivial cases
{- we must choose between importing a SRule and a trivial case
according to the type "x" representing "AttrFam l (Index c)"
-}
data SRuleChoice d a g l c where
  SRuleDefined :: (AttrDefined l (Index c), SRule d a g l c
                  ) => SRuleChoice d a g l c
  SRuleTrivial :: (AttrTrivial l (Index c)
                  ) => SRuleChoice d a g l c

class (x ~ AttrFam l (Index c), n ~ Index c)
      => SRuleChoose x n d a g l c where
  srule_choose :: SRuleChoice d a g l c

instance (AttrTrivial l n, n ~ Index c)
         => SRuleChoose (Const3 ()) n d a g l c where
  srule_choose = SRuleTrivial

instance (AttrDefined l n, SRule d a g l c, n ~ Index c)
         => SRuleChoose (Type' n) n d a g l c where
  srule_choose = SRuleDefined

-- **** Syn Type
{- Defining a synthesized attribute alone. -}

type Syn c d a l = forall p n.
  c p n -> Rec a d I n -> Prod p (Rec a d S) -> Attr l a d S n

-- ***** Conversion
{- "syn" builds a singleton attribute -}
syn :: (SynAttr l, Container c) => Syn c c a l -> Frag c a '[l] r
syn srule = Frag
 { frule = \c (LocAttrs i ss)
           -> LocAttrs (srule c i ss :& X)
                       (ppure (container c) $ AttrDual :& X)
 , froot = const (AttrDual :& X)
 }
-- **** SRule' class
type SRuleT' g l c d a = g :# d :#N -> Syn c d a l

class (SynAttr l, a :=> l) => SRule' l c d a (g :: *) where
  srule' :: SRuleT' g l c d a

instance ( SRuleChoose (AttrFam l (Index c)) (Index c) d a g l c
         , SRuleCtxt l c
         , c :< d
         , a :=> l
         , AttrCaseOf l (Index c)
         ) => SRule' l (C c) d a g where
  srule' = res $ \x _ (C c) i s -> case detP (chooseP x) srule_choose of
     SRuleDefined -> attr $ prod_uncurry (srule x i c) s
     SRuleTrivial -> attrTrivial
   where
    res :: Cont (SRuleT' g l (C c) d a) (d :# a :# g :# l :# c :#N)
    res c = c proxies -- Eta expansion is necessary for typechecking
    chooseP :: (d :# a :# g :# l :# c :#N) -> P (SRuleChoice d a g l c)
    chooseP _ = P

instance (SRule' l c d a g, SRule' l c' d a g)
         => SRule' l (c :+: c') d a g where
  srule' = liftA2 sumElim srule' srule'

instance (SynAttr l, a :=> l) => (SRule' l EmptyC d a g) where
  srule' _ = \case{}

-- *** IRule
-- **** Methods types: InhV, InhC
type InhV c d a l k =
  ( ListAt (ChildDom c) k ~ n
  , GetAttr a l I d n
  ) =>
  Rec a d I (Index c) ->
  c ->
  Prod (ChildDom c) (Rec a d S) ->
  (Type l a d n)

type InhC c d a l k =
  ( ListAt (ChildDom c) k ~ n
  , GetAttr a l I d n
  ) =>
  Rec a d I (Index c) ->
  c ->
  Curry (ChildDom c) (Rec a d S)
    (Type l a d n)

-- **** IRule Context
type IRuleCtxt l c =
  ( Constructor c
  , InhAttr l)

-- **** IRule class
class (IRuleCtxt l c) => IRule d a (g :: *) l c (k :: Nat) where
  irule :: (c :< d) => d :# a :# g :# l :# c :# k :#N -> InhC c d a l k  
  irulev :: (c :< d) => d :# a :# g :# l :# c :# k :#N -> InhV c d a l k

  irule x i c = prod_curry $ irulev x i c
  irulev x i c = prod_uncurry $ irule x i c

-- **** Complete IRule with trivial cases
type ChildAttrFam l c k     = AttrFam l (ListAt (ChildDom c) k)
type ChildAttrTrivial l c k = AttrTrivial l (ListAt (ChildDom c) k)
type ChildAttrDefined l c k = AttrDefined l (ListAt (ChildDom c) k)
type ChildAttrCaseOf l c k  = AttrCaseOf l (ListAt (ChildDom c) k)

data IRuleChoice d a g l c k where
  IRuleTrivial ::
    ( ChildAttrTrivial l c k
    , ChildAttrCaseOf l c k) => IRuleChoice d a g l c k
  IRuleDefined ::
    ( ChildAttrDefined l c k
    , IRule d a g l c k
    , ChildAttrCaseOf l c k) => IRuleChoice d a g l c k

class ( x ~ ChildAttrFam l c k, ChildAttrCaseOf l c k
      ) => IRuleMatch x d a g l c (k :: Nat) where
  irule_match :: IRuleChoice d a g l c k

instance ( ChildAttrTrivial l c k
         , ChildAttrCaseOf l c k
         ) => IRuleMatch (Const3 ()) d a g l c k where
  irule_match = IRuleTrivial

instance ( ChildAttrDefined l c k
         , IRule d a g l c k
         , ChildAttrCaseOf l c k
         , n ~ ListAt (ChildDom c) k
         ) => IRuleMatch (Type' n) d a g l c k where
  irule_match = IRuleDefined

-- ***** IRuleChoose
{- We must make sure "k" is used only once in the parameter
list, because we're going to quantify over it using the
Forall constraint family -}

class IRuleChoose d a g l c (k :: Nat) where
  irule_choose :: IRuleChoice d a g l c k
instance (IRuleMatch (ChildAttrFam l c k) d a g l c k)
 => IRuleChoose d a g l c k where
  irule_choose = irule_match

irule_choose_from_dict :: IsNat k =>
  Dict2 (IRuleChoose d a g l c) k ->
  IRuleChoice d a g l c k
irule_choose_from_dict Dict2 = irule_choose

-- **** Inh type
{- Inh defines the rules for the whole inherited attribute family -}
type Inh c d a l = forall p m n k.
  c p m ->
  Rec a d I m ->
  Prod p (Rec a d S) ->
  Prod p (Attr l a d I)
-- ***** Conversions
{- "inh" builds a singleton attribute, from a Inh rule and an
   initialisation function. -}

inh :: (InhAttr l) =>
  Inh c c a l -> (Rec a c S r -> Attr l a c I r) -> Frag c a '[l] r
inh irule init = Frag
  { frule = \c (LocAttrs i ss) ->
                LocAttrs (AttrDual :& X) ((:& X) `pmap` irule c i ss)
  , froot = (:& X) . init
  }

{- inh' does the job of inh with a constant initialisation value -}
inh' :: (InhAttr l) =>
  Inh c c a l -> Attr l a c I r -> Frag c a '[l] r
inh' irule init = inh irule (const init)

-- **** IRule' class
type IRuleT l c d a g = g :# d :#N -> Inh c d a l

class (InhAttr l, a :=> l) => IRule' l c d a (g :: *) where
  irule' :: IRuleT l c d a g

instance ( IRuleCtxt l c
         , Forall (Range (ChildDom c))
                  (IRuleChoose d a g l c)
         , a :=> l
         , c :< d
         ) => IRule' l (C c) d a g where
  irule' gd (C c) i s = ptabT (is_list $ child_dom' c) $
   \k -> res c (k :# gd) $
   \(chooseP :# choiceP :# dom :# y) ->
    case detP choiceP $ irule_choose_from_dict $ pgetDP k dom
            $ forallD chooseP $ range_is_listP dom of
        IRuleDefined -> attr $ prod_uncurry (irule y i c) s
        IRuleTrivial -> attrTrivial
   where
     res :: c -> k :# g :# d :#N ->
            Cont (Attr l a d I (ListAt (ChildDom c) k))
                 ( IRuleChoose d a g l c :#
                   IRuleChoice d a g l c k :#
                   ChildDom c :#
                   d :# a :# g :# l :# c :# k :#N)
     res = cst2 ($ proxies)

instance (IRule' l c d a g, IRule' l c' d a g)
         => IRule' l (c :+: c') d a g where
  irule' = liftA2 sumElim irule' irule'

instance (InhAttr l, a :=> l) => (IRule' l EmptyC d a g) where
  irule' _ = \case{}

-- ** Default rule instances, importing rules
{- the default SRule and IRule can import rules from other grammars
The import list is given by a type family "Import g"
The default grammar, by a type family "Default g"

The import list allows to pick and choose rules from
different grammars, by naming the attributes explicitely,
therefore, only a finite number of rules can be imported this
way.  On the other hand, the default grammar will be resorted
to when all the other possibilities were exhausted: no rule
defined for the label in the current grammar or any of the
imported list.  Note that if the default grammar is extended
with new rules, they would also benefit all the grammars that
use it by default.  -}

-- *** Import and Default

{- all the rules of "Default g" are imported In particular,
the grammar "Copy" implements the automatic propagation of
inherited attributes from parents to children if the
attribute has the same type for both.
-}
type family Default g

-- *** Import specification
-- we can import rules matching an attribute or a constructor
data ImportItem aspect list
 = IA aspect list
 | IC aspect list
 | IAC aspect list list
type Match_Attributes = IA
type Match_Constructors = IC
type Match_Both = IAC

aspectIA :: P (IA g a ': xs) -> P g
aspectIC :: P (IC g a ': xs) -> P g
aspectIAC :: P (IAC g a b ': xs) -> P g

tailIA ::
  P (IA g (l ': ls) ': xs) ->
  P (IA g ls ': xs)
tailIC ::
  P (IC g (c ': cs) ': xs) ->
  P (IC g cs ': xs)
tailIAC_A ::
  P (IAC g (l ': ls) cs ': xs) ->
  P (IAC g ls cs ': xs)
tailIAC_C ::
  P (IAC g ls (c ': cs) ': xs) ->
  P (IAC g ls cs ': xs)

aspectIA  = const P
aspectIC  = const P
aspectIAC = const P
tailIA    = const P
tailIC    = const P
tailIAC_A = const P
tailIAC_C = const P

type family Import g :: [ImportItem * [*]]

importP :: P g -> P (Import g)
importP = const P
importAllP :: P g -> P (Default g)
importAllP = const P

-- *** Union of SRule and IRule
{- The import list works for both IRule and SRule, so we
    package their methods in a union type.
The type "n" is irrelevant for SRule, we use Zero in the instance.
-}
data Rule s l n c d a where
  RuleS :: SynC c d a l -> Rule S l n c d a
  RuleI :: InhC c d a l n -> Rule I l n c d a

-- *** ImportList
class (Attribute l, Mode l ~ s, Constructor c
      ) => ImportList (xs :: [ImportItem * [*]])
                      i s l n c d a where
  import_list ::
    xs :# i :# s :# l :# n :# c :# d :# a :#N ->
    Rule s l n c d a

-- **** SRules
-- ***** Attribute for every constructor
-- "l" matches
instance ( SRuleCtxt l c
         , SRuleMethodCtxt l c d a
         , SRule d a g l c
         ) => ImportList (IA g (l ': ls) ': xs) i S l n c d a where
  import_list (xs :# i :# s :# l :# n :# c :# d :# a :#N)
    = RuleS $ srule (d :# a :# aspectIA xs :# l :# c :#N)

-- ***** Constructor for every attribute
-- "c" matches
instance ( SRuleCtxt l c
         , SRuleMethodCtxt l c d a
         , SRule d a g l c
         ) => ImportList (IC g (c ': cs) ': xs) i S l n c d a where
  import_list (xs :# i :# s :# l :# n :# c :# d :# a :#N)
    = RuleS $ srule (d :# a :# aspectIC xs :# l :# c :#N)

-- ***** Cartesian product of attribute and constructor lists
-- "c" and "l" match.
instance ( SRuleCtxt l c
         , SRuleMethodCtxt l c d a
         , SRule d a g l c
         ) => ImportList (IAC g (l ': ls) (c ': cs) ': xs) i S l n c d a where
  import_list (xs :# i :# s :# l :# n :# c :# d :# a :#N)
    = RuleS $ srule (d :# a :# aspectIAC xs :# l :# c :#N)

-- ***** Default Import
instance ( SRuleCtxt l c
         , SRuleMethodCtxt l c d a
         , SRule d a g l c
         ) => ImportList '[] g S l n c d a where
  import_list (xs :# g :# s :# l :# n :# c :# d :# a :#N)
    = RuleS $ srule (d :# a :# g :# l :# c :#N)

-- **** IRule
-- ***** Attribute for every constructor
-- "l" matches
instance ( IRuleCtxt l c
         , c :< d
         , IRule d a g l c n
         ) => ImportList (IA g (l ': ls) ': xs) i I l n c d a where
  import_list (xs :# i :# s :# l :# n :# c :# d :# a :#N)
    = RuleI $ irule (d :# a :# aspectIA xs :# l :# c :# n :#N)

-- ***** Constructor for every attribute
-- "c" matches
instance ( IRuleCtxt l c
         , c :< d
         , IRule d a g l c n
         ) => ImportList (IC g (c ': cs) ': xs) i I l n c d a where
  import_list (xs :# i :# s :# l :# n :# c :# d :# a :#N)
    = RuleI $ irule (d :# a :# aspectIC xs :# l :# c :# n :#N)  

-- ***** Cartesian product of attribute and constructor lists
-- "c" and "l" match.
instance ( IRuleCtxt l c
         , c :< d
         , IRule d a g l c n
         ) => ImportList (IAC g (l ': ls) (c ': cs) ': xs) i I l n c d a where
  import_list (xs :# i :# s :# l :# n :# c :# d :# a :#N)
    = RuleI $ irule (d :# a :# aspectIAC xs :# l :# c :# n :#N)

-- ***** Default import
instance ( IRuleCtxt l c
         , c :< d
         , IRule d a g l c n
         ) => ImportList '[] g I l n c d a where
  import_list (xs :# g :# s :# l :# n :# c :# d :# a :#N)
    = RuleI $ irule (d :# a :# g :# l :# c :# n :#N)

-- **** Iterating through the lists
-- ***** Next attribute of an IA list
instance ( ImportList (IA g ls ': xs) i s l n c d a
         ) => ImportList (IA g (l' ': ls) ': xs) i s l n c d a where
  import_list (xs :# rest)
    = import_list (tailIA xs :# rest)

-- ***** Next constructor of an IC list
instance ( ImportList (IC g cs ': xs) i s l n c d a
         ) => ImportList (IC g (c' ': cs) ': xs) i s l n c d a where
  import_list (xs :# rest)
    = import_list (tailIC xs :# rest)

-- ***** Next attribute of an IAC list
instance ( ImportList (IAC g ls (c ': cs) ': xs) i s l n c d a
         ) => ImportList (IAC g (l' ': ls) (c ': cs) ': xs) i s l n c d a where
  import_list (xs :# rest)
    = import_list (tailIAC_A xs :# rest)

-- ***** Next constructor of an IAC list
instance ( ImportList (IAC g (l' ': ls) cs ': xs) i s l n c d a
         ) => ImportList (IAC g (l' ': ls) (c' ': cs) ': xs) i s l n c d a where
  import_list (xs :# rest)
    = import_list (tailIAC_C xs :# rest)

-- ***** Next item in the import list
-- ****** IA: Empty list
instance ( ImportList xs i s l n c d a
         ) => ImportList (IA g '[] ': xs) i s l n c d a where
  import_list (xs :# rest)
    = import_list (tailP xs :# rest)
-- ****** IC: Empty list
instance ( ImportList xs i s l n c d a
         ) => ImportList (IC g '[] ': xs) i s l n c d a where
  import_list (xs :# rest)
    = import_list (tailP xs :# rest)
-- ****** IAC: Empty attribute list
instance ( ImportList xs i s l n c d a
         ) => ImportList (IAC g '[] (c' ': cs) ': xs) i s l n c d a where
  import_list (xs :# rest)
    = import_list (tailP xs :# rest)
-- ****** IAC: Empty constructor list
instance ( ImportList xs i s l n c d a
         ) => ImportList (IAC g (l' ': ls) '[] ': xs) i s l n c d a where
  import_list (xs :# rest)
    = import_list (tailP xs :# rest)
-- ****** IAC: Both empty lists 
instance ( ImportList xs i s l n c d a
         ) => ImportList (IAC g '[] '[] ': xs) i s l n c d a where
  import_list (xs :# rest)
    = import_list (tailP xs :# rest)
      
-- *** Default SRule
instance (ImportList (Import g) (Default g) S l Zero c d a)
  => SRule d a g l c where
  srule (d :# a :# g :# l :# c :#N) =
    case import_list $ importP g :# importAllP g :# synthesizedP
                                 :# l :# n0 :# c :# d :# a :#N
     of RuleS rule -> rule

-- *** Default IRule
instance (ImportList (Import g) (Default g) I l n c d a)
  => IRule d a g l c n where
  irule (d :# a :# g :# l :# c :# n :#N) =
    case import_list $ importP g :# importAllP g :# inheritedP
                                 :# l :# n :# c :# d :# a :#N
     of RuleI rule -> rule

-- ** Building fragments
{- we design a generic operator that builds a fragment from
an attribute label, it works with three different types:

a SRule needs just the attribute label
an IRule needs to initialise the attribute for the root,
  either with a function from the synthesized attribute record
  or with a constant.
-}

-- *** Rules
-- Careful, unnecessarily kind polymorphic
class EmptyRule c d a g where
instance EmptyRule c d a g where

-- Product of grammar rules
class (r1 c d a g, r2 c d a g) => PairRules r1 r2 c d a g where
instance (r1 c d a g, r2 c d a g) => PairRules r1 r2 c d a g where

type family Rules (i :: [*]) (s :: [*]) where
  Rules (i ': ii) s = IRule' i `PairRules` Rules ii s
  Rules '[] (s ': ss) = SRule' s `PairRules` Rules '[] ss
  Rules '[] '[] = EmptyRule

-- **** lemmas
{- Those lemmas are used in the definition of pglue and (|->) -}

-- ***** Bringing together inherited and synthesized rules
rules_pair ::
  Rules i '[] c d a g =>
  Rules '[] s c d a g =>
  s :# c :# d :# a :# g :#N ->
  TList i ->
  Dict (Rules i s c d a g)
rules_pair p TNil = Dict
rules_pair p (TCons _ i) =
  case rules_pair p i of Dict -> Dict

-- ***** Splitting inherited and synthesized rules
rules_split ::
  Rules i s c d a g =>
  s :# c :# d :# a :# g :#N ->
  TList i ->
  ( Dict (Rules '[] s c d a g)
  , Dict (Rules i '[] c d a g))
rules_split p TNil = (Dict, Dict)
rules_split p (TCons _ i) =
  case rules_split p i of (Dict, Dict) -> (Dict, Dict)

-- ***** (S) splitting the rules of an appended list
rules_append_s ::
  Rules '[] (s1 :++ s2) c d a g =>
  s2 :# c :# d :# a :# g :#N ->
  TList s1 ->
  ( Dict (Rules '[] s1 c d a g)
  , Dict (Rules '[] s2 c d a g))
rules_append_s p TNil = (Dict, Dict)
rules_append_s p (TCons _ s1) =
  case rules_append_s p s1 of
   (Dict, Dict) -> (Dict, Dict)

-- ***** (I) splitting the rules of an appended list
rules_append_i ::
  Rules (i1 :++ i2) '[] c d a g =>
  i2 :# c :# d :# a :# g :#N ->
  TList i1 ->
  ( Dict (Rules i1 '[] c d a g)
  , Dict (Rules i2 '[] c d a g))
rules_append_i p TNil = (Dict, Dict)
rules_append_i p (TCons _ i1) =
  case rules_append_i p i1 of
   (Dict, Dict) -> (Dict, Dict)

-- ***** Parallel append
{- we first split, append separately inherited an synthesized rules
  and then combine.
-}
rules_append ::
  Rules (i1 :++ i2) (s1 :++ s2) c d a g =>
  i1 :# i2 :# s1 :# s2 :# c :# d :# a :# g :#N ->
  TList i1 ->
  TList i2 ->
  TList s1 ->
  ( Dict (Rules i1 s1 c d a g)
  , Dict (Rules i2 s2 c d a g))
rules_append (i1' :# i2' :# s1' :# s2' :# r) i1 i2 s1 =
  case rules_split (appendP s1' s2' :# r) (appendT i1 i2) of
    (Dict,Dict) ->
      case ( rules_append_i (i2' :# r) i1
           , rules_append_s (s2' :# r) s1) of
        ((Dict,Dict),(Dict,Dict)) ->
          ( rules_pair (s1' :# r) i1
          , rules_pair (s2' :# r) i2)

-- *** PFrag
{-
 - i :: list of attribute labels that must have a IRule instance
 - s ::  list of attribute labels that must have a SRule instance
 - c :: container of the expression on which the grammar is ultimately run
 - a :: attribute record on which the rules of i and s lists must apply
 - r :: the renamed attribute record which will be used in practice
 - f :: the attributes computed by this fragment
 - n :: the non-terminal of the expression on which to run this fragment.
-}
newtype PFrag i s c a r f n = PFrag {fromPFrag :: forall g .
  Rules i s c c a g => P g -> Frag c r f n}

{- In the library, the only way to use a PFrag is to execute the grammar.
Therefore we keep universal quantification for all fragments,
only when executing the grammar do we need to give the proxy.
-}
run :: (Rules i s c c a' g) =>
  g -> PFrag i s c a' a a n -> Expr c n -> Rec a c 'S n
run g f = runAG $ ag $ fromPFrag f (proxy g)

pfrag_syn :: (SynAttr l, Container c) =>
  l -> PFrag '[] '[l] c a a '[l] n
pfrag_syn l = PFrag $ \ g -> syn $ srule' $ g :# proxies

pfrag_inh :: (InhAttr l) =>
  (Rec a c S n -> Attr l a c I n) ->
  PFrag '[l] '[] c a a '[l] n
pfrag_inh init = PFrag $ \g -> inh (irule' $ g :# proxies) init

-- *** MkFrag
type family MkFragT t c a r n where
  MkFragT (PFrag i s c a r l n) c a r n = (PFrag i s c a r l n)
  MkFragT (Rec a c S n -> Attr l a c I n) c a a n = PFrag '[l] '[] c a a '[l] n
  MkFragT (Attr l a c I n) c a a n = PFrag '[l] '[] c a a '[l] n
  MkFragT l c a a n = PFrag '[] '[l] c a a '[l] n

class MkFrag t c a r n where
  frag :: (MkFragT t c a r n ~ PFrag i s c a r l n)
         => t -> PFrag i s c a r l n

-- Thanks to this instance, we use only one glue operator: "&"
instance (MkFragT (PFrag i s c a r l n) c a r n
         ~ PFrag i s c a r l n
         , c ~ c', a ~ a', r ~ r', n ~ n'
         ) => MkFrag (PFrag i s c a r l n) c' a' r' n' where
  frag = id

instance ( SynAttr l
         , Container c
         , MkFragT l c a a n ~ PFrag '[] '[l] c a a '[l] n
         , a ~ a'
         ) => MkFrag l c a a' n where
  frag = pfrag_syn

instance ( InhAttr l
         , MkFragT (Rec a c S n -> Attr l a c I n) c a a n
           ~ PFrag '[l] '[] c a a '[l] n
         , x ~ Rec a c S n, c' ~ c, a' ~ a, a ~ a'', n' ~ n, s ~ S, i ~ I
         ) => MkFrag (x -> Attr l a' c' i n') c a a'' n where
   frag = pfrag_inh

instance ( InhAttr l
         ,  MkFragT (Attr l a c I n) c a a n
            ~ PFrag '[l] '[] c a a '[l] n
         , c' ~ c, a' ~ a, a'' ~ a, n' ~ n, s ~ I)
         => MkFrag (Attr l a' c' s n') c a a'' n where
   frag = pfrag_inh . const

pglue ::
  ( AppendRecF f1 f2
  , IsList i1, IsList i2, IsList s1) =>
  PFrag i1 s1 c a r f1 n ->
  PFrag i2 s2 c a r f2 n ->
  PFrag (i1 :++ i2) (s1 :++ s2) c a r (f1 :++ f2) n
pglue p1@(PFrag f1) p2@(PFrag f2) = PFrag $ \ g ->
  let p@(i1 :# i2 :# s1 :# _) = prox p1 p2 g
  in case rules_append p (is_list i1) (is_list i2) (is_list s1) of
       (Dict,Dict) -> f1 g `glue` f2 g
  where
    prox ::
      PFrag i1 s1 c a r f1 n ->
      PFrag i2 s2 c a r f2 n ->
      P g -> (i1 :# i2 :# s1 :# s2 :# c :# c :# a :# g :#N)
    prox = cst3 proxies

infix 2 `as`, `asAttr`, `with`, `withAttr`
infixr 1 &
x & y = frag x `pglue` frag y

asAttr :: Attr l a c s n -> l -> Attr l a c s n
x `asAttr` t = x

as ::
  ( AttrCaseOf l n
  , AttrDefined l n
  ) =>
  Type l a c n -> l -> Attr l a c (Mode l) n
x `as` t = attr x `asAttr` t

with = flip as
withAttr = flip asAttr

-- ** Renaming attributes
{- To reuse a fragment more than once in a AG, we must rename
the attributes it uses and produces. Otherwise the leftmost
in the attribute record will override its homonyms.
-}
rename :: (RecBifunctor f', Container c) =>
  (Rec a' :~~~> Rec a) ->
  (Rec a :~~~> Rec a') ->
  (RecF f :~~~~> RecF f') ->
  Frag c a f r ->
  Frag c a' f' r
rename from_a to_a to_f (Frag rule root) = Frag
 { frule = \c -> mapLocAttrs2 (rmap from_a to_a . to_f)
                 . rule c . mapLocAttrs2 from_a
 , froot = rmap from_a to_a . to_f . root . from_a
 }

{- When working with the SRule and IRule classes, we don't
have access to the concrete attribute record type. The following
function allows to rename exactly one attribute.
-}

type RenameCtxt l l' r r' f f' =
  ( ModifyBothWays l l' r r'
  , Modify l l' f f'
  , Attribute l
  , Attribute l'
  , Mode l ~ Mode l'
  , RecBifunctor r
  , RecBifunctor r'
  , RecBifunctor f'
  , Exchange l l')

rename1 :: (RenameCtxt l l' r r' f f', Container c) =>
  l -> l' ->
  Frag c r  f :->
  Frag c r' f'
rename1 l l' =
  rename (modifyRec (coerceAttr to) (coerceAttr from))
         (modifyRec (coerceAttr from) (coerceAttr to))
         (modify (coerceAttr to))
  where
    to = l # l' # N
    from = l' # l # N


infix 9 |->
(|->) :: (RenameCtxt l l' r r' f f', Container c) =>
  l -> l' ->
  PFrag i s c a r  f :->
  PFrag i s c a r' f'
(|->) l l' (PFrag f) = PFrag $ rename1 l l' . f

renaming = flip ($)

{- note: (.) is exported with fixity 9 by the prelude, we must lower it.
to avoid parentheses around |-> pairs when composing them.
This is done as a local binding in the following example: -}

renaming_example f a b c d m n =
  f `renaming`  (a |-> b . c |-> d . m |-> n)
  where infixr 8 .
        (.) = (Prelude..)
