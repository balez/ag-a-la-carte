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
    , GADTs
    , TypeFamilies
    , LambdaCase
    , RankNTypes
    , EmptyCase
    , ConstraintKinds
    , PolyKinds
    , DataKinds
 #-}
-- ** Module
module Language.Grammars.AGalacarte.Rule.Chain where
-- ** Import
import Language.Grammars.AGalacarte.Prelude
import Language.Grammars.AGalacarte.Proxy
import Language.Grammars.AGalacarte.DependentTypes
import Language.Grammars.AGalacarte.Indexed
import Language.Grammars.AGalacarte.IndexedContainer
import Language.Grammars.AGalacarte.Product
import Language.Grammars.AGalacarte.Attribute
import Language.Grammars.AGalacarte.Core
import Language.Grammars.AGalacarte.Rule.Collect

import Data.Maybe (fromMaybe)

-- * Chain Rule
{- The chain rules are defined for a pair of inherited and
synthesized attributes of the same type. They're defined only
on the productions such that:
 - both attributes are defined for the constructor
 - for all children (if any) both attributes are either both trivial or
     both defined.
 - all the chain attributes (inherited, synthesized, for the constructor and its children)
   have the same type.

If all the previous conditions hold, then the chain rules pass the
inherited attribute to the leftmost child of a production for
which the attributes are defined. This child's 
synthesized attribute is then inherited by the next sibling on the right
which has both attributes, and so on until the rightmost child that has both attributes
returns its synthesized attribute which is passed on as the constructor's
attribute value. -}

-- The aspect is parameterised by the attributes
data Chain (i :: *) (s :: *) = Chain
type ChainAspect i s cs = IAC (Chain i s) '[i, s] cs

-- *** equal or trivial attribute
data EqualOrTrivial l a c t n where
  EOT_Trivial ::
    AttrTrivial l n
    => EqualOrTrivial l a c t n
  EOT_Equal ::
    ( AttrDefined l n
    , t ~ Type l a c n
    ) => EqualOrTrivial l a c t n

class ( x ~ AttrFam l n
      ) => EqualOrTrivialMatch l a c t (n :: *) x where
  equal_or_trivial_match :: EqualOrTrivial l a c t n

instance
  ( AttrTrivial l n
  ) => EqualOrTrivialMatch l a c t n (Const3 ()) where
  equal_or_trivial_match = EOT_Trivial

instance
  ( t ~ Type l a c n
  , AttrDefined l n
  ) => EqualOrTrivialMatch l a c t n (Type' n) where
  equal_or_trivial_match = EOT_Equal

-- **** Dictionary for the children's condition
class IsEqualOrTrivial l a c t (n :: *) where
  is_equal_or_trivial :: EqualOrTrivial l a c t n

instance (EqualOrTrivialMatch l a c t n (AttrFam l n))
 => IsEqualOrTrivial l a c t n where
  is_equal_or_trivial = equal_or_trivial_match

is_equal_or_trivial_from_dict ::
  Dict2 (IsEqualOrTrivial l a c t) :->
  EqualOrTrivial l a c t
is_equal_or_trivial_from_dict Dict2 = is_equal_or_trivial

-- *** Chainable
{- i, s: the inherited and synthesized attributes of the chain rule
   a, c: the attribute record and container of the rules
   t: the type of i and s when they're defined
   n: the non-terminal of the child
-}

class Chainable c a i s t n where
  chainable :: (EqualOrTrivial i a c t :* EqualOrTrivial s a c t) n

instance ( IsEqualOrTrivial i a c t n
         , IsEqualOrTrivial s a c t n
         ) => Chainable c a i s t n where
  chainable = is_equal_or_trivial :* is_equal_or_trivial

chainable_from_dict ::
  Dict2 (Chainable c a i s t) :->
  (EqualOrTrivial i a c t :* EqualOrTrivial s a c t)
chainable_from_dict Dict2 = chainable

-- *** Rule context
type ChainCtxt d a li ls c =
  ( AttrDefined li (Index c)
  , AttrDefined ls (Index c)
  , Type li a d (Index c) ~ Type ls a d (Index c)
  , Forall (ChildDom c)
      (Chainable d a li ls (Type li a d (Index c)))
  , Use a '[li] '[ls]
  )

-- *** IRule
{- if there is a previous child with both attribute, we
   inherit from his synthesized attribute
  otherwise, we inherit from our parent.
-}

instance
  ( IRuleCtxt li c
  , ChainCtxt d a li ls c
  , Type li a d (ListAt (ChildDom c) k)
    ~ Type ls a d (Index c)
  , IsNat k
  ) => IRule d a (Chain li ls) li c k where
  irulev x i c s =
    fromMaybe (getP li i) $ pred_in_chain k chain_syn
   where
    k = is_nat $ rule_child x
    li = rule_label x
    ls = iP1 $ rule_aspect x 
    chain_syn = pzip syn vchainable
    vchainable = chainable_from_dict `pmap`
                 forallD (chainableP x) dom_list
    syn = pmap (getAttrP ls) s
    dom_list = child_dom_list $ proxy c
    chainableP ::  d :# a :# Chain li ls :# li :# c :# k :#N ->
      P (Chainable d a li ls (Type li a d (Index c)))
    chainableP _ = P
-- **** Find the previous suitable sibling
pred_in_chain ::
  TNat n ->
  Prod ts  (Attr ls a d S
           :* EqualOrTrivial li a d t
           :* EqualOrTrivial ls a d t) ->
  Maybe t  
pred_in_chain n v = case n of
  TZero -> Nothing
  TSucc n -> case pgetT n v of
    (x :* EOT_Equal :* EOT_Equal) -> Just $ fromDefined x
    _ -> pred_in_chain n v

-- *** SRule
-- **** Precondition: at least one child is defined with the same type
data HasEqualAttr l a d c where
  HasEqualAttr ::
    ( AttrDefined l n
    , Type l a d n ~ Type l a d (Index c)
    , n ~ ListAt (ChildDom c) k
    , IsNat k)
    => P k -> HasEqualAttr l a d c

{- we must derive an existential statement
ns is used to continue the search if the match fails on "n"
-}
class (x ~ AttrFam l (ListAt (ChildDom c) k)
      , IsNat k
      , Forall ks IsNat)
    => HasEqualAttrMatch l a d c (ks :: [Nat]) (k :: Nat) x where
  equal_attr_match :: k :# ks :#N -> HasEqualAttr l a d c

instance
  ( AttrDefined l n
  , Type l a d n ~ Type l a d (Index c)
  , n ~ ListAt (ChildDom c) k
  , IsNat k
  , Forall ks IsNat
  ) => HasEqualAttrMatch l a d c ks k (Type' n) where
  equal_attr_match (k :#_) = HasEqualAttr k

-- if the match failed, search another "n"
instance
  ( HasEqualAttrMatch l a d c ks k2 x
  , AttrTrivial l (ListAt (ChildDom c) k1)
  , IsNat k1
  , IsNat k2
  , Forall ks IsNat
  ) => HasEqualAttrMatch l a  d c (k2 ': ks) k1 (Const3 ()) where
  equal_attr_match (_ :# k2_ks :#N) =
    equal_attr_match (headP k2_ks :# tailP k2_ks :#N)

class HasEqualChildAttr l a d c where
  has_equal_child_attr :: l :# a :# d :# c :#N -> HasEqualAttr l a d c

instance
  ( HasEqualAttrMatch l a d c (Range (ChildDom c)) Zero (AttrFam l n)
  , n ~ ListAt (ChildDom c) Zero
  ) => HasEqualChildAttr l a d c where
  has_equal_child_attr x = equal_attr_match (n_ns (p4 x))
    where n_ns :: P c -> Zero :# Range (ChildDom c) :#N
          n_ns _ = proxies

-- **** SRule
instance
  ( SRuleCtxt ls c
  , ChainCtxt d a li ls c
  , HasEqualChildAttr ls a d c
  , AttrDefined ls (Index c)
  ) => SRule d a (Chain li ls) ls c where
  srulev x i c s = case has_equal_child_attr ladc of
    HasEqualAttr n ->
      last_in_chain chain_syn (fromDefined $ pget n syn)
   where
    ladc = ls :# rule_record x :# rule_container x :# rule_constructor x :#N
    ls = iP1 $ rule_aspect x 
    chain_syn = pzip syn vchainable
    vchainable = chainable_from_dict `pmap`
                 forallD (chainableP x) dom_list
    syn = pmap (getAttrP ls) s
    dom_list = child_dom_list $ proxy c
    chainableP ::  d :# a :# Chain li ls :# ls :# c :#N ->
      P (Chainable d a li ls (Type ls a d (Index c)))
    chainableP _ = P

-- -- **** Find the last suitable child
last_in_chain ::
  Prod ts  (Attr ls a d S
           :* EqualOrTrivial li a d t
           :* EqualOrTrivial ls a d t) ->
  t -> t
last_in_chain E x = x
last_in_chain ((x :* EOT_Equal :* EOT_Equal) :. xs) y =
  last_in_chain xs (fromDefined x)
last_in_chain (_ :. xs) y = last_in_chain xs y

