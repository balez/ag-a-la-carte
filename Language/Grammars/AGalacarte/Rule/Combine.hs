-- * Header
{- GHC version 7.8.3
Author: Florent Balestrieri
-}
-- ** Ghc options
{-# LANGUAGE
      MultiParamTypeClasses
    , FlexibleContexts
    , FlexibleInstances
    , UndecidableInstances
    , OverlappingInstances
    , TypeFamilies
    , ConstraintKinds
    , TypeOperators
    , DataKinds
    , GADTs
 #-}
-- ** Module
module Language.Grammars.AGalacarte.Rule.Combine where
-- ** Imports
import Language.Grammars.AGalacarte.Prelude
import Language.Grammars.AGalacarte.Proxy
import Language.Grammars.AGalacarte.DependentTypes
import Language.Grammars.AGalacarte.Indexed
import Language.Grammars.AGalacarte.IndexedContainer
import Language.Grammars.AGalacarte.Product
import Language.Grammars.AGalacarte.Attribute
import Language.Grammars.AGalacarte.Core

import Language.Grammars.AGalacarte.Rule.Collect

-- * Combine
{- Combine is like Collect without the monoid identity.  The
combine rule is defined for a synthesized attribute that has
a binary operator, defined by the class instance "BinOp".  It
only applies to constructors for which the attribute is
defined and whose children either do not have this attribute,
or if they have it, it must be convertible to the same type
as the constructor's through a "Convert" instance. There must
be at least one such children.  -}

-- ** Convertible Child Attribute
{- this is similar to the conditions of Chain, except that
we use convertibility rather than equality -}

-- Precondition: at least one child is defined with a convertible type
data HasConvertAttr l a d c where
  HasConvertAttr ::
    ( AttrDefined l n
    , Convert (Type l a d n) (Type l a d (Index c))
    , n ~ ListAt (ChildDom c) k
    , IsNat k)
    => P k -> HasConvertAttr l a d c

{- we must derive an existential statement
ns is used to continue the search if the match fails on "n"
-}
class (x ~ AttrFam l (ListAt (ChildDom c) k)
      , IsNat k
      , Forall ks IsNat)
    => HasConvertAttrMatch l a d c (ks :: [Nat]) (k :: Nat) x where
  convert_attr_match :: k :# ks :#N -> HasConvertAttr l a d c

instance
  ( AttrDefined l n
  , Convert (Type l a d n) (Type l a d (Index c))
  , n ~ ListAt (ChildDom c) k
  , IsNat k
  , Forall ks IsNat
  ) => HasConvertAttrMatch l a d c ks k (Type' n) where
  convert_attr_match (k :#_) = HasConvertAttr k

-- if the match failed, search another "n"
instance
  ( HasConvertAttrMatch l a d c ks k2 x
  , AttrTrivial l (ListAt (ChildDom c) k1)
  , IsNat k1
  , IsNat k2
  , Forall ks IsNat
  ) => HasConvertAttrMatch l a  d c (k2 ': ks) k1 (Const3 ()) where
  convert_attr_match (_ :# k2_ks :#N) =
    convert_attr_match (headP k2_ks :# tailP k2_ks :#N)

-- The constructor has at least one child whose attribute
-- type is convertible to the constructor's attribute type.
class HasConvertChildAttr l a d c where
  has_convert_child_attr :: l :# a :# d :# c :#N -> HasConvertAttr l a d c

instance
  ( HasConvertAttrMatch l a d c (Range (ChildDom c)) Zero (AttrFam l n)
  , n ~ ListAt (ChildDom c) Zero
  ) => HasConvertChildAttr l a d c where
  has_convert_child_attr x = convert_attr_match (n_ns (p4 x))
    where n_ns :: P c -> Zero :# Range (ChildDom c) :#N
          n_ns _ = proxies

-- ** Binary operator
-- Associativity is not required. Combine will apply the
-- operator left to right.
class BinOp a where
  binOp :: a -> a -> a

-- ** Aspect/ Namespace
data Combine = Combine

-- ** Rule
{- the constraint "HasConvertibleChildAttr" ensures foldr1 doesn't
  get an empty list.
I could probably factorise Combine and Collect into their common expression
because 99 per cent is duplicated.
-}
instance
  ( AttrDefined l (Index c)
  , BinOp (Type l a d (Index c))
  , HasConvertChildAttr l a d c
  , Forall (ChildDom c)
      (IsConvertOrTrivial l a d (Type l a d (Index c)))
  , SRuleCtxt l c
  ) => SRule d a Combine l c
  where
    srulev x i c s =
      foldr1 binOp $
      keepJusts $
      pToList keep_defined $
      pzip (pmap is_convert_or_trivial_from_dict $
             forallD (is_cot x) dom_list) $
      pmap (getAttrP (rule_label x)) $ s
     where
      is_cot :: d :# a :# g :# l :# c :#N ->
        P (IsConvertOrTrivial l a d (Type l a d (Index c)))
      is_cot _ = P
      dom_list = child_dom_list $ proxy c
      keep_defined ::
        (ConvertOrTrivial l a d t :* Attr l a d S) n ->
        Maybe t
      keep_defined (cot :* x) = case cot of
        COT_Trivial -> Nothing
        COT_Convert -> Just . convert . fromDefined $ x
