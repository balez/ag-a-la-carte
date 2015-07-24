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
module Language.Grammars.AGalacarte.Rule.Collect where
-- ** Imports
import Language.Grammars.AGalacarte.Prelude
import Language.Grammars.AGalacarte.Proxy
import Language.Grammars.AGalacarte.DependentTypes
import Language.Grammars.AGalacarte.Indexed
import Language.Grammars.AGalacarte.IndexedContainer
import Language.Grammars.AGalacarte.Product
import Language.Grammars.AGalacarte.Attribute
import Language.Grammars.AGalacarte.Core

import Data.Monoid (Monoid(..))

-- * Collect Rule
{- The collect rule is defined for a synthesized attribute
whose type is a monoid. It only applies to constructors for which the attribute is defined
and whose children (if any) either do not have this attribute, or if they have it,
it must be of the same type as the constructor's.

Then the monoid operations are used to compute the
attribute's value for the constructor.

Combining children's value left to right, and using the
monoid identity otherwise.
-}

-- *** Precondition for the rule
{- We can apply the collect rule at a constructor "c"
if the attribute is trivial for "c"
or if it can be converted to the same type for all the children for which it is defined,
and there is a Monoid instance for that type.
-}
class Convert a b where
  convert :: a -> b

instance Convert a a where
  convert = id
-- **** Condition on children
data ConvertOrTrivial l a c t n where
  COT_Trivial ::
    AttrTrivial l n
    => ConvertOrTrivial l a c t n
  COT_Convert ::
    ( AttrDefined l n
    , Convert (Type l a c n) t
    ) => ConvertOrTrivial l a c t n

class ( x ~ AttrFam l n
      ) => ConvertOrTrivialMatch l a c t (n :: *) x where
  convert_or_trivial_match :: ConvertOrTrivial l a c t n

instance
  ( AttrTrivial l n
  ) => ConvertOrTrivialMatch l a c t n (Const3 ()) where
  convert_or_trivial_match = COT_Trivial

instance
  ( Convert (Type l a c n) t
  , AttrDefined l n
  ) => ConvertOrTrivialMatch l a c t n (Type' n) where
  convert_or_trivial_match = COT_Convert

-- **** Dictionary for the children's condition
class IsConvertOrTrivial l a c t (n :: *) where
  is_convert_or_trivial :: ConvertOrTrivial l a c t n

instance (ConvertOrTrivialMatch l a c t n (AttrFam l n))
 => IsConvertOrTrivial l a c t n where
  is_convert_or_trivial = convert_or_trivial_match

is_convert_or_trivial_from_dict ::
  Dict2 (IsConvertOrTrivial l a c t) :->
  ConvertOrTrivial l a c t
is_convert_or_trivial_from_dict Dict2 = is_convert_or_trivial

-- *** Generic collect rule
-- Aspect
data Collect = Collect

instance
  ( AttrDefined l (Index c)
  , Monoid (Type l a d (Index c))
  , Forall (ChildDom c)
      (IsConvertOrTrivial l a d (Type l a d (Index c)))
  , SRuleCtxt l c
  ) => SRule d a Collect l c
  where
    srulev x i c s =
      foldr mappend mempty $
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
        COT_Convert -> Just $ convert $ fromDefined x
