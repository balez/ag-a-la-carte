-- * Header
{- GHC version 7.8.3
Author: Florent Balestrieri
-}
-- ** Ghc options
{-# LANGUAGE
      MultiParamTypeClasses
    , FlexibleInstances
    , TypeFamilies
    , ConstraintKinds
 #-}
-- ** Module
module Language.Grammars.AGalacarte.Rule.Copy where
-- ** Import
import Language.Grammars.AGalacarte.Prelude
import Language.Grammars.AGalacarte.Core
import Language.Grammars.AGalacarte.DependentTypes
import Language.Grammars.AGalacarte.IndexedContainer
import Language.Grammars.AGalacarte.Attribute

-- * Copy rule
{- A grammar with only one generic rule for copying the
   parent's inherited attribute when it has the same type.
No more instances should EVER be defined for Copy.
The rule is that a user should only modify its own grammars,
importing other's people grammar is ok.
-}

data Copy

instance ( IRuleCtxt l c
         , Type l a d (ListAt (ChildDom c) k) ~ Type l a d (Index c)
         , AttrDefined l (Index c))
         => IRule d a Copy l c k where
  irulev x i c s = getP (rule_label x) i
