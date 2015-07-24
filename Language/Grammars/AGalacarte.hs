-- * Header
{- GHC version 7.8.3
Author: Florent Balestrieri

This program uses complex contexts and can exhaust the
context stack if it is too small. Use -fcontext-stack to use
a bigger stack.
-}
-- ** Exports
module Language.Grammars.AGalacarte
( module Language.Grammars.AGalacarte.Prelude
, module Language.Grammars.AGalacarte.Proxy
, module Language.Grammars.AGalacarte.DependentTypes
, module Language.Grammars.AGalacarte.Indexed
, module Language.Grammars.AGalacarte.IndexedContainer
, module Language.Grammars.AGalacarte.Product
, module Language.Grammars.AGalacarte.Attribute
, module Language.Grammars.AGalacarte.Core
, module Language.Grammars.AGalacarte.Rule.Copy
, module Language.Grammars.AGalacarte.Rule.Macro
, module Language.Grammars.AGalacarte.Rule.Chain
, module Language.Grammars.AGalacarte.Rule.Collect
, module Language.Grammars.AGalacarte.Rule.Combine
{-
-- Grammars
Constructor
, Production
, Arr
, (:==>)
-- Attributes
, Attribute
, Mode
, I_S(..)
, I, S
, Inherited
, Synthesized
, Type
, Domain
, Dom(..)
, Everywhere
, Over
-- Aspects
, IA, Match_Attributes
, IC, Match_Constructors
, IAC, Match_Both

-}
) where
-- ** Imports
import Language.Grammars.AGalacarte.Prelude
import Language.Grammars.AGalacarte.Proxy
import Language.Grammars.AGalacarte.DependentTypes
import Language.Grammars.AGalacarte.Indexed
import Language.Grammars.AGalacarte.IndexedContainer
import Language.Grammars.AGalacarte.Product
import Language.Grammars.AGalacarte.Attribute
import Language.Grammars.AGalacarte.Core
import Language.Grammars.AGalacarte.Rule.Copy
import Language.Grammars.AGalacarte.Rule.Macro
import Language.Grammars.AGalacarte.Rule.Chain
import Language.Grammars.AGalacarte.Rule.Collect
import Language.Grammars.AGalacarte.Rule.Combine
