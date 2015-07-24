-- * Description
{- Author: Florent Balestrieri

Repmin defined using modular attribute grammars.

Global definitions:

  extree :: TreeT
    -- example tree

  repmin :: TreeT -> TreeT
    -- Bird's repmin
    -- Compute a tree structurally equivalent butwith all leaves
    -- replaced with the smallest value.

  newRepmin :: TreeT -> TreeT
    -- De Moor's repmin
    -- Compute a tree structurally equivalent where the leaves
    -- contain the number of occurence of the smallest value on
    -- their left in the inorder traversal.

  labelling :: TreeT -> TreeT
    -- Compute a tree structurally equivalent where the leaves
    -- are labelled in the in-order traversal.

  showTree :: TreeT -> String
    -- Computes a representation of a tree, with "*" as a node infix operator

  main :: IO ()
    -- prints the result of the previous functions on "extree".
-}

-- * Header
-- ** GHC Options
{-# Language
  TypeOperators
, DataKinds
, FlexibleInstances
, FlexibleContexts
, UndecidableInstances
, MultiParamTypeClasses
, TypeFamilies
, ConstraintKinds
, NoMonomorphismRestriction
 #-}
-- ** Imports
module Language.Grammars.AGalacarte.Examples.Repmin where
import Language.Grammars.AGalacarte
import Data.Monoid
import Control.Applicative

-- * Main
main = putStr $ unlines $ zipWith (++)
  ["extree: ", "repmin: ", "newRepmin: ", "labelling: "]
  (map showTree $
   [id, repmin, newRepmin, labelling] <*> pure extree)

-- * Operations
-- ** Min
data Min a = Min {fromMin :: a}
instance (Ord a) => BinOp (Min a) where
  binOp x y = Min $ fromMin x `min` fromMin y

-- ** Trees
type TreeT = Expr (CSum '[Node, Leaf]) Tree
newtype WTree = WTree {fromWTree :: TreeT}
instance BinOp WTree where
  binOp l r = WTree $ fromWTree l `node` fromWTree r

-- * Non terminals
-- Parameterised non terminals are possible
data Tree

-- * Productions
-- ** Node
-- Parameterised constructors are possible
data Node = Node
instance Constructor Node where
  type Production Node = Tree :==> '[Tree,Tree]

-- *** children names
type LeftTree = N0
type RightTree = N1
left_tree = n0
right_tree = n1

-- *** smart constructor
node = injC proxies Node

-- ** Leaf
data Leaf = Leaf Int
instance Constructor Leaf where
  type Production Leaf = Tree :==> '[]

leaf = injC proxies . Leaf

-- * Attributes
-- ** Global minimum
data Gmin = Gmin
instance Attribute Gmin where
  type Mode Gmin = Inherited
  type Type Gmin a c n = Int
  type Domain Gmin = Over '[Tree]
instance Bifunctor Gmin where bimap = cst3 id
-- ** Local minimum
data Lmin = Lmin
instance Attribute Lmin where
  type Mode Lmin = Synthesized
  type Type Lmin a c n = Min Int
  type Domain Lmin = Over '[Tree]
instance Bifunctor Lmin where bimap = cst3 id
-- ** New tree
{- parameterised by theinherited attribute that we use to
   give a value for the leaves -}
data Ntree = Ntree
instance Attribute Ntree where
  type Mode Ntree = Synthesized
  type Type Ntree a c n = WTree
  type Domain Ntree = Over '[Tree]
instance Bifunctor Ntree where bimap = cst3 id

-- ** Render
data Render = Render
instance Attribute Render where
  type Mode Render = Synthesized
  type Type Render a c n = String
  type Domain Render = Everywhere
instance Bifunctor Render where bimap = cst3 id

-- ** Counting the occurrences of the global min on the left of leaves
-- it's chained attribute
data ICount = ICount
instance Attribute ICount where
  type Mode ICount = Inherited
  type Type ICount a c n = Int
  type Domain ICount = Over '[Tree]
instance Bifunctor ICount where bimap = cst3 id

data Count = Count
instance Attribute Count where
  type Mode Count = Synthesized
  type Type Count a c n = Int
  type Domain Count = Over '[Tree]
instance Bifunctor Count where bimap = cst3 id

-- * Semantic Rules
-- ** Rendering
{- The function could be made more efficient by computing a
   Wadler list instead: (String -> String) -}
data Rendering = Rendering
type instance Import Rendering = '[]
instance SRule d a Rendering Render Node where
  srule _ i Node l r = "(" ++ Render! l ++ " * " ++ Render! r ++ ")"

instance SRule d a Rendering Render Leaf where
  srule _ i (Leaf x) = show x

-- ** Repmin
data Repmin = Repmin -- the normal repmin
type instance Import Repmin =
 '[ IA Copy '[Gmin]
  , IAC Combine '[Lmin] '[Node]
  , IAC Combine '[Ntree] '[Node]
  ]

instance SRule d a Repmin Lmin Leaf where
  srule _ i (Leaf x) = Min x

instance (UseI a '[Gmin]) => SRule d a Repmin Ntree Leaf where
  srule _ i (Leaf x) = WTree $ leaf $ Gmin! i

-- ** New Repmin
{- This is the variation studied in "First-class Attribute
Grammars" by Oege De Moor, Kevin Backhouse, S. Doaitse
Swierstra.

<quote>
  Let us consider how the above attribute grammar would have to
  be modified for a slightly different problem. Instead of
  replacing each leaf L by the global minimum, we aim to
  replace it by the number of times the global minimum occurred
  to the left of L in the inorder traversal of the tree. For
  this we introduce an additional chained attribute count that
  keeps track of that number.
</quote>
-}

data NewRepmin = NewRepmin -- the new tree has "Counts" in the leaves
type instance Default NewRepmin = ()
type instance Import NewRepmin =
 '[ IA Repmin '[Gmin, Lmin]
  , ChainAspect ICount Count '[Node]
  , IAC Combine '[Ntree] '[Node]
  ]
instance (UseI a '[ICount, Gmin])
    => SRule d a NewRepmin Count Leaf where
  srule _ i (Leaf x) = update $ ICount! i
    where update = if x == Gmin!i then (1 +) else id

instance (UseI a '[ICount]) => SRule d a NewRepmin Ntree Leaf where
  srule _ i (Leaf x) = WTree $ leaf $ ICount! i

-- * Fragments
repminF = Lmin & (\s -> fromMin (Lmin! s) `as` Gmin) & Ntree
newRepminF = (0 `as` ICount) & Count & repminF

showTree :: TreeT -> String
showTree t = Render! runAG' Rendering (frag Render) t

repmin, newRepmin :: TreeT -> TreeT
repmin t = fromWTree $ Ntree! runAG' Repmin repminF t
newRepmin t = fromWTree $ Ntree! runAG' NewRepmin newRepminF t

extree :: TreeT
extree =
     (l 2 * ((l 3 * l 2) * l 5))
   * ((l 2 * l 4) * l 7)
  where
     l = leaf
     (*) = node

-- * Inorder labelling
data Labelling = Labelling
type instance Import Labelling =
 '[ ChainAspect ICount Count '[Node]
  , IAC Combine '[Ntree] '[Node]
  ]
instance (UseI a '[ICount])
    => SRule d a Labelling Count Leaf where
  srule _ i (Leaf _) = 1 + ICount! i

instance (UseI a '[ICount]) => SRule d a Labelling Ntree Leaf where
  srule _ i (Leaf _) = WTree $ leaf $ ICount! i

labelF = (0 `as` ICount) & Count & Ntree
labelling t = fromWTree $ Ntree! runAG' Labelling labelF t
