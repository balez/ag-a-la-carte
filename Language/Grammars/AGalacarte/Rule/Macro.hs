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
    , RankNTypes
 #-}
-- ** Module
module Language.Grammars.AGalacarte.Rule.Macro where
-- ** Import
import Language.Grammars.AGalacarte.Prelude
import Language.Grammars.AGalacarte.Proxy
import Language.Grammars.AGalacarte.DependentTypes
import Language.Grammars.AGalacarte.Indexed
import Language.Grammars.AGalacarte.IndexedContainer
import Language.Grammars.AGalacarte.Product
import Language.Grammars.AGalacarte.Attribute
import Language.Grammars.AGalacarte.Core
import Language.Grammars.AGalacarte.Rule.Copy

import Data.Function (fix)
-- ** Utils
-- *** Namespace
{- let's make a new namespace for the attributes needed by macros -}
data Utils = Utils
type instance Import Utils =
  '[ Copy `Match_Attributes` '[Recurse, SynNode]]

type UtilsAspect =
  Utils `Match_Attributes`
     '[Recurse, SynNode, Self, InhSubtree, SynChildren, InheritedRec]

utilsP :: P Utils
utilsP = P
utilsFromP :: d :# a :# g :# r -> d :# a :# Utils :# r
utilsFromP (d :# a :# _ :# r) = d :# a :# utilsP :# r

-- *** Self: Current Expression
data Self = Self
instance Attribute Self where
  type Mode Self = Synthesized
  type Type Self a c n = Expr c n
  type Domain Self = Everywhere
instance Bifunctor Self where bimap = cst3 id

{- We can write a GENERIC rule that works for any constructor -}
instance (c :< d) => SRule d a Utils Self c where
   srulev _ i c s = injV c (pmap (Self!) s)

-- *** Recurse: when an AG needs to run itself recursively
{- a macro is simply a syn rule that computes all the
synthesized attributes generically by running the AG on a
term constructed from its subterms.
-}

{- Recurse should contain the partial evaluation of an attribute grammar
  using runAG

  A type family cannot have a polymorphic type, therefore
  the attribute is packaged in a newtype.

  Note that Recurse is not a strictly positive functor, and
  its "bimap" implementation uses both "from" and "to" maps.
-}
type RunAGT c a = forall r . Rec a c I r -> Expr c r -> Rec a c S r
newtype  RunAG c a = RunAG {fromRunAG :: RunAGT c a}
data Recurse = Recurse
instance Attribute Recurse where
  type Mode Recurse = Inherited
  type Type Recurse a c n = RunAG c a
  type Domain Recurse = Everywhere
instance Bifunctor Recurse where
  bimap _ from to (RunAG run) =
    RunAG $ \inh -> to . run (from inh)

{- When accessing this attribute, we usually apply it to the
   same inherited attribute record.
-}

recurse :: (UseI a '[Recurse], Container c) =>
  Rec a c I r -> Expr c r -> Rec a c S r

recurse i = get Recurse i `fromRunAG` i

{- The default generic copy rule is what we want, so that
 every node inherits the same ~Recurse~ attribute
-}

-- *** InheritedRec: Collecting the inherited attributes
data InheritedRec = InheritedRec
instance Attribute InheritedRec where
  type Mode InheritedRec = Synthesized
  type Type InheritedRec a c n = Rec a c I n
  type Domain InheritedRec = Everywhere
instance Bifunctor InheritedRec where
  bimap _ f t = t

-- Generic rule for all constructors
instance (Constructor c) => SRule d a Utils InheritedRec c where
  srulev _ i c s = i

-- *** SynChildren: Children's synthesized attributes
{- the attribute ~Children c s n~ contains all the synthesized
 attribute of the children of a node.

In combination with InheritedRec, it allows to access the
inherited attribute of children, which is sometimes useful if
we can define one in term of the others.  However we must be
careful that they don't mutually depend on each other in a
non-terminating way.  -}

data SynChildren = SynChildren
instance Attribute SynChildren where
  type Mode SynChildren = Synthesized
  type Type SynChildren a c n = Ext c (Rec a c S) n
  type Domain SynChildren = Everywhere
instance Bifunctor SynChildren where
  bimap _ f t = imap t

-- Generic rule for every constructor
instance (c :< d) => SRule d a Utils SynChildren c where
  srulev _ i c s = injExt c s

-- *** InhSubtree: Subtree's inherited attributes
{- we built the subtrees containing all the inherited attributes
Note that this makes the attribute InheritedRec redundant.
When we use this attribute, we must be careful not to introduce circular definitions.
-}

data InhSubtree = InhSubtree
instance Attribute InhSubtree where
  type Mode InhSubtree = Synthesized
  type Type InhSubtree a c n = Expr (Tag c (Rec a c I)) n
  type Domain InhSubtree = Everywhere
instance Bifunctor InhSubtree where
  bimap _ f t = hmapTag t

-- Generic rule for every constructor
instance (Constructor c, c :< d) => SRule d a Utils InhSubtree c where
  srulev x i c s = InFree (Tag (inj c) i) $ pmap (InhSubtree!) s

-- *** SynNode: This node's Synthesized attributes
{- SynNode is very useful to define a synthesized attribute in terms of other
synthesized attribute **of the same node**.
Note that in conjunction with InhSubtree, this will give a
full attribution of the subtree.
Of course we must be careful not to introduce circular definitions.
-}

data SynNode = SynNode
instance Attribute SynNode where
  type Mode SynNode = Inherited
  type Type SynNode a c n = Rec a c S n
  type Domain SynNode = Everywhere
instance Bifunctor SynNode where bimap _ f t = t

-- Generic rule for every constructor and every non-terminal
instance (Constructor c, IsNat n) => IRule d a Utils SynNode c n where
  irulev x i c s = pget (rule_child x) s


-- ** Macros
{- "Macro c" is an inherited attribute containing the macro parameterisation
for constructor "c".
-}
{- we can't use the same aspect as the other macro attributes because
  we will override their copy rule -}
data Macros = Macros

-- *** Defining macros
{- A macro definition is given in two parts -}
data MacroDef c d = MacroDef
  { smacro_def :: SMacro c d
  , imacro_def :: IMacro c d
  }

{- The first part computes an expression from the children of
   the constructor for which the macro is defined. -}
type SMacro c d = forall x . P x ->
   Curry (ChildDom c) (Free d x) (Free d x (Index c))

{- the second part gives a vector of paths which select a subtree of the
  expression given by SMacro. Each path corresponds to the subtree whose inherited attributes
are given to the immediate children of the original expression.
-}
type IMacro c d = forall x .
  Children c (Path (Tag d x) (Index c))

-- *** Macro attribute
newtype Macro (c :: *) = Macro c
instance (Constructor c) => Attribute (Macro c) where
  type Mode (Macro c) = Inherited
  type Type (Macro c) a d n = MacroDef c d
  type Domain (Macro c) = Everywhere
instance Bifunctor (Macro c) where bimap = cst3 id

-- *** Macro instance for synthesized attributes
instance
  ( Use a '[Recurse] '[Macro c, Self]
  , SRuleCtxt l c
  ) => SRule d a Macros l c where
  srulev x i c s = getP l $ recurse i $ subst $ macro_expansion
    where
      m = smacro_def $ Macro c ! i
      children = pmap (returnP d . (Self!)) s
      macro_expansion = prod_uncurry (m (exprP d)) children
      d = rule_container x
      l = rule_label x

-- *** Macro instance for inherited attributes
{- Assuming InSubtree and SynNode have not been overriden,
they will reflect the macro substitution rather than the real
subtree.  thus yielding the inherited value of the
substituted expressions.
-}

instance
  ( Use a '[Recurse, SynNode] '[Macro c, Self, InhSubtree]
  , IRuleCtxt l c
  , IsNat k
  ) => IRule d a Macros l c k where
  irulev x i c s = getP (rule_label x) i'
    where
      i' = untag $ matchPath' (InhSubtree! SynNode! i) path
      untag = extTag . fromRight' . outFree
      path = pget (rule_child x) $ imacro_def $ Macro c ! i

-- ** HOAG: Running a recursive attribute grammar 
-- p is a parameter used to initialize some inherited attributes.
runHoag ::
  (Rules i s c c a' g) =>
  g ->
  (RunAG c a -> p :-> PFrag i s c a' a a) ->
  (Rec a c I :-> p) ->
  RunAG c a
runHoag aspect f init =
  fix $ \this -> RunAG $ \i e -> fix $ \s ->
    run aspect (f this (init i)) e

runHoagWithParam :: (Rules i s c c a' g) =>
  g ->
  (RunAG c a -> p :-> PFrag i s c a' a a) ->
  (Rec a c I :-> p) ->
  p n ->
  Expr c n ->
  Rec a c S n
runHoagWithParam aspect fragment init param =
  run aspect $ fragment (runHoag aspect fragment init) param

utilsF run =
  run `as` Recurse & (`as` SynNode) & Self & InhSubtree

withUtils :: (IsList i, Container c) =>
  (p :-> PFrag i s c a a f) ->
  RunAG c a ->
  p :-> (PFrag (Recurse ': SynNode ': i)
              (Self ': InhSubtree ': s)
              c a a
              (Recurse ': SynNode ': Self ': InhSubtree ': f))

withUtils f this p = utilsF this & f p

-- here, we add the necessary attributes to the fragment
runHoagWithUtils ::
  ( Rules (Recurse ': SynNode ': i) (Self ': InhSubtree ': s) c c a g
  , a ~ (Recurse ': SynNode ': Self ': InhSubtree ': b)
  , Container c
  , IsList i
  ) =>
  g ->
  (p :-> PFrag i s c a a b) ->
  (Rec a c I :-> p) ->
  p n ->
  Expr c n ->
  Rec a c S n
runHoagWithUtils g f =
  runHoagWithParam g (withUtils f)
