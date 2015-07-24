-- * Header
{- GHC version 7.8.3
Author: Florent Balestrieri
-}
-- ** Ghc options
{-# LANGUAGE
      GADTs
    , ConstraintKinds
    , PolyKinds -- for dictionaries
 #-}
-- ** Module
module Language.Grammars.AGalacarte.Prelude where
-- ** Import
import Language.Grammars.AGalacarte.Indexed

--import Data.Monoid
-- * Prelude
-- ** Debugging
impossible = error "impossible (should be unreachable)"

-- use this function with a hole: "what_type _ puzzle"
what_type :: a -> a -> b
what_type = cst2 $ error "what_type"

-- ** Lists
single x = [x]
keepJusts = concat . fmap (maybe [] single)

-- ** Endo functions
type Endo a = a -> a

-- ** Dictionnaries
data Dict c where
  Dict :: c => Dict c

data Dict2 c t where
  Dict2 :: c t => Dict2 c t

-- ** Continuations
type Cont r a = (a -> r) -> r
-- ** Constant functors
-- kind polymorphic constant functors
newtype Const t a = Const {fromConst :: t}
newtype Const2 t a b = Const2 {fromConst2 :: t}
newtype Const3 t a b c = Const3 {fromConst3 :: t}
newtype FlipConst t n a = FlipConst {fromFlipConst :: t n}

-- ** Constant functions
-- cstN :: a -> (x1 -> ... -> xN -> a)
cst1 = const
cst2 = cst1 . cst1
cst3 = cst1 . cst2
cst4 = cst1 . cst3
cst5 = cst1 . cst4

-- ** Function composition
-- *** Composition of n-ary functions
-- resN :: (a -> b) -> (x1 -> ... -> xN -> a) -> (x1 -> ... -> xN -> b)
-- resN f g x1 ... xN = f (g x1 .. xN)
res1 = (.)
res2 = res1 . res1
res3 = res1 . res2
res4 = res1 . res3
res5 = res1 . res4

-- ** Bijections
data Bij a b = Bij (a -> b) (b -> a)
binop :: Bij a b -> (a -> a -> a) -> (b -> b -> b)
binop (Bij to from) op x y = to (from x `op` from y)
