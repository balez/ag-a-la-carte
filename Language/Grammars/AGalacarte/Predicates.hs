-- * Header
{- GHC version 7.8.3
Author: Florent Balestrieri
-}
-- ** Ghc options
{-# LANGUAGE
      TypeOperators
    , GADTs
    , LambdaCase
    , RankNTypes
    , EmptyCase
    , PolyKinds
 #-}
-- ** Module
module Language.Grammars.AGalacarte.Predicates where
import Language.Grammars.AGalacarte.Indexed

-- * Predicates

{- Predicates are can be thought of as sets of types
singleton sets are predicates ~Equal n~
we have the empty set ~Empty~
and union of two sets ~a :\/ b~.They are right parenthesised lists of ~Equal n~ built with ~:|~
and ~Empty~ is the empty list.
predicates are built out of the empty predicate Empty
  singletons (Equal n)
and disjunction (q :\/ q')
-}

-- *** Falsehood, empty set
data Empty n -- empty indexed type

-- from falsehood, we can deduce anything
emptyElim :: Empty :-> x
emptyElim = \case{}

-- *** Equality, singleton set
data Equal a b where
  Refl :: Equal a a

type a :~: b = Equal a b
infix 1 :~:

equal_trans :: Equal a b -> Equal b c -> Equal a c
equal_trans Refl Refl = Refl
equal_sym :: Equal a b -> Equal b a
equal_sym Refl = Refl

equal_pair :: Equal (a,b) (c,d) -> (Equal a c, Equal b d)
equal_pair Refl = (Refl,Refl)

-- *** Disjunction
infixl 2 :\/, :|
data (q1 :\/ q2) n = DisjLeft (q1 n) | DisjRight (q2 n)

{- to define predicates by extensions:
Equal a :| b :| c :| d
corresponds to the set {a,b,c,d}
-}
type n :| p = Equal n :\/ p

disj_case ::
  (p :-> a) ->
  (q :-> a) ->
  (p :\/ q) :-> a
disj_case f g = \case
  DisjLeft p -> f p
  DisjRight q -> g q
