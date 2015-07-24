-- * Header
{- GHC version 7.8.3
Author: Florent Balestrieri
-}
-- ** Ghc options
{-# LANGUAGE
      RankNTypes
    , TypeOperators
    , PolyKinds
 #-}

-- *** before
{- LANGUAGE
      MultiParamTypeClasses
    , FlexibleContexts
    , TypeOperators
    , UndecidableInstances
    , DeriveFunctor
    , NoMonomorphismRestriction
    , StandaloneDeriving
    , ViewPatterns
    , GADTs
    , MultiParamTypeClasses
    , TypeFamilies
    , FlexibleInstances
    , DeriveFunctor
    , OverlappingInstances
    , LambdaCase
    , RankNTypes
    , FunctionalDependencies
    , EmptyCase
    , RecordWildCards
    , ConstraintKinds              -- useful for typeclass synonyms
    , PolyKinds -- useful for proxies
--    , ScopedTypeVariables
    , LiberalTypeSynonyms
    , AllowAmbiguousTypes
    , GeneralizedNewtypeDeriving
    , DataKinds
 #-}
-- ** Module
module Language.Grammars.AGalacarte.Proxy where
-- ** Import
import Language.Grammars.AGalacarte.Indexed
import Language.Grammars.AGalacarte.Prelude (cst2)

import Control.Applicative

-- * Type Proxies

{- A type proxy is used to guide the typechecker, for
instance when a class instance is ambiguous. -}

data P (t :: k) = P
proxy :: t -> P t
proxy _ = P

-- *** list of proxies of any kind
infixr 1 :#, :##, #
data (a :: k) :# t = P a :# t
-- **** kind *
type (a :: *) :## t = a :# t
data N = N

a # b = proxy a :# b

-- projections from tuples of proxies
p1 :: a :# b -> P a
p1 (pa :# b) = pa
pt :: a :# b -> b
pt (pa :# b) = b
pt1 = pt
pt2 = pt . pt
pt3 = pt . pt2
pt4 = pt . pt3
pt5 = pt . pt4
p2 = p1 . pt1
p3 = p1 . pt2
p4 = p1 . pt3
p5 = p1 . pt4
p6 = p1 . pt5

-- *** List of proxies are automatically covered by the proxies method.
class Proxies l where
  proxies :: l
instance Proxies N where
  proxies = N
instance Proxies l => Proxies (t :# l) where
  proxies = P :# proxies

-- *** Dealing with parameterised types
-- **** Better breaking
-- p_expand_last :: (P x -> z :# P y) -> a :% x -> a :% y :% z
-- p_expand_last m (a :% x) = a :% y :% z
--  where y :% z = m x


-- **** Breaking a parameterised type into each constituent
breakP1 :: P a -> a :#N
breakP2 :: P (a b) -> b :# a :#N
breakP3 :: P (a b c) -> c :# b :# a :#N
breakP4 :: P (a b c d) -> d :# c :# b :# a :#N
breakP5 :: P (a b c d e) -> e :# d :# c :# b :# a :#N

breakP1 = const proxies
breakP2 = const proxies
breakP3 = const proxies
breakP4 = const proxies
breakP5 = const proxies

break1 = breakP1 . proxy
break2 = breakP2 . proxy
break3 = breakP3 . proxy
break4 = breakP4 . proxy
break5 = breakP5 . proxy

-- indices
iP1 = p1 . breakP2
iP2 = p2 . breakP3
iP3 = p3 . breakP4
iP4 = p4 . breakP5


i1 = p1 . break2
i2 = p2 . break3
i3 = p3 . break4
i4 = p4 . break5

-- **** stiching
stitch1 :: a :#N -> P a
stitch2 :: b :# a :#N -> P (a b)
stitch3 :: c :# b :# a :#N -> P (a b c)
stitch4 :: d :# c :# b :# a :#N -> P (a b c d)
stitch5 :: e :# d :# c :# b :# a :#N -> P (a b c d e)
stitch1 = const P
stitch2 = const P
stitch3 = const P
stitch4 = const P
stitch5 = const P

-- **** proxy application (can be chained)
appP :: P t -> P a -> P (t a)
appP = cst2 P

-- *** determine a type:
detP :: P t -> t -> t
detP _ = id

-- **** detProj in combination with break is extremely expressive.
detProj :: a -> (t -> a) -> t -> t
detProj _ _ = id

-- **** determine a type with a fixedpoint
detFix :: (t -> a) -> (a -> t) -> t
detFix p f = t
  where
    a = p t
    t = detProj a p (f a)

-- *** functoriality
{- the monad instance is useful in case we have a proxy of a
  complex type and want to compute a proxy on a subterm of that type:
for instance:

\p -> snd <$> (cod =<< cod =<< p)
  :: P (a -> (b -> (c, d))) -> P d

-}
instance Functor P where
  fmap _ _ = P
instance Monad P where
  return _ = P
  m >>= f = P
instance Applicative P where
  pure _ = P
  f <*> x = P

class FunctorI (f :: (* -> *) -> *) where
  mapi :: (a :-> b) -> f a -> f b
instance FunctorI  P where
  mapi _ _ = P

familyPP :: forall (a :: k -> j) (b :: k) . P (a b) -> P a
familyPP _ = P
indexPP :: forall (a :: k -> j) (b :: k) . P (a b) -> P b
indexPP _ = P

indexP :: a n -> P n
indexP _ = P
index1 :: c p n -> P p
index1 _ = P
index2 :: c p n -> P n
index2 _ = P

domP :: (a -> b) -> P a
domP _ = P
codP :: (a -> b) -> P b
codP _ = P

idomP :: (a :-> b) -> P a
idomP _ = P
icodP :: (a :-> b) -> P b
icodP _ = P

iidomP :: (a :--> b) -> P a
iidomP _ = P
iicodP :: (a :--> b) -> P b
iicodP _ = P

-- *** Proxies of type-lists

{- using type lists
data P (t :: k) = P
tp :: P (a ': b) -> P b
tp _ = P

type family BreakP t where
  BreakP '[] = ()
  BreakP (a ': b) = (P a, BreakP b)

class BreakPClass t where
  breakP :: P t -> BreakP t
instance BreakPClass '[] where
  breakP _ = ()
instance BreakPClass b => BreakPClass (a ': b) where
  breakP ab = (P, breakP (tp ab))
-}


{-
-- ** Snoc Proxies
data P (t :: k) = P
p :: t -> P t
p _ = P

infixl 1 :%
data p :% (t :: k) = (:%) {p' :: p, p0 :: P t}

-- *** Projections
p1' = p'
p2' = p' . p'
p3' = p' . p2'
p4' = p' . p3'
p5' = p' . p4'
p_2 = p0 . p1'
p_3 = p0 . p2'
p_4 = p0 . p3'
p_5 = p0 . p4'
p_6 = p0 . p5'

-- *** Construction
class Ps l where
  ps :: l
instance Ps (P t) where
  ps = P
instance Ps t => Ps (t :% x) where
  ps = ps :% P

-- *** Functoriality

pmap1 :: (a -> b) -> a :% x -> b :% x
pmap1 m (a :% x) = m a :% x

pmap2 :: (P x -> P y) -> a :% x -> a :% y
pmap2 m (a :% x) = a :% m x
-}
