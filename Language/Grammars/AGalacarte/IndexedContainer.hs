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
    , OverlappingInstances
    , GADTs
    , TypeFamilies
    , LambdaCase
    , RankNTypes
    , EmptyCase
    , ConstraintKinds
    , PolyKinds
    , DataKinds
    , ViewPatterns
 #-}
-- ** Module
module Language.Grammars.AGalacarte.IndexedContainer where
-- ** Import
import Language.Grammars.AGalacarte.Prelude (cst2, res2, Endo)
import Language.Grammars.AGalacarte.Proxy
import Language.Grammars.AGalacarte.DependentTypes
import Language.Grammars.AGalacarte.Predicates
import Language.Grammars.AGalacarte.Indexed
import Language.Grammars.AGalacarte.Product

import Control.Applicative ((<$>))
import Data.Maybe (fromJust)

-- * Indexed containers
-- ** Containers
class Container (c :: [*] -> * -> *) where
  container :: c p n -> TList p

-- ** Ext: Indexed Container Extension
{- Base functor of an indexed W type.
This is also the extension of an indexed container.
 -}
infix 4 :-
data Ext (c :: [*] -> * -> *)
         (x :: * -> *)
         (i :: *) where
  (:-) :: c ts i -> Prod ts x -> Ext c x i

-- the shape of a container
data Shape c where
  Shape :: c p n -> Shape c

shape :: Ext c x i -> Shape c
shape (s :- p) = Shape s

-- We never use IFunctor in this library
instance IFunctor (Ext a) where
  imap m (shape :- payload) =
    shape :- (m `pmap` payload)

-- ** Free Monad and Fixpoint (Expr)
{- free monad of indexed container functors
we use them to implement AG macros.
By defining W types in terms of Free, we can reuse the same smart constructors
injecting alacarte constructors to a fixpoint.
 -}
data Free (c :: [*] -> * -> *) x n where
  Return :: x n -> Free c x n
  InFree :: c ts n -> Prod ts (Free c x) -> Free c x n

outFree :: Free c x n -> Either (x n) (Ext c (Free c x) n)
outFree (Return x) = Left x
outFree (InFree c v) = Right (c :- v)

-- *** IFunctor, HFunctor
  -- Free takes a IFunctors "f" and makes a Ifunctors "Free f"
instance (Container c) => IFunctor (Free c) where
  imap m = \case
    Return x -> Return $ m x
    InFree c v -> InFree c $ pmap (imap m) v

-- A higher order functor on container functors
class HFunctor h where
  hmap :: (Container f, Container g) => f :--> g -> h f :--> h g

instance HFunctor Free where
  hmap m = \case
    Return x -> Return x
    InFree c v -> InFree (m c) $ pmap (hmap m) v

-- *** Expr: W type
-- W types are the fixed-points of container functors.
type Expr c = Free c Empty

outExpr :: Expr c :-> Ext c (Expr c)
outExpr (outFree -> Right x) = x

inExpr :: Ext c (Expr c) :-> Expr c
inExpr (c :- v) = InFree c v

-- *** Substitution
{- Substitution is the join of the indexed monad structure of Free -}
-- works also for "Expr" when "x == Empty"
subst :: Container c => Free c (Free c x) :-> Free c x
subst = \case
  Return x -> x
  InFree c v -> InFree c $ pmap subst v

-- *** Proxies
exprP :: P d -> P (Expr d)
exprP = const P

returnP :: P f -> x n -> Free f x n
returnP _ = Return

-- ** Container Algebras and catamorphisms
type Alg c x = Ext c x :-> x
cata :: Alg c x -> Expr c :-> x
cata alg = alg . imap (cata alg) . outExpr

-- ** Sum
{- having a kind-polymorphic sums allows to use the same type
for sums of indexed functors and sums of indexed containers
-}

data (:+:) (f :: j -> k -> *)
           (g :: j -> k -> *)
           (x :: j)
           (y :: k)
  = InL (f x y) | InR (g x y) deriving (Read,Show)
infixr 2 :+:

sumElim :: (f e i -> r) -> (g e i -> r) -> (f :+: g) e i -> r
sumElim l r = \case
  InL x -> l x
  InR x -> r x

instance (IFunctor f, IFunctor g) => IFunctor (f :+: g) where
  imap m = sumElim (InL . imap m) (InR . imap m)

instance (Container a, Container b) => Container (a :+: b) where
  container = \case
    InL x -> container x
    InR x -> container x

-- ** Constructor
-- *** Productions
data Arr a b = a :==> b
class (IsList (ChildDom p)) => Constructor p where
  type Production p :: Arr * [*]

type family Lhs (production :: Arr * [*]) where
  Lhs (a :==> b) = a

type family Rhs (production :: Arr * [*]) where
  Rhs (a :==> b) = b

type Index t = Lhs (Production t)
type ChildDom t = Rhs (Production t)

type Children c = Prod (ChildDom c)

-- **** Proxies
constr_index :: P t -> P (Index t)
constr_index _ = P

childrenP :: P t -> P (Children t)
childrenP t = P

child_dom :: P t -> P (ChildDom t)
child_dom _ = P
child_dom' = child_dom . proxy

child_dom_list :: Constructor t => P t -> TList (ChildDom t)
child_dom_list = is_list . child_dom

-- *** C
-- The container corresponding to the instance "Constructor t"
data C t p n where
  C :: t -> C t (ChildDom t) (Index t)

instance Constructor t => Container (C t) where
  container (C t) = is_list P

cshape :: C t p n -> t
cshape (C t) = t
cP :: P t -> P (C t)
cP _ = P

-- *** Empty Container
data EmptyC (ts :: [*]) (n :: *) -- empty

instance Container EmptyC where
  container = \case{}

-- *** Sum of constructors
{- Alternatively, instead of a type family, I could define a gadt:
data CSum ts p n where
  CHead :: Container t => C t -> CSum (t ': ts) (ChildPos t) (Index t)
  CTail :: CSum ts p n -> CSum (t ': ts) p n
-}

type family CSum ts where
  CSum '[] = EmptyC
  CSum (t ': ts) = C t :+: CSum ts

-- If every element in the sum is a constructor, then the sum is a container.
-- csumContainerD :: Forall cs Constructor =>
--   TList cs -> Dict (Container (CSum cs))
-- csumContainerD = \case
--   TNil -> Dict
--   TCons h t -> case csumContainerD t of Dict -> Dict

-- ** Automatic injections A la carte
{- A fixed set of instances allows to inject a 
constructor into container. No more instances should be
added. We rely on right parenthesizing the sums.

prj and inj are not in the same class because we may be
able to project without being able to inject. Example:
tagging.  We can project from a tagged container but not inject
without knowing the tag. Tags are used to implement macros.
-}

infix 1 :<<
class (Constructor f, Container g) => f :<< g where
  prj :: g e i -> Maybe (e :~: ChildDom f, f)

infix 1 :<
class (f :<< g) => f :< g where
  inj :: f -> g (ChildDom f) (Index f)

instance Constructor c => c :<< C c where
  prj (C x) = Just (Refl, x)
instance Constructor c => c :< C c where
  inj = C

instance (Constructor c, Container f) => c :<< (C c :+: f) where
  prj = sumElim prj (const Nothing)
instance (Constructor c, Container f) => c :< (C c :+: f) where
  inj = InL . inj

instance (c :<< f, Container c') => c :<< (c' :+: f) where
  prj = sumElim (const Nothing) prj
instance (c :< f, Container c') => c :< (c' :+: f) where
  inj = InR . inj

-- ** Injections
-- Injecting into the fixedpoint (inferred)
injV :: (g :< f) => g -> Children g (Free f x) -> Free f x (Index g)
injV = InFree . inj

injC :: (c :< d, Constructor c) =>
  x :# d :#N -> c ->
  Curry (ChildDom c) (Free d x)
    (Free d x (Index c))

injC p x = prod_curry $ det p x . injV x
  where
    det = cst2 id :: x :# c :#N -> t -> Endo (Free c x (Index t))

injExt :: (c :< d) => c -> Children c x -> Ext d x (Index c)
injExt x p = inj x :- p

-- ** Pattern matching
{- containers offer a very nice generic programming technique for
 programming with paths -}

prjP :: (f :<< g) => P f -> g e i -> Maybe (e :~: ChildDom f, f)
prjP _ = prj

prjExtP :: (c :<< f) =>
  P c -> Ext f x (Index c) -> Maybe (Ext (C c) x (Index c))
prjExtP cP (c :- v) = prjP cP c >>= \(Refl, x) -> return $ C x :- v

-- Match returns the children of a constructor if it matches the shape
match :: (c :<< f) =>
  P c -> Ext f x (Index c) -> Maybe (Children c x)
match cP (prjExtP cP -> Just (C x :- y)) = Just y
match _ _ = Nothing

-- Partial function, always expects the match to succeed.
match' :: (c :<< f) =>
  P c -> Ext f x (Index c) -> Children c x
match' = fromJust `res2` match

-- **** Deep matching, Free monad
{- When working with the free monad, we can nest pattern
matching.  We define operators (>-, -->, ->-, #-) for pattern
matching on the free monad, so that nested matches are nice
to read. The number is the index of the child.

   f  >- addP --> p0
     ->- factP --> p0

is equal to

   do  PFun g <- match addP (outFree f)
       PFun h <- match factP $ outFree $ g AddLeft
       return $ h FactP
-}

-- a pairing operator that doesn't require parenthesis.
infix 9 -->
(-->) a b = (a,b)

-- matching operator
-- infixl 8 >-
-- infixl 7 ->-, #-
(>-) ::
  ( c :<< f
  , Index c ~ x
  , v ~ ChildDom c
  , IsNat n
  , ListAt v n ~ y
  ) =>
  Free f e x -> (c, P n) -> Maybe (Free f e y)

(>-) e (c, n) = 
  pget n <$> (match (proxy c) =<< fromRight (outFree e))
  
fromRight :: Either a b -> Maybe b
fromRight = either (const Nothing) Just

-- partial
fromRight' = fromJust . fromRight
            
-- takes a maybe argument
(->-) m s = m >>= (>- s)

-- partial function, always expect the match to succeed.
(#-) e s = fromJust (e >- s)

{- snoc paths, so that a path expression looks similar to
   the matching expression, by replacing (>-) with (:>)
   and the expression by Top.
-}
infixl 8 :>
data Path f x y where
  Top :: Path f x x
  (:>) :: ( Index c ~ y
          , c :<< f
          , v ~ ChildDom c
          , IsNat n
          , ListAt v n ~ z
          ) =>
        Path f x y -> (c, P n) -> Path f x z

matchPath :: Free f e x -> Path f x y -> Maybe (Free f e y)
matchPath e p = matchPathM (Just e) p

-- partial function, always expect the match to succeed.
matchPath' :: Free f e x -> Path f x y -> Free f e y
matchPath' e = fromJust . matchPath e

-- a path catamorphism
matchPathM :: Maybe (Free f e x) -> Path f x y -> Maybe (Free f e y)
matchPathM e Top = e
matchPathM e (path :> step) =
  matchPathM e path ->- step

-- ** Tags
{- Tag pairs some value with some type dependent information
   being kind-polymorphic, it works both with containers and functors
so do the instances for :<< and :<
-}
data Tag f t x n = Tag
  { tagged :: f x n
  , tag :: t n }

extTag :: Ext (Tag f t) x n -> t n
extTag (s :- p) = tag s

instance (f :<< d) => f :<< Tag d t where
  prj = prj . tagged

instance (f :< d) => f :< Tag d Unit where
  inj x = Tag (inj x) Unit

instance IFunctor c => IFunctor (Tag c t) where
  imap m (Tag x t) = Tag (imap m x) t

instance Container c => Container (Tag c t) where
  container = container . tagged

-- In particular works with the "h" being the Free monad
hmapTag :: (Container f, HFunctor h) =>
  (a :-> b) -> h (Tag f a) :--> h (Tag f b)
hmapTag m = hmap (mapTag m)

-- specialisation of hmapTag to the identity higher order functor
mapTag :: (a :-> b) -> Tag c a :--> Tag c b
mapTag m (Tag x t) = Tag x (m t)
