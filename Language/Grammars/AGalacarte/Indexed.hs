-- * Header
{- GHC version 7.8.3
Author: Florent Balestrieri
-}
-- ** Ghc options
{-# LANGUAGE
     TypeOperators
    , RankNTypes
    , PolyKinds
 #-}

module Language.Grammars.AGalacarte.Indexed where

-- * Indexed types and functions
{- functors between type families -}
infixr 1 :->
data IFun a b i = IFun {appIFun :: a i -> b i}

type All x = forall i . x i

-- The number of dashes correspond to the number of indices
type f :-> g  = forall x . f x -> g x
type f :--> g = forall x . f x :-> g x
type f :---> g = forall x . f x :--> g x
type f :----> g = forall x . f x :---> g x

type Arr2 f g h = f -> g -> h
type Arr2_1 f g h = forall x . Arr2 (f x) (g x) (h x)
type Arr2_2 f g h = forall x . Arr2_1 (f x) (g x) (h x)
type Arr2_3 f g h = forall x . Arr2_2 (f x) (g x) (h x)
type Arr2_4 f g h = forall x . Arr2_3 (f x) (g x) (h x)

newtype Arr2_1' f g h = Arr2_1 {fromArr2_1 :: Arr2_1 f g h}
newtype Arr2_2' f g h = Arr2_2 {fromArr2_2 :: Arr2_2 f g h}
newtype Arr2_3' f g h = Arr2_3 {fromArr2_3 :: Arr2_3 f g h}
newtype Arr2_4' f g h = Arr2_4 {fromArr2_4 :: Arr2_4 f g h}

newtype PFun a b = PFun {pfun :: a :-> b}

class IFunctor f where
  imap :: a :-> b -> f a :-> f b

data Unit n = Unit
instance Functor Unit where
  fmap m Unit = Unit

-- ** Product
-- product functor
data (f :* g) i = (:*) (f i) (g i) deriving (Read,Show)
infixr 2 :*
instance (Functor f, Functor g) => Functor (f :* g) where
  fmap m (f :* g) = (fmap m f :* fmap m g)

  
-- product of functors
data (f :*: g) (e :: * -> *) i = (:*:) (f e i) (g e i) deriving (Read,Show)
infixr 2 :*:
instance (IFunctor f, IFunctor g) => IFunctor (f :*: g) where
  imap m (f :*: g) = (imap m f :*: imap m g)
