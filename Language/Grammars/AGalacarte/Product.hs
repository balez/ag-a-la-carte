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
    , GADTs
    , TypeFamilies
    , LambdaCase
    , RankNTypes
    , ConstraintKinds
    , PolyKinds
    , DataKinds
 #-}
-- ** Module
module Language.Grammars.AGalacarte.Product
( Prod(..)
, phead
, ptail
, pmap
, ppure
, papp
, plift2
, pzip
, pgetT
, pget
, PElem(..)
, ptabT
, PTabT(..)
, ptab
, pToList
, WithCtxt(..)
, prod_pull_ctxt
, forallD
, forallD'
, pgetD
, pgetD'
, pgetDP
, pairCtxt
, zipDict
, Curry(..)
, prod_uncurry
, prod_curry'
, prod_curry
, psnoc
)
  where
-- ** Import
import Language.Grammars.AGalacarte.Prelude hiding ((.))
import Language.Grammars.AGalacarte.Proxy
import Language.Grammars.AGalacarte.DependentTypes
import Language.Grammars.AGalacarte.Predicates
import Language.Grammars.AGalacarte.Indexed

-- * Product
{- Given an indexed type "el : u -> *" which
interprets codes in a universe "u", and a list of codes
'[c1,...,cn] which are types of kind "u",
the type "Prod '[c1,...cn] el"
is the product of the interpretations of "c1"..."cn", that is:
"(el c1, ..., el cn)".

Expressed as a dependent type function (this is not Haskell):

Prod : (U : Type) -> (El : U -> Type) -> List U -> Type
Prod U El [] = T
Prod U El (c:cs) = El c ** Prod U El cs

where T is the unit type and ** the product.

In Haskell, we implement Prod as a gadt of kind
[u] -> (u -> *) -> *
where 'u' is a kind corresponding to the universe of codes.
-}

infixr 5 :.
data Prod (cs :: [u]) (el :: u -> *) where
  (:.) :: el c -> Prod cs el -> Prod (c ': cs) el
  E :: Prod '[] el

infixr 1 `pmap`, `papp`

phead :: Prod (t ': ts) x -> x t
phead (h :. t) = h

ptail :: Prod (t ': ts) x -> Prod ts x
ptail (h :. t) = t

-- ** functoriality
pmap :: (x :-> y) -> Prod ts x -> Prod ts y
pmap m = \case
  E -> E
  h :. t -> m h :. pmap m t

-- ** applicative functor
ppure :: TList ts -> All x -> Prod ts x
ppure TNil x = E
ppure (TCons t ts) x = x :. ppure ts x

papp :: Prod ts (IFun x y) -> Prod ts x -> Prod ts y
papp E E = E
papp (IFun f :. fs) (x :. xs) = f x :. papp fs xs

plift2 :: Arr2_1 x y z -> Prod ts x -> Prod ts y -> Prod ts z
plift2 f E E = E
plift2 f (x :. xs) (y :. ys) =
  f x y :. plift2 f xs ys

pzip :: Prod ts x -> Prod ts y -> Prod ts (x :* y)
pzip = plift2 (:*)

-- ** Projections
{- Interestingly, if "n" is out of range, then "ListAt ts n" is
   the empty datatype, so it's actually impossible to compute "pgetT n".
-}
pgetT :: TNat n -> Prod ts x -> x (ListAt ts n)
pgetT TZero (x :. xs) = x
pgetT (TSucc n) (x :. xs) = pgetT n xs

pget :: (IsNat n) => P n -> Prod ts x -> x (ListAt ts n)
pget = pgetT . is_nat

-- ** Tabulation
-- "PElem p x n" has the type of the n-th element of product "Prod p x"
type PElem ts x n = (n :<: Len ts, IsNat n) => P n -> x (ListAt ts n)

ptabT :: TList ts -> All (PElem ts x) -> Prod ts x
ptabT t f = case t of
  TNil -> E
  TCons t ts -> f n0 :. ptabT ts (\n -> f (succP n))

type PTabT ts x = All (PElem ts x) -> Prod ts x
ptab :: (IsList ts) => PTabT ts x
ptab = res $ ptabT . is_list
 where res :: Cont (PTabT ts x) (P ts)
       res = ($ P)

-- ** ToList

pToList :: (forall t . x t -> y) -> Prod ts x -> [y]
pToList cast E = []
pToList cast (x :. xs) = cast x : pToList cast xs

-- ** Context
-- we can eliminate local context

newtype WithCtxt c x n = WithCtxt {fromWithCtxt :: c n => x n}

-- this direction is easy
prod_pull_ctxt :: (Forall p c) =>
  Prod p (WithCtxt c x) ->
  Prod p x
prod_pull_ctxt = \case -- we can write "pmap fromWithCtxt"
  E -> E
  x :. p -> fromWithCtxt x :. prod_pull_ctxt p

-- ** Product of dictionaries

forallD :: Forall ts c => P c -> TList ts -> Prod ts (Dict2 c)
forallD c = \case
  TNil -> E
  TCons t ts -> Dict2 :. forallD c ts

forallD' :: (Forall ts c, IsList ts) => ts :# c :#N -> Prod ts (Dict2 c)
forallD' (ts :# c :#N) = forallD c (is_list ts)

-- *** Projecting a dictionary from a product
pgetD ::
  TNat n ->
  TNat a ->
  Leq2 N1 n ->
  Leq3 a k ->
  Leq (Succ k) (a + n) ->
  IntervalRel n a i ->
  Prod i (Dict2 c) ->
  Dict2 c k
-- k == a  
pgetD _ _ _ LeqRefl3 _ (IntervalSucc i) (d :. ds) = d
-- n == 1 ==> k == a
-- (this case is in fact never executed since the previous
-- equation is prioritary)

pgetD n@(TSucc TZero) a LeqRefl k q
  (IntervalSucc IntervalZero) (d :. E) =
    case plus_sym a n of
      Refl -> case leq_antisym q (LeqS (leq3_to_leq k)) of
        Refl -> d
-- k > a, n > 1
pgetD (TSucc n) a (LeqLess ln) (LeqLess3 k) p
      (IntervalSucc i) (d :. ds) =
  case plus_succ_right a n of
    Refl -> pgetD n (TSucc a) ln k p i ds

pgetD' ::
  TNat k ->
  TList ts ->
  Leq (Succ k) (Len ts) ->
  Prod (Range ts) (Dict2 c) ->
  Dict2 c k
pgetD' k ts leq p =
  pgetD (len ts)
        TZero
        (leq_to_leq2 len_positive (len ts))
        (leq_to_leq3 LeqZ k)
        leq
        (interval_rel (len ts) $ n0 :# rangeP tsP :#N)
        p
  where
    tsP = indexP ts
    len_positive = LeqS LeqZ `leq_trans` leq

pgetDP :: (n :<: Len ts, IsNat n, IsList ts) =>
  P n -> P ts -> Prod (Range ts) (Dict2 c) -> Dict2 c n
pgetDP n ts p =
  pgetD' (is_nat n) (is_list ts) (leq $ succP n :# lenP ts :#N) p

-- *** Zipping the context
pairCtxt :: Arr2_1 (Dict2 c) x (WithCtxt c x)
pairCtxt d x = WithCtxt $ case d of Dict2 -> x

zipDict :: Prod ts (Dict2 c) -> Prod ts x -> Prod ts (WithCtxt c x)
zipDict = plift2 pairCtxt

-- ** Currying
type family Curry ts x r where
  Curry '[] x r = r
  Curry (t ': ts) x r = x t -> Curry ts x r

prod_uncurry :: Curry ts x r -> Prod ts x -> r
prod_uncurry x E = x
prod_uncurry f (x :. p) = prod_uncurry (f x) p

prod_curry' :: TList ts -> (Prod ts x -> r) -> Curry ts x r
prod_curry' TNil f = f E
prod_curry' (TCons t ts) f =
  \x -> prod_curry' ts (\p -> f $ x :. p)

prod_curry :: IsList ts => (Prod ts x -> r) -> Curry ts x r
prod_curry = res $ \ts -> prod_curry' (is_list ts)
  where res :: Cont ((Prod ts x -> r) -> Curry ts x r) (P ts)
        res c = c P
-- ** Snoc
psnoc :: Prod ts x -> x t -> Prod (Snoc ts t) x
psnoc E z = z :. E
psnoc (y :. ys) z = y :. psnoc ys z
