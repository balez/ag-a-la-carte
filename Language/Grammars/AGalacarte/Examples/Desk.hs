-- * Top
{- GHC version 7.8.3
Author: Florent Balestrieri

Use -fcontext-stack=35 to compile.

Simple attribute grammar example of a desk calculator, taken from 

"Attribute Grammar Paradigms -- a High-level Methodology in Language Implementation"
by Jukka Paakki

also illustrated in

"Zipper-based Attribute Grammars and their Extensions"
by Pedro Martins, João Paulo Fernandes, João Saraiva
-}

-- ** Options
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

-- ** Module
module Language.Grammars.AGalacarte.Examples.Desk where
-- ** Import
import Language.Grammars.AGalacarte

import Prelude hiding (print)
import qualified Prelude
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)

main = do
  Prelude.print $ runDeskG deskExample
  Prelude.print $ runRenameDeskG deskExample
  Prelude.print $ testDeskExt twiceExample

-- * Description
{- attribute grammar from
"LocAttribute Grammar Paradigms\&Mdash;a High-level Methodology in Language Implementation"
verbatim from "Zipper-based Attribute Grammars and their Extensions"

(p1) Prog -> PRINT Exp Cons
{ Prog.code = if Cons.ok then Exp.code + (PRINT, 0) + (HALT, 0) else (HALT,  0)
, Exp.envi = Cons.envs }

(p2) Exp1 -> Exp2 ’+’ Fact
{ Exp1.code = if Fact.ok then Exp2.code + (ADD, Fact.value) else (HALT, 0)
, Exp2 .envi = Exp1 .envi
, Fact.envi = Exp1 .envi }

(p3) Exp -> Fact
{ Exp.code = if Fact.ok then (LOAD, Fact.value) else (HALT, 0)
, Fact.envi = Exp.envi }

(p4) Fact -> Name
{ Fact.ok = isin (Name.name, Fact.envi)
, Fact.value = getvalue (Name.name, Fact.envi) }

(p5) Fact -> Number
{ Fact.ok = true
, Fact.value = Number.value }

(p6) Name -> Id
{ Name.name = Id.name }

(p7) Cons -> empty
{ Cons.ok = true
, Cons.envs = () }

(p8) Cons -> WHERE DefList
{ Cons.ok = DefList.ok
, Cons.envs = DefList.envs }

(p9) DefList1 -> DefList2 ’,’ Def
{ DefList1.ok = DefList2.ok && not isin (Def.name, DefList2.envs)
, DefList1.envs = DefList2.envs + (Def.name, Def.value) }

(p10) DefList -> Def
{ DefList.ok = true
, DefList.envs = (Def.name, Def.value) }

(p11) Def -> Name ’=’ Number
{ Def.name = Name.name
, Def.value = Number.value}
-}

-- * Datatypes for Desk programs

-- note we use quotes because the same names are 
-- used later to define the AG-a-la-carte implementation.

data Prog  = Print' Exp' [Def']          deriving Show
data Exp'  = Exp' :+ Fact' | Fact' Fact' deriving Show
data Fact' = Var' String | Cst' Int      deriving Show
data Def'  = String := Int               deriving Show

deskExample =
  Print' (Fact' (Var' "x") :+ Var' "y" :+ Cst' 11) ["x" := 22, "y" := 33]

{- deskExample represents the desk program

PRINT x + y + 11 WHERE x = 22, y = 33
-}

-- ** Target language
{- Instructions of the target machine, we want to produce a
  list of instructions from a desk program.

The previous example compiles to:
GHCI> runDeskG deskExample
[LOAD 22, ADD 33, ADD 11, PRINT, HALT]
-}
data Instr = LOAD Int | ADD Int | PRINT | HALT
  deriving Show

-- ** Container representation
{- Representation of the context free grammar
  using containers -}

-- *** Non Terminals
data PROG
data EXP
data DEF
data DEFS
data FACT

-- *** Productions
-- **** Print
data Print = Print
instance Constructor Print where
  type Production Print = PROG :==> '[EXP, DEFS]

-- **** Add
data Add = Add
instance Constructor Add where
  type Production Add = EXP :==> '[EXP, FACT]

-- **** Fact
data Fact = Fact
instance Constructor Fact where
  type Production Fact = EXP :==> '[FACT]

-- **** Var
data Var = Var String
instance Constructor Var where
  type Production Var = FACT :==> '[]

-- **** Cst
data Cst = Cst Int
instance Constructor Cst where
  type Production Cst = FACT :==> '[]

-- **** Defnil
data Defnil = Defnil
instance Constructor Defnil where
  type Production Defnil = DEFS :==> '[]

-- **** Defcons
data Defcons = Defcons
instance Constructor Defcons where
  type Production Defcons = DEFS :==> '[DEF, DEFS]

-- **** Def
data Def = Def String Int
instance Constructor Def where
  type Production Def = DEF :==> '[]

-- *** Children Names
type PrintEXP  = N0
type PrintDEFS = N1
type AddLeft   = N0
type AddRight  = N1
type DefHead   = N0
type DefTail   = N1
type FactP     = N0

print_exp  = n0
print_defs = n1
add_left   = n0
add_right  = n1
def_head   = n0
def_tail   = n1
fact_p     = n0


-- *** Smart constructors
print   = injC proxies Print
add     = injC proxies Add
fact    = injC proxies Fact
var     = injC proxies . Var
cst     = injC proxies . Cst
defnil  = injC proxies Defnil
defcons = injC proxies Defcons
def     = injC proxies `res2` Def

-- ** Generic view
-- *** Constructor list
{- When writing a grammar on a fixed datatype, it may be
interesting to specialise the type of the container, so that
the infered types are readable. This only requires to define
a newtype around the CSum container, and add instances for
Container, IRule', SRule', :<< and :<.
-}

type DeskCList = '[Print, Add, Fact, Var, Cst, Defnil, Defcons, Def]
newtype DeskC p n = DeskC {fromDeskC :: CSum DeskCList p n}
instance Container DeskC where
  container = container . fromDeskC
instance IRule' l (CSum DeskCList) d a g => IRule' l DeskC d a g where
  irule' x = irule' x . fromDeskC
instance SRule' l (CSum DeskCList) d a g => SRule' l DeskC d a g where
  srule' x = srule' x . fromDeskC
instance (a :<< CSum DeskCList) => a :<< DeskC where
  prj (DeskC x) = prj x 
instance (a :< CSum DeskCList) => a :< DeskC where
  inj = DeskC . inj

-- *** Conversion

type DeskExpr = Expr DeskC
progE  :: Prog  -> DeskExpr PROG
expE   :: Exp'   -> DeskExpr EXP
factE  :: Fact'  -> DeskExpr FACT
defsE  :: [Def'] -> DeskExpr DEFS
defE   :: Def'   -> DeskExpr DEF

progE (Print' e ds) = print (expE e) (defsE ds)
expE (e1 :+ e2)    = add (expE e1) (factE e2)
expE (Fact' f)      = fact $ factE f
factE (Var' v)      = var v
factE (Cst' x)      = cst x
defsE []           = defnil
defsE (d:ds)       = defcons (defE d) (defsE ds)
defE  (v := x)     = def v x

-- * Attributes

{- code  - synthesized target code
   name  - synthesized name of a variable
   value - synthesized value of a constant or an expression
   ok    - synthesized attribute that indicates correcteness
   envs  - synthesized environment (symbol table)
   envi  - inherited environment (symbol table)
-}

-- *** Attribute Types
-- **** Code
data Code = Code
instance Attribute Code where
  type Mode Code = Synthesized
  type Type Code a c n = [Instr]
  type Domain Code = Over '[PROG, EXP]
instance Bifunctor Code where bimap = cst3 id

-- **** Name
data Name = Name
instance Attribute Name where
  type Mode Name = Synthesized
  type Type Name a c n = String
  type Domain Name = Over '[DEF]
instance Bifunctor Name where bimap = cst3 id

-- **** Value
data Value = Value
instance Attribute Value where
  type Mode Value = Synthesized
  type Type Value a c n = Int
  type Domain Value = Over '[DEF, FACT]
instance Bifunctor Value where bimap = cst3 id

-- **** Ok
data Ok = Ok
instance Attribute Ok where
  type Mode Ok = Synthesized
  type Type Ok a c n = Bool
  type Domain Ok = Over '[DEFS, FACT]
instance Bifunctor Ok where bimap = cst3 id

-- **** EnvS
type SymbolTable = Map String Int
data EnvS = EnvS
instance Attribute EnvS where
  type Mode EnvS = Synthesized
  type Type EnvS a c n = SymbolTable
  type Domain EnvS = Over '[DEFS]
instance Bifunctor EnvS where bimap = cst3 id

-- **** EnvI
data EnvI = EnvI
instance Attribute EnvI where
  type Mode EnvI = Inherited
  type Type EnvI a c n = SymbolTable
  type Domain EnvI = Over '[EXP, FACT]
instance Bifunctor EnvI where bimap = cst3 id

-- * Semantic rules
-- Desk is a namespace / a rule set.
data Desk = Desk

type DeskAspect =
  IA Desk '[Code, EnvS, Ok, Value, Name, EnvI]

-- **** Code
instance (UseS a '[Ok]) => SRule c a Desk Code Print where
  srule _ i Print e d =
    if Ok! d then Code! e ++ [PRINT, HALT] else [HALT]

instance (UseS a '[Ok, Value]) => SRule c a Desk Code Add where
  srule _ i Add e f =
    if Ok! f
    then Code! e ++ [ADD $ Value! f]
    else [HALT]

instance (UseS a '[Ok, Value]) => SRule c a Desk Code Fact where
  srule _ i Fact f =
    if Ok! f then [LOAD $ Value! f] else [HALT]

-- **** EnvS
instance SRule c a Desk EnvS Defnil where
  srule _ i Defnil = Map.empty
instance (UseS a '[Name, Value]) => SRule c a Desk EnvS Defcons where
  srule _ i Defcons h t =
    Map.insert (Name! h) (Value! h) (EnvS! t)
          
-- **** Ok
instance (UseI a '[EnvI]) => SRule c a Desk Ok Var where
  srule _ i (Var name) = Map.member name (EnvI! i)
instance SRule c a Desk Ok Cst where
  srule _ i _ = True
instance SRule c a Desk Ok Defnil where
  srule _ i _ = True
instance (UseS a '[Name, EnvS]) => SRule c a Desk Ok Defcons where
  srule _ i Defcons h t =
    Ok! t && not (Map.member (Name! h) (EnvS! t))

-- **** Value
instance (UseI a '[EnvI]) => SRule c a Desk Value Var where
  srule _ i (Var name) = fromJust $ Map.lookup name (EnvI! i)
instance SRule c a Desk Value Cst where
  srule _ i (Cst x) = x
instance SRule c a Desk Value Def where
  srule _ i (Def name value) = value

-- **** Name
instance SRule c a Desk Name Def where
  srule _ i (Def name value) = name

-- **** EnvI
{- Inherited Attribute.

Cases for Add and Fact are taken care of by the default
instance which automatically copies attributes from parents
to children. For this we need to fall back to the Copy grammar
by default.
-}

type instance Import Desk = '[]
type instance Default Desk = Copy

{-
The only case that is not either copying the attribute or trivial,
and thus requires a IRule instance is the initialisation.
Note that the other child of Print is DEFS
which doesn't inherit EnvI. So we let the default instance of
IRule take care of it.

This order of attributes in a fragment do not matter.
-}

instance (UseS a '[EnvS]) => IRule c a Desk EnvI Print PrintEXP where
  irule _ i Print e d = EnvS ! d

-- * Running the AG
deskF envi = envi `asAttr` EnvI & Code & EnvS & Ok & Name & Value

--runDeskG :: Prog -> [Instr]
runDeskG prog = Code ! run Desk (deskF attrTrivial) exp
  where exp = progE prog

-- ** renaming
{- Completely boiler plate,
Would benefit from a template haskell implementation -}
data Ok' = Ok'
instance Attribute Ok' where
  type Mode Ok' = Mode Ok
  type Type Ok' a c n = Type Ok a c n
  type Domain Ok' = Domain Ok
instance Bifunctor Ok' where
  bimap (_ :# p) = bimap ((P :: P Ok) :# p)
instance Coerce Ok' Ok where
  coerce _ = id
instance Coerce Ok Ok' where
  coerce _ = id

data EnvI' = EnvI'
instance Attribute EnvI' where
  type Mode EnvI' = Mode EnvI
  type Type EnvI' a c n = Type EnvI a c n
  type Domain EnvI' = Domain EnvI
instance Bifunctor EnvI' where
  bimap (_ :# p) = bimap ((P :: P EnvI) :# p)
instance Coerce EnvI' EnvI where
  coerce _ = id
instance Coerce EnvI EnvI' where
  coerce _ = id

renameDeskF envi =
  deskF envi `renaming` (Ok |-> Ok' . EnvI |-> EnvI')
  where infixr 8 .
        (.) = (Prelude..)

runRenameDeskG prog = Code ! run Desk (renameDeskF attrTrivial) exp
  where exp = progE prog


-- ** Macros (Twice)
-- *** Datatype definition
data Twice' = Twice'
instance Constructor Twice' where
  type Production Twice' = EXP :==> '[FACT]
type TwiceP = N0
twice_p = n0
itwice = injC proxies Twice'

-- *** Grammar Rules for Twice
-- **** New Aspect
{- Note that creating a new aspect namespace was not
necessary here, we could have extended Desk. -}

-- We make a new namespace
data DeskExt = DeskExt
withDeskExtP :: DeskExt :# c :#N
withDeskExtP = proxies

type instance Import DeskExt =
  '[ IA Copy '[Macro Twice']
   , IC Macros '[Twice']
   , DeskAspect
   , UtilsAspect]

{- We need to provide a instance for Self on Twice because
there is a overlap between the Self instance on every constructor
and the Twice' instance on every attribute.

They behave differently: if we keep the Twice' instance, the
result would be "Add x x" instead of "Twice' x" if we use the
Self instance.

Self is defined on the grammar Utils, so we get the
implementation by "srule . macroFromP".
-}

{- This requires overlapping instances, since it
    overlaps with the macro rules
   alternatively, we could define it in a different aspect that only imports the
   macro for specific attributes.
-}
-- instance (Twice' :< c)
--          => SRule c a DeskExt Self Twice' where
--   srule = srule . utilsFromP

-- *** Macro definition
{- The constraints on the constructors are inferred
twice_macro
  :: (Add :< c, Fact :< c) =>
     PFrag '[Macro Twice'] '[] c r r '[Macro Twice'] n
-}

twice_macro = frag $ Macro Twice' `with`
   MacroDef (\_ e -> add (fact e) e)
            (Top :> Add --> add_left
                 :> Fact --> fact_p
            :. E)

testDeskExt ::
  Expr (C Twice' :+: DeskC) PROG -> [Instr]
testDeskExt e =
  Code ! runHoagWithUtils DeskExt
           (\envi -> deskF envi & twice_macro)
           (getAttr EnvI)
           attrTrivial e

-- **** Example with twice
-- Since the initial desk type doesn't have the twice constructor,
-- we use alacarte constructors directly.
infixr 5 `defcons`
infixl 5 `add`
twiceExample :: Expr (C Twice' :+: DeskC) PROG
twiceExample =
  print (itwice (var "x")
          `add` var "y"
          `add` (cst 11))
          (def "x" 22
           `defcons`
           def "y" 33
           `defcons`
           defnil)
ex = print (fact (var "x") `add` var "y" `add` cst 11)
      (def "x" 22 `defcons` def "y" 33 `defcons` defnil)
