-- * Top
{- GHC version 7.8.3
Direct translation of the table formatting example of
From "Designing and Implementing Combinator Languages"
AFP'98
by Swierstra, S. D. and Azero Alocer, P. R. and Saraiava, J.

Note that the algorithm requires the table to have
the same number of columns in every row.

Use -fcontext-stack=38 to compile
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
, LambdaCase
 #-}


module  Language.Grammars.AGalacarte.Examples.TableFormatting where
-- ** Import
import Language.Grammars.AGalacarte hiding (Elem, Sum, All)
import Data.Monoid hiding (Sum)
-- * Table Formatting
-- ** Auxiliary definitions
-- ** Monoids
data Max = Max {fromMax :: Int}
data Sum = Sum {fromSum :: Int}
maxBij = Bij Max fromMax
sumBij = Bij Sum fromSum

instance Monoid Max where
 mempty = Max 0
 mappend = binop maxBij max
instance Monoid Sum where
 mempty = Sum 0
 mappend = binop sumBij (+)

instance Convert Int Max where
  convert = Max
instance Convert Max Sum where
  convert = Sum . fromMax

instance Convert a [a] where
  convert x = [x]


-- ** AG Namespace
data TableFmt = TableFmt

type instance Import TableFmt =
  '[ IA Utils '[SynNode]
   , IA Collect '[MinHeight, MinWidths, Lines]
   , IA Copy '[FinalHeight, FinalWidths]
  ]

-- Attributes exported by the namespace TableFmt
type TableFmtA = IA TableFmt
  '[Lines, MinHeight, MinWidths, LineMinWidths, FinalHeight, FinalWidths]

-- ** Listing 21 TableData.ag
-- *** Non Terminals
data TABLE
data ROWS
data ROW
data ELEMS
data ELEM

-- *** Productions
data Table = Table
instance Constructor Table where
  type Production Table = TABLE :==> '[ROWS]

data RowsNil = RowsNil
instance Constructor RowsNil where
  type Production RowsNil = ROWS :==> '[]

data RowsCons = RowsCons
instance Constructor RowsCons where
  type Production RowsCons = ROWS :==> '[ROW, ROWS]

data Row = Row
instance Constructor Row where
  type Production Row = ROW :==> '[ELEMS]

data ElemsNil = ElemsNil
instance Constructor ElemsNil where
  type Production ElemsNil = ELEMS :==> '[]

data ElemsCons = ElemsCons
instance Constructor ElemsCons where
  type Production ElemsCons = ELEMS :==> '[ELEM, ELEMS]

data ElemStr = ElemStr String
instance Constructor ElemStr where
  type Production ElemStr = ELEM :==> '[]

data ElemTab = ElemTab
instance Constructor ElemTab where
  type Production ElemTab = ELEM :==> '[TABLE]

-- *** Children Names
type Head = N0
type Tail = N1
type RowElems = N0
type TableRows = N0

-- *** Smart constructors
table     = injC proxies Table
rowsNil   = injC proxies RowsNil
rowsCons  = injC proxies RowsCons
row       = injC proxies Row
elemsNil  = injC proxies ElemsNil
elemsCons = injC proxies ElemsCons
elemStr   = injC proxies . ElemStr
elemTab   = injC proxies ElemTab

-- *** Table Constructors
type TableCons = '[Table, RowsNil, RowsCons, Row, ElemsNil, ElemsCons, ElemStr, ElemTab]
type TableExpr = Expr (CSum TableCons)
-- ** Example
exTable = table $ rowsCons (row $ elemsCons (elemStr "the")
                                $ elemsCons (elemStr "table")
                                $ elemsNil)
                $ rowsCons (row $ elemsCons (elemTab innerTable)
                                $ elemsCons (elemStr "carte")
                                $ elemsNil)
                $ rowsNil
 where
    innerTable = table $ rowsCons (row $ elemsCons (elemTab t1)
                                       $ elemsCons (elemStr "using")
                                       $ elemsNil)
                       $ rowsCons (row $ elemsCons (elemTab t2)
                                       $ elemsCons (elemTab t3)
                                       $ elemsNil)
                  $ rowsNil
    t1 = table $ rowsCons (row $ elemsCons (elemStr "formatter") elemsNil)
               $ rowsCons (row $ elemsCons (elemStr "written") elemsNil)
               $ rowsNil
    t2 = table $ rowsCons (row $ elemsCons (elemStr "attribute")
                               $ elemsCons (elemStr "grammars")
                               $ elemsNil)
               $ rowsNil
    t3 = table $ rowsCons (row $ elemsCons (elemStr "a") elemsNil)
               $ rowsCons (row $ elemsCons (elemStr "la") elemsNil)
               $ rowsNil

-- ** Listing 22 TableHeight.ag
-- *** Attribute declaration
{- synthesized attribute 'mh' for minimal height. I rename it
   for more clarity -}

data MinHeight = MinHeight
instance Attribute MinHeight where
  type Mode MinHeight = Synthesized
  type Type MinHeight a c n = MH n
  type Domain MinHeight = Everywhere
instance Bifunctor MinHeight where bimap = cst3 id

{- We use the monoids Max and Sum and the generic rule Collect
to take care of the cases for ROW, ROWS and ELEMS.
All the other cases need a concrete SRule instance.
-}

type family MH n where
  MH TABLE = Int
  MH ROW = Sum
  MH ROWS = Sum
  MH ELEMS = Max
  MH ELEM = Int

-- *** Semantic rules
instance SRule d a TableFmt MinHeight Table where
  srule _ lhs Table rows =  fromSum (MinHeight! rows) + 1

instance SRule d a TableFmt MinHeight ElemStr where
  srule _ lhs (ElemStr _) = 2

instance SRule d a TableFmt MinHeight ElemTab where
  srule _ lhs ElemTab table = MinHeight! table + 1

{- the semantic rules for ROWS and ELEMS are defined using the "Collect" rule
with the monoids (+,0) and (max,0) -}
minHeight :: TableExpr TABLE -> Int
minHeight table =
  MinHeight ! runAG' TableFmt (frag MinHeight) table

-- ** Listing 23 TableWidths.ag
-- *** Attribute declaration
{- synthesized attribute 'mws' for minimal widths. I rename it
   MinWidths for more clarity -}

data MinWidths = MinWidths
instance Attribute MinWidths where
  type Mode MinWidths = Synthesized
  type Type MinWidths a c n = MWS n
  type Domain MinWidths = Everywhere
instance Bifunctor MinWidths where bimap = cst3 id

type family MWS n where
  MWS TABLE = Int
  MWS ROWS  = [Int]
  MWS ROW   = [Int]
  MWS ELEMS = [Int]
  MWS ELEM  = Int

{- A local definition like "lmw" is implemented as a synthesized attribute
We use the inherited attribute "SynNode" to access the
synthesized attribute of the current node.
we rename "lmw" to "LineMinWidths"
Thus (LineMinWidths! SynNode! lhs) gives us the value.
-}
data LineMinWidths = LineMinWidths
instance Attribute LineMinWidths where
  type Mode LineMinWidths = Synthesized
  type Type LineMinWidths a c n = Int
  type Domain LineMinWidths = Over '[TABLE]
instance Bifunctor LineMinWidths where bimap = cst3 id

-- *** Semantic rules
instance (UseS a '[MinWidths]) =>
         SRule d a TableFmt LineMinWidths Table where
  srule _ lhs Table rows = sum (MinWidths! rows)

instance (Use a '[SynNode] '[LineMinWidths]) =>
         SRule d a TableFmt MinWidths Table where
  srule _ lhs Table rows = (LineMinWidths! SynNode! lhs) + 1

instance SRule d a TableFmt MinWidths RowsNil where
  srule _ lhs RowsNil = repeat 0

instance SRule d a TableFmt MinWidths RowsCons where
  srule _ lhs RowsCons r rs =
    zipWith max (MinWidths! r) (MinWidths! rs)

instance SRule d a TableFmt MinWidths ElemStr where
  srule _ lhs (ElemStr s) = length s + 1

instance SRule d a TableFmt MinWidths ElemTab where
  srule _ lhs ElemTab table = MinWidths!table + 1

{- -- implicit with Collect
instance SRule d a TableFmt MinWidths Row where
  srule _ lhs Row es = MinWidths! es

instance SRule d a TableFmt MinWidths ElemsNil where
  srule _ lhs ElemsNil = []

instance SRule d a TableFmt MinWidths ElemsCons where
  srule _ lhs ElemsCons e es = MinWidths!e : MinWidths!es
-}

minWidths :: TableExpr TABLE -> Int
minWidths table =
  MinWidths! runAG' TableFmt (MinWidths & LineMinWidths & (`as` SynNode)) table

-- ** Listing 24 TableDistr.ag
{- Using inherited attributes, 'FinalHeight' and 'FinalWidths' corresponding to 'ah' and 'aws' in the article,
the MinHeight and MinWidths values of the table are propagated back to the elements so that
they can be formatted correctly.
-}
-- *** Attribute declaration
{- inherited attribute 'ah' for minimal widths. I rename it
   MinWidths for more clarity -}

data FinalHeight = FinalHeight
instance Attribute FinalHeight where
  type Mode FinalHeight = Inherited
  type Type FinalHeight a c n = Int
  type Domain FinalHeight = Over '[ELEMS]
instance Bifunctor FinalHeight where bimap = cst3 id

data FinalWidths = FinalWidths
instance Attribute FinalWidths where
  type Mode FinalWidths = Inherited
  type Type FinalWidths a c n = [Int]
  type Domain FinalWidths = Over '[ROWS, ROW, ELEMS]
instance Bifunctor FinalWidths where bimap = cst3 id

-- *** Semantic rules
{- we rely on the generic copy rule to cover all the other cases -}

instance (UseS a '[MinHeight]) =>
          IRule c a TableFmt FinalHeight Row RowElems where
  irule _ lhs Row elems = fromMax $ MinHeight! elems

instance (UseS a '[MinWidths]) =>
          IRule c a TableFmt FinalWidths Table TableRows where
  irule _ lhs Table rows = MinWidths! rows

instance IRule c a TableFmt FinalWidths ElemsCons Tail where
  irule _ lhs ElemsCons h t = tail $ FinalWidths! lhs

-- ** Listing 25 TableFormats.ag
-- *** Attribute declaration
{- Synthesized attribute 'lines' is a list of each line to be displayed to represent the table. -}

data Lines = Lines
instance Attribute Lines where
  type Mode Lines = Synthesized
  type Type Lines a c n = [String]
  type Domain Lines = Everywhere
instance Bifunctor Lines where bimap = cst3 id

-- *** Semantic rules
{- the cases for
ElemTab, ElemsNil, ElemsCons are covered the Collect rule,
using the list monoid.
-}
instance (Use a '[SynNode] '[LineMinWidths]) =>
          SRule d a TableFmt Lines Table where
  srule _ lhs Table rows =
    bot_right (LineMinWidths! SynNode! lhs) (Lines! rows)

instance SRule d a TableFmt Lines ElemsNil where
  srule _ lhs ElemsNil = repeat []

instance (Use a '[MinHeight, MinWidths]
          '[FinalHeight, FinalWidths])
        => SRule d a TableFmt Lines ElemsCons where
  srule _ lhs ElemsCons e es =
    zipWith (++)
      (top_left (Lines! e) (MinHeight! e) (FinalHeight! lhs)
                    (MinWidths! e) (head $ FinalWidths! lhs))
      (Lines! es)

instance SRule d a TableFmt Lines ElemStr where
  srule _ lhs (ElemStr s) = [s]

-- ** Listing 26 TableFinal.ag
{- Additional layout functions -}

top_left lines mh ah mw aw
 = ("|" ++ hor_line (aw - 1))
 : ["|" ++ l ++ hor_glue (aw-mw) | l <- lines]
 ++ ["|" ++ vg | vg <- ver_glue (aw - 1) (ah-mh)]

bot_right mw lines = [ l ++ "|"
                     | l <- lines ++ ["|" ++ hor_line (mw -1)]]

hor_glue h = replicate h ' '
ver_glue h v = replicate v $ hor_glue h
hor_line n = replicate n '-'

-- ** Format Table
fmtFrag = Lines & MinHeight & MinWidths & LineMinWidths
       & (`as` SynNode)
       & (attrTrivial `asAttr` FinalHeight)
       & (attrTrivial `asAttr` FinalWidths)

printTable ::
  ( c ~ CSum TableCons
  , Rules i s c c a' g
  , ls :=> Lines) =>
   g -> PFrag i s c a' ls ls TABLE -> TableExpr TABLE -> IO ()
printTable namespace fragment table =
  putStr $ unlines $ Lines ! runAG' namespace fragment table

formatTable :: TableExpr TABLE -> IO ()
formatTable = printTable TableFmt fmtFrag

-- * Extensions
{- so far we implemented the table formatting algorithm
exactly as it was specified in the AFP'98 article. Now we
illustrate the modularity offered by the library. We check
that the table is well-formed: it must have the same number
of columns on each row. -}

-- ** TableCheck namespace
data TableCheck = TableCheck
type instance Import TableCheck =
 '[ IA Collect '[CountColumns, CheckColumns]
  ]

-- All attributes defined in namespace TableCheck
type TableCheckA =
  IA TableCheck '[CountColumns, CheckColumns]
-- ** CountColumns
data CountColumns = CountColumns
instance Attribute CountColumns where
  type Mode CountColumns = Synthesized
  type Type CountColumns a c n = CountColumnsT n
  type Domain CountColumns = Everywhere
instance Bifunctor CountColumns where bimap = cst3 id

type family CountColumnsT n where
  CountColumnsT TABLE = [Int]
  CountColumnsT ROWS = [Int]
  CountColumnsT n = Sum

instance SRule d a TableCheck CountColumns ElemStr where
  srule _ lhs (ElemStr s) = Sum 1

instance SRule d a TableCheck CountColumns ElemTab where
  srule _ lhs ElemTab t = Sum 1

-- The other cases are covered with Collect on the monoid Int (0,(+)) 
-- and [Int] ([],(++))

instance Convert Sum [Int] where
  convert x = [fromSum x]

countColumns :: TableExpr TABLE -> [Int]
countColumns table =
  CountColumns! runAG' TableCheck (frag CountColumns) table

-- ** CheckColumns
{- every row must have the same number of columns -}
allequal [] = True
allequal (h:t) = all (== h) t

data CheckColumns = CheckColumns
instance Attribute CheckColumns where
  type Mode CheckColumns = Synthesized
  type Type CheckColumns a c n = CheckColumnsT n
  type Domain CheckColumns = Everywhere
instance Bifunctor CheckColumns where bimap = cst3 id

type family CheckColumnsT n where
  CheckColumnsT TABLE = Bool
  CheckColumnsT ELEM = Bool
  CheckColumnsT n = All

instance SRule d a TableCheck CheckColumns ElemStr where
  srule _ lhs (ElemStr s) = True

instance (UseS a '[CountColumns]) =>
         SRule d a TableCheck CheckColumns ElemTab where
  srule _ lhs ElemTab t = allequal $ CountColumns! t

instance (UseS a '[CountColumns]) =>
         SRule d a TableCheck CheckColumns Table where
  srule _ lhs Table rs = getAll (CheckColumns! rs)
                         && allequal (CountColumns! rs)

-- all other cases covered by Collect with monoid All: Bool(True,And)
instance Convert Bool All where
  convert = All

checkColumns :: TableExpr TABLE -> Bool
checkColumns table =
  CheckColumns! runAG' TableCheck (CountColumns & CheckColumns) table

badTable = table $ rowsCons (row $ elemsCons (elemStr "this")
                                $ elemsCons (elemStr "is")
                                $ elemsCons (elemStr "an")
                                $ elemsNil)
                $ rowsCons (row $ elemsCons (elemStr "invalid")
                                $ elemsCons (elemStr "table")
                                $ elemsNil)
                $ rowsNil

-- ** Combining aspects from multiple namespaces
{- we now combine the check with the formatting -}
data CheckFmt = CheckFmt
type instance Import CheckFmt =
 '[ TableCheckA
  , TableFmtA
  , IA Utils '[SynNode]
  ]

{- We modify the rule for Lines on TABLE, displaying an error
   in case the check is false, otherwise calling the rule defined
 by the aspect TableFmt.
-}
instance (Use a '[SynNode] '[CheckColumns, LineMinWidths]
         ) =>
     SRule d a CheckFmt Lines Table where
  srule p lhs Table rows
    | CheckColumns! SynNode! lhs
         = srule (p `with_namespace` TableFmt) lhs Table rows
    | otherwise = ["Error: some rows have different numbers of columns."]


checkFrag = CheckColumns & CountColumns & fmtFrag

checkFormatTable = printTable CheckFmt checkFrag

{-
We can override a rule for any production, The rest of the
rules are inherited and would call
the new version.

We now change the way the frames are displayed: each corner
used to be drawn with "|", we now use "+".
-}

-- New namespace
data CrossCorner = CrossCorner
type instance Import CrossCorner = 
 '[ TableFmtA
  , IA Utils '[SynNode]
  ]

instance (Use a '[SynNode] '[LineMinWidths]) =>
          SRule d a CrossCorner Lines Table where
  srule _ lhs Table rows =
    cross_bot_right (LineMinWidths! SynNode! lhs) (Lines! rows)

instance (Use a '[MinHeight, MinWidths]
          '[FinalHeight, FinalWidths])
        => SRule d a CrossCorner Lines ElemsCons where
  srule _ lhs ElemsCons e es =
    zipWith (++)
      (cross_top_left (Lines! e) (MinHeight! e) (FinalHeight! lhs)
                    (MinWidths! e) (head $ FinalWidths! lhs))
      (Lines! es)

cross_top_left lines mh ah mw aw
 = ("+" ++ hor_line (aw - 1))
 : ["|" ++ l ++ hor_glue (aw-mw) | l <- lines]
 ++ ["|" ++ vg | vg <- ver_glue (aw - 1) (ah-mh)]

cross_bot_right mw lines =
  (head lines ++ "+")
  : [ l ++ "|" | l <- tail lines]
  ++ ["+" ++ hor_line (mw -1) ++"+"]

crossFormatTable = printTable CrossCorner fmtFrag

-- ** Function Parameters using Inherited Attributes
{- in fact, the only difference between the rules from
"TableFmt" and CrossCorner" is in the deleguated function call "bot_right" or "cross_bot_right"
and "top_left" or "cross_bot_left".
This difference doesn't really justify two different rules.
We could use inherited attributes to hold the external function.
Let us right a third version parameterised by an inherited attribute.
-}

-- Namespace
data ParamFrame = ParamFrame
type ParamFrameAC = IAC ParamFrame '[Lines] '[Table, ElemsCons]

-- Table drawing functions as inherited attributes
data TopLeft = TopLeft
instance Attribute TopLeft where
  type Mode TopLeft = Inherited
  type Type TopLeft a c n =
     [String] -> Int -> Int -> Int -> Int -> [String]
  type Domain TopLeft = Everywhere
instance Bifunctor TopLeft where bimap = cst3 id

data BotRight = BotRight
instance Attribute BotRight where
  type Mode BotRight = Inherited
  type Type BotRight a c n = Int -> [String] -> [String]
  type Domain BotRight = Everywhere
instance Bifunctor BotRight where bimap = cst3 id


instance (Use a '[BotRight, SynNode] '[LineMinWidths]) =>
          SRule d a ParamFrame Lines Table where
  srule _ lhs Table rows =
    (BotRight!lhs) (LineMinWidths! SynNode! lhs) (Lines! rows)

instance (Use a '[TopLeft, MinHeight, MinWidths]
                '[FinalHeight, FinalWidths])
        => SRule d a ParamFrame Lines ElemsCons where
  srule _ lhs ElemsCons e es =
    zipWith (++)
      ((TopLeft!lhs) (Lines! e) (MinHeight! e) (FinalHeight! lhs)
                    (MinWidths! e) (head $ FinalWidths! lhs))
      (Lines! es)

-- ** Namespace parameter
{- The rule CheckFmt for Lines and Table inherits from
TableFmt directly, so we can't combine it with other
namespace like ParamFrame.  So we need to parameterise that
rule with the namespace that it will use to deleguate the
work.
-}
data ParamCheck super = ParamCheck super

instance (Use a '[SynNode] '[CheckColumns]
         , SRule d a super Lines Table
         ) =>
     SRule d a (ParamCheck super) Lines Table where
  srule p lhs Table rows
    | CheckColumns! SynNode! lhs
         = srule (with_super p) lhs Table rows
    | otherwise = ["Error: some rows have different numbers of columns."]

type ParamCheckAC = IAC (ParamCheck ParamFrame) '[Lines] '[Table]

-- ** Combining
{- We combine ParamCheck, ParamFrame, TableCheck, TableFmt -}
  
data ParamCheckFmt = ParamCheckFmt
type instance Import ParamCheckFmt =
 '[ ParamCheckAC
  , ParamFrameAC
  , TableCheckA
  , TableFmtA
  , IA Utils '[SynNode]
  , IA Copy '[TopLeft, BotRight]
  ]

paramCheckFrag tl br = checkFrag & tl `as` TopLeft & br `as` BotRight
paramCheckTable = printTable ParamCheckFmt
  (paramCheckFrag cross_top_left cross_bot_right)
