-- * Top
{- GHC version 7.8.3
Direct translation of the pretty printing example of
From "Designing and Implementing Combinator Languages"
AFP'98
by Swierstra, S. D. and Azero Alocer, P. R. and Saraiava, J.

There are a lot of details missing from that paper,
but most of it can be found in:
"Optimal pretty-printing combinators" by Azero and Doaitse Swierstra. 

There are other ways this library could be implemented.  For
instance instead of defining the type 'Format' with fields
for the height, total width, last line width, text
representation, as well as the combinators on that type, we
could define each field independently as a synthesized attribute.

The types STRF and TextStruc could also be implemented as an
attribute grammar, thereby providing a much easier
programming interface: rather than manipulating string
functions, we would write a string term having Nil, Cons and
Append as constructors.

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


module  Language.Grammars.AGalacarte.Examples.PrettyPrinting where
-- ** Import
import Language.Grammars.AGalacarte hiding (Elem, Sum, All)
import Data.List.Utils (merge) -- MissingH package
import Data.List (sort)
-- * Pretty printing
-- ** Combinators
{- this is straight from "Optimal pretty-printing combinators" by
  Azero and Doaitse Swierstra.
Please refer to that article for detailed explanations.
-}

-- *** TextStruc
type STRF      = String -> String
type TextStruc = ([STRF], STRF    )
--               (body , last line)

spaces = repeat ' '
empty_ts :: TextStruc
empty_ts = ([], (""++))
text_ts :: String -> TextStruc
text_ts s = ([], (s++) )
above_ts :: TextStruc -> TextStruc -> TextStruc
above_ts (ub,ul) (lb,ll) = (ub ++ ul:lb,ll)
beside_ts::Int-> TextStruc-> TextStruc-> TextStruc
beside_ts _ (lb,ll) ([]       ,rl) = (lb,ll . rl)
beside_ts ne (lb,ll) ((rb:rbs),rl)
  = let sp = (take ne spaces ++)
        nb = lb ++ (ll . rb):map (sp .) rbs
        nl = sp . rl
    in (nb,nl)
indent_ts j (b,l) = (map (sp .) b, sp . l)
  where sp = (take j spaces ++)

-- *** Format describing one layout
data Format = Elem { height  :: Int
                   , last_w  :: Int
                   , total_w :: Int
                   , txtstr  :: TextStruc }
           deriving (Eq,Ord)

instance Eq (String -> String) where
  a == b = a [] == b []

instance Ord (String -> String) where
  a <= b = a [] <= b []

empty_fmt :: Format
empty_fmt = Elem 0 0 0 empty_ts
s2fmt     :: String -> Format
s2fmt s   = Elem 1 l l (text_ts s)
  where l = length s

above_fmt :: Format -> Format -> Format
(Elem 0 0 0 _ ) `above_fmt`     l   = l

u   `above_fmt` (Elem 0 0 0     _ ) = u

(Elem uh ul uw ut) `above_fmt`  (Elem lh ll lw lt)
  = Elem (uh + lh) ll (uw `max` lw)
         (ut `above_ts` lt)

beside_fmt :: Format -> Format -> Format
(Elem 0 0 0 _ ) `beside_fmt` r = r

l `beside_fmt` (Elem 0 0 0 _ ) = l

(Elem lh ll lw lt) `beside_fmt` (Elem rh rl rw rt)
  = Elem (lh + rh - 1) (ll + rl)
         (lw `max` (ll + rw)) (beside_ts ll lt rt)

indent_fmt :: Int -> Format -> Format
indent_fmt i e@(Elem 0 0 0 _ ) = e
indent_fmt i (Elem dh dl dw dt)
   = Elem dh (i + dl) (i + dw) (indent_ts i dt)


-- *** Sets of alternative layouts
-- page width
type PW      = Int
-- sets of layouts ordered in decreasing widths and increasing heights
type Formats = [Format]

empty_fmts :: Formats
empty_fmts = [ empty_fmt ]
text_fmts :: PW -> String -> Formats
text_fmts pw s | length s <= pw = [ s2fmt s ]
               | otherwise      = []


indent_fmts :: PW -> Int -> Formats -> Formats
{- specification 
indent_fmts pw i ds = dropWhile (notFits pw)
                    $ map (indent_fmt i) ds
-}
-- implementation
indent_fmts pw i = map (indent_fmt i)
                 . dropWhile (notFits (pw - i))

notFits pw x = total_w x > pw


above_fmts  :: Formats -> Formats -> Formats

{- -- specification

above_fmts pw us ls = sort [ u `above_fmt` l
                           | u <- us , l <- ls ]
-}

{- Implementation.
   Assuming sorted lists "us", "ls" by decreasing widths. -}
above_fmts us ls
  = mergel [map (u `above_fmt`) ls
           | u <- us]

beside_fmts :: PW -> Formats -> Formats -> Formats
{- -- specification
beside_fmts pw ls rs
  = let l_beside_rs rs l = map (l `beside_fmt`)
                         . dropWhile (tooWide pw l)
                         $ rs
    in sort . concat . map (l_beside_rs rs) $ ls
-}
{- Implementation.
   Assuming sorted lists "us", "ls" by decreasing widths
-}
beside_fmts pw ls rs
  = mergel [ map (l `beside_fmt`)
           . dropWhile (tooWide pw l)
           $ rs
           | l <- ls
           ]

mergel :: Ord a => [[a]] -> [a]
mergel = foldr merge []

tooWide pw x y
  = let new_w=total_w x `max` (last_w x+total_w y)
    in new_w > pw

choice_fmts :: Formats -> Formats -> Formats
choice_fmts as bs
  | null as = bs
  | null bs = as
  | otherwise   = merge as bs



-- ** Context-free grammar
-- Only one non terminal
data PP
-- *** Productions (listing 27)
data Empty = Empty
instance Constructor Empty where
  type Production Empty = PP :==> '[]
 
data Text = Text String
instance Constructor Text where
  type Production Text = PP :==> '[]

data Indent = Indent Int
instance Constructor Indent where
  type Production Indent = PP :==> '[PP]

type Child = N0

data Beside = Beside
instance Constructor Beside where
  type Production Beside = PP :==> '[PP,PP]
type Left = N0
type Right = N1

data Above = Above
instance Constructor Above where
  type Production Above = PP :==> '[PP,PP]

type Upper = N0
type Lower = N1

data Choice = Choice
instance Constructor Choice where
  type Production Choice = PP :==> '[PP,PP]

type Opt_A = N0
type Opt_B = N1

-- *** Menu du jour (set of constructors)
type PP_C = '[Empty, Text, Indent, Beside, Above, Choice]
type PP_E = Expr (CSum PP_C) PP

-- *** smart constructors
infixr 2 >|<
infixr 1 >-<
infixr 0 >^<

empty     = injC proxies Empty
text      = injC proxies . Text
indent    = injC proxies . Indent
(>|<)     = injC proxies Beside
(>-<)     = injC proxies Above
(>^<)     = injC proxies Choice

-- insert a space between to components
a >||< b = a >|< text " " >|< b


-- *** Examples
pp_ites c t e
  =   ifc >||< thent >||< elsee  >||< fi
  >^< ifc >||<  text "then"
      >-< indent 2 t
      >-< text "else"
      >-< indent 2 e
      >-< fi
  >^< ifc >-< thent >-< elsee  >-< fi
  >^< ifc >||< (thent >-< elsee) >-< fi
  where ifc   = text "if"   >||< c
        thent = text "then" >||< t
        elsee = text "else" >||< e
        fi    = text "fi"

example1 = pp_ites (text "x < y") (text "print foobar") (text "print y")

-- ** Attributes
{- we build a list of possible formatting, in decreasing
width and increasing height -}

data Fmts = Fmts
instance Attribute Fmts where
  type Mode Fmts = Synthesized
  type Type Fmts a c n = Formats
  type Domain Fmts = Everywhere
instance Bifunctor Fmts where bimap = cst3 id

data PageWidth = PageWidth
instance Attribute PageWidth where
  type Mode PageWidth = Inherited
  type Type PageWidth a c n = PW
  type Domain PageWidth = Everywhere
instance Bifunctor PageWidth where bimap = cst3 id

-- ** Filtering with page width listing 28
{- we use the combinators directly -}
data PP1 = PP1 -- rule set
type instance Import PP1 =
  '[IA Copy '[PageWidth]]

instance SRule d a PP1 Fmts Empty where
  srule _ lhs Empty = empty_fmts

instance (UseI a '[PageWidth]) => SRule d a PP1 Fmts Text where
  srule _ lhs (Text s) = text_fmts (PageWidth ! lhs) s

instance (UseI a '[PageWidth]) => SRule d a PP1 Fmts Indent where
  srule _ lhs (Indent n) x =
    indent_fmts (PageWidth ! lhs) n (Fmts! x)

instance (UseI a '[PageWidth]) => SRule d a PP1 Fmts Beside where
  srule _ lhs Beside left right =
    beside_fmts (PageWidth ! lhs) (Fmts! left) (Fmts! right)

instance SRule d a PP1 Fmts Above where
  srule _ lhs Above upper lower =
    above_fmts (Fmts! upper) (Fmts! lower)

instance SRule d a PP1 Fmts Choice where
  srule _ lhs Choice optA optB =
    choice_fmts (Fmts! optA) (Fmts! optB)

-- *** testing
        
pp1 w pp =
  Fmts ! runAG' PP1 (Fmts & w `as` PageWidth) pp

test1 w = display $ pp1 w (example1 :: PP_E)

display :: Formats -> IO ()
display [] = error "The page is too narrow."
display (x:_) = display_ts . txtstr $ x -- the best fit is the first element
--display xs = display_ts . txtstr . head . sort $ xs

-- display all solutions from best to worse fit (in terms of height)
displayall = mapM_ (\x -> display_ts (txtstr x) >> newline)
display_ts :: TextStruc -> IO ()
display_ts (body, last) = do
  putStr (unlines (map ($[]) body))
  putStrLn (last [])

newline = putStrLn ""

-- * Better Filtering with frames, listing 29,30
{- In PP1, the page width is a filter that eliminates
layouts when they are too wide.
We now compute some bounds on the width of local expressions,
so that we can eliminate sublayouts earlier.
-}

-- ** Attributes
-- minimum width of a frame
data MinW = MinW
instance Attribute MinW where
  type Mode MinW = Synthesized
  type Type MinW a c n = Int
  type Domain MinW = Everywhere
instance Bifunctor MinW where bimap = cst3 id

-- minimum width of the last line of a frame
data MinLL = MinLL
instance Attribute MinLL where
  type Mode MinLL = Synthesized
  type Type MinLL a c n = Int
  type Domain MinLL = Everywhere
instance Bifunctor MinLL where bimap = cst3 id

data Frame = Frame
instance Attribute Frame where
  type Mode Frame = Inherited
  type Type Frame a c n = (Int,Int) -- body min width, last line min width
  type Domain Frame = Everywhere
instance Bifunctor Frame where bimap = cst3 id
  
-- ** Rules
{- listing 29
SEM PP [ -> minw USE " `max` " "0" : Int
            minll USE " `max` " "0" : Int ]
  | Text   LOC.minw = "length string"
           LHS.minll = "minw"
  | Indent LHS.minw = "int + pP_minw"
              .minll = "int + pP_minll"
  | Beside LHS.minw = "left_minw `max` (left_minll + right_minw)"
              .minll = "left_minll + right_minll"
  | Above LHS.minll = "lower_minll"
  | Choice LHS.minw = "opta_minw `min` optb_minw"
              .minll = "opta_minll `min` optb_minll"
-}

{- I didn't use the collect rule (max, 0)
because it's only used for Empty(0) and Above(max).
-}
                               
data PP2 = PP2

instance SRule d a PP2 MinW Empty where
  srule _ _ Empty = 0
instance SRule d a PP2 MinLL Empty where
  srule _ _ Empty = 0

instance SRule d a PP2 MinW Text where
  srule _ lhs (Text s) = length s
  
instance SRule d a PP2 MinLL Text where
  srule _ lhs (Text s) = length s
  
instance SRule d a PP2 MinW Indent where
  srule _ lhs (Indent n) pp = n + MinW! pp
  
instance SRule d a PP2 MinLL Indent where
  srule _ lhs (Indent n) pp = n + MinLL! pp
  
instance (UseS a '[MinLL])
          => SRule d a PP2 MinW Beside where
  srule _ lhs Beside left right =
    (MinW!left) `max` (MinLL!left + MinW!right)
  
instance SRule d a PP2 MinLL Beside where
  srule _ lhs Beside left right =
    MinLL!left + MinLL!right

instance SRule d a PP2 MinW Above where
  srule _ lhs Above upper lower = (MinW!upper) `max` (MinW!lower)
  
instance SRule d a PP2 MinLL Above where
  srule _ lhs Above upper lower = MinLL!lower

instance SRule d a PP2 MinW Choice where
  srule _ lhs Choice a b = (MinW!a) `min` (MinW!b)
  
instance SRule d a PP2 MinLL Choice where
  srule _ lhs Choice a b = (MinLL!a) `min` (MinLL!b)

-- *** frame
{- listing 30
SEM PP [ frame : T_Frame  <- ]
  | Indent pP   .frame =  "narrow_frame int lhs_frame"
  | Beside left .frame =  "narrow_ll right_minw lhs_frame"
           right.frame =  "narrow_frame left_minll lhs_frame"
SEM Root [ pw : T_PW <- ]
  | Best pP.frame = "(lhs_pw,lhs_pw)"
-->narrow_frame i (s,l)   =  (s-i, l-i)
-->narrow_ll    i (s,l)   =  (s , l-i)
-}

narrow_frame i (s,l)   =  (s-i, l-i)
narrow_ll    i (s,l)   =  (s , l-i)

instance IRule d a PP2 Frame Indent Child where
  irule _ lhs (Indent n) pp = narrow_frame n (Frame!lhs)

instance (UseS a '[MinW])
          => IRule d a PP2 Frame Beside Left where
  irule _ lhs Beside left right =
    narrow_ll (MinW!right) (Frame!lhs)

instance (UseS a '[MinLL])
         => IRule d a PP2 Frame Beside Right where
  irule _ lhs Beside left right =
    narrow_frame (MinLL!left) (Frame!lhs)

-- other cases use the copy rule.

{- I didn't implement the root datatype since it is not
necessary since we can intialise the frame when
running the grammar.  -}

-- *** Formats
{- The implementation using frames is not given explicitly in the articles.
But it's not too difficult to derive it. The inherited frame gives
bounds for the current node on the total width it may occupy
and on the width of the last line.
-}

maxll x = snd (Frame!x)
maxw x = fst (Frame!x)

{- Assuming the text is a single line, it must fit on the
   remaining space of the last line of the previous block.
-}
instance (UseI a '[Frame]) => SRule d a PP2 Fmts Text where
  srule _ lhs (Text s) = text_fmts (maxll lhs) s

instance SRule d a PP2 Fmts Indent where
  srule _ lhs (Indent n) x = map (indent_fmt n) (Fmts!x)
          -- no need for dropWhile since the child node has
          -- already taken care of the layouts that do not fit
 
instance (UseI a '[Frame]) => SRule d a PP2 Fmts Beside where
  srule _ lhs Beside left right =
    beside_fmts (maxw lhs) (Fmts! left) (Fmts! right)

-- empty, above and choice rules are the same as in PP1

type instance Import PP2 =
  '[ IAC PP1 '[Fmts] '[Empty, Above, Choice]
   , IA Copy '[Frame]
   ]

-- ** Tests
pp2 w pp =
  Fmts ! runAG' PP2 (Fmts & (w,w) `as` Frame & MinLL & MinW) pp

test2 w = display $ pp2 w (example1 :: PP_E)

-- * Let Binding
{- In the article, they introduce a single placeholder PAR
and an operation "APPLY" with a list of PP
expressions. Rather than using this approach, we will
implement variable bindings. 
-}

-- ** Let
-- (Let v :- x :. d :. E) corresponds to (let v = x in d)
data Let = Let String
instance Constructor Let where
  type Production Let = PP :==> '[PP,PP]
type Def = N0
type Body = N1

letin = injC proxies . Let

-- ** Variable
data Var = Var String
instance Constructor Var where
  type Production Var = PP :==> '[]

var = injC proxies . Var

-- ** Expressions
type PP_C2 = '[Var,Let] :++ PP_C
type PP_E2 = Expr (CSum PP_C2) PP

-- ** Example
pp_ites2 c t e
  =   letin "ifc" (text "if"   >||< c)
    $ letin "thent" (text "then" >||< t)
    $ letin "elsee" (text "else" >||< e)
    $ letin "fi" (text "fi")
    $ letin "then_else" (var "thent" >-< var "elsee")
    $
      var "ifc" >||< var "thent" >||< var "elsee"  >||< var "fi"
       >^< var "ifc" >||<  text "then"
           >-< indent 2 t
           >-< text "else"
           >-< indent 2 e
           >-< var "fi"
       >^< var "ifc" >-< then_else  >-< var "fi"
       >^< var "ifc" >||< then_else >-< var "fi"
example2 = pp_ites2 (text "x < y") (text "print foobar") (text "print y")
