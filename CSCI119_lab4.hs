-- CSci 119, Lab 4

import Data.List (sort, stripPrefix) -- for your solution to Lab 3
import Control.Monad (replicateM)    -- for strings function at the end


---------------- Code provided to you in Lab 3 ----------------


-- Normalize a list: sort and remove normlicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent normlicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Cartesian product, preserves normalization
cart :: [a] -> [b] -> [(a,b)]
cart xs ys = [(x,y) | x <- xs, y <- ys]

-- Powerset, preserves normalization. Examples:
-- power [] = [[]]
-- power [1] = [[],[1]]
-- power [1,2] = [[],[1],[1,2],[2]]
-- power [1,2,3] = [[],[1],[1,2],[1,2,3],[1,3],[2],[2,3],[3]]
power :: Ord a => [a] -> [[a]]
power [] =  [[]] 
power (x:xs) = norm( power xs ++ [x:ys| ys <- power xs] )


---------------- Length-ordered lists

-- Length-Ordered Lists over "character type" a (aka "strings over a")
-- Invariant: In LOL n xs, n == length xs
-- Note that automatically-derived Ord instance correctly orders LOLs
data LOL a = LOL Int [a] deriving (Eq,Ord)

instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Concatenation of LOLs, preserves invariant
dot :: LOL a -> LOL a -> LOL a
dot (LOL x xs) (LOL y ys) = LOL (x+y) (xs ++ ys) 

-- Reverse of LOLs, preserves invariant
rev :: LOL a -> LOL a
rev (LOL x xs) = LOL x (reverse xs)



---------------- Languages

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is ordered with no normlicates
type Lang a = [LOL a]


-- Constructor for languages, establishes invariant
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

-- Membership for languages (inf lists satisfying invariant included)
memb :: Ord a => LOL a -> Lang a -> Bool
memb x [] = False
memb x (y:ys) = case compare x y of
                LT -> False
                EQ -> True
                GT -> memb x ys
{- memb testing
*Main> memb (LOL 4 "abab") [(LOL 2 "ab"),(LOL 3 "aba"),(LOL 4 "abab")]
True
*Main> memb (LOL 2 "ab") [(LOL 2 "ab"),(LOL 3 "aba"),(LOL 4 "abab")]
True
*Main> memb (LOL 2 "ab") [(LOL 2 "bb"),(LOL 3 "aba"),(LOL 4 "abab")]
False
*Main> memb (LOL 2 "ab") [(LOL 2 "bb"),(LOL 3 "aba"),(LOL 4 "abab")]
False
*Main> memb (LOL 2 "ab") [(LOL 3 "aba"),(LOL 4 "abab")]
False
-}

-- Merge of langages (aka "union")
merge :: Ord a => Lang a -> Lang a -> Lang a
merge [] x = x
merge x [] = x
merge (xs@(x:xr)) (ys@(y:yr)) = if x < y then x : merge xr ys
						else if y < x then y : merge xs yr 
							else if y == x then x : merge xr yr 
							else merge xr yr

-- Concatenation of languages
cat :: Ord a => Lang a -> Lang a -> Lang a
cat [] ys = []
cat xs [] = []
cat (x:xs) (ys@(y:yr)) = dot x y : merge (map (dot x) (yr)) (cat xs ys)

-- Kleene star of languages
kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr 
kstar xs = eps : cat xs (kstar xs)

-- Left quotient of a language by an LOL (cf. Definition 2.16)
-- Hint: Use the stripPrefix function
leftq :: Ord a => LOL a -> Lang a -> Lang a
leftq (LOL i xs) [] = []
leftq (LOL i xs) (LOL j y:ys) = case stripPrefix xs y of
                    Nothing -> leftq (LOL i xs) ys
                    Just zs -> (LOL (j-i) zs):leftq (LOL i xs) ys


---- Regular expressions and the languages they denote 
data RegExp = Empty                -- Empty language
            | Let Char             -- Single letter language
            | Union RegExp RegExp  -- Union
            | Cat RegExp RegExp    -- Concatenation
            | Star RegExp          -- Kleene star
            deriving (Show, Eq)

-- Compact display form for RegExp
newtype Compact = Compact RegExp

instance (Show Compact) where    -- use precedence to minimize parentheses
  showsPrec d (Compact r) = sp d r where
    sp d Empty         = showString "@"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star r1)     = sp 9 r1 .     -- prec(Star) = 8
                         showString "*"


-- Quick and dirty postfix RegExp parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = go w [] where
  go [] [r]              = r
  go ('+':xs) (r2:r1:rs) = go xs (Union r1 r2:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat r1 r2:rs)
  go ('*':xs) (r:rs)     = go xs (Star r:rs)
  go ('@':xs) rs         = go xs (Empty:rs)
  go (x:xs) rs           = go xs (Let x:rs)


-- The language associated to a regular expression, i.e., [[r]]
lang_of :: RegExp -> Lang Char
lang_of (Empty) = []
lang_of (Let c) = [LOL 1 [c]]
lang_of (Union r1 r2) = merge (lang_of r1) (lang_of r2)
lang_of (Cat r1 r2) = cat (lang_of r1) (lang_of r2)
lang_of (Star r1) = kstar (lang_of r1)


-- The one-string and finite languages of Theorem 3.2. It should be the case
-- that, for any string w, lang_of (onestr w) == [w], and for any (finite) list
-- of (distinct, sorted) strings l, lang_of (finite l) == l.
onestr :: String -> RegExp
onestr [] = Star Empty
onestr xs   | (length xs == 1) = Let (head xs)
            | otherwise = Cat (onestr (take 1 xs)) (onestr (tail xs))

finite :: [String] -> RegExp
finite [] = Star Empty
finite [x] = onestr x
finite (x:xs) = Union (onestr x) (finite xs)




---------------- Part 1 ----------------

-- Implement the seven recursive predicates/operations on RegExp given in
-- Section 3.3 of the notes; call them empty, unitary, byp, inf, rever, lq,
-- and nep. Each should begin with a type declaration. Include several tests
-- for each function.
empty :: RegExp -> Bool
empty (Empty) = True
empty (Let c) = False
empty (Union r1 r2) = empty(r1) && empty(r2)
empty (Cat r1 r2) = empty (r1) || empty(r2)
empty (Star r1) = False
{- Emptiness testing
*Main> empty (Empty)
True
*Main> empty (Let 'c')
False
*Main> empty (Union  (Let 'c') (Empty))
False
*Main> empty (Union  (Empty) (Let 'c'))
False
*Main> empty (Union  (Let 'a') (Let 'c'))
False
*Main> empty (Union  (Empty) (Empty))
True
*Main> empty (Cat  (Let 'c') (Empty))
True
*Main> empty (Cat  (Empty) (Let 'c'))
True
*Main> empty (Cat  (Let 'a') (Let 'c'))
False
*Main> empty (Cat  (Empty) (Empty))
True
*Main> empty (Star (Empty))
False
*Main> empty (Star (Let 'a'))
False
-}

unitary :: RegExp -> Bool
unitary (Empty) = False
unitary (Let c) = False
unitary (Union r1 r2) =(unitary (r1) && empty(r2)) || (empty (r1) && unitary (r1)) || (unitary (r1) && unitary (r2))
unitary (Cat r1 r2) = unitary (r1) && unitary (r2)
unitary (Star r) = empty (r) || unitary (r)  
{- Unitarity testing
*Main> unitary (Empty)
False
*Main> unitary (Let 'c')
False
*Main> unitary (Union (Empty) (Let 'c'))
False
*Main> unitary (Union (Let 'c') (Empty))
False
*Main> unitary (Union (Let 'c') (Let 'a'))
False
*Main> unitary (Union (Empty) (Empty))
False
*Main> unitary (Cat (Let 'c') (Empty))
False
*Main> unitary (Cat  (Empty) (Let 'c'))
False
*Main> unitary (Cat  (Let 'a') (Let 'c'))
False
*Main> unitary (Cat  (Empty) (Empty))
False
*Main> unitary (Star (Empty))
True
*Main> unitary (Star (Let 'c'))
False
-}

byp :: RegExp -> Bool
byp (Empty) = False
byp (Let c) = False
byp (Union r1 r2) = byp (r1) || byp (r2)
byp (Cat r1 r2) = byp (r1) && byp (r2)
byp (Star r1) = True

{- Bypassabiltiy testing
*Main> byp (Empty)
False
*Main> byp (Let 'c')
False
*Main> byp (Union (Empty) (Let 'c'))
False
*Main> byp (Union (Let 'c') (Empty))
False
*Main> byp (Union (Let 'a') (Let 'c'))
False
*Main> byp (Union (Empty) (Empty))
False
*Main> byp (Cat (Empty) (Let 'c'))
False
*Main> byp (Cat (Let 'c') (Empty))
False
*Main> byp (Cat (Let 'a') (Let 'c'))
False
*Main> byp (Cat (Empty) (Empty))
False
*Main> byp (Star (Empty))
True
*Main> byp (Star (Let 'a'))
True
-}

inf :: RegExp -> Bool
inf (Empty) = False
inf (Let c) = False
inf (Union r1 r2) = inf (r1) || inf (r2)
inf (Cat r1 r2) = (inf (r1) && not(empty (r2))) || (not(empty (r1)) && inf (r2))
inf (Star r) = not(empty (r)) && not(unitary (r))

{- Infiniteness testing
*Main> inf (Empty)
False
*Main> inf (Let 'a')
False
*Main> inf (Union (Empty) (Let 'c'))
False
*Main> inf (Union (Let 'c') (Empty))
False
*Main> inf (Union (Let 'a') (Let 'c'))
False
*Main> inf (Union (Let 'a') (Let 'c'))
False
*Main> inf (Cat (Empty) (Let 'c'))
False
*Main> inf (Cat (Let 'c') (Empty))
False
*Main> inf (Cat (Let 'a') (Let 'c'))
False
*Main> inf (Cat (Empty) (Empty))
False
*Main> inf (Star (Empty))
False
*Main> inf (Star (Let 'c'))
True
-}

rever :: RegExp -> RegExp
rever (Empty) = Empty
rever (Let c) = Let c
rever (Union r1 r2) = Union (rever (r1)) (rever (r2))
rever (Cat r1 r2) = Cat (rever (r1)) (rever (r2))
rever (Star r) = (Star (rever (r)))

{- Reversal testing
*Main> rever (Empty)
Empty
*Main> rever (Let 'a')
Let 'a'
*Main> rever (Union (Empty) (Let 'c'))
Union Empty (Let 'c')
*Main> rever (Union (Let 'c') (Empty))
Union (Let 'c') Empty
*Main> rever (Union (Let 'a') (Let 'c'))
Union (Let 'a') (Let 'c')
*Main> rever (Union (Let 'a') (Let 'c'))
Union (Let 'a') (Let 'c')
*Main> rever (Cat (Empty) (Let 'c'))
Cat Empty (Let 'c')
*Main> rever (Cat (Let 'c') (Empty))
Cat (Let 'c') Empty
*Main> rever (Cat (Let 'a') (Let 'c'))
Cat (Let 'a') (Let 'c')
*Main> rever (Cat (Empty) (Empty))
Cat Empty Empty
*Main> rever (Star (Empty))
Star Empty
*Main> rever (Star (Let 'c'))
Star (Let 'c')
-}

lq :: Char -> RegExp -> RegExp
lq h (Empty) = Empty
lq h (Let c) =    
    if h == c 
    then (Star (Empty))
    else (Empty)
lq h (Union r1 r2) = 
    (Union (lq h r1) (lq h r2))
lq h (Cat r1 r2) =    
    if (byp r1)
    then (Union (Cat (lq h r1) r2) (lq h r2))
    else (Cat (lq h r1) r2)
lq h (Star r1) = (Cat (lq h r1) (Star r1))

{- Left quotient testing
*Main> lq 'h' (Empty)
Empty
*Main> lq 'h' (Let 'a')
Empty
*Main> lq 'h' (Union (Empty) (Let 'c'))
Union Empty Empty
*Main> lq 'h' (Union (Let 'c') (Empty))
Union Empty Empty
*Main> lq 'h' (Union (Let 'a') (Let 'c'))
Union Empty Empty
*Main> lq 'h' (Union (Let 'a') (Let 'c'))
Union Empty Empty
*Main> lq 'h' (Cat (Empty) (Let 'c'))
Cat Empty (Let 'c')
*Main> lq 'h' (Cat (Let 'c') (Empty))
Cat Empty Empty
*Main> lq 'h' (Cat (Let 'a') (Let 'c'))
Cat Empty (Let 'c')
*Main> lq 'h' (Cat (Empty) (Empty))
Cat Empty Empty
*Main> lq 'h' (Star (Empty))
Cat Empty (Star Empty)
*Main> lq 'h' (Star (Let 'c'))
Cat Empty (Star (Let 'c'))
-}

nep :: RegExp -> RegExp
nep (Empty) = Empty
nep (Let c) = Let c
nep (Union r1 r2) = (Union (nep r1) (nep r2))
nep (Cat r1 r2) =
    if (byp r1)
    then (Union (Cat (nep r1) r2) (nep r2))
    else (Cat (nep r1) r2)
nep (Star r1) = (Cat (nep r1) (Star r1))

{- Nonempty part testing
*Main> nep (Empty)
Empty
*Main> nep (Let 'a')
Let 'a'
*Main> nep (Union (Empty) (Let 'c'))
Union Empty (Let 'c')
*Main> nep (Union (Let 'c') (Empty))
Union (Let 'c') Empty
*Main> nep (Union (Let 'a') (Let 'c'))
Union (Let 'a') (Let 'c')
*Main> nep (Union (Let 'a') (Let 'c'))
Union (Let 'a') (Let 'c')
*Main> nep (Cat (Empty) (Let 'c'))
Cat Empty (Let 'c')
*Main> nep (Cat (Let 'c') (Empty))
Cat (Let 'c') Empty
*Main> nep (Cat (Let 'a') (Let 'c'))
Cat (Let 'a') (Let 'c')
*Main> nep (Cat (Empty) (Empty))
Cat Empty Empty
*Main> nep (Star (Empty))
Cat Empty (Star Empty)
*Main> nep (Star (Let 'c'))
Cat (Let 'c') (Star (Let 'c'))
-}

---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes,
-- where the second algorithm is the modified one I posted on Piazza (@96).
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits xs = [ (take x xs, drop x xs) | x <- [0..(length xs)] ] 

{- spltis testing
*Main> splits "abc"
[("","abc"),("a","bc"),("ab","c"),("abc","")]
*Main> splits "123"
[("","123"),("1","23"),("12","3"),("123","")]
*Main> splits "xyz"
[("","xyz"),("x","yz"),("xy","z"),("xyz","")]
-}

match1 :: RegExp -> String -> Bool
match1 (Empty) w = False
match1 (Let c) "" = False
match1 (Let c) (x:w) = (c == x)
match1 (Union r1 r2) w = (match1 r1 w) || (match1 r2 w)
match1 (Cat r1 r2) w = or [(match1 r1 w1) && (match1 r2 w2) | (w1, w2) <- (splits w)]  
match1 (Star r) w = (w == "") || or [(w1 /= "") && (match1 r w1) && (match1 (Star r) w2) | (w1, w2) <- (splits w)]

{- match1 testing
*Main> match1 (Empty) "a"
False
*Main> match1 (Let 'c') ""
False
*Main> match1 (Let 'c') "c"
True
*Main> match1 (Let 'c') "a"
False
*Main> match1 (ab) "aa"
True
*Main> match1 (ttla) "abb"
True
*Main> match1 (Union ttla ab) "abb"
True
*Main> match1 (Union ttla ab) "aa"
True
*Main> match1 (Cat ttla ab) "aa"
False
*Main> match1 (Cat ttla ab) "abb"
True
*Main> match1 (Star(Empty)) "a"
False
*Main> match1 (Star(Empty)) ""
True
*Main> match1 (Star(ab)) "aa"
True
-}

match2 :: RegExp -> String -> Bool
match2 rs w = match2help [rs] w where
  match2help :: [RegExp] -> String -> Bool 
  match2help [] w  = (w == "") 
  match2help ((Empty):rs) w = False
  match2help ((Let a):rs) "" = False
  match2help ((Let a):rs) (x:w) = ((a:w) == (x:w)) && (match2help rs w) 
  match2help ((Union r1 r2):rs) w = (match2help (r1:rs) w) || (match2help (r2:rs) w)
  match2help ((Cat r1 r2):rs) w =(match2help (r1:r2:rs) w) || ( (byp r1) &&(match2help (r2:rs) w))
  match2help ((Star r1):rs) w =  ( (match2help rs w )) ||  (match2help ((nep r1):(Star r1):rs) w)

{- match2 testing
*Main> match2 [Empty] "a" True
False
*Main> match2 [Empty] "a" False
False
*Main> match2 [Let 'c'] "c" False
True
*Main> match2 [Let 'c'] "c" True
True
*Main>
*Main> match2 [Empty] "a" True
False
*Main> match2 [Empty] "a" False
False
*Main> match2 [Let 'c'] "" True
False
*Main> match2 [Let 'c'] "c" True
True
*Main> match2 [Let 'c'] "a" True
False
*Main> match2 [ab] "aa" True
True
*Main> match2 [ttla] "abb" True
True
*Main> match2 [Union ttla ab] "abb" True
True
*Main> match2 [Union ttla ab] "aa" True
True
*Main> match2 [Cat ttla ab] "aa" True
False
*Main> match2 [Cat ttla ab] "abb" True
True
*Main> match2 [Star(Empty)] "a" True
False
*Main> match2 [Star(Empty)] "" True
False
*Main> match2 [Star(ab)] "aa" True
True
-}

-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get). 

sigma = ['a', 'b']                -- Alphabet used in all examples belo
ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once


-- For your tests, you may also find the following helpful. For example,
-- you can generate all strings of length 10 (or 20) or less and then test
-- to see whether match1 r w == memb (lol w) (lang_of r) for each such w.

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

