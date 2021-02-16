-- Lab 6:  FSM constructions for regular operators

import Data.List
import Data.Array
import Control.Monad (replicateM)  -- for strings function below

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)  
--type FSM = ([Int], Int, [Int], Int -> Char -> Int)
type FSM a = ([a], a, [a], a -> Char -> a)


---------------- Your solution to Lab 5, ported to FSM a -------------------

---------------- Part 1: Representing FSMs

-- Check whether a finite state machine (qs, s, fs, d) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (s is in qs)
-- (3) Final states are states (fs is a subset of qs)
-- (4) Transition function d gives a state in qs for every state in qs and
--     letter from sigma
subset :: [Int] -> [Int] -> Bool
subset [] _ = True
subset (x:xs) ys = (elem x ys) && subset xs ys
--checks for subset

trans :: (Int -> Char -> Int) -> [Int] -> Bool
trans ds qs = and [elem (ds q c) qs | q <- qs, c <- sigma]
--trans function for FSM

noDup :: [Int] -> Bool
noDup [] = True
noDup (x:xs) = not (elem x xs) && noDup xs
--Returns true when there are no duplicate
					
checkFSM :: FSM Int -> Bool
checkFSM (qs, s, fs, ds) = (noDup qs) && (elem s qs) && (subset fs qs) && (trans ds qs)

-- Gives the delta* function (recursive in w)
dstar :: FSM Int -> Int -> [Char] -> Int
dstar m q [] = q
dstar m@(qs, s, fs, ds) q (w:ws) = 
    if (elem q qs && elem w sigma)
    then ((dstar m) (ds q w) ws) 
    else -1 --false value

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM Int -> [Char] -> Bool
accept1 (m@(qs, s, fs, ds)) w = elem (dstar m s w) fs 
-- *Main> accept1 oddbs "baab"
-- False
-- *Main> accept1 oddbs "aaaabbbbaaaabbb"
-- True
-- *Main> accept1 oddbs "123a"
-- False


-- Machine acceptance, Definition 2 (via L_q(M))
accept2 :: FSM Int -> [Char] -> Bool
accept2 (m@(qs, s, fs, d)) w = aux s w where
  -- aux q w = whether the machine, starting in q, accepts w (recursive in w)
  aux :: Int -> [Char] -> Bool
  aux x [] = elem x fs
  aux x (w:ws) = aux (d x w) ws
  -- *Main> accept2 oddbs "aaaabbbbaaaabbb"
-- True
-- *Main> accept2 oddbs "baab"
-- False


---------------- Part 2: FSM construction

-- Define a machine that accepts exactly the strings with an odd number of b's
-- (Solution given for illustration)
oddbs :: FSM Int
oddbs = ([0,1], 0, [1], d) where
  d q 'a' = q        -- stay in the same state
  d q 'b' = 1 - q    -- switch states

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM Int
avoid_aab = ([0, 1, 2, 3], 0, [0, 1, 2], d) where
	d 0 'a' = 1
	d 0 _ = 0
	d 1 'a' = 2
	d 1 _ = 0
	d 2 'a' = 2
	d 2 'b' = 3
	d 2 _ = 0
	d 3 _ = 3
	

-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM Int
end_ab = ([0, 1, 2], 0, [2], d) where
	 d 0 'a' = 1
	 d 0 _   = 0
	 d 1 'b' = 2
	 d 1 'a' = 1
	 d 1 _   = 0
	 d 2 'a' = 1
	 d 2 _   = 0

-- Define a function that takes a string and returns a machine that accepts
-- exactly that string and nothing else (compare to 'onestr' from Lab 3)
-- Hint: the expression w ! i gives the i-th character of the string w
exactly :: String -> FSM Int
exactly w= (qs, s, fs, d) where
    i   = length w
    qs  = [0..i+1]
    s   = 0
    fs  = [i]
    d q c  | i < q + 1      = i + 1
            | c == (w !! q)  = q + 1
            | otherwise      = i + 1

-- Test the machines above. Also, try out the exerices at the end of Section 3.2
-- in my notes as FSMs. Do they produce the same results as your RegExp's did?





---------------- Some additional useful functions --------------------------

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Cartesian product (preserves normalization)
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Powerset  (preserves normalization)
power :: [a] -> [[a]]
power [] = [[]]
power (x:xs) = let ys = power xs
               in [] : map (x:) ys ++ tail ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys


---------------- Lab 6 begins here -----------------------------------------

-- Complete the FSM constructions for the regular expression operators
-- and test your functions adquately


-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = ([0], 0, [], d) where d 0 _ = 0 --[[0],[] ] 

-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM x = ([0, 1, 2], 0, [1], d) where d q a = if a == x && q == 0 then 1 else 2
--assume that "a" in sigma

-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs = [(q1, q2) | q1 <- qs1, q2<-qs2, elem q1 fs1 || elem q2 fs2] 
  d (q1,q2) a = (d1 q1 a, d2 q2 a)

-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM m1@(qs1, s1, fs1, d1) m2@(qs2, s2, fs2, d2) = (qs, s, fs, d) where
  x  = power qs2
  correctX q x = norm $ (x ++ [s2 | elem q fs1])
  qs = [(q, x') | q <- qs1, x' <- x, (correctX q x') == x']
  s  = (s1, correctX s1 [])
  fs = [(q, x') | (q, x') <- qs, overlap x' fs2]
  d2' x2 a = [d2 q2 a | q2 <- x2] -- used in d
  d (q, x) a = (q',correctX q' (d2' x a)) where
        q' = d1 q a

-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  x  = power qs1
  correctX x = norm $ (x ++ [s1 | overlap fs1 x])
  qs = [x' |x' <- x, (correctX x') == x', subset x' qs1]
  s  = []
  fs = [] ++ [x' |x' <- x, elem x' qs, overlap x'  fs1]
  d [] a = norm $ [d1 s1 a] 
  d x a  = norm $ [d1 x' a | x' <- x] 


---------------- Bonus Features (for testing and experimenting) ------------

-- Unary set closure (where "set" = normalized list)
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, s, fs, d) = (qs', s, fs', d) where
  qs' = uclosure [s] (\q -> map (d q) sigma)
  fs' = filter (`elem` fs) qs'

-- Change the states of an FSM from an equality type to Int 
-- and use an array lookup for the transition function
intify :: Eq a => FSM a -> FSM Int
intify (qs, s, fs, d) = ([0..n-1], s', fs', d') where
  n = length qs
  m = length sigma
  s'  = ind qs s
  fs' = map (ind qs) fs
  arr = listArray ((0,0), (n-1,m-1)) [ind qs (d q a) | q <- qs, a <- sigma]
  d' q a = arr ! (q, ind sigma a)
  ind (q':qs) q = if q == q' then 0 else 1 + ind qs q

reduce :: Ord a => FSM a -> FSM Int
reduce = intify . reachable

---- Regular expressions, along with output and input
data RegExp = Empty
             | Let Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp

instance (Show RegExp) where    -- use precedence to minimize parentheses
  showsPrec d Empty         = showString "@"
  showsPrec d (Let c)    = showString [c]
  showsPrec d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                              showsPrec 6 r1 .
                              showString "+" .
                              showsPrec 6 r2
  showsPrec d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                              showsPrec 7 r1 .
                              showsPrec 7 r2
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
                              showString "*"

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Let x:rs)

-- Use constructions above to get reduced machine associated with regex
-- Warning: it can take a lot of time/memory to compute these for "big" regex's
-- We will see much better ways later in the course
re2fsm :: RegExp -> FSM Int
re2fsm Empty = emptyFSM
re2fsm (Let c) = letterFSM c
re2fsm (Union r1 r2) = reduce $ unionFSM (re2fsm r1) (re2fsm r2)
re2fsm (Cat r1 r2) = reduce $ catFSM (re2fsm r1) (re2fsm r2)
re2fsm (Star r1) = reduce $ starFSM (re2fsm r1)
