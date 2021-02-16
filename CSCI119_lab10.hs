import Data.List
import Data.Array
import Control.Monad (replicateM)  -- for strings function below

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)  
--type FSM = ([Int], Int, [Int], Int -> Char -> Int)
type FSM a = ([a], a, [a], a -> Char -> a)
type Trans a = a -> Char -> [a]
type NFSM a = ([a], [a], [a], Trans a)


-- Boolean binary operation on FSMs. Examples:
-- binopFSM (||) m1 m2 computes union machine
-- binopFSM (&&) m1 m2 computes intersection machine
binopFSM :: (Eq a, Eq b) => (Bool -> Bool -> Bool) -> FSM a -> FSM b -> FSM (a,b)
binopFSM  op (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs = [(q1, q2) | q1 <- qs1, q2<-qs2, elem q1 fs1 `op` elem q2 fs2] 
  d (q1,q2) a = (d1 q1 a, d2 q2 a)
  

-- Reverse FSM to a NFSM. Output machine accepts reverse of language of input machine.
reverseFSM :: Eq a => FSM a -> NFSM a
reverseFSM (qs, s, fs, d) = (nqs, ns, nfs, nd) where
	nqs = qs
	ns = fs
	nfs = [s]
	nd q' a = [q | q <- qs, q' == (d q a)] 


-- Reachable states of a NFSM (similar to reachable but on NFSMs)
nreachable :: Ord a => NFSM a -> [a] 
nreachable m@(qs, s, fs, d) = uclosure s h where
	h q = concat (map (d q) sigma)  
	
  
-- Minimize a FSM. Put all of the above together to compute the minimum machine for m
minimize :: Ord a => FSM a -> FSM a
minimize (qs,s1,f1,d1) = (q1,s,f,d) where
    q1 = qs
    s = s1
    f = [q'|q'<- q1, elem q' f1]
    d q a = _
		   


-- A XOR B = A.B' + A'.B = (A+B).(A'+B') 
-- Test. For example, make sure that the minimal machine agrees with the original machine
-- on lots of input strings. Try for multiple machines.
-- *Main> qs1 = ["", "a", "aa", "ab", "ba", "bb"]
-- *Main> d1 q c = if length q < 2 then q ++ [c] else tail (q ++ [c])
-- *Main> [(q, a, d1 q a)|q <- qs1, a <- sigma]
-- [("",'a',"a"),("",'b',"b"),("a",'a',"aa"),("a",'b',"ab"),("aa",'a',"aa"),("aa",'b',"ab"),("ab",'a',"ba"),("ab",'b',"bb"),("ba",'a',"aa"),("ba",'b',"ab"),("bb",'a',"ba"),("bb",'b',"bb")]

---------Functions from prev labs------------

-- Use constructions above to get reduced machine associated with regex
-- Warning: it can take a lot of time/memory to compute these for "big" regex's
-- We will see much better ways later in the course
-- re2fsm :: RegExp -> FSM Int
-- re2fsm Empty = emptyFSM
-- re2fsm (Let c) = letterFSM c
-- re2fsm (Union r1 r2) = reduce $ unionFSM (re2fsm r1) (re2fsm r2)
-- re2fsm (Cat r1 r2) = reduce $ catFSM (re2fsm r1) (re2fsm r2)
-- re2fsm (Star r1) = reduce $ starFSM (re2fsm r1)


 byp :: RegExp' -> Bool 
byp Zero = False
byp One = True
byp (Let' c) = False
byp (Union' rs) = or [byp r | r<-rs]
byp (Cat' rs) = and [byp r| r<-rs]
byp (Star' r) = True

-- Regular-expression derivatives (aka left quotients) on extended regular
-- expressions, computed directly by recursion.
deriv :: Char -> RegExp' -> RegExp'
deriv _ Zero = Zero
deriv _ One = Zero
deriv a (Let' c) 
    | a == c = One
    | otherwise = Zero
deriv a (Union' rs) = Union' (map (\r-> deriv a r)rs) 
--Union' [(deriv a r) , deriv a (Union' rs)]
deriv a (Cat' rs) = Union' (dCat'_h a rs)
deriv a (Star' r) = Cat'[deriv a r,(Star' r)] 

dCat'_h :: Char -> [RegExp']-> [RegExp']
dCat'_h a [] = []
dCat'_h a (r:rs) = (Cat' ((deriv a r):rs) ):(if byp r then dCat'_h a rs else [])

conv :: RegExp' -> FSM RegExp'
conv r = (qs,s,f,t) where
    qs = uclosure [s] (\q -> [simp (deriv a q) |a <-sigma])
    s = simp r
    f = [q'| q'<-qs, byp q']
    t q a= simp(deriv a q) 

testRE' = toRE' "ab+"
testRE'1 = toRE' "ab+*a+"
-- check if they are valid fsm's
check_test = checkFSM (intify(conv testRE'))
--derivs with valid outputs
test_d = simp$ deriv 'b' testRE'
test_d1 =  testRE'1
--test of zero's
test_dZ =simp$ deriv 'c' (Cat'[Let' 'a', Let' 'f']) 
test_byp = byp testRE' --false
test_byp1 =byp testRE'1 --true

testMachine = conv testRE'1
testMachine1 = conv testRE'
testaccMach = accept1 testMachine ['a','b'] --true
testaccMach1 = accept1 testMachine1 ['a','b'] --false
--
--
--
--
checkFSM :: FSM Int -> Bool
checkFSM (qs, s, fs, ts) 
    | not (dupCheck qs) = False
    | not (s `elem` qs) = False  
    | not (and [a `elem` qs| a <-fs]) = False
    | not(and [(ts a sig) `elem` qs  | a<-qs,sig <- sigma]) = False
    | otherwise = True

dupCheck :: [Int] -> Bool
dupCheck [] = True
dupCheck (x:xs) 
    | x `elem` xs = False
    | otherwise = dupCheck xs

conv' :: FSM Int -> RegExp'
conv' m@(_,s,_,_) = simp $ solution !! s where
  (matrix, consts) = toSPLE m
  solution = solve matrix consts

intify :: Eq a => FSM a -> FSM Int
intify (qs, s, fs, d) = ([0..n-1], s', fs', d') where
  n = length qs
  m = length sigma
  s'  = ind qs s
  fs' = map (ind qs) fs
  arr = listArray ((0,0), (n-1,m-1)) [ind qs (d q a) | q <- qs, a <- sigma]
  d' q a = arr ! (q, ind sigma a)
  ind (q':qs) q = if q == q' then 0 else 1 + ind qs q

lq :: Char -> RegExp -> RegExp
lq s Empty = Empty
lq s (Let a) 
    | s == a = Star Empty
    | otherwise = Empty
lq s (Union r1 r2) = (Union (lq s r1) ( lq s r2))
lq s (Cat r1 r2) 
  --  | byp r1 = (Union (Cat (lq s r1) r2)  (lq s r2))
    |otherwise = (Cat (lq s r1) r2)
lq s (Star r) = (Cat (lq s r) (Star r))
-- Unary set closure (where "set" = normalized list) WTF
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr



-- included for lab
-- Finite state machines (as records), indexed by the type of their states
sigma :: [Char]
sigma = ['a','b']

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys


type FSM a = ([a], a, [a], a -> Char -> a)

data RegExp = Empty
             | Let Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp
             deriving (Show, Eq)
--compact display
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

-- Extended regular expressions, including a name for One = Star Empty,
-- and arbitrary numbers of arguments for (associative) Union and Cat
data RegExp' = Zero | One | Let' Char |
               Union' [RegExp'] | Cat' [RegExp'] | Star' RegExp'
  deriving (Eq, Ord, Show)

-- Convert ordinary RegExps into extended REs
fromRE :: RegExp -> RegExp'
fromRE Empty = Zero
fromRE (Let c) = Let' c
fromRE (Union r1 r2) = Union' [fromRE r1, fromRE r2]
fromRE (Cat r1 r2) = Cat' [fromRE r1, fromRE r2]
fromRE (Star r1) = Star' (fromRE r1)

-- Convert extended REs into ordinary REs, eliminating Union' and Cat' on
-- lists of length < 2, and right-associating them on longer lists
fromRE' :: RegExp' -> RegExp
fromRE' Zero = Empty
fromRE' One = Star Empty
fromRE' (Let' c) = Let c
fromRE' (Union' []) = Empty
fromRE' (Union' [r]) = fromRE' r
fromRE' (Union' (r:rs)) = Union (fromRE' r) (fromRE' (Union' rs))
fromRE' (Cat' []) = Star Empty
fromRE' (Cat' [r]) = fromRE' r
fromRE' (Cat' (r:rs)) = Cat (fromRE' r) (fromRE' (Cat' rs))
fromRE' (Star' r) = Star (fromRE' r)

-- Basic postfix parser for RegExp', assuming binary + and ., for testing
toRE' :: String -> RegExp'
toRE' w = go w [] where
  go [] [r] = r
  go ('0':xs) rs = go xs (Zero:rs)
  go ('1':xs) rs = go xs (One:rs)
  go ('+':xs) (r2:r1:rs) = go xs (Union' [r1,r2]:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat' [r1,r2]:rs)
  go ('*':xs) (r:rs) = go xs (Star' r:rs)
  go (x:xs) rs = go xs (Let' x:rs)

simp :: RegExp' -> RegExp'
simp Zero = Zero
simp One = One
simp (Let' c) = Let' c
simp (Union' rs) = union' $ flat_uni $ map simp rs
simp (Cat' rs) = union' $ flat_cat $ map simp rs
simp (Star' r) = star' $ simp r
-- Smart constructor for Union' that normalizes its arguments and
-- handles the empty and singleton cases
union' :: [RegExp'] -> RegExp'
union' rs =  case norm rs of
  []  ->  Zero
  [r] -> r
  rs  -> Union' rs

-- Smart constructor for Cat' that handles the empty and singleton cases
cat' :: [RegExp'] -> RegExp'
cat' [] = One
cat' [r] = r
cat' rs = Cat' rs

-- Smart constructor for Star' that handles the constant and Star' cases
star' :: RegExp' -> RegExp'
star' Zero = One
star' One = One
star' (Star' r) = star' r
star' r = Star' r

-- Flatten a list of arguments to Union'; assumes each argument is simplified
flat_uni :: [RegExp'] -> [RegExp']
flat_uni [] = []
flat_uni (Zero:rs) = flat_uni rs
flat_uni (Union' rs':rs) = rs' ++ flat_uni rs
flat_uni (r:rs) = r : flat_uni rs

-- Flatten a list of arguments to Cat', turning them into a list of arguments
-- to Union'; assumes each argument is simplified
flat_cat :: [RegExp'] -> [RegExp']
flat_cat rs = fc [] rs where
  -- fc (args already processed, in reverse order) (args still to be processed)
  fc :: [RegExp'] -> [RegExp'] -> [RegExp']
  fc pr [] = [cat' $ reverse pr]
  fc pr (Zero:rs) = []
  fc pr (One:rs) = fc pr rs
  fc pr (Cat' rs':rs) = fc (reverse rs' ++ pr) rs
  fc pr (Union' rs':rs) = concat $ map (fc pr . (:rs)) rs'
  fc pr (r:rs) = fc (r:pr) rs

-- Solve a system of proper linear equations
-- You can assume that the system is correctly formed and proper
solve :: [[RegExp']] -> [RegExp'] -> [RegExp']

solve [] [] = []
solve ((l11:l1J) : rows) (l1':lI') = simp x1 : xI where
  -- l11 is the corner element, and l1J = [l12,...,l1n] is the rest of 1st row
  -- rows are the rest of the rows [[l21,...,l2n], ..., [ln1,...,lnn]]
  -- l1' is the first constant
  -- lI' are the rest of the contants [l2',...,ln']
  
  -- first column [l21, ..., ln1]
  lI1 = map head rows

  -- sub-matrix [[l22,...,l2n], ..., [ln2,...,lnn]]
  lIJ = map tail rows -- drop one on each list within rows

  -- [[l22_bar,...,l2n_bar], ..., [ln2_bar,...,lnn_bar]] computed via (6)
  lIJ_bar = zipWith sixes lI1 lIJ            -- loops for i = 2 .. n
  sixes li1 liJ = zipWith (six li1) l1J liJ  -- loops for j = 2 .. n
  six li1 l1j lij =  Union' [Cat' [li1, Star' l11, l1j], lij] 

--map(\x -> Union'[Cat' [Star' l11,li1, l1j], x]) lij

  -- [l2'_bar,..., ln'_bar] computed via (7)
  lI'_bar = zipWith seven lI1 lI'
  seven li1 li' = Union' [Cat' [li1, Star' l11, l1'], li']
    
  -- recursively solve the system of size n-1
  xI = solve lIJ_bar lI'_bar

  -- compute x1 from xI via (5)
  x1 = Cat' [ Star' l11, Union' (zipWith (\l j -> Cat' [l,j]) l1J xI ++ [l1'])] 
 -- HOW to union the rest of row including 


-- Generate a regular SPLE from an FSM via formulas in Theorem 6.5
toSPLE :: FSM Int -> ([[RegExp']], [RegExp'])
toSPLE (qs,s,fs,d) = (lIJ, lI') where
  
  -- Construct matrix of coefficients (coef i j = Lij)
  lIJ = [[simp (coef i j) | j <- qs] | i <- qs]
  coef i j = Union' [Cat' [Let' a, Star' (Zero)] | a <- sigma, (d i a == j)]


  -- Construct constants
  lI' = [if elem q fs then One else Zero| q <- qs]
--FROM LAB6
delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star (_, _, _, d) = foldl d

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(_, s, fs, _) w = elem (delta_star m s w) fs

-- Powerset  (preserves normalization)
power :: [a] -> [[a]]
power [] = [[]]
power (x:xs) = let ys = power xs
               in [] : map (x:) ys ++ tail ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

--FROM LAB4
finite :: [String] -> RegExp
finite [] = Empty
finite [w] = onestr w
finite (w:ws) = Union (onestr w) (finite ws)


-- Invariant: In LOL n xs, n == length xs
data LOL a = LOL Int [a] deriving (Eq,Ord)

instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is sorted with no duplicates
type Lang a = [LOL a]

-- Smart constructor for (finite) languages
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

-- The one-string and finite languages of Theorem 3.2.
onestr :: String -> RegExp
onestr [] = Star Empty
onestr [x] = Let x
onestr (x:xs) = Cat (Let x) (onestr xs)

lang_of :: RegExp -> Lang Char
lang_of Empty = []
lang_of (Let a) = lang [[a]]
lang_of (Union r1 r2) = merge (lang_of r1) (lang_of r2)
lang_of (Cat r1 r2) = cat (lang_of r1) (lang_of r2)
lang_of (Star r1) = kstar (lang_of r1)

kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr
kstar xs = eps : cat xs (kstar xs)

cat :: Ord a => Lang a -> Lang a -> Lang a
cat [] _ = []
cat _ [] = []
cat (x:xr) ys@(y:yr) = dot x y : merge (map (dot x) yr) (cat xr ys)

dot :: LOL a -> LOL a -> LOL a
dot xs (LOL 0 _) = xs
dot (LOL x xs) (LOL y ys) = LOL (x+y) (xs++ys)

merge :: Ord a => Lang a -> Lang a -> Lang a
merge [] ys = ys
merge xs [] = xs
merge xs@(x:xr) ys@(y:yr) =
  case compare x y of
    LT -> x : merge xr ys
    EQ -> x : merge xr yr
    GT -> y : merge xs yr

