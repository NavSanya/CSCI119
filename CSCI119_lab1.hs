---- CSci 119, Lab 1 ----

-- Note: you will replace all instances of "undefined" below with your answers.


---- Boolean operators

-- The following code tests whether "and" is commutative:
bools = [True, False]
and_commutes = and [(p && q) == (q && p) | p <- bools, q <- bools]

-- Write similar defintions that test whether "or" is commutative,
-- "and" and "or" are associative, "and" distributes over "or",
-- "or" distributes over "and"
or_commutes = and  [(p || q) == (q || p) | p <- bools, q <- bools]
and_assoc = and [((p && q) && r) == (p && (q && r)) | p<-bools, q<-bools, r<-bools]
or_assoc = and [((p || q) || r) == (p || (q || r)) | p<-bools, q<-bools, r<-bools]
and_dist = and [(p && (q || r)) == ((p && q) || (p && r)) |  p<-bools, q<-bools, r<-bools]
or_dist = and [(p || (q && r)) == ((p || q) && (p || r)) |  p<-bools, q<-bools, r<-bools]
          
-- The exclusive-or operation on Bool in Haskell is equivalent to /=.
-- Test the properties of this operation (commutativity, associativity,
-- distributivity over and+or, and distributivity of and+or over it)
-- using the same method as above
xor_commutes = and [(p /= q) == (q /= p) | p <- bools, q <- bools]
xor_assoc    = and [((p /= q) /= r) == (p /= (q /= r)) | p<-bools, q<-bools, r<-bools]
xor_dist_and = and [(p /= (q && r)) == ((p /= q)&&(p /= r)) | p<-bools, q<-bools, r<-bools]
xor_dist_or  = and [(p /= (q || r)) == ((p /= q)||(p /= r)) | p<-bools, q<-bools, r<-bools]
and_dist_xor = and [(p && (q /= r)) == ((p && q)/=(p && r)) | p<-bools, q<-bools, r<-bools]
or_dist_xor  = and [(p || (q /= r)) == ((p || q)/=(p || r)) | p<-bools, q<-bools, r<-bools]
               
-- The implication operator on Bool in Haskell is equivalent to <=.
-- Check whether implication is associative or commutative:
assoc_imp = and [((p <= q) <= r) == (p <= (q <= r)) | p<-bools, q<-bools, r<-bools]
comm_imp = and [(p <= q) == (q <= p) | p <- bools, q <- bools]


----- Evaluating statements involving quantifiers

-- Assume that the universe of discourse is the set {1,2,3,4,5,6,7,8},
-- that is, that the word "number" temporarily means 1, 2, ..., 8.
-- Your solutions to the problems below should work no matter what
-- finite list of integers u is. For example, u = [5, 2, 17, 58, 21].

u = [1..8]

-- Translate each of the following statements first, in a comment, into a
-- logical statement involving forall, exists, and, or, imp, and not,
-- and then into Haskell code that checks ("brute force") whether
-- the statement is true. I'll work one example.

-- 1. "Every number that's greater than 2 is greater than 1"
-- A: forall n, (n > 2) imp (n > 1)
prob1_1 = and [(n > 2) <= (n > 1) | n <- u]   -- direct translation
prob1_2 = and [n > 1 | n <- u, n > 2]         -- using bounded quantifier

-- 2. Every number is either greater than 1 or less than 2
-- A: for all n, (n > 1) or (n > 2)
prob2 = and [(n > 1) || (n < 2) | n <- u]
-- 3. Every two numbers are comparable with <= (i.e., either one is <=
--    the other or vice-versa)
-- A: For all n and k where either (n imp k) or (k imp n)
prob3 = and [((n <= k) || (k <= n)) | n <- u, k <- u]
-- 4. There is an odd number greater than 4
-- A: There exists n, n > 4 and n is odd 
prob4 = or [((n > 4) && (odd n)) | n <- u]

-- 5: There are two odd numbers that add up to 10
-- A: There exists n and k, n+k=10 and n is odd and k is odd
prob5 = or [(n + k == 10) | n <- u, odd n, k <- u, odd k]

-- 6. For every odd number, there is a greater even number (use the Haskell
--    predicates odd, even :: Integral a => a -> Bool)
-- A: For all n, n is odd There exists k, k > n and k is even
prob6 = and [ or [ (k > n) | k <- u, even k] | n <- u, odd n]

-- 7. For every even number, there is a greater odd number
-- A: For all n, n is even There exists k, k > n and k is odd
prob7 = and [ or [ (k > n) | k <- u, odd k] | n <- u, even n]

-- 8. There are two odd numbers that add up to 6
-- A: There exists n, n is odd There exists k, k is odd and n + k = 6
prob8 = or [or [(n + k == 6) | k <- u, odd k] | n <- u, odd n]

-- 9. There is a number that is at least as large as every number
--    (i.e., according to >=)
-- A: For all n, there exists k, k >= n
prob9 = and [ or [ (k >= n) | k <- u] | n <- u]

-- 10. For every number, there is a different number such that there are no
--    numbers between these two.
-- A: For all n, there exists k, for all x , either {(x < n) and (x < k)} or {(x > n) and (x > k)}
prob10 = 
    and [ or [ and [(((x < n) && (x < k)) || ((x > n) && (x > k)))| x <- u] 
    | k <- u] |  n <-u]
