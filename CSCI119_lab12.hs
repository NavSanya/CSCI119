import Data.List (foldl')
import Data.Char (isUpper)

-- CFG G = (Start, Follows)
type CFG = (Char, Char -> Char -> [String])

accept :: CFG -> [Char] -> Bool
accept (s,d) = elem [] . foldl' (\xs c -> concatMap (lq c) xs) [[s]] where
  lq a [] = []
  lq a (x:xs) | isUpper x = map (++ xs) $ d x a          -- nonterminal
              | otherwise = if a == x then [xs] else []  -- terminal

-- Example 1: Balanced parentheses (not including the empty string)
-- original: S --> () | (S) | SS
-- in TNF:   S --> () | ()S | (S) | (S)S
bp :: CFG
bp = ('S', d) where
  d 'S' '(' = [")", ")S", "S)", "S)S"]
  d 'S' ')' = []

-- Example 2: {a^i b^j c^{i+j} | i >= 0, j > 0}
-- original: S --> aSc | T
--           T --> bTc | bc
-- in TNF:   S --> aSc | bTc | bc
--           T --> bTc | bc
pl = ('S', d) where
  d 'S' 'a' = ["Sc"]  ;  d 'S' 'b' = ["Tc","c"]  ;  d 'S' 'c' = []
  d 'T' 'a' = []      ;  d 'T' 'b' = ["Tc","c"]  ;  d 'T' 'c' = []
  
-- original: S--> b | a | ab | bS | Sa | aSb  -- after remove epsilon
-- in TNF:   S--> b | a | ab | bS | aSb | aS
g_six :: CFG
g_six = ('S', d) where
  d 'S' 'a' = ["Sb", "b", "S", []]; d 'S' 'b' = ["S", []]
 
-- original: S--> ab | ba | SS | S | S | aSb | bSa -- after remove epsilon
-- in TNF:   S--> ab | ba | aSb | bSa
g_five :: CFG
g_five = ('S', d) where
  d 'S' 'a' = ["Sb", "b"]; d 'S' 'b' = ["Sa", "a"]
  
g_two :: CFG          
g_two = ('R', d) where
  --d 'R' 'a' = ["A", "AA", "AA + A"]
  d 'R' '0' = []
  d 'R' '1' = []
  d 'R' 'a' = ["A", "AA", "+A", []]
  d 'R' 'b' = ["A", "AA", "+A", []]
  d 'R' '(' = ["R)"] 
  d 'A' '0' = []
  d 'A' '1' = []
  d 'A' 'a' = []
  d 'A' 'b' = []
  d 'A' '*' = []
  d 'A' '(' = ["R)"]
  d 'A' ')' = []

