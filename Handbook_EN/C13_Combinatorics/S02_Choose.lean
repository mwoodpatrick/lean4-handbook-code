/- English edition source: Handbook/C13_Combinatorics/S02_Choose.lean. -/
import Mathlib

namespace Handbook.C13

open scoped Nat

-- BOOK: begin choose-eval
-- output: 120 (arrangements of five objects)
#eval Nat.factorial 5
#eval Nat.descFactorial 5 2  -- output: 20 (arrange two of five, ₅P₂)
#eval Nat.choose 5 2         -- output: 10 (choose two of five, ₅C₂)
-- BOOK: end choose-eval

-- BOOK: begin choose-formula
-- The textbook formula C(n,k) = n! / (k!(n-k)!)
example (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k = n ! / (k ! * (n - k)!) :=
  Nat.choose_eq_factorial_div_factorial h

-- Pascal’s rule (the recurrence for Pascal’s triangle)
example (n k : ℕ) :
    Nat.choose (n + 1) (k + 1)
      = Nat.choose n k + Nat.choose n (k + 1) :=
  Nat.choose_succ_succ n k
-- BOOK: end choose-formula

-- BOOK: begin choose-symm
-- Symmetry C(n,k) = C(n,n−k): choosing is the same as leaving behind
example (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k = Nat.choose n (n - k) :=
  (Nat.choose_symm h).symm

#eval Nat.choose 10 7  -- output: 120 (= C(10,3))
-- BOOK: end choose-symm

-- BOOK: begin choose-card
-- The central counting fact: the number of k-element subsets is C(n,k)
example (n k : ℕ) :
    ((Finset.range n).powersetCard k).card = Nat.choose n k := by
  simp
-- BOOK: end choose-card

-- BOOK: begin perm-enum
-- Permutations can be enumerated: the full list of 3! = 6 arrangements.
#eval [1, 2, 3].permutations
-- output: [[1,2,3], [2,1,3], [3,2,1], [2,3,1], [3,1,2], [1,3,2]]

example : [1, 2, 3].permutations.length = Nat.factorial 3 := by
  rw [List.length_permutations]
  decide
-- BOOK: end perm-enum

-- BOOK: begin choose-handshake
-- If 30 people each shake hands once, there are C(30,2) = 30·29/2 = 435
-- handshakes
example : Nat.choose 30 2 = 435 := by
  rw [Nat.choose_two_right]

-- The general formula C(n,2) = n(n−1)/2 is available as a named theorem
example (n : ℕ) : Nat.choose n 2 = n * (n - 1) / 2 :=
  Nat.choose_two_right n
-- BOOK: end choose-handshake

-- BOOK: begin choose-lattice
-- Lattice paths: a shortest path four right and three up chooses which
-- three of seven steps go upward
example : Nat.choose 7 3 = 35 := by decide

#eval Nat.choose 7 3  -- output: 35
-- BOOK: end choose-lattice

-- BOOK: begin choose-multiset
-- Permutations with repetition: arrangements of MISSISSIPPI (I×4, S×4,
-- P×2)
#eval Nat.factorial 11 /
  (Nat.factorial 4 * Nat.factorial 4 * Nat.factorial 2)
-- output: 34650

example :
    Nat.factorial 11 /
      (Nat.factorial 4 * Nat.factorial 4 * Nat.factorial 2)
      = 34650 := by
  decide
-- BOOK: end choose-multiset

end Handbook.C13
