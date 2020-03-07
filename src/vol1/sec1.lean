-- Chapter 1. Sequences and Patterns

import data.nat.prime data.nat.sqrt tactic.norm_num
import ..common

example: 15 = 3*5 := rfl
example: 16 = 2^4 := rfl
example: nat.prime 17 := by norm_num
example: 18 = 2*3^2 := rfl

-- Shorthand: seq [1..n] f = [f 1, .., f n]
def seq {α β :Type} (l: list α) (f: α -> β) := list.map f l

example: seq [1, 2, 3, 4] fib = [1, 1, 2, 3] := rfl

def self_pow: ℕ -> ℕ
| 0 := 0
| n := n^n

example: seq [1, 2, 3, 4] self_pow = [1, 4, 27, 256] := rfl 
-- example: self_pow 5 = 3125 := rfl -- TIMEOUT
#eval self_pow 5
#eval self_pow 6

-- samll prime numbers < 100,
def small_primes := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

-- list.nth with degeneration none -> 0
def nth_or_0 (l : list ℕ) (n: ℕ) := match (list.nth l n) with
| none := 0
| (some v) := v
end

-- a "mimiced prime enumeration" up to small_primes
def nth_prime := nth_or_0 small_primes

-- prime_mul n = ((n-1)-th prime) * (n-th prime)
def prime_mul: ℕ -> ℕ
| 0 := 1 -- sentinel
| (n+1) := (nth_prime n) * (nth_prime (n+1))

example: seq [1, 2, 3, 4, 5] prime_mul = [6, 15, 35, 77, 143] := rfl

-- a small initial segment of π = 3.14159265358979...
def π_init := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9]

def π_digit := nth_or_0 π_init
-- 2*(n-th π digit), up to π_init
def doubled_π_digit (n: ℕ) := 2*(π_digit n)

example: seq [0, 1, 2, 3, 4,  5,  6,  7,  8, 9] doubled_π_digit =
             [6, 2, 8, 2, 10, 18, 4, 12, 10, 6] := rfl

-- an "unpredictable" sequence
def unpredictable: ℕ -> ℕ
| 0 := 0
| 1 := 1
| 2 := 2
| 3 := 3
| 4 := 4
| 5 := 10
| 6 := 20
| 7 := 30
| 8 := 40
| 9 := 100
| 10 := 200
| 11 := 300
| 12 := 400
| n := arbitrary ℕ


-- C_2 m = C(2, m) = m(m+1)/2
def C_2 (m: ℕ) := (m*(m+1))/2
-- [C(2, m), ..., C(2, m+1)-1]
def box (m: ℕ) := seg (C_2 m) (C_2 (m+1))
#eval box 4
-- box_of n = m, s.t. n ∈ box m
def box_of (n: ℕ) := find (λ m, n ∈ (box m)) (list.range (n+1))
#eval box_of 13


-- comb_23 = 2^m * 3^n, s.t.:
-- comb_23 0 = 2^0 * 3^0, in which exponents sum up to 0
--         1 = 2^1 * 3^0
--         2 = 2^0 * 3^1, in which exponents sum up to 1
--         2 = 2^2 * 3^0
--         3 = 2^1 * 3^1
--         4 = 2^0 * 3^2, in which exponents sum up to 2
--         and so force...
def comb_23 (n: nat) := 
  let m := box_of n in
  let bm := box m in
  let e3 := list.index_of n bm in
  let e2 := (list.length bm) - e3 - 1 in
  2^e2 * 3^e3

example: seq [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] comb_23 = [
  2^0*3^0,

  2^1*3^0,
  2^0*3^1,

  2^2*3^0,
  2^1*3^1,
  2^0*3^2,

  2^3*3^0,
  2^2*3^1,
  2^1*3^2,
  2^0*3^3
] := by split; norm_num