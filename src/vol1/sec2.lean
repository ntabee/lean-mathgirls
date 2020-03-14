-- Chapter 2. Love Letters Called Formulas

import tactic.norm_num
import ..common
import ..factorize

set_option profiler true
set_option trace.check true

open tactic

local attribute [simp, reducible] nat.factors
local attribute [simp, reducible] ite

example: 1024 = 2^10 := rfl
#eval divisors 1024
lemma divisors_of_1024: divisors 1024 = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024] := begin
norm_num,
reflexivity,
end

#eval (divisors 1024).length -- = 11
example: (divisors 1024).length = 11 := begin
rw divisors_of_1024, reflexivity,
end

example: (divisors 1024).sum = 2047 := begin
rw divisors_of_1024, reflexivity,
end

#print nat.prime -- the definition of primes
example: ¬ (nat.prime 1) := begin
unfold nat.prime, intro h, let h:=h.left,
have: ¬ (2 ≤ 1), from dec_trivial, contradiction
end

example: 24=2*2*2*3 ∧ 24=1*2*2*2*3 ∧ 24=1*1*2*2*2*3 := by repeat {split}; reflexivity

example {x: ℤ}: x = -3 -> abs(-x) = 3 := begin
intro h, 
calc abs(-x) = abs(-(-3)): by rw [h]
... = abs(3): rfl
... = 3: rfl
end

-- Problem 2.7:
-- Let n: ℕ ≥ 1, show how to derive "the sum of n's divisors".
@[simp, reducible]
def sumdiv (n: ℕ) := (divisors n).sum
#eval sumdiv 1024 -- = 2047
#eval sumdiv 6 -- = 12

open pnat
open decidable

-- sum_pow n e = Σ n^k (k = 0...e)
@[simp, reducible]
def sum_pow (n e: ℕ) := (list.map (λ e, n^e) (list.range (e+1))).sum

#eval sum_pow 2 10 -- = 2047

-- Wrong equation:
--  let n = factorize n = p1^b1 * p2^b2 * ... pm^bm, where
--    pi: ℙ, bi ≥ 1,
--  sumdiv n = (sum_pow p1 b1) + ... + (sum_pow pm bm) = Σ(sum_pow pi bi) (i=1..m) :: wrong!
@[simp, reducible]
def sum_sum_pow (n: ℕ) := (list.map (λ (p: ℕ × ℕ), sum_pow p.1 p.2) (factorize n)).sum -- shorthand
#eval sum_sum_pow 6 -- = 7

def wrong_eqn := ∀ n, sumdiv n = sum_sum_pow n

attribute [simp, reducible] nat.factors
attribute [simp, reducible] ite

-- Show wrong_eqn is indeed wrong
lemma wrong_eqn_is_wrong: ¬ wrong_eqn := begin
intro h,
specialize h 6,
have l: sumdiv 6 = 12, {
  norm_num,
  reflexivity,
},
have r: sum_sum_pow 6 = 7, {
  unfold sum_sum_pow,
  have: factorize 6 = [(2, 1), (3, 1)], {
    norm_num,
    have: nat.min_fac (1+2) = 3, by norm_num, rw this, clear this,
    by_eval (list (ℕ × ℕ)),
  }, rw this, clear this,
  reflexivity,
},
rw [l, r] at h,
have: 12 ≠ 7, from dec_trivial,
contradiction,
end

-- Theorem:
--  let n = factorize n = p1^b1 * p2^b2 * ... pm^bm, as above,
--  sumdiv n = (sum_pow p1 b1) * ... * (sum_pow pm bm) = Π(sum_pow pi bi) (i=1..m)
def prod_sum_pow (n: ℕ) := (list.map (λ (p: ℕ × ℕ), sum_pow p.1 p.2) (factorize n)).prod

#eval prod_sum_pow 1
#eval prod_sum_pow 6

theorem sumdiv_eqn: ∀ n, sumdiv n = prod_sum_pow n := begin
intro,
rw [sumdiv, divisors, divisors_factorized],
rw [prod_sum_pow, factorize],
destruct (nat.factors n), {
  intro h,
  rw h, reflexivity,
}, {
  intros hd tl h,
  have: hd ∈ (nat.factors n), by rw h; 
}
-- case list.cons {
--   have: hd ∈ (nat.factors n), 
--   let F := nat.factors n,
--   change (nat.factors n) with F,
--   have: hd ∈ F, by assumption,
--   have hp: nat.prime hd, by apply nat.mem_factors this, 
-- }

end

#eval factorize 1
#eval (let fs : list (ℕ × ℕ) := factorize n in sumdiv n = prod_sum_pow n) list.nil