-- Chapter 2. Love Letters Called Formulas

import tactic.norm_num tactic.tauto tactic
import init.data.list.lemmas
import ..common ..list ..factorize

open tactic

local attribute [simp, reducible] nat.factors
local attribute [simp, reducible] ite

example: 1024 = 2^10 := rfl
#eval divisors 1024
-- TIMEOUT
-- lemma divisors_of_1024: divisors 1024 = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024] := begin
-- norm_num,
-- reflexivity,
-- end

#eval (divisors 1024).length -- = 11

#eval (divisors 1024).sum -- 2047

#print nat.prime -- the definition of primes
example: ¬ (nat.prime 1) := begin
unfold nat.prime, intro h, let h:=h.left,
have: ¬ (2 ≤ 1), from dec_trivial, contradiction
end

-- Regarding `1` a prime brakes prime-decomposition uniqueness
example: 24=2*2*2*3 ∧ 24=1*2*2*2*3 ∧ 24=1*1*2*2*2*3 := by repeat {split}; reflexivity

example {x: ℤ}: x = -3 -> abs(-x) = 3 := begin
intro h, 
calc abs(-x) = abs(-(-3)): by rw [h]
... = abs(3): rfl
... = 3: rfl
end

section sec_2_7
-- Problem 2.7:
-- Let n: ℕ ≥ 1, show how to derive "the sum of n's divisors".
@[simp, reducible]
def sumdiv (n: ℕ) := (divisors n).sum
#eval sumdiv 1024 -- = 2047
#eval sumdiv 6 -- = 12

open pnat
open decidable

-- sum_pow (n, e) = Σ n^k (k = 0...e)
--   For notational bravity, recall geom p=(n, e) = [n^0, n^1, n^e],  abbr. <| p |>
@[simp, reducible]
def sum_pow (p: ℕ × ℕ) := <| p |>.sum

#eval sum_pow (2, 10) -- = 2047

-- Wrong equation:
--  let n = factorize n = p1^b1 * p2^b2 * ... pm^bm, where
--    pi: ℙ, bi ≥ 1,
--  sumdiv n = (sum_pow p1 b1) + ... + (sum_pow pm bm) = Σ(sum_pow pi bi) (i=1..m) :: wrong!
@[simp, reducible]
def sum_sum_pow (n: ℕ) := (list.map sum_pow (factorize n)).sum -- shorthand
#eval sum_sum_pow 6 -- = 7

def wrong_eqn := ∀ n, sumdiv n = sum_sum_pow n

-- Show wrong_eqn is indeed wrong, by
--  sumdiv 6 = 12 ≠ sum_sum_pow 6 = 7

-- I'll excessively use `factorize 6`, for which dumb `simp factorize 6` timeouts; 
-- so, hand-reproduce the outcome here
lemma factorize_6: factorize 6 = [(2,1), (3,1)] := begin
unfold factorize,
have: nat.factors 6 = [2, 3], {
  unfold nat.factors,
  have: nat.min_fac (4+2) = 2, {
    unfold nat.min_fac,
    have: 2 ∣ 4, by norm_num,
    have: ite (2 ∣ 4) 2 _ = 2, by apply if_pos; assumption, assumption,
  }, rw this, clear this,
  simp,
  have: nat.factors 3 = [3], {
    unfold nat.factors,
    have: nat.min_fac 3 = 3, {
      unfold nat.min_fac,
      have: (nat.min_fac_aux (1 + 2) 3) = 3, {
        rw nat.min_fac_aux,
        reflexivity,
      }, rw this, clear this,
      have: ¬ (2 ∣ 1), by norm_num,
      have: ite (2 ∣ 1) _ 3 = 3, by apply if_neg; assumption, assumption,
    }, rw this, clear this,
    simp,
  },
  have triv3: (nat.succ (4/2)) = 3, by reflexivity,
  rw [triv3, this],
}, rw this, clear this,
simp,
have: list.count 2 [3] = 0, by reflexivity, rw this, clear this,
have: list.count 3 [2, 3] = 1, by reflexivity, rw this, clear this,
have: list.nodup [(2,1), (3,1)], by norm_num,
apply list.erase_dup_eq_self.mpr this,
end

lemma sumdiv_6: sumdiv 6 = 12 := begin
unfold sumdiv, unfold divisors,
rw factorize_6,
norm_num,
have: list.range 2 = [0, 1], by reflexivity, rw this, clear this,
reflexivity,
end

lemma sum_sum_pow_6: sum_sum_pow 6 = 7 := begin
unfold sum_sum_pow, rw factorize_6, reflexivity,
end

theorem wrong_eqn_is_wrong: ¬ wrong_eqn := begin
intro h,
specialize h 6,
rw [sumdiv_6, sum_sum_pow_6] at h,
have: 12 ≠ 7, from dec_trivial,
contradiction,
end

-- Theorem:
--  let n = factorize n = p1^b1 * p2^b2 * ... pm^bm, as above,
--  sumdiv n = (sum_pow p1 b1) * ... * (sum_pow pm bm) = Π(sum_pow pi bi) (i=1..m)
@[simp, reducible]
def prod_sum_pow (n: ℕ) := (list.map sum_pow (factorize n)).prod

theorem sumdiv_eqn: ∀ n, sumdiv n = prod_sum_pow n := begin
intro,
rw [sumdiv, divisors],
rw [prod_sum_pow],
induction (factorize n), reflexivity, {
  rw divisors_aux,
  rw tensor_sum,
  rw ih,
  rw list.map_cons,
  rw list.prod_cons,
}
end

end sec_2_7

section sec_2_8
-- Section 2.8: elaborates Thm 2.7

end sec_2_8