-- Chapter 2. Love Letters Called Formulas

import tactic.norm_num
import ..common

set_option profiler true
set_option trace.check true

def Sigma (m: multiset ℕ) := m.fold (+) 0.

example: 1024 = 2^10 := rfl
#eval (divisors 1024).card -- = 11
#eval (divisors 1024)
#eval Sigma (divisors 1024) -- = 2047

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
def sumdiv (n: ℕ+) := (divisors n).fold (+) 0
-- #eval sumdiv 1024 -- = 2047


open pnat
open decidable

-- "automagic"
meta def wipe_coe :tactic unit := `[
  unfold lift_t, unfold has_lift_t.lift, unfold coe_t, unfold has_coe_t.coe, unfold coe_b, unfold has_coe.coe
]

-- For p: prime, Σ (divisors p) = p+1.
--
-- Lemma: p: prime, divisors p = {1, p}
lemma prime_divisors (p: ℙ): divisors p = {1, p} := begin
unfold divisors, simp,
have pms: factor_multiset p = prime_multiset.of_prime p, by apply factor_multiset_of_prime,
have pms2: factor_multiset_equiv p = factor_multiset p, by refl,
rw [pms2, pms, prime_multiset.of_prime, coe],
clear pms pms2,
wipe_coe,
dsimp [prime_multiset.to_nat_multiset],
simp,
reflexivity,
end
-- Get the desired property as a collorary:
lemma sumdiv_case_prime (p: ℙ): sumdiv p = p+1 := begin
dsimp [sumdiv],
rw [prime_divisors p],
reflexivity,
end 

-- sum_pow n e = Σ n^k (k = 0...e)
def sum_pow: ℕ -> ℕ -> ℕ
| _ 0 := 1
| n (e+1) := (sum_pow n e) + (n^(e+1))

-- Wrong equation:
--  let n = factorize n = p1^b1 * p2^b2 * ... pm^bm, where
--    pi: ℙ, bi ≥ 1,
--  sumdiv n = (sum_pow p1 b1) + ... + (sum_pow pm bm) = Σ(sum_pow pi bi) (i=1..m) :: wrong!
def sum_sum_pow (n: ℕ+) := Sigma (multiset.map (λ (p: ℙ × ℕ), sum_pow p.1 p.2) (factorize n) ) -- shorthand
def wrong_eqn := ∀ n, sumdiv n = sum_sum_pow n

-- Special case: p: ℙ -> sum_sum_pow p = p+1
-- Lemma: factorize p = {(p, 1)}
lemma factorize_prime (p: ℙ): factorize p = {(p, 1)} := begin
rw factorize, norm_num1,
have pms: factor_multiset p = prime_multiset.of_prime p, by apply factor_multiset_of_prime,
have pms2: factor_multiset_equiv p = factor_multiset p, by refl,
rw [pms2, pms, prime_multiset.of_prime],
clear pms pms2, 
simp,
end
-- Get the desired property as a collorary:
lemma ssp_prime (p: ℙ): sum_sum_pow p = p+1 := begin
rw sum_sum_pow,
have: factorize p = {(p, 1)}, by apply factorize_prime p, rw [this],
simp,
dsimp [Sigma],
simp,
rw [sum_pow],rw [sum_pow], 
simp,
end

-- Special case: p, q: ℙ, p ≠ q -> factorize p*q = {(p, 1), (q, 1)}
lemma factorize_prime_mul (p q: ℙ) (h: p ≠ q): factorize (p*q) = {(p, 1), (q, 1)} := begin
rw factorize, 
simp,
have: factor_multiset_equiv (p*q) = factor_multiset (p*q), by refl, rw [this], clear this,
rw factor_multiset_mul p q,

have: factor_multiset p = prime_multiset.of_prime p, by apply factor_multiset_of_prime,
rw [this], clear this,
have: factor_multiset q = prime_multiset.of_prime q, by apply factor_multiset_of_prime,
rw [this], clear this,

dsimp [prime_multiset.of_prime],
simp,

have: multiset.count q (q::p::0) = 1, {
  have: (q::p::0) = (p::q::0), by apply multiset.cons_swap q p 0, rw[this], clear this,
  rw multiset.count_cons_of_ne h.symm (q::0),
  apply multiset.count_singleton,
}, rw [this], clear this,
have: multiset.count p (q::p::0) = 1, {
  rw multiset.count_cons_of_ne h (p::0),
  apply multiset.count_singleton,
}, rw [this], clear this,

dsimp [has_insert.insert],
have: multiset.nodup {(p,1), (q,1)}, {
  have hneq: (q, 1) ≠ (p, 1), {
    intro hc,
    have: p=q, by apply (prod.mk.inj hc).left.symm,
    contradiction,
  },
  have: (q, 1) ∉ ((p, 1)::0 : multiset _), {
    intro h,
    rw [multiset.mem_cons] at h,
    cases h with l r, 
      contradiction,
      have: (q, 1) ∉ (0: multiset _), by apply multiset.not_mem_zero (q, 1), contradiction,
  },
  apply multiset.nodup_cons_of_nodup this,
  apply multiset.nodup_singleton,
},
apply multiset.erase_dup_eq_self.mpr, 
assumption,
end
-- ...then, sum_sum_pow (p*q) = (p+1)+(q+1)
lemma ssp_prime_mul (p q: ℙ) (h: p ≠ q): sum_sum_pow (p*q) = (p+1)+(q+1) := begin
rw sum_sum_pow,
have: factorize (p*q) = {(p, 1), (q, 1)}, by apply factorize_prime_mul p q h, rw [this],
dsimp [Sigma],
dsimp [has_insert.insert],
simp, 
dsimp [sum_pow],
simp,
end

#eval nat.factors 6
-- example: sum_sum_pow (2*3) = (2+1)+(3+1) := ssp_prime_mul ⟨2, prime2⟩ ⟨3, prime3⟩ dec_trivial
-- Show wrong_eqn is indeed wrong
lemma wrong_eqn_is_wrong: ¬ wrong_eqn := begin
intro h,
specialize h (2*3),
let p2: ℙ := ⟨2, by norm_num1⟩,
let p3: ℙ := ⟨3, by norm_num1⟩,
have: sumdiv (2*3) = 12, {
  unfold sumdiv, unfold divisors, 
  simp,
  have: factor_multiset_equiv (2*3) = factor_multiset (2*3), by refl,
  rw this,
  -- rw [this, coe], clear this,
  -- unfold lift_t, unfold has_lift_t.lift, unfold coe_t, unfold has_coe_t.coe, unfold coe_b, unfold has_coe.coe,
  
  have: factor_multiset (2*3) = (factor_multiset 2) + (factor_multiset 3), by apply factor_multiset_mul,
  rw this, clear this,

  have: factor_multiset 2 = factor_multiset p2, by reflexivity,
  rw this, clear this,
  have: factor_multiset p2 = prime_multiset.of_prime p2, by apply factor_multiset_of_prime,
  rw [this], clear this,
  --
  have: factor_multiset 3 = factor_multiset p3, by reflexivity,
  rw this, clear this,
  have: factor_multiset p3 = prime_multiset.of_prime p3, by apply factor_multiset_of_prime,
  rw [this], clear this,

  simp [multiset.powerset],
  -- rw coe,
  -- unfold lift_t, unfold has_lift_t.lift, unfold coe_t, unfold has_coe_t.coe, unfold coe_b, unfold has_coe.coe,

  -- simp [prime_multiset.of_prime],
  -- dsimp [prime_multiset.to_nat_multiset],
  
  have: multiset.nodup {p2, p3}, {
    have: p3 ≠ p2, by norm_num,
    have: p3 ∉ (p2::0 : multiset _), {
      intro h,
      rw [multiset.mem_cons] at h,
      cases h with l r, 
        contradiction,
        have: p3 ∉ (0: multiset _), by apply multiset.not_mem_zero p3, contradiction,
    },
    apply multiset.nodup_cons_of_nodup this,
    apply multiset.nodup_singleton,
  },
  have: {p2, p3} = apply multiset.erase_dup_eq_self.mpr,
  
},
have: sum_sum_pow (2*3) = (2+1)+(3+1), by apply ssp_prime_mul p2 p3 dec_trivial,
end
#check tactic.eval_expr nat `(3*3)
