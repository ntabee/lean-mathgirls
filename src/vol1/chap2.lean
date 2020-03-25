-- Chapter 2. Love Letters Called Formulas

import init.data.list.lemmas init.data.nat.lemmas init.data.list.basic init.data.int.order
import tactic.norm_num tactic.tauto tactic tactic.basic
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

-- A wrong equation:
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
rw divisors_aux,
simp,
repeat {rw list.map},
simp only [list.range, list.range_core],
norm_num,
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

-- Theorem (geometric series):
--  1 + x + x^2 + ... x^n = (1-x^(n+1))/(1-x), (x ≠ 1)
theorem geom_sum (x: ℤ) (n: ℕ) (h: x ≠ 1): <| (x, n) |>.sum = (1 - x^(n+1))/(1-x) := begin
have h': 1-x ≠ 0, by_contradiction hc, {
  simp at hc,
  have: x=1, by rw add_neg_eq_zero.mp hc,
  contradiction,
},
have: (1 - x^(n+1)) = (1-x)*(<| (x, n) |>.sum), {
  induction n,
  case nat.zero {
    simp,
  },
  case nat.succ: n ih {
    rw geom_succ (x, n),
    rw list.sum_cons,
    have: (x, n).fst = x, by reflexivity, rw this, clear this,
    rw mul_add,
    rw scalar_l_sum,
    rw [<-mul_assoc (1-x), mul_comm (1-x) x],
    rw mul_assoc x (1-x) (list.sum _),
    rw <-ih,
    repeat {rw pow_succ},
    simp,
    rw [mul_add, <-add_assoc, mul_one, add_comm (-x) x, add_neg_self],
    rw mul_neg_eq_neg_mul_symm,
    rw zero_add,
  },
},
symmetry,
rw [this, mul_comm],
rw int.mul_div_cancel (<|(x, n)|>.sum) h',
end

-- Shorthand for (1 - x^(n+1))/(1-x)
@[simp]
def gs (p: ℤ × ℕ) := (1 - p.1^(p.2+1))/(1-p.1)

-- I will type-cast ℕ <- from&to -> ℤ
lemma gs_nonneg {p: ℤ × ℕ} (h: p.1 ≥ 0): (gs p) ≥ 0 := begin
unfold gs,
have: p.1 = 1 ∨ p.1 ≠ 1, by apply decidable.em,
cases this,
  rw this, simp,
  rw <-geom_sum p.1 p.2 this, simp, clear this,
  have hran: ∀ m ∈ list.range (1 + p.snd), pow p.1 m ≥ 0,{
    intros, apply pow_nonneg, assumption,
  },
  have: ∀ z:ℤ, z ∈ (list.map (pow p.fst) (list.range (1 + p.snd))) -> z ≥ 0, by tidy,
  apply sum_nonneg, assumption,
end

@[simp]
def nonneg_gs_to_nat (p: ℤ × ℕ) (h: p.1 ≥ 0): ℕ := nonneg_to_nat (gs p) (gs_nonneg h)

@[simp]
def gs_nat (p: ℕ × ℕ): ℕ := nonneg_gs_to_nat (↑p: ℤ × ℕ) (by tidy)

lemma gs_eq_gs_nat {p: ℕ × ℕ}: gs ↑p = gs_nat p := begin
have h: (↑p: (ℤ × ℕ)).1 ≥ 0, by tidy,
have: gs ↑p ≥ 0, from gs_nonneg h,
rw gs_nat, 
rw nonneg_gs_to_nat,
apply nonneg_to_nat_eq,
end

lemma int_one {x: ℤ}: 1=x ↔ 1-x = 0 := begin
apply iff.intro,
  omega,
  omega,
end
lemma int_ne_one {x: ℤ}: 1 ≠ x ↔ 1-x ≠ 0 := begin
apply iff.intro, 
  omega,
  omega,
end

lemma geom_sum_cast (x: ℕ) (n: ℕ): (<| (x, n) |>.sum: ℤ) = <| ((x: ℤ), n) |>.sum := begin
induction n with n ih, {
  simp,
}, {
  rw geom_succ (x, n), rw geom_succ (↑x, n),
  rw list.sum_cons, rw list.sum_cons,
  rw scalar_l_sum, rw scalar_l_sum,
  rw <-ih,
  norm_cast,
}
end

theorem geom_sum_nat (x: ℕ) (n: ℕ) (h: x ≠ 1): (<| (x, n) |>.sum: ℤ) = (1 - (x:ℤ)^(n+1))/(1-x) := begin
have h': (1:ℤ) + (-(x: ℤ)) ≠ 0, {
  apply int_ne_one.mp,
  symmetry, assumption_mod_cast,
},
have h_int: (x: ℤ) ≠ 1, by tidy,
rw <-geom_sum (x: ℤ) n h_int,
rw geom_sum_cast x n,
end

-- Lift the theorems to lists (of prime powers)
lemma geom_sums {l: list (ℤ × ℕ)} (h: ∀ p: ℤ × ℕ, p ∈ l -> p.1 ≠ 1): 
  list.map (λ (x: ℤ × ℕ), <| x |>.sum) l = list.map gs l := begin
induction l, reflexivity,
case list.cons: hd tl ih {
  have hps: hd.fst ≠ 1 ∧ ∀ (x : ℤ × ℕ), x ∈ tl → x.fst ≠ 1, from list.forall_mem_cons.mp h,
  repeat {rw list.map_cons},
  have hhd': hd.1 ≠ 1, from hps.1,
  have hhd: (hd.1 : ℤ) ≠ 1, by assumption_mod_cast, clear hhd',
  rw geom_sum (hd.1: ℤ) hd.2 hhd,
  rw ih hps.2,
  reflexivity,
}
end

lemma geom_sums_nat {l: list (ℕ × ℕ)} (h: ∀ p: ℕ × ℕ, p ∈ l -> p.1 ≠ 1): 
  (list.map (λ (x: ℕ × ℕ), <| x |>.sum) l) = list.map (λ p:ℕ × ℕ, gs_nat p) l := begin
induction l, reflexivity,
case list.cons: hd tl ih {
  have hps: hd.fst ≠ 1 ∧ ∀ (x : ℕ × ℕ), x ∈ tl → x.fst ≠ 1, from list.forall_mem_cons.mp h,
  repeat {rw list.map_cons},
  have hhd': hd.1 ≠ 1, from hps.1,
  have hhd: (↑hd: ℤ × ℕ).1 ≠ 1, {
    have: ↑(hd.1) = (↑hd: ℤ × ℕ).1, by tidy,
    intro hc, rw <-this at hc, clear this,
    have: ↑(hd.1) = (1: ℤ) -> hd.1 = 1, by tidy,
    exact hhd' (this hc),
  }, clear hhd',
  rw ih hps.2,
  norm_cast,
  apply and.intro, {
    have: (<|hd|>.sum : ℤ) = (gs_nat hd: ℤ), {
      rw <-gs_eq_gs_nat,
      rw gs,
      rw <-geom_sum _ _ hhd,
      rw geom_sum_cast,
      have: (↑(hd.fst), hd.snd) = ((↑hd: ℤ × ℕ).fst, (↑hd: ℤ × ℕ).snd), by tidy,
      rw this,
    },
    assumption_mod_cast,
  }, {
    reflexivity,
  }
}
end

-- Theorem 2.8:
--  sumdiv n = Π (1-p^(m+1)/(1-p)), (p, m) ∈ factorize n
theorem sumdiv_eqn': ∀ n, sumdiv n = (list.map (λ p:ℕ × ℕ, gs_nat p) (factorize n)).prod := begin
intro,
unfold sumdiv, unfold divisors,
have all_ne_1: ∀ p: ℕ × ℕ, p ∈ (factorize n) -> p.1 ≠ 1, by {
  intros p h,
  cases p,
  have: nat.prime p_fst, from factors_are_prime h,
  simp,
  apply nat.prime.ne_one, assumption,
},
rw <- geom_sums_nat all_ne_1,

induction (factorize n), reflexivity,
{
  rw divisors_aux,
  rw tensor_sum,
  rw ih,
  rw list.map_cons,
  rw list.prod_cons,
}
end
end sec_2_8

section sec_2_9
-- Section 2.9 "At the School Library"
--  2.9.1: Equations and Identities,

-- "x - 1 = 0" is an equation,
example: ∃ x: ℤ, x - 1 = 0 := ⟨1, rfl⟩ -- x = 1 ↔ x - 1 = 0

-- while "2(x-1) = 2x - 2" is an identity.
example: ∀ x: ℤ, 2*(x-1) = 2*x - 2 := begin 
intros, apply mul_add,
end

-- A rewrite chain of identities
lemma sub_left_comm (a b c: ℤ): a - b - c = a - c - b := begin
rw sub_eq_add_neg a b, 
rw sub_eq_add_neg _ c,
norm_num,
end

theorem square_completion_one (x: ℤ): (x+1)*(x-1) = x^2 - 1 := calc 
  (x+1)*(x-1) = 
  (x+1)*x - (x+1)*1: by rw mul_sub
  ... = x*x + 1*x -(x+1)*1: by rw add_mul
  ... = x*x + 1*x - x*1 - 1*1: by rw [add_mul, sub_add_eq_sub_sub_swap, sub_left_comm]
  ... = x^2 + x - x - 1: by rw [<-pow_two, mul_one, one_mul, one_mul]
  ... = x^2 - 1: by rw [sub_eq_add_neg _ x, add_assoc (x^2), add_neg_self x, add_zero]
.
-- This is an identity: holds for all x:
#check square_completion_one

-- Square-complete x^2 - 5*x + 6
theorem square_completion_2_and_3 (x: ℤ): x^2 - 5*x + 6 = (x-2)*(x-3) := by ring.
-- if it's an equation (of RHS = 0), the solutions are 2&3
example (x: ℤ): x^2 - 5*x + 6 = 0 -> x=2 ∨ x=3 := begin
rw square_completion_2_and_3 x,
intro h,
simp  at h,
omega,
end

-- 2.9.2: Product Forms and Sum Forms
--  elementary quadratic equations over a general (commutative) ring R
variables {R: Type}
variable [comm_ring R] 
variables {x α β: R}

-- A complete-form equation of R:
#check (x-α)*(x-β) = 0
-- Expand this one-step into: x^2 - α*x - β*x +α*β
theorem expand1: (x-α)*(x-β) = x^2 - α*x - β*x +α*β := begin
norm_num,
repeat { rw mul_add <|> rw add_mul },
rw pow_two,
tidy,
rw mul_comm x β,
apply add_comm,
end
-- ... then, group the degree-1 terms:
theorem group1: x^2 - α*x - β*x +α*β = x^2 - (α+β)*x +α*β := begin
ring,
end
-- Confirm these two forms are equivalent:
theorem square_completion_id: (x-α)*(x-β) = 0 ↔ x^2 - (α+β)*x +α*β = 0 := begin
apply iff.intro, {
  intro h,
  rw pow_two,
  ring at h,
  rw sub_eq_neg_add at h,
  repeat {rw add_mul at h},
  rw add_mul,
  rw sub_eq_neg_add,
  rw neg_eq_neg_one_mul,
  rw mul_add,
  repeat {rw <-mul_assoc},
  repeat {rw <-neg_eq_neg_one_mul},
  rw mul_comm α β,
  rw add_comm (-α*x) _,
  rw add_comm (x*x) at h, 
  assumption,
}, {
  intro h,
  rw pow_two at h,
  repeat {rw sub_mul <|> rw mul_sub},
  rw sub_eq_add_neg, rw neg_eq_neg_one_mul,
  rw mul_sub,
  repeat {rw <-neg_eq_neg_one_mul},
  rw neg_sub_neg,
  rw add_mul at h,
  rw sub_add_eq_sub_sub_swap at h,
  rw mul_comm β x at h,
  tidy,
}
end

end sec_2_9
