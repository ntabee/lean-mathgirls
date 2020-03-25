import data.list
import tactic.norm_num
import .common .tree_sort .list

local attribute [simp, reducible] nat.factors

@[simp, reducible]
def list.zip_with_count {α: Type*} [decidable_eq α] (l: list α): list (α × ℕ) :=
  list.map (λ x, (x, list.count x l)) l

@[simp, reducible]
def factorize (n: ℕ) : list (ℕ × ℕ) := 
  list.erase_dup (nat.factors n).zip_with_count

#eval factorize (2*2*3*5*5)
example: (factorize (2*2*3)) ~ [(2, 2), (3, 1)] := by norm_num; reflexivity

theorem factors_ge_2 {n p m: ℕ}: (p, m) ∈ (factorize n) -> p ≥ 2 := begin
intro h,
simp at h,
cases h with a w,
  rw w.right.left.symm,
  have: nat.prime a, by apply nat.mem_factors w.left,
  apply nat.prime.two_le,
  assumption,
end

theorem factors_are_nat_factors {n p m: ℕ}: (p, m) ∈ (factorize n) -> p ∈ (nat.factors n) := begin
intro h,
simp at h,
cases h with a w,
  rw w.right.left.symm,
  apply w.left,
end

theorem factors_are_prime {n p m: ℕ}: (p, m) ∈ (factorize n) -> nat.prime p := begin
intro h,
simp at h,
cases h with a w,
  rw w.right.left.symm,
  apply nat.mem_factors w.left,
end

@[simp, reducible]
def Prod: list ℕ -> ℕ := list.prod
theorem prod_singleton_id {x}: Prod [x] = x := by simp
theorem prod_singleton_of_lift_id {x}: (Prod ∘ (λ x, [x])) x = x := by simp

@[simp, reducible]
def divisors_aux: list (ℕ × ℕ) -> list ℕ
| [] := [1]
| (p::ps) := (<| p |>) <*> (divisors_aux ps)

#eval divisors_aux (factorize (2*2*3*5*5))

@[simp, reducible]
def divisors (n: ℕ) := divisors_aux (factorize n)

#eval divisors (2*2*3*5*5)
#eval divisors (2*2*3)
example: tree_sort.sort (λ a b, to_bool (a < b)) (divisors (2*2*3)) = [1, 2, 3, 4, 6, 12] := by norm_num; reflexivity
