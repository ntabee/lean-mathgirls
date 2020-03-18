import data.list
import tactic.norm_num
import .common .tree_sort

local attribute [simp, reducible] nat.factors

set_option profiler true

@[simp, reducible]
def list.zip_with_count {α: Type*} [decidable_eq α] (l: list α): list (α × ℕ) :=
  list.map (λ x, (x, list.count x l)) l

@[simp, reducible]
def factorize (n: ℕ) : list (ℕ × ℕ) := 
  list.erase_dup (nat.factors n).zip_with_count

#eval factorize (2*2*3*5*5)
example: (factorize (2*2*3)) ~ [(2, 2), (3, 1)] := by norm_num; reflexivity

@[simp, reducible]
def Prod: list ℕ -> ℕ := list.prod
theorem prod_singleton_id {x}: Prod [x] = x := by simp
theorem prod_singleton_of_lift_id {x}: (Prod ∘ (λ x, [x])) x = x := by simp

-- scalar * vector
@[simp, reducible]
def scalar (x: ℕ) (l: list ℕ) := list.map (λ y, y*x) l
infixr * := scalar
-- "vectors' direct product": [a1, a2, ... am] <*> [b1, b2, .., bn] = [a1*b1, a1*b2, ..., a1*bn, ..., am*bm]
@[simp, reducible]
def diprod: list ℕ -> list ℕ -> list ℕ
| [] ys := []
| (x::xs) ys := (x * ys) ++ (diprod xs ys)
-- ist.map Prod (l1 ⊗ [l2])
infixr <*> := diprod
#eval [1, 2] <*> [1, 3, 9]

lemma scalar_sum_commutes {x: ℕ} {l: list ℕ}: (x * l).sum = x * l.sum := begin
induction l, reflexivity,
case list.cons: hd tl ih {
  rw list.sum_cons,
  simp,
  simp at ih,
  rw ih,
  rw left_distrib,
  rw mul_comm,
}
end

lemma diprod_sum_commutes {l1 l2: list ℕ}: (l1 <*> l2).sum = l1.sum * l2.sum := begin
induction l1, {
  rw diprod, simp,
},
case list.cons: hd tl ih {
  rw list.sum_cons,
  rw right_distrib,
  rw diprod,
  rw list.sum_append,
  rw scalar_sum_commutes,
  rw ih,
}
end

-- pow_seq (n, e) = [n^0, n^1, ..., n^e]
@[simp, reducible]
def pow_seq (p: ℕ × ℕ) := list.map (λ c, (p.1 ^ c)) (list.range (p.2+1))
local notation `<|` p `|>` := pow_seq p

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

