import data.list data.list.sort data.bool
import tactic.norm_num tactic.omega

attribute [simp, reducible] nat.factors
attribute [simp, reducible] ite

notation `ℙ` := nat.primes

set_option profiler true

meta def by_eval (typ: Type*) [reflected typ]: tactic unit := do
e <- tactic.target,
match expr.is_eq e with
| (some (e1, e2)) := tactic.eval_expr' typ e1 >> tactic.reflexivity
| none := tactic.failed
end

namespace tree_sort

inductive tree (α: Type*) --[has_lt α] [h : decidable_rel ((<) : α → α → Prop)]
| l {} : tree
| n : tree -> α -> tree -> tree

@[simp, reducible]
def tree.ins {α: Type*} (lt : α → α → bool) (x: α): tree α -> tree α
| tree.l := tree.n tree.l x tree.l
| (tree.n t y s) := cond (lt y x) (tree.n t y (tree.ins s)) (tree.n (tree.ins t) y s)

@[simp, reducible]
def tree.flat {α: Type*}: tree α -> list α
| tree.l := []
| (tree.n t x s) := (tree.flat t) ++ (x::(tree.flat s))

@[simp, reducible]
def sort {α: Type*}  (lt : α → α → bool) (l: list α) :=
  tree.flat (list.foldl (λ t x, tree.ins lt x t) tree.l l)

end tree_sort
example: (tree_sort.sort (λ x y, to_bool (x < y)) (list.range 100)).length = 100 := by omega_nat ff

-- 1-based
def fib: nat -> nat
| 0 := 0 -- sentinel
| 1 := 1
| 2 := 1
| (n+2) := (fib (n)) + (fib (n+1))

@[simp]
def nat.sum (n: ℕ) := ((n+1)*n)/2

-- seg a b = [a, ..., b)
@[simp, reducible]
def seg (a b: ℕ) := (list.range (b-a)).map(λ x, x+a)
-- #eval seg 3 5 

@[simp, reducible]
def find {α: Type} (p: α -> Prop) [decidable_pred p] [inhabited α] : list α -> α
| [] := arbitrary α
| (h::t) := cond (p h) h (find t)

@[simp, reducible]
def list.uniq {α: Type*} [decidable_eq α]: list α -> list α
| [] := []
| [a] := [a]
| (a::b::t) := cond (a = b) (list.uniq (b::t)) (a::(list.uniq (b::t)))

-- factorize n = the list of pairs [(p1, e1), ..., (pm, em)], where Π pi^ei = n
@[simp, reducible]
def factorize (n: ℕ) : list (ℕ × ℕ) := 
  let l := tree_sort.sort (λ a b, to_bool (a < b)) (nat.factors n) in
  let (c: list ℕ) := list.map (λ x, list.count x l) l in
  let l' := tree_sort.sort (λ a b, to_bool (a < b)) (list.zip l c) in
  l'.uniq

#eval factorize (2*2*3*5*5)

example: factorize (2*2*3*5*5) = [(2, 2), (3, 1), (5, 2)] := begin
norm_num,
reflexivity,
end

@[simp, reducible]
def list.subl {α: Type*} [has_lt α] [decidable_eq α] [decidable_rel ((<) : α → α → Prop)]: list α -> list (list α)
| [] := [[]]
| (h::t) := 
  let sort := tree_sort.sort (λ (x y: list α), x.length < y.length) in
  let ss := sort ((list.subl t) ++ (list.subl t).map(list.cons h)) in
  (tree_sort.sort (λ (x y: list α), to_bool ((x.length, x) < (y.length, y))) ss).uniq

#eval (nat.factors (2*2*3*5*5)).subl
@[simp, reducible]
def divisors_factorized (n: ℕ) :=
  (tree_sort.sort (λ s t, (list.length s) < (list.length t)) (nat.factors n).subl)

#eval divisors_factorized (2*2*3*5*5)
example: divisors_factorized (2*2*3*5*5) = [
  [], [5], [3], [2], [5, 5], [3, 5], [2, 5], [2, 3], 
  [2, 2], [3, 5, 5], [2, 5, 5], [2, 3, 5], [2, 2, 5], [2, 2, 3], [2, 3, 5, 5], 
  [2, 2, 5, 5], [2, 2, 3, 5], [2, 2, 3, 5, 5]
] := begin
norm_num,
reflexivity,
end 

#eval divisors_factorized (2*2*3*5*5)

@[simp, reducible]
def divisors (n: ℕ) := 
  tree_sort.sort (λ x y, to_bool (x < y)) ((divisors_factorized n).map list.prod)

#eval divisors (2*2*3*5*5)
example: divisors (2*2*3*5*5) = [1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 25, 30, 50, 60, 75, 100, 150, 300] := begin
norm_num,
reflexivity,
end

