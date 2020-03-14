import tactic.omega

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
