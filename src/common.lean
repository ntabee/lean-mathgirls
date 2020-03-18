import data.list.basic data.list.perm
import tactic.omega tactic.basic

notation `ℙ` := nat.primes

meta def by_eval (typ: Type*) [reflected typ]: tactic unit := do
e <- tactic.target,
match expr.is_eq e with
| (some (e1, e2)) := tactic.eval_expr' typ e1 >> tactic.reflexivity
| none := tactic.failed
end

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
