-- 1-based
def fib: nat -> nat
| 0 := 0 -- sentinel
| 1 := 1
| 2 := 1
| (n+2) := (fib (n)) + (fib (n+1))

def nat.sum (n: ℕ) := ((n+1)*n)/2

-- seg a b = [a, ..., b)
def seg (a b: ℕ) := (list.range (b-a)).map(λ x, x+a)
-- #eval seg 3 5 

def find {α: Type} (p: α -> Prop) [decidable_pred p] [inhabited α] : list α -> α
| [] := arbitrary α
| (h::t) := if p h then h else (find t)
