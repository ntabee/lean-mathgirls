import data.pnat.factors data.multiset

notation `ℙ` := nat.primes

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

-- prime_factors n = the set of prime factors of n
def prime_factors (n: ℕ+) :=
  (pnat.factor_multiset_equiv n).erase_dup
-- #eval prime_factors (2*2*3*5*5) -- = {2, 3, 5} (as primes, not ℕ+)

-- factorize n = the set of pairs {(p1, e1), ..., (pm, em)}, where Π pi^ei = n
def factorize (n: ℕ+): multiset (ℙ × ℕ) := 
  let m := pnat.factor_multiset_equiv n in 
  let m' := m.map(fun x, (x, m.count x)) in
  m'.erase_dup
-- #eval factorize (2*2*3*5*5) -- = {(2, 2), (3, 1), (5, 2)}

-- ensure `factorize` is dupe-free
theorem factorize_nodup: ∀ n, multiset.nodup (factorize n) := begin
  intros; 
  unfold factorize,
  simp,
end

def divisors_factorized (n: ℕ+): multiset (multiset ℙ) := 
  let m := pnat.factor_multiset_equiv n in
  m.powerset.erase_dup
-- #eval divisors_ms (2*2*3*5*5) -- = {
  -- {2, 2, 3, 5, 5}, {2, 2, 3, 5}, {2, 2, 3}, {2, 2, 5, 5}, 
  -- {2, 2, 5}, {2, 2}, {2, 3, 5, 5}, {2, 3, 5}, 
  -- {2, 3}, {2, 5, 5}, {2, 5}, {2}, {3, 5, 5}, {3, 5}, {3}, {5, 5}, {5}, {}
  -- }

def divisors (n: ℕ+) := 
  let (m: multiset ℕ) := ↑(pnat.factor_multiset_equiv n) in
  m.powerset.erase_dup.map(λ ns, multiset.fold (*) 1 ns)
-- #eval divisors (2*2*3*5*5) -- = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 25, 30, 50, 60, 75, 100, 150, 300}