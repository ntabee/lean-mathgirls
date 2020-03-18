import data.list init.algebra.classes
import tactic.norm_num tactic.tauto tactic.rewrite tactic.rewrite_all
import tactic.hint

variables {α: Type*}
variables [semiring α]

@[simp]
def scalar_l [has_mul α] (x: α) (l: list α) := list.map (λ y, x*y) l
infixr `[*]`:100 := scalar_l

@[simp]
def scalar_r [has_mul α] (l: list α) (x: α) := list.map (λ y, y*x) l

@[simp]
def tensor [has_mul α]: list α -> list α -> list α
| [] ys := []
| (x::xs) ys := (x [*] ys) ++ (tensor xs ys)
infixr `<*>` := tensor
infixr ` ⊗`:100 := tensor

theorem scalar_sum {x: α} {l: list α}: (x [*] l).sum = x * l.sum := begin
induction l, simp,
case list.cons: hd tl ih {
  rw list.sum_cons,
  simp,
  simp at ih,
  rw ih,
  rw left_distrib,
}
end

theorem tensor_sum {l1 l2: list α}: (l1 ⊗ l2).sum = l1.sum * l2.sum := begin
induction l1, {
  rw tensor, simp,
},
case list.cons: hd tl ih {
  rw list.sum_cons,
  rw right_distrib,
  rw tensor,
  rw list.sum_append,
  rw scalar_sum,
  rw ih,
}
end

-- geom (n, e) = [n^0, n^1, ..., n^e]
@[simp, reducible]
def geom (p: ℕ × ℕ) := list.map (λ c, (p.1 ^ c)) (list.range (p.2+1))
notation `<|` p `|>` := geom p

