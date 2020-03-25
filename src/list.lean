import data.list init.algebra.classes
import tactic.norm_num tactic.tauto tactic.rewrite tactic.rewrite_all tactic.omega tactic.tidy
import tactic.hint

variables {α: Type*}
variables [semiring α]

@[simp]
theorem map_id {l: list α}: list.map (λ x, x) l = l := begin
induction l, reflexivity, simp, assumption,
end

theorem map_forall {β: Type*} {l: list α} {f: α -> β} {p: β -> Prop} (h: ∀ b:β, p b):
  (∀ a ∈ l, p (f a)) -> ∀ b ∈ (list.map f l), p b := by tidy

@[simp]
def scalar_l (x: α) (l: list α) := list.map (λ y, x*y) l
infixr `[*]`:1000 := scalar_l

@[simp]
def scalar_add_l (x: α) (l: list α) := list.map (λ y, x+y) l
infixr `[+]`:500 := scalar_add_l

@[simp]
def scalar_r (l: list α) (x: α) := list.map (λ y, y*x) l

@[simp]
def scalar_add_r (l: list α) (x: α) := list.map (λ y, y+x) l

@[simp]
def tensor : list α -> list α -> list α
| [] ys := []
| (x::xs) ys := (x [*] ys) ++ (tensor xs ys)
infixr `<*>` := tensor
infixr ` ⊗`:1000 := tensor

@[simp]
def vec_add: list α -> list α -> list α
| [] ys := ys
| xs [] := xs
| (x::xs) (y::ys) := (x+y)::(vec_add xs ys)
infixr `<+>`:500 := vec_add

@[simp]
theorem scalar_l_sum {x: α} {l: list α}: (x [*] l).sum = x * l.sum := begin
induction l, simp,
case list.cons: hd tl ih {
  rw list.sum_cons,
  simp,
  simp at ih,
  rw ih,
  rw left_distrib,
}
end

@[simp]
theorem scalar_l_cons {x y: α} {l: list α}: (x [*] (y::l)) = (x*y)::(x [*] l) := by simp

@[simp]
theorem add_scalar_l_distrib {x y: α} {l: list α}: (x + y) [*] l = (x[*]l) <+> (y[*]l) := begin
induction l, reflexivity,
case list.cons: hd tl ih {
  repeat {rw scalar_l_cons },
  rw ih,
  simp,
  rw semiring.right_distrib,
  reflexivity,
}
end

@[simp]
theorem tensor_l_id {l: list α}: [1] <*> l = l := begin
induction l, reflexivity,
case list.cons: hd tl ih {
  simp,
}
end

@[simp]
theorem tensor_r_id {l: list α}: l <*> [1] = l := begin
induction l, 
  reflexivity,
  simp, assumption,
end

-- @[simp]
-- theorem tensor_cons {x: α} {l1 l2: list α}: (x::l1) <*> l2 = (x [*] l2) ++ (l1 <*> l2) := begin
-- induction l2, simp,
-- case list.cons: hd tl ih {
--   rw scalar_l_cons,
--   rw tensor, rw list.foldl_cons, rw scalar_l_cons, rw list.nil_append,
--   have hf: (λ (zs : list α) (x : α), zs ++ x[*](hd :: tl)) = (λ (zs : list α) (x : α), zs ++ ((x*hd) :: (x[*]tl))), {
--     funext, rw scalar_l_cons,
--   }, rw hf,

--   rw tensor,
--   rw hf,
  
-- }
-- end

-- @[simp]
-- theorem tensor_foldl_distrib {l: list α} {ls: list (list α)}: 
--   list.foldl (<*>) l ls = l <*> (list.foldl (<*>) [1] ls) := begin
-- induction l, simp,
-- case list.cons: hd tl ih {
  
--   rw list.foldl_cons (<*>) l lh lt,
--   rw list.foldl_cons (<*>) [1] lh lt, rw tensor_l_id,
--   rw <-ih,
-- }
-- end

@[simp]
theorem tensor_sum {l1 l2: list α}: (l1 <*> l2).sum = l1.sum * l2.sum := begin
induction l1, {
  rw tensor, simp,
},
case list.cons: hd tl ih {
  rw list.sum_cons,
  rw right_distrib,
  rw tensor,
  rw list.sum_append,
  rw scalar_l_sum,
  rw ih,
}
end

-- geom (n, e) = [n^0, n^1, ..., n^e]
@[simp, reducible]
def geom (p: α × ℕ) := list.map (λ c, (p.1 ^ c)) (list.range (p.2+1))
notation `<|` p `|>` := geom p

@[simp]
theorem geom_zero (e: α): <| (e, 0) |> = [1] := rfl

@[simp]
theorem geom_succ (p: α × ℕ): <| (p.1, p.2+1) |> = 1::(p.1 [*] <| p |>) := begin
simp,
repeat { rw add_comm, rw list.range_succ_eq_map, rw list.map_cons},
simp,
have: (pow p.fst) ∘ nat.succ ∘ nat.succ = (pow p.fst ∘ nat.succ) ∘ nat.succ, by simp,
rw this, clear this,
have: (pow p.fst ∘ nat.succ) = (has_mul.mul p.fst ∘ pow p.fst), {
  apply funext,
  intro,
  simp,
  rw pow_succ,
},
rw this,
end