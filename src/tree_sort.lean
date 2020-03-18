import data.list.basic data.list.perm
import tactic tactic.basic tactic.omega

namespace tree_sort

inductive tree (α: Type*) --[has_lt α] [h : decidable_rel ((<) : α → α → Prop)]
| l {} : tree
| n : tree -> α -> tree -> tree

def tree.has_dec_eq {α: Type*} [e: decidable_eq α]: decidable_eq (tree α)
| tree.l tree.l := is_true rfl
| tree.l (tree.n l x r) := is_false (λ h, tree.no_confusion h)
| (tree.n l x r) tree.l := is_false (λ h, tree.no_confusion h)
| (tree.n l1 x r1) (tree.n l2 y r2) := 
  match (e x y) with 
  | is_true h := (
    match ((tree.has_dec_eq l1 l2), (tree.has_dec_eq r1 r2)) with
    | (is_true hl, is_true hr) := is_true (begin
      apply eq.subst hl,
      apply eq.subst hr,
      apply eq.subst h, reflexivity,
    end)
    | (is_false hln, _) := is_false (λ hc, tree.no_confusion hc (λ hl _ _, absurd hl hln))
    | (_, is_false hrn) := is_false (λ hc, tree.no_confusion hc (λ _ _ hr, absurd hr hrn))
    end
  )
  | is_false hn := is_false (λ h, tree.no_confusion h (λ _ h _, absurd h hn))
  end
.

instance {α} [decidable_eq α] : decidable_eq (tree α) := tree.has_dec_eq

@[simp, reducible]
def tree.ins {α: Type*} (lt : α → α → bool) (x: α): tree α -> tree α
| tree.l := tree.n tree.l x tree.l
| (tree.n t y s) := cond (lt y x) (tree.n t y (tree.ins s)) (tree.n (tree.ins t) y s)

@[simp, reducible]
def tree.flat {α: Type*}: tree α -> list α
| tree.l := []
| (tree.n t x s) := (tree.flat t) ++ (x::(tree.flat s))

@[simp, reducible]
def build {α: Type*} (lt : α → α → bool) (l: list α) :=
  (list.foldr (λ x t , tree.ins lt x t) tree.l l)

@[simp, reducible]
def sort {α: Type*} (lt : α → α → bool) (l: list α) :=
  tree.flat (build lt l)

@[simp, reducible]
def mem {α} [decidable_eq α] (x: α): tree α -> Prop
| tree.l := false
| (tree.n l y r) :=  (mem l) ∨ (x = y) ∨ (mem r)

@[simp, reducible]
def subtree {α} [decidable_eq α]: tree α -> tree α -> Prop
| tree.l _ := true
| _ tree.l := false
| t1 t2@(tree.n l2 y r2) := (
  if (t1 = t2) then true
  else if (t1 = l2) then true
  else if (t1 = r2) then true
  else false
)

@[simp]
lemma flat_mem {α} [decidable_eq α]: ∀ (x: α) (t: tree α), mem x t -> x ∈ (t.flat) := begin
intros x t h,
induction t, {
  tautology,
}, 
case tree.n: {
  simp, simp at h,
  tautology,
}
end

@[simp]
lemma mem_ins {α} {lt: α → α → bool} [decidable_eq α] (x y: α) (t: tree α): mem x t -> mem x (tree.ins lt y t) := begin
intro h,
induction t, tautology,
case tree.n: l z r ih_l ih_r {
  simp,
  cases (lt z y); {
    simp, simp at h,
    cases h, {
      exact (or.inl $ ih_l h) <|> exact (or.inl h),
    }, {
      cases h, 
        exact (or.inr (or.inl h)),
        exact (or.inr (or.inr h)) <|> exact (or.inr (or.inr $ ih_r h)),
    }
  },
}
end

@[simp]
lemma ins_mem_id {α} {lt: α → α → bool} [decidable_eq α] (x: α) (t: tree α): mem x (tree.ins lt x t) := begin
induction t, simp,
case tree.n: l y r ih_l ih_r {
  simp,
  cases (lt y x), {
    simp, apply or.inl, assumption,
  }, {
    simp, apply or.inr, apply or.inr, assumption,
  }
}

end

@[simp]
lemma mem_cons {α} {lt: α → α → bool} [decidable_eq α] (x: α) (l: list α): mem x (build lt (x::l)) := by simp.

@[simp]
lemma mem_build {α} {lt: α → α → bool} [decidable_eq α] (x: α) (l: list α): x ∈ l -> mem x (build lt l) := begin
intro h,
induction l, {
  tautology,
}, 
case list.cons: y t ih{
  by_cases hxy: x = y, {
    rw hxy, simp,
  }, {
    have: x ∈ t, {
      simp at h,
      apply or.elim h,
        intro, contradiction,
        intro, assumption,
    },
    unfold build,
    simp,
    rw <-build,
    apply mem_ins,
    exact (ih this)
  }
}
end

@[simp]
lemma flat_nil {α}: (@tree.l α).flat = [] := by simp.

#check list.perm.trans
@[simp]
lemma flat_cons {α} {lt: α → α → bool} [decidable_eq α]: 
  ∀ (x: α) (t: tree α), (tree.ins lt x t).flat ~ x::(t.flat) := begin
intros,
induction t, simp,
case tree.n: tl y tr ih_l ih_r {
  simp,
  cases (lt y x), {
    simp,
    apply list.perm_app_left _ ih_l,
  }, {
    simp,
    
    have: x :: (tree.flat tl ++ y :: tree.flat tr) ~ (tree.flat tl) ++ x::y::(tree.flat tr),
      by apply list.perm_middle.symm,
    symmetry,
    transitivity  (tree.flat tl) ++ x::y::(tree.flat tr),
      assumption, clear this,

    apply list.perm_app_right,
    transitivity, {
      apply list.perm.swap y x,
    }, {
      from (list.perm_cons y).mpr ih_r.symm,
    },
  }
}
end

@[simp]
lemma perm_cons_left {α} [decidable_eq α]: 
  ∀ {a: α} {l1 l2 rhs: list α} (p: l1 ~ l2), (a::l1) ~ rhs ↔ (a::l2) ~ rhs := begin
intros,
apply iff.intro, {
  intro h,
  have: a::l1 ~ a::l2, by apply (list.perm_cons a).mpr p,
  apply this.symm.trans, assumption,
}, {
  intro h,
  have: a::l1 ~ a::l2, by apply (list.perm_cons a).mpr p,
  apply this.trans, assumption,
}
end

@[simp]
lemma perm_subterm {α} [decidable_eq α]: 
  ∀ {l1 l2 ini rhs: list α} (p: l1 ~ l2), (ini++l1) ~ rhs ↔ (ini++l2) ~ rhs := begin
intros,
apply iff.intro, {
  intro h,
  have: ini++l1 ~ ini++l2, by apply list.perm_app_right ini p,
  apply this.symm.trans, assumption,
}, {
  intro h,
  have: ini++l1 ~ ini++l2, by apply list.perm_app_right ini p,
  apply this.trans, assumption,
}
end

@[simp]
lemma flat_ins {α} {lt: α → α → bool} [decidable_eq α]: 
  ∀ (x: α) (t: tree α) (l: list α), l ~ (t.flat) -> (x::l) ~ (tree.ins lt x t).flat := begin
intros x t l h,
induction t, {
  simp, simp at h, rw list.perm_nil at h, rw h,
}, 
case tree.n: tl y tr ih_l ih_r {
  simp, cases (lt y x), {
    simp, simp at h,
    apply ((list.perm_cons x).mpr h).trans,
    have: tree.flat (tree.ins lt x tl) ~ x::(tree.flat tl), by apply flat_cons,
    apply (list.perm_app_left (y::tr.flat) this).symm.trans,
    reflexivity,
  }, {
    simp, simp at h,
    apply ((list.perm_cons x).mpr h).trans,
    have h1: tree.flat (tree.ins lt x tr) ~ x::(tree.flat tr), by apply flat_cons,
    have: y::tree.flat (tree.ins lt x tr) ~ y::x::(tree.flat tr),
      by apply ((list.perm_cons y).mpr h1),
    symmetry,
    apply (list.perm_app_right tl.flat this).trans, clear this h1,
    have: tree.flat tl ++ y :: x :: tree.flat tr ~ tree.flat tl ++ x :: y :: tree.flat tr, {
      apply list.perm_app_right tl.flat,
      apply list.perm.swap x y,
    },
    apply this.trans, clear this,
    have: x :: (tree.flat tl ++ y :: tree.flat tr) ~ (tree.flat tl ++ x :: y :: tree.flat tr), 
      by apply list.perm_middle.symm,
    apply this.symm.trans, reflexivity,
  }
}
end

protected theorem sort_equiv {α} [decidable_eq α] (lt : α → α → bool) (l: list α): l ~ (sort lt l) := begin
induction l, reflexivity,
case list.cons: h t ih {
  simp, simp at ih,
  apply flat_ins, assumption,
}
end

example: (tree_sort.sort (λ x y, to_bool (x < y)) (list.range 100)).length = 100 := by omega_nat ff
end tree_sort
