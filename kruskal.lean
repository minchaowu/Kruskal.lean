import data.fin data.list
open fin nat function list eq.ops

inductive finite_tree : Type :=
| node : finite_tree
| cons : Π {n : ℕ},  (fin n → finite_tree) → finite_tree

namespace finite_tree

definition size : finite_tree → ℕ
| node         := 1
| (@cons n ts) := Suml (upto n) (λ i, size (ts i)) + 1

theorem exists_eq_cons_of_ne_nil {A : Type} {l : list A} : l ≠ [] → ∃ a, ∃ l', l = a::l' := list.rec_on l (λ H, absurd rfl H) 
(λ a, λ l', λ IH, λ H, exists.intro a (exists.intro l' rfl))

lemma map_val_upto (n : nat) : map fin.val (upto n) = list.upto n := 
map_dmap_of_inv_of_pos (val_mk n) (@lt_of_mem_upto n) 
 
lemma length_upto (n : nat) : length (upto n) = n := -- in the latest library
calc
  length (upto n) = length (list.upto n) : (map_val_upto n ▸ length_map fin.val (upto n))⁻¹
  ... = n                    : list.length_upto n
 
lemma upto_ne_nil_of_ne_zero (n : nat) (Hn : n ≠ 0) : upto n ≠ [] := 
begin 
  intro Hup, 
  apply Hn, 
  rewrite [-(@length_nil (fin n)), -Hup], 
  apply eq.symm !length_upto 
end 

theorem pos_of_size (t : finite_tree) : 0 < size t :=
finite_tree.induction_on t dec_trivial 
(λ n, λ ts, λ IH,  by+ apply dec_trivial)

theorem pos_of_Suml {n : ℕ} (H : n ≠ 0) (ts : fin n → finite_tree) : 0 < Suml (upto n) (λ i, size (ts i)) :=
have upto n ≠ nil, from upto_ne_nil_of_ne_zero n H,
have ∃ a, ∃ l', fin.upto n = a::l', from exists_eq_cons_of_ne_nil this,
obtain a ha, from this,
obtain l' hl', from ha,
let f := λ i, size (ts i) in
have Suml (a::l') f = f a + Suml l' f, from Suml_cons f a l',
have f a > 0, from pos_of_size (ts a),
have f a + Suml l' f > 0, from add_pos_left this (Suml l' f),
by+ simp

theorem le_of_elt_Suml {n : ℕ} (ts : fin n → finite_tree) (k : fin n) : size (ts k) ≤ Suml (upto n) (λ i, size (ts i)) := -- what if n = 0?
have k ∈ upto n, from mem_upto n k,
have ∃s t, upto n = s ++ (k::t), from mem_split this,
obtain (s t) hst, from this,
have Suml (upto n) (λ i, size (ts i)) = Suml (s ++ (k::t)) (λ i, size (ts i)), by+ simp,
have Suml (s ++ (k::t)) (λ i, size (ts i)) = Suml s (λ i, size (ts i)) + Suml (k::t) (λ i, size (ts i)), from Suml_append s (k::t) (λ i, size (ts i)),
have Suml (k::t) (λ i, size (ts i)) = size (ts k) + Suml t (λ i, size (ts i)), from Suml_cons (λ i, size (ts i)) k t,
have size (ts k) ≤ size (ts k) + Suml t (λ i, size (ts i)), from le_add_right (size (ts k)) (Suml t (λ i, size (ts i))),
have le1 : size (ts k) ≤ Suml (k::t) (λ i, size (ts i)), by+ simp,
have Suml (k::t) (λ i, size (ts i)) ≤ Suml s (λ i, size (ts i)) + Suml (k::t) (λ i, size (ts i)), from le_add_left (Suml (k::t) (λ i, size (ts i))) (Suml s (λ i, size (ts i))),
have size (ts k) ≤ Suml s (λ i, size (ts i)) + Suml (k::t) (λ i, size (ts i)), from le.trans le1 this,
by+ simp

definition embeds : finite_tree → finite_tree → Prop
| embeds node _              := true
| embeds (cons ts) node      := false
| embeds (cons ts) (cons us) := (∃ j, embeds (cons ts) (us j)) ∨
                                  (∃ f, injective f ∧ ∀ i, embeds (ts i) (us (f i)))

/-
  -- here is a "hands on" definition of the same predicate:
  definition embeds (s t : finite_tree) : Prop :=
  (finite_tree.rec
    (finite_tree.rec true (λ m ss embss, false))
    (λ n ts embts,
      finite_tree.rec true (λ m ss embss,
        (∃ j, embts j (cons ss)) ∨ (∃ f, injective f ∧ ∀ i, embts (f i) (ss i)))))
  t s
-/

infix ` ≼ `:50 := embeds  -- \preceq

proposition node_embeds (t : finite_tree) : node ≼ t :=
by induction t; repeat (apply trivial)

proposition not_cons_embeds_node {n : ℕ} (ts : fin n → finite_tree) : ¬ cons ts ≼ node :=
not_false

-- curiously, with either definition above, this doesn't work with = and rfl
proposition cons_embeds_cons_iff {m n : ℕ} (ss : fin m → finite_tree) (ts : fin n → finite_tree) :
  cons ss ≼ cons ts ↔ (∃ j, cons ss ≼ ts j) ∨ (∃ f, injective f ∧ ∀ i, ss i ≼ ts (f i)) :=
!iff.refl

proposition cons_embeds_cons_left {m n : ℕ} {ss : fin m → finite_tree} {ts : fin n → finite_tree}
    {j : fin n} (H : cons ss ≼ ts j) :
  cons ss ≼ cons ts :=
or.inl (exists.intro j H)

proposition cons_embeds_cons_right {m n : ℕ} {ss : fin m → finite_tree} {ts : fin n → finite_tree}
    {f : fin m → fin n} (injf : injective f) (Hf : ∀ i, ss i ≼ ts (f i)) :
  cons ss ≼ cons ts :=
or.inr (exists.intro f (and.intro injf Hf))

proposition cons_embeds_cons_dest {m n : ℕ} {ss : fin m → finite_tree} {ts : fin n → finite_tree}
    (H : cons ss ≼ cons ts) :
  (∃ j, cons ss ≼ ts j) ∨ (∃ f, injective f ∧ ∀ i, ss i ≼ ts (f i)) :=
H

proposition embeds_refl (t : finite_tree) : t ≼ t :=
finite_tree.induction_on t trivial
  (take n ts ih, cons_embeds_cons_right injective_id ih)

private proposition embeds_trans_aux : ∀ {u s t}, t ≼ u → s ≼ t → s ≼ u :=
begin
  intro u,
  induction u with l us ihu,
    intro s t, cases s with n ss,
      intros, apply node_embeds,
    cases t, repeat (intros; contradiction),
  intro s t,
    cases s with n ss,
      intros, apply node_embeds,
    cases t with m ts,
      intros, contradiction,
  intro H₁, cases (cons_embeds_cons_dest H₁) with H₁₁ H₁₂,
    cases H₁₁ with i H₁₁, intro H₂,
    have cons ss ≼ us i, from ihu _ H₁₁ H₂,
    apply cons_embeds_cons_left this,
  cases H₁₂ with f Hf, cases Hf with injf Hf,
  intro H₂, cases (cons_embeds_cons_dest H₂) with H₂₁ H₂₂,
    cases H₂₁ with j H₂₁,
    have cons ss ≼ us (f j), from ihu _ (Hf j) H₂₁,
    apply cons_embeds_cons_left this,
  cases H₂₂ with g Hg, cases Hg with injg Hg,
  apply cons_embeds_cons_right,
  apply injective_compose injf injg,
  intro i, apply ihu _ (Hf (g i)) (Hg i)
end

proposition embeds_trans {s t u : finite_tree} (H₁ : s ≼ t) (H₂ : t ≼ u) : s ≼ u :=
embeds_trans_aux H₂ H₁

proposition cons_embeds_iff {m : ℕ} (ss : fin m → finite_tree) (t : finite_tree) :
  cons ss ≼ t ↔ ∃ n (ts : fin n → finite_tree), t = cons ts ∧
                  ((∃ j, cons ss ≼ ts j) ∨ (∃ f, injective f ∧ ∀ i, ss i ≼ ts (f i))) :=
begin
  apply iff.intro,
    intro H, cases t with n ts,
      contradiction,
    existsi n, existsi ts, split, reflexivity, apply cons_embeds_cons_dest H,
  intro H, cases H with n H, cases H with ts H, cases H with teq H,
  rewrite teq, exact H
end

end finite_tree
