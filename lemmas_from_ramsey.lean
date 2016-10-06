import data.nat data.set
open classical nat function set

section
-- the least number principle.

lemma alt_of_wf {A : set ℕ}: ∀ n, n ∈ A → ∃₀ a ∈ A, ∀₀ b ∈ A, a ≤ b := 
take n,
nat.strong_induction_on n
(take n, assume IH, assume ninA,  
by_cases
(suppose ∃₀ m ∈ A,  m < n, 
obtain m (Hm : m ∈ A ∧ m < n), from this,
IH m (and.right Hm) (and.left Hm))
(suppose ¬ ∃₀ m ∈ A,  m < n, 
have ∀₀ m ∈ A,  ¬ m < n, by+ rewrite not_bounded_exists at this ; exact this,
have ∀ m, m ∈ A → n ≤ m, from λ m, λ HmA, le_of_not_gt (this HmA),
exists.intro n (and.intro ninA this)))

theorem wf_of_le (S : set ℕ) (H : S ≠ ∅) : ∃₀ a ∈ S, ∀₀ b ∈ S, a ≤ b :=
have ∃ x, x ∈ S, from exists_mem_of_ne_empty H,
obtain n (Hn : n ∈ S), from this,
alt_of_wf n Hn

noncomputable definition chooseleast (S : set ℕ) (H : S ≠ ∅) : ℕ := 
have ∃₀ a ∈ S, ∀₀ b ∈ S, a ≤ b, from wf_of_le S H,
some this

theorem least_is_mem (S : set ℕ) (H : S ≠ ∅) : chooseleast S H ∈ S := 
have H1 : ∃₀ a ∈ S, ∀₀ b ∈ S, a ≤ b, from wf_of_le S H,
have inS : some H1 ∈ S, from sorry, --and.left (some_spec H1),
have chooseleast S H = some H1, from rfl,
by+ rewrite -this at inS ; exact inS

theorem minimality {S : set ℕ} {a : ℕ} {H0 : S ≠ ∅} (H : a = chooseleast S H0): 
∀₀ x ∈ S, a ≤ x :=
take b, assume Hb,
have H1 : ∃₀ n ∈ S, ∀₀ m ∈ S, n ≤ m, from wf_of_le S H0,
have chooseleast S H0 = some H1, from rfl,
have eq : a = some H1, by+ rewrite this at H;exact H,
have ∀₀ m ∈ S, some H1 ≤ m, from sorry, --and.right (some_spec H1), 
have some H1 ≤ b, from this Hb,
by+ simp 

end

lemma nonzero_card_of_finite {A : Type} {S : set A} (H : card S ≠ 0) : finite S :=
by_contradiction
(suppose ¬ finite S,
have card S = 0, from card_of_not_finite this,
H this)

lemma mem_not_in_diff {A : Type} {S : set A} {a : A} : a ∉ S \ '{a} := 
by_contradiction
(suppose ¬ a ∉ S \ '{a},
have a ∈ S \ '{a}, from not_not_elim this,
have a ∉ '{a}, from not_mem_of_mem_diff this,
this (mem_singleton a))

lemma insert_of_diff_singleton {A : Type} {S : set A} {a : A} (H : a ∈ S) : insert a (S \ '{a}) = S :=
ext
(take x, iff.intro
  (assume H1, 
   or.elim H1
   (λ Hl, by+ simp)
   (λ Hr, and.left Hr))
  (assume H2,
   by_cases
   (suppose x = a, or.intro_left (x ∈ S \ '{a}) this)
   (suppose neq : x ≠ a, 
    have x ∉ '{a}, from by_contradiction 
     (suppose ¬ x ∉ '{a}, 
      have x ∈ '{a}, from not_not_elim this,
      have x = a, from eq_of_mem_singleton this,
      neq this),
    have x ∈ S \ '{a}, from and.intro H2 this,
    or.intro_right (x = a) this))
)


lemma union_of_diff_singleton {A : Type} {S : set A} {a : A} (H : a ∈ S) : S \ '{a} ∪ '{a} = S := 
ext
(take x, iff.intro
(assume H1, 
  or.elim H1
  (assume Hl, and.left Hl)
  (assume Hr, 
   have x = a, from (and.left (mem_singleton_iff x a)) Hr,
   show x ∈ S, by+ rewrite -this at H;exact H))
(assume H2,
  by_cases
  (suppose x ∈ '{a}, or.intro_right (x ∈ S \ '{a}) this)
  (suppose x ∉ '{a}, 
   have x ∈ S \ '{a}, from and.intro H2 this,
   or.intro_left (x ∈ '{a}) this))
)

lemma finite_singleton {A : Type} {a : A} : finite '{a} := 
have carda : card '{a} = 1, from card_singleton a,
have (1:ℕ) ≠ 0, from dec_trivial,
have card '{a} ≠ 0, by+ rewrite -carda at this;exact this,
nonzero_card_of_finite this

lemma sub_of_eq {A : Type} {S T: set A} (H : S = T) : S ⊆ T :=
have T ⊆ T, from subset.refl T,
by+ rewrite -H at this{1};exact this

theorem ne_empty_of_mem' {X : Type} {s : set X} {x : X} (H : x ∈ s) : s ≠ ∅ :=
begin intro Hs, rewrite Hs at H, apply not_mem_empty _ H end --this is on github
