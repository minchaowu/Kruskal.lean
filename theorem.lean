import kruskal lemmas1 lemmas2 data.list
open classical fin set nat subtype finite_tree kruskal function prod

noncomputable theory

theorem dne {p : Prop} (H : ¬¬p) : p := or.elim (em p) (assume Hp : p, Hp) (assume Hnp : ¬p, absurd Hnp H) -- why do we need [decidable p] in not_not_elim?

lemma tag_eq_of_eq {A : Type} {P : A → Prop} {a b : subtype P} (H : a = b) : elt_of a = elt_of b := by rewrite H

theorem eq_of_prod {A B : Type} {p q : A × B} (H1 : pr1 p = pr1 q) (H2 : pr2 p = pr2 q) : p = q :=
have mk (pr1 q) (pr2 q) = q, from eta q,
have mk (pr1 p) (pr2 p) = q, by+ simp,
have mk (pr1 p) (pr2 p) = p, from eta p,
by+ simp

theorem ne_empty_of_image_on_univ {A B : Type} (f : A → B) [inhabited A] : f ' univ ≠ ∅ :=
have (∅ : set A) ≠ univ, from empty_ne_univ,
have ∃ a, a ∈ univ, from exists_mem_of_ne_empty (ne.symm this),
obtain a h, from this,
have f a ∈ f ' univ, from exists.intro a (and.intro h rfl),
ne_empty_of_mem this

theorem val_mapsto (n : ℕ) : maps_to val (@univ (fin n)) {i : ℕ | i < n} :=
take x, assume Ha, is_lt x

theorem injective_val_on_univ (n : ℕ): inj_on val (@univ (fin n)) :=
take x₁ x₂, assume H1, assume H2, assume eq, val_inj eq

theorem finite_univ_of_fin [instance] (n : ℕ) : finite (@univ (fin n)) :=
finite_of_inj_on (val_mapsto n) (injective_val_on_univ n)

theorem refl_of_image_on_univ {A B: Type} (f : A → B) : f ' (@univ A) = {b : B | ∃ x, f x = b} :=
have Hl : f ' (@univ A) ⊆ {b : B | ∃ x, f x = b}, from 
  take x, assume Hx, obtain i h, from Hx, exists.intro i (and.right h),
have {b : B | ∃ x, f x = b} ⊆ f ' (@univ A), from 
  take x, assume Hx, obtain i h, from Hx, exists.intro i (and.intro trivial h),
subset.antisymm Hl this

theorem finite_image_of_fin {A : Type} {n : ℕ} (f : fin n → A) : finite {a : A | ∃ x, f x = a} := 
have f ' (@univ (fin n)) = {a : A | ∃ x, f x = a}, from refl_of_image_on_univ f,
have finite (f ' @univ (fin n)), from finite_image f univ,
by+ simp

theorem exists_eq_cons_of_ne_node {t : finite_tree} : t ≠ node → ∃ n, ∃ ts : fin n → finite_tree, t = cons ts :=
finite_tree.rec_on t
(λ H, absurd rfl H)
(λ n, λ tt, λ IH, λ H, exists.intro n (exists.intro tt rfl))

definition num_of_branches_at_root (t : finite_tree) (H : t ≠ node) : ℕ := 
some (exists_eq_cons_of_ne_node H)

definition branches_at_root (t : finite_tree) (H : t ≠ node) :=
some (some_spec (exists_eq_cons_of_ne_node H))

definition set_of_branches {n : ℕ} (ts : fin n → finite_tree) : set (finite_tree × ℕ) := {x : finite_tree × ℕ | ∃ a : fin n, ts a = pr1 x ∧ val a = pr2 x}

theorem empty_branches (ts : fin 0 → finite_tree) : set_of_branches ts = ∅ :=
have ∀ x, x ∉ set_of_branches ts, from 
  take x, 
  by_contradiction 
  (suppose ¬ x ∉ set_of_branches ts,
   have x ∈ set_of_branches ts, from dne this,
   obtain a ha, from this,
   have le : val a < 0, from is_lt a,
   have ¬ val a < 0, from dec_trivial,
   this le),
eq_empty_of_forall_not_mem this

definition set_of_branches_at_root : finite_tree → set (finite_tree × ℕ) 
| node := ∅
| (@cons n ts) := set_of_branches ts

theorem embeds_of_branches {t : finite_tree × ℕ} {T: finite_tree} : t ∈ (set_of_branches_at_root T) → pr1 t ≼ T := finite_tree.induction_on T 
(assume H, absurd H (not_mem_empty t)) 
(λ n, λ ts, λ IH, λ H, obtain a h, from H, 
  by_cases
  (suppose pr1 t = node, have node ≼ cons ts, from trivial, by+ simp)
  (suppose pr1 t ≠ node, 
   have ∃ k, ∃ tt : fin k → finite_tree, pr1 t = cons tt, from exists_eq_cons_of_ne_node this,
   obtain k hk, from this, 
   obtain tt htt, from hk, 
   have cons tt = ts a, by+ simp, 
   have cons tt ≼ cons tt, from embeds_refl (cons tt), 
   have cons tt ≼ ts a, by+ simp, 
   have cons tt ≼ cons ts, from or.intro_left ((∃ f, injective f ∧ ∀ i, embeds (tt i) (ts (f i)))) (exists.intro a this), 
   by+ simp))

theorem lt_of_size_of_branches {t : finite_tree × ℕ} {T : finite_tree} : t ∈ set_of_branches_at_root T → size (pr1 t) < size T :=
by_cases
(suppose T = node, assume H, 
 have set_of_branches_at_root node = ∅, from rfl,
 have t ∈ ∅, by+ simp,
 absurd this (not_mem_empty t))
(suppose T ≠ node, assume H,
 have ∃ n, ∃ ts : fin n → finite_tree, T = cons ts, from exists_eq_cons_of_ne_node this,
 obtain n hn, from this,
 by_cases
 (suppose n = 0, 
  have ets : ∃ ts : fin 0 → finite_tree, T = cons ts, by+ rewrite this at hn;exact hn,
  obtain ts hts, from ets,  
  have set_of_branches_at_root T = set_of_branches_at_root (cons ts), by+ simp,
  have set_of_branches_at_root T = set_of_branches ts, from this,
  have Ht : t ∈ set_of_branches ts, by+ rewrite this at H;exact H,
  have set_of_branches ts = ∅, from empty_branches ts,
  have t ∈ ∅, by+ rewrite this at Ht;exact Ht,
  absurd this (not_mem_empty t))
 (assume Hneg : n ≠ 0, 
  obtain ts hts, from hn,
  by_cases 
  (suppose pr1 t = node, 
   have 0 < Suml (upto n) (λ i, size (ts i)), from pos_of_Suml Hneg ts,
   have 1 + Suml (upto n) (λ i, size (ts i)) > 1, from nat.lt_add_of_pos_right this,
   have 1 + Suml (upto n) (λ i, size (ts i)) = Suml (upto n) (λ i, size (ts i)) + 1, from add.comm 1 (Suml (upto n) (λ i, size (ts i))),
   have Suml (upto n) (λ i, size (ts i)) + 1 > 1, by+ simp,
   have size (cons ts) = Suml (upto n) (λ i, size (ts i)) + 1, from rfl,
   have size T > 1, by+ simp,
   have size node = 1, from rfl,
   by+ simp) 
  (suppose pr1 t ≠ node, 
   have ∃ tn, ∃ tt : fin tn → finite_tree, pr1 t = cons tt, from exists_eq_cons_of_ne_node this, 
   obtain tn htn, from this,
   obtain tt htt, from htn,
   have t ∈ set_of_branches ts, by+ rewrite hts at H;exact H,
   obtain a ha, from this,
   have ts a = pr1 t, from and.left ha,
   have ts a = cons tt, by+ rewrite htt at this;exact this,
   have size (ts a) ≤ Suml (upto n) (λ i, size (ts i)), from le_of_elt_Suml ts a,
   have size (ts a) < size (cons ts), from (and.right (lt_succ_iff_le (size (ts a)) (Suml (upto n) (λ i, size (ts i))))) this, -- cons ts = T
   by+ simp)))

theorem finite_set_of_branches {n : ℕ} (ts : fin n → finite_tree) : finite (set_of_branches ts) := 
let f (a : fin n) : finite_tree × ℕ := (ts a, val a) in
let S : set (finite_tree × ℕ) := {x : finite_tree × ℕ | ∃ a : fin n, f a = x} in
have finS : finite S, from finite_image_of_fin f,
have H1 : S ⊆ set_of_branches ts, from 
  take x, assume Hx,
  obtain b hb, from Hx,
  have (ts b, val b) = x, from hb,
  have ts b = pr1 (ts b, val b), from rfl,
  have Hl : ts b = pr1 x, by+ simp,
  have val b = pr2 (ts b, val b), from rfl,
  have val b = pr2 x, by+ simp,
  exists.intro b (and.intro Hl this),
have set_of_branches ts ⊆ S, from
  take x, assume Hx,
  obtain b hb, from Hx,
  have (pr1 x, pr2 x) = x, from eta x,
  have (ts b, val b) = x, by+ simp,
  exists.intro b this,
have S = set_of_branches ts, from subset.antisymm H1 this,
by+ rewrite this at finS;exact finS

theorem finite_set_of_branches_at_root (t : finite_tree) : finite (set_of_branches_at_root t) := finite_tree.induction_on t finite_empty (λ n, λ ts, λ IH, finite_set_of_branches ts)

check @minimal_bad_seq

section
parameter H : ∃ f, ¬ is_good f embeds

definition mbs_of_finite_tree := minimal_bad_seq size H 

theorem bad_mbs_finite_tree : ¬ is_good mbs_of_finite_tree embeds := badness_of_mbs size H

theorem ne_node_of_elt_of_mbs_finite_tree (n : ℕ) : mbs_of_finite_tree n ≠ node :=
 suppose mbs_of_finite_tree n = node,
 have node ≼ mbs_of_finite_tree (succ n), from node_embeds (mbs_of_finite_tree (succ n)),
 have Hr : mbs_of_finite_tree n ≼ mbs_of_finite_tree (succ n), by+ simp,
 have n < succ n, from lt_succ_self n,
 have is_good mbs_of_finite_tree embeds, from exists.intro n (exists.intro (succ n) (and.intro this Hr)),
 bad_mbs_finite_tree this

theorem minimality_of_mbs_finite_tree0 (f : ℕ → finite_tree) (Hf : ¬ is_good f embeds) : size (mbs_of_finite_tree 0) ≤ size (f 0) := minimality_of_mbs_0 size H f Hf

theorem minimality_of_mbs_finite_tree (n : ℕ) (f : ℕ → finite_tree) (H1 : extends_at n mbs_of_finite_tree f ∧ ¬ is_good f embeds) : size (mbs_of_finite_tree (succ n)) ≤ size (f (succ n)) := minimality_of_mbs size H n f H1

definition seq_branches_of_mbs_tree (n : ℕ) : set (finite_tree × ℕ) := set_of_branches_at_root (mbs_of_finite_tree n)

theorem mem_of_seq_branches {n i : ℕ} (ts : fin n → finite_tree) (k : fin n) (Heq : mbs_of_finite_tree i = cons ts) : (ts k, val k) ∈ seq_branches_of_mbs_tree i :=
have ts k = pr1 (ts k, val k) ∧ val k = pr2 (ts k, val k), from and.intro rfl rfl,
have ∃ a, ts a = pr1 (ts k, val k) ∧ val a = pr2 (ts k, val k), from exists.intro k this,
have (ts k, val k) ∈ set_of_branches_at_root (cons ts), from this,
by+ rewrite -Heq at this;exact this

definition mbs_tree : Type₁ := {t : finite_tree × ℕ | ∃ i, t ∈ seq_branches_of_mbs_tree i}

definition embeds' (t : mbs_tree) (s : mbs_tree) : Prop := pr1 (elt_of t) ≼ pr1 (elt_of s)

theorem embeds'_refl (t : mbs_tree) : embeds' t t := embeds_refl (pr1 (elt_of t))

theorem embeds'_trans (a b c : mbs_tree) : embeds' a b → embeds' b c → embeds' a c :=
assume H₁, assume H₂, embeds_trans H₁ H₂

section

parameter H' : ∃ f, ¬ is_good f embeds'

definition R : ℕ → mbs_tree := some H'

definition family_index_of_r (n : ℕ) : ℕ := some (has_property (R n)) 

definition index_set_of_mbs_tree : set ℕ := family_index_of_r ' univ

proposition index_ne_empty : index_set_of_mbs_tree ≠ ∅ := ne_empty_of_image_on_univ family_index_of_r

definition min_family_index := chooseleast index_set_of_mbs_tree index_ne_empty

proposition exists_min_r : ∃ i, family_index_of_r i = min_family_index :=
have min_family_index ∈ index_set_of_mbs_tree, from least_is_mem index_set_of_mbs_tree index_ne_empty,
obtain i h, from this,
exists.intro i (and.right h)

definition index_of_R'0 : ℕ := some exists_min_r

definition R' (n : ℕ) : mbs_tree := R (index_of_R'0 + n)

definition family_index_of_r' (n : ℕ) : ℕ :=  family_index_of_r (index_of_R'0 + n)

theorem bad_R' : ¬ is_good R' embeds' :=
suppose is_good R' embeds',
obtain (i j) hij, from this,
have Hr : embeds' (R' i) (R' j), from and.right hij,
have index_of_R'0 + i < index_of_R'0 + j, from add_lt_add_left (and.left hij) _,
have is_good R embeds', from exists.intro (index_of_R'0 + i) (exists.intro (index_of_R'0 + j) (and.intro this Hr)),
(some_spec H') this

theorem Kruskal's_Hg : ¬ is_good (pr1 ∘ (elt_of ∘ R')) embeds := bad_R'

theorem trans_of_R' {i j : ℕ} (H1 : mbs_of_finite_tree i ≼ pr1 (elt_of (R' j))) : mbs_of_finite_tree i ≼ mbs_of_finite_tree (family_index_of_r' j) := 
have elt_of (R' j) ∈ set_of_branches_at_root (mbs_of_finite_tree (family_index_of_r' j)), from some_spec (has_property (R' j)),
have pr1 (elt_of (R' j)) ≼ mbs_of_finite_tree (family_index_of_r' j), from embeds_of_branches this,
embeds_trans H1 this

theorem size_elt_R'_lt_mbs_finite_tree (n : ℕ) : size (pr1 (elt_of (R' n))) < size (mbs_of_finite_tree (family_index_of_r' n)) := lt_of_size_of_branches (some_spec (has_property (R' n)))

theorem Kruskal's_Hbp : size (pr1 (elt_of (R' 0))) < size (mbs_of_finite_tree (family_index_of_r' 0)) := size_elt_R'_lt_mbs_finite_tree 0

lemma family_index_in_index_of_mbs_tree (n : ℕ) : family_index_of_r' n ∈ index_set_of_mbs_tree :=
have family_index_of_r' n = family_index_of_r (index_of_R'0 + n), from rfl,
exists.intro (index_of_R'0 + n) (and.intro trivial rfl)

theorem Kruskal's_Hh (n : ℕ) : family_index_of_r' 0 ≤ family_index_of_r' n :=
have family_index_of_r' 0 = family_index_of_r (index_of_R'0 + 0), from rfl,
have family_index_of_r' 0 = family_index_of_r index_of_R'0, by+ simp,
have family_index_of_r index_of_R'0 = min_family_index, from some_spec exists_min_r,
have family_index_of_r' 0 = min_family_index, by+ simp,
minimality this (family_index_in_index_of_mbs_tree n)

theorem Kruskal's_H : ∀ i j, mbs_of_finite_tree i ≼ pr1 (elt_of (R' (j - family_index_of_r' 0))) → mbs_of_finite_tree i ≼ mbs_of_finite_tree (family_index_of_r' (j - family_index_of_r' 0)) := λ i j, λ H1, trans_of_R' H1

definition Kruskal's_comb_seq (n : ℕ) : finite_tree := @comb_seq_with_mbs _ embeds (pr1 ∘ (elt_of ∘ R')) family_index_of_r' size H n

theorem Kruskal's_local_contradiction : false := local_contra_of_comb_seq_with_mbs family_index_of_r' size Kruskal's_Hh H Kruskal's_Hg Kruskal's_H Kruskal's_Hbp

end

check Kruskal's_local_contradiction

theorem embeds'_is_good : ∀ f, is_good f embeds' := 
by_contradiction
(suppose ¬ ∀ f, is_good f embeds',
 have ∃ f, ¬ is_good f embeds', from exists_not_of_not_forall this,
 Kruskal's_local_contradiction this)

definition wqo_mbs_tree [instance] : wqo mbs_tree :=
wqo.mk embeds' embeds'_refl embeds'_trans embeds'_is_good

definition wqo_finite_subsets_of_mbs_tree : wqo (finite_subsets mbs_tree) := wqo_finite_subsets

definition os : finite_subsets mbs_tree → finite_subsets mbs_tree → Prop := wqo.le

-- type mbs_tree is the collection of all branches at roots appearing in the mbs_of_finite_tree
-- hence, mbs_of_finite_tree can be viewed as a sequence on finite_subsets mbs_tree. We call this sequence a copy (or a mirror) of mbs_of_finite_tree.
-- the following theorem says given any sequence f : ℕ → finite_subsets mbs_tree,  there exists i j such that there exists a f' : mbs_tree → mbs_tree which is injective and nondescending from (f i) to (f j). 
theorem good_finite_subsets_of_mbs_tree : ∀ f, is_good f os := wqo.is_good

-- Intuitively, the above f' is already a witness of the goodness of mbs_of_finite_tree, as it maps each branch of mbs_of_finite_tree i to a branch of mbs_of_finite_tree j. (Also note that there is no node in the mbs_of_finite_tree.)

-- However, according to the definition of embeds, f' has to be of type fin n → fin m, representing a permutation on the labels of the branches. The following construction recovers the desired function from f'.

-- branches at root of mbs_of_finite_tree form a set of mbs_tree
definition elt_copy_of_seq_branches (n : ℕ) : set mbs_tree := {x : mbs_tree | elt_of x ∈ seq_branches_of_mbs_tree n}

theorem copy_refl_left (x : mbs_tree) (n : ℕ) : x ∈ elt_copy_of_seq_branches n → elt_of x ∈ seq_branches_of_mbs_tree n := assume Hx, Hx

theorem copy_refl_right (x : mbs_tree) (n : ℕ) : elt_of x ∈ seq_branches_of_mbs_tree n → x ∈ elt_copy_of_seq_branches n := assume Hx, Hx

theorem finite_seq_branches [instance] (n : ℕ) : finite (seq_branches_of_mbs_tree n) := finite_set_of_branches_at_root (mbs_of_finite_tree n)

theorem finite_elt (n : ℕ) : finite (elt_copy_of_seq_branches n) := 
have mapsto : maps_to elt_of (elt_copy_of_seq_branches n) (seq_branches_of_mbs_tree n), from take x, assume Hx, copy_refl_left x n Hx,
have inj_on elt_of (elt_copy_of_seq_branches n), from take x₁ x₁, assume H₁, assume H₂, subtype.eq,
finite_of_inj_on mapsto this

definition copy_of_seq_branches (n : ℕ) : finite_subsets mbs_tree := tag (elt_copy_of_seq_branches n) (finite_elt n)

theorem good_copy : ∃ i j, i < j ∧ os (copy_of_seq_branches i) (copy_of_seq_branches j) := good_finite_subsets_of_mbs_tree copy_of_seq_branches

section
parameters {i j : ℕ}
parameter f' : mbs_tree → mbs_tree
parameter ni : ℕ
parameter tsi : fin ni → finite_tree
parameter Htsi : ∀ a, (tsi a, val a) ∈ seq_branches_of_mbs_tree i
parameter inj : inj_from_to f' (elt_copy_of_seq_branches i) (elt_copy_of_seq_branches j)
parameter nond : ∀ a, elt_of a ∈ seq_branches_of_mbs_tree i → pr1 (elt_of a) ≼ pr1 (elt_of (f' a)) ∧ elt_of (f' a) ∈ seq_branches_of_mbs_tree j
parameter nj : ℕ
parameter tsj : fin nj → finite_tree
parameter eqi : mbs_of_finite_tree i = cons tsi
parameter eqj : mbs_of_finite_tree j = cons tsj

lemma eltini (ti : fin ni) : (tsi ti, val ti) ∈ seq_branches_of_mbs_tree i := Htsi ti

lemma pmbsa (ti : fin ni) : ∃ i, (tsi ti, val ti) ∈ seq_branches_of_mbs_tree i := exists.intro i (eltini ti)

definition mbsa (ti : fin ni) : mbs_tree := tag (tsi ti, val ti) (pmbsa ti)

theorem eq_of_mbsa {a₁ a₂ : fin ni} (Heq : mbsa a₁ = mbsa a₂) : a₁ = a₂ :=
have elt_of (mbsa a₁) = (tsi a₁, val a₁), from rfl,
have elt_of (mbsa a₂) = (tsi a₂, val a₂), from rfl,
have elt_of (mbsa a₁) = elt_of (mbsa a₂), by rewrite Heq,
have (tsi a₁, val a₁) = (tsi a₂, val a₂), by+ simp,
have val a₁ = val a₂, by+ simp,
eq_of_veq this

theorem mem_mbsa (a : fin ni) : mbsa a ∈ elt_copy_of_seq_branches i := eltini a

lemma mem (ti : fin ni) : elt_of (f' (mbsa ti)) ∈ set_of_branches_at_root (mbs_of_finite_tree j) := and.right (nond _ (eltini ti))

definition recover (ti : fin ni) : fin nj :=
have elt_of (f' (mbsa ti)) ∈ seq_branches_of_mbs_tree j, from proof and.right (nond _ (eltini ti)) qed,
have mem : elt_of (f' (mbsa ti)) ∈ set_of_branches_at_root (mbs_of_finite_tree j), from this,
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches_at_root (mbs_of_finite_tree j), from rfl,
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches_at_root (cons tsj), by+ rewrite eqj at this{2};exact this, 
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches tsj, from this,
have elt_of (f' (mbsa ti)) ∈ set_of_branches tsj, by+ rewrite this at mem;exact mem,
have ∃ a : fin nj, tsj a = pr1 (elt_of (f' (mbsa ti))) ∧ val a = pr2 (elt_of (f' (mbsa ti))), from this,
some this

theorem perm_recover (ti : fin ni) : tsi ti ≼ tsj (recover ti) := 
have elt_of (f' (mbsa ti)) ∈ seq_branches_of_mbs_tree j, from proof and.right (nond _ (eltini ti)) qed,
have mem : elt_of (f' (mbsa ti)) ∈ set_of_branches_at_root (mbs_of_finite_tree j), from this,
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches_at_root (mbs_of_finite_tree j), from rfl,
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches_at_root (cons tsj), by+ rewrite eqj at this{2};exact this, 
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches tsj, from this,
have elt_of (f' (mbsa ti)) ∈ set_of_branches tsj, by+ rewrite this at mem;exact mem,
have ∃ a : fin nj, tsj a = pr1 (elt_of (f' (mbsa ti))) ∧ val a = pr2 (elt_of (f' (mbsa ti))), from this,
have tsj (recover ti) = pr1 (elt_of (f' (mbsa ti))), from proof and.left (some_spec this) qed,
have tsi ti ≼ pr1 (elt_of (f' (mbsa ti))), from proof and.left (nond _ (eltini ti)) qed,
by+ simp

theorem inj_recover : injective recover := 
take a₁ a₂, assume Heq,
have elt_of (f' (mbsa a₁)) ∈ seq_branches_of_mbs_tree j, from proof and.right (nond _ (eltini a₁)) qed,
have mem : elt_of (f' (mbsa a₁)) ∈ set_of_branches_at_root (mbs_of_finite_tree j), from this,
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches_at_root (mbs_of_finite_tree j), from rfl,
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches_at_root (cons tsj), by+ rewrite eqj at this{2};exact this, 
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches tsj, from this,
have elt_of (f' (mbsa a₁)) ∈ set_of_branches tsj, by+ rewrite this at mem;exact mem,
have eeq1 : ∃ a : fin nj, tsj a = pr1 (elt_of (f' (mbsa a₁))) ∧ val a = pr2 (elt_of (f' (mbsa a₁))), from this,
have pr11 : tsj (recover a₁) = pr1 (elt_of (f' (mbsa a₁))), from proof and.left (some_spec eeq1) qed,
have pr21 : val (recover a₁) = pr2 (elt_of (f' (mbsa a₁))), from proof and.right (some_spec eeq1) qed,
have elt_of (f' (mbsa a₂)) ∈ seq_branches_of_mbs_tree j, from proof and.right (nond _ (eltini a₂)) qed,
have mem : elt_of (f' (mbsa a₂)) ∈ set_of_branches_at_root (mbs_of_finite_tree j), from this,
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches_at_root (mbs_of_finite_tree j), from rfl,
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches_at_root (cons tsj), by+ rewrite eqj at this{2};exact this, 
have set_of_branches_at_root (mbs_of_finite_tree j) = set_of_branches tsj, from this,
have elt_of (f' (mbsa a₂)) ∈ set_of_branches tsj, by+ rewrite this at mem;exact mem,
have eeq2 : ∃ a : fin nj, tsj a = pr1 (elt_of (f' (mbsa a₂))) ∧ val a = pr2 (elt_of (f' (mbsa a₂))), from this,
have pr12 : tsj (recover a₂) = pr1 (elt_of (f' (mbsa a₂))), from proof and.left (some_spec eeq2) qed,
have pr22 : val (recover a₂) = pr2 (elt_of (f' (mbsa a₂))), from proof and.right (some_spec eeq2) qed,
have eq1 : pr1 (elt_of (f' (mbsa a₁))) = pr1 (elt_of (f' (mbsa a₂))), by+ simp,
have pr2 (elt_of (f' (mbsa a₁))) = pr2 (elt_of (f' (mbsa a₂))), by+ simp,
have elt_of (f' (mbsa a₁)) = elt_of (f' (mbsa a₂)), from eq_of_prod eq1 this,
have f'eq : f' (mbsa a₁) = f' (mbsa a₂), from subtype.eq this,
have ∀ x₁ x₂ : mbs_tree, x₁ ∈ elt_copy_of_seq_branches i → x₂ ∈ elt_copy_of_seq_branches i → f' x₁ = f' x₂ → x₁ = x₂, from and.right inj,
have mbsa a₁ = mbsa a₂, from this (mbsa a₁) (mbsa a₂) (mem_mbsa a₁) (mem_mbsa a₂) f'eq,
eq_of_mbsa this

end

check @recover

theorem good_mbs_of_finite_tree :  ∃ i j, i < j ∧ mbs_of_finite_tree i ≼ mbs_of_finite_tree j :=
obtain (i j) h, from good_copy,
have mbs_of_finite_tree i ≠ node, from ne_node_of_elt_of_mbs_finite_tree i,
have ∃ ni, ∃ tsi : fin ni → finite_tree, mbs_of_finite_tree i = cons tsi, from exists_eq_cons_of_ne_node this,
obtain ni hni, from this,
obtain tsi htsi, from hni,
have mbs_of_finite_tree j ≠ node, from ne_node_of_elt_of_mbs_finite_tree j,
have ∃ nj, ∃ tsj : fin nj → finite_tree, mbs_of_finite_tree j = cons tsj, from exists_eq_cons_of_ne_node this,
obtain nj hnj, from this,
obtain tsj htsj, from hnj,
obtain f' hf', from and.right h,
have Htsi : ∀ a, (tsi a, val a) ∈ seq_branches_of_mbs_tree i, from take a, mem_of_seq_branches tsi a htsi,
have inj : inj_from_to f' (elt_copy_of_seq_branches i) (elt_copy_of_seq_branches j), from and.left hf',
have pf' : ∀ a : mbs_tree, a ∈ elt_copy_of_seq_branches i → embeds' a (f' a) ∧ (f' a) ∈ elt_copy_of_seq_branches j, from and.right hf',
have nond :  ∀ a, elt_of a ∈ seq_branches_of_mbs_tree i → pr1 (elt_of a) ≼ pr1 (elt_of (f' a)) ∧ elt_of (f' a) ∈ seq_branches_of_mbs_tree j, from 
  take a, assume Ha, 
  have mema : a ∈ elt_copy_of_seq_branches i, from copy_refl_right a i Ha,
  have Hl : pr1 (elt_of a) ≼ pr1 (elt_of (f' a)), from and.left (pf' a mema),
  have elt_of (f' a) ∈ seq_branches_of_mbs_tree j, from copy_refl_left (f' a) j (and.right (pf' a mema)),
  and.intro Hl this,
let f (a : fin ni) : fin nj := recover f' ni tsi Htsi nond nj tsj htsj a in
have Hl : injective f, from inj_recover f' ni tsi Htsi inj nond nj tsj htsj,
have ∀ z : fin ni, tsi z ≼ tsj (f z), from take z, perm_recover f' ni tsi Htsi nond nj tsj htsj z,
have ∃ f, injective f ∧ ∀ z, tsi z ≼ tsj (f z), from proof exists.intro f (and.intro Hl this) qed,
have cons tsi ≼ cons tsj, from or.intro_right (∃ b, cons tsi ≼ tsj b) this,
have mbs_of_finite_tree i ≼ mbs_of_finite_tree j, by+ simp,
exists.intro i (exists.intro j (and.intro (and.left h) this))

theorem Kruskal's_contradiction : false := bad_mbs_finite_tree good_mbs_of_finite_tree

end

theorem embeds_is_good : ∀ f, is_good f embeds :=
by_contradiction
(suppose ¬ ∀ f, is_good f embeds,
 have ∃ f, ¬ is_good f embeds, from exists_not_of_not_forall this,
 Kruskal's_contradiction this)

definition wqo_finite_tree [instance] : wqo finite_tree :=
wqo.mk embeds embeds_refl @embeds_trans embeds_is_good

