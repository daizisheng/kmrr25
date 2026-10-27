import Kmrr25.Basic

/-!
# Question 5.23 and Question §5.4(b): the literal question has a negative answer

This file formalizes Theorem \ref{G:thm:q523literal} and Lemma \ref{G:lem:folnergrow} of the
paper, for an arbitrary infinite group `G`, an arbitrary left Følner sequence `Φ` and every
dimension `d ≥ 2` (written `d = k + 2`, points of `G^d` being maps `Fin (k + 2) → G`).

* `IsLeftFolner Φ`: `Φ N` nonempty finite and `|g Φ_N △ Φ_N| / |Φ_N| → 0` for all `g`;
  `isLeftFolner_iff` shows this is the paper's condition `|Φ_N ∩ g Φ_N| / |Φ_N| → 1`.
* `relDens F S = |F ∩ S| / |F|` and `HasDensityAlong Φ S δ`: `relDens (Φ N) S → δ`.
* `card_tendsto_atTop`: Lemma \ref{G:lem:folnergrow}.
* `countable_of_isLeftFolner`: a group with a left Følner sequence is countable (the remark
  before Lemma \ref{G:lem:folnergrow}).
* `cornerSet e k`: the set `A_d = {x | x_1 = g_n, x_d = g_m, n < m}` for an enumeration
  `e : ℕ ≃ G`.
* `q523literal`: parts (i)–(iv) of Theorem \ref{G:thm:q523literal}, including the statement
  that for injective `b` only finitely many `(b(i) t_1, t_2, …, t_d)` lie in `A_d`.
* `q523_negative`: the resulting negative answer: conditions (I) and (II) (iterated `liminf`s,
  the outer one along the cofinite filter) hold with value `1`, but `A_d` contains no corner
  configuration `HasCorner A t b` with injective `b`.

Amenability is not assumed separately: the existence of a left Følner sequence is the only
hypothesis used, and countability is derived from it.
-/

open Filter Topology Finset
open scoped Classical symmDiff

noncomputable section

namespace Kmrr25.Q523

variable {G : Type*} [Group G]

/-- A *left Følner sequence* in a group `G`: a sequence `Φ N` of nonempty finite subsets of `G`
such that `|g Φ_N △ Φ_N| / |Φ_N| → 0` for every `g ∈ G`. -/
def IsLeftFolner (Φ : ℕ → Finset G) : Prop :=
  (∀ N, (Φ N).Nonempty) ∧
    ∀ g : G, Tendsto (fun N => (#(((Φ N).image (g * ·)) ∆ Φ N) : ℝ) / #(Φ N)) atTop (𝓝 0)

theorem card_image_symmDiff (g : G) (F : Finset G) :
    #((F.image (g * ·)) ∆ F) + 2 * #(F ∩ F.image (g * ·)) = 2 * #F := by
  have hT : #(F.image (g * ·)) = #F := Finset.card_image_of_injective _ (mul_right_injective g)
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  have h1 := Finset.card_sdiff_add_card_inter (F.image (g * ·)) F
  have h2 := Finset.card_sdiff_add_card_inter F (F.image (g * ·))
  rw [Finset.inter_comm] at h1
  omega

/-- The definition of a left Følner sequence via symmetric differences agrees with the one used
in the paper, `|Φ_N ∩ g Φ_N| / |Φ_N| → 1` for every `g`. -/
theorem isLeftFolner_iff {Φ : ℕ → Finset G} :
    IsLeftFolner Φ ↔ (∀ N, (Φ N).Nonempty) ∧
      ∀ g : G, Tendsto (fun N => (#(Φ N ∩ (Φ N).image (g * ·)) : ℝ) / #(Φ N)) atTop (𝓝 1) := by
  have key : ∀ (g : G) (N : ℕ), (Φ N).Nonempty →
      (#(((Φ N).image (g * ·)) ∆ Φ N) : ℝ) / #(Φ N) =
        2 - 2 * ((#(Φ N ∩ (Φ N).image (g * ·)) : ℝ) / #(Φ N)) := by
    intro g N hN
    have hp : (0 : ℝ) < #(Φ N) := by exact_mod_cast hN.card_pos
    have h := card_image_symmDiff g (Φ N)
    have h' : (#(((Φ N).image (g * ·)) ∆ Φ N) : ℝ) + 2 * #(Φ N ∩ (Φ N).image (g * ·)) =
        2 * #(Φ N) := by exact_mod_cast h
    field_simp
    linarith
  constructor
  · rintro ⟨hne, hg⟩
    refine ⟨hne, fun g => ?_⟩
    have := ((tendsto_const_nhds (x := (2 : ℝ))).sub (hg g)).div_const (2 : ℝ)
    rw [show ((2 : ℝ) - 0) / 2 = 1 by norm_num] at this
    refine this.congr (fun N => ?_)
    rw [key g N (hne N)]
    ring
  · rintro ⟨hne, hg⟩
    refine ⟨hne, fun g => ?_⟩
    have := (tendsto_const_nhds (x := (2 : ℝ))).sub ((hg g).const_mul (2 : ℝ))
    rw [show (2 : ℝ) - 2 * 1 = 0 by norm_num] at this
    refine this.congr (fun N => ?_)
    rw [key g N (hne N)]

/-- The relative density `|F ∩ S| / |F|` of a set `S` in a finite set `F`. -/
def relDens {α : Type*} (F : Finset α) (S : Set α) : ℝ :=
  (#{x ∈ F | x ∈ S} : ℝ) / #F

/-- Computing `relDens` with an arbitrary decidable predicate describing `S`. -/
theorem relDens_eq {α : Type*} (F : Finset α) (S : Set α) (P : α → Prop) [DecidablePred P]
    (h : ∀ x, x ∈ S ↔ P x) : relDens F S = (#{x ∈ F | P x} : ℝ) / #F := by
  unfold relDens
  congr 3
  exact Finset.filter_congr (fun x _ => h x)

/-- `S` has density `δ` along the sequence of finite sets `Φ`:
`|S ∩ Φ_N| / |Φ_N| → δ`. -/
def HasDensityAlong {α : Type*} (Φ : ℕ → Finset α) (S : Set α) (δ : ℝ) : Prop :=
  Tendsto (fun N => relDens (Φ N) S) atTop (𝓝 δ)

/-- Paper, Lemma \ref{G:lem:folnergrow}. In an infinite group the sets of a left Følner
sequence have cardinalities tending to infinity. -/
theorem card_tendsto_atTop [Infinite G] {Φ : ℕ → Finset G} (hΦ : IsLeftFolner Φ) :
    Tendsto (fun N => #(Φ N)) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  by_contra h
  rw [not_eventually] at h
  simp only [not_le] at h
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq G K
  have hK : (0 : ℝ) < 1 / K := by
    obtain ⟨N, hN⟩ := h.exists
    have : 0 < K := lt_of_le_of_lt (Nat.zero_le _) hN
    positivity
  have hev : ∀ᶠ N in atTop, ∀ x ∈ S,
      (#(((Φ N).image (x * ·)) ∆ Φ N) : ℝ) / #(Φ N) < 1 / K := by
    rw [eventually_all_finset]
    intro x _
    exact (hΦ.2 x).eventually (gt_mem_nhds hK)
  obtain ⟨N, hN, hN'⟩ := (h.and_eventually hev).exists
  have hpos : 0 < #(Φ N) := (hΦ.1 N).card_pos
  have hfix : ∀ x ∈ S, (Φ N).image (x * ·) = Φ N := by
    intro x hx
    have h1 := hN' x hx
    by_contra hne
    have hc : 1 ≤ #(((Φ N).image (x * ·)) ∆ Φ N) := by
      rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
      intro h0
      exact hne (symmDiff_eq_bot.mp h0)
    have : (1 : ℝ) / K ≤ (#(((Φ N).image (x * ·)) ∆ Φ N) : ℝ) / #(Φ N) := by
      rw [div_le_div_iff₀ (by exact_mod_cast (lt_trans hpos hN)) (by exact_mod_cast hpos)]
      have : (#(Φ N) : ℝ) ≤ K := by exact_mod_cast hN.le
      have : (1 : ℝ) ≤ #(((Φ N).image (x * ·)) ∆ Φ N) := by exact_mod_cast hc
      nlinarith
    linarith
  obtain ⟨y, hy⟩ := hΦ.1 N
  have hsub : S.image (· * y) ⊆ Φ N := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    rw [← hfix x hx]
    exact Finset.mem_image_of_mem _ hy
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (mul_left_injective y), hS] at this
  omega


/-- A group admitting a left Følner sequence is countable: every `g` satisfies
`g Φ_N ∩ Φ_N ≠ ∅` for large `N`, so `g ∈ ⋃_N Φ_N Φ_N⁻¹`. -/
theorem countable_of_isLeftFolner {Φ : ℕ → Finset G} (hΦ : IsLeftFolner Φ) : Countable G := by
  let T : Set G := ⋃ N, (((Φ N ×ˢ Φ N).image (fun p => p.1 * p.2⁻¹) : Finset G) : Set G)
  have hT : T.Countable := Set.countable_iUnion fun N => (Finset.countable_toSet _)
  have huniv : (Set.univ : Set G) ⊆ T := by
    intro g _
    obtain ⟨N, hN⟩ := ((hΦ.2 g).eventually (gt_mem_nhds (zero_lt_one' ℝ))).exists
    have hpos : 0 < #(Φ N) := (hΦ.1 N).card_pos
    have hnd : ¬ Disjoint ((Φ N).image (g * ·)) (Φ N) := by
      intro hd
      rw [hd.symmDiff_eq_sup, Finset.sup_eq_union, Finset.card_union_of_disjoint hd,
        Finset.card_image_of_injective _ (mul_right_injective g)] at hN
      have hp : (0 : ℝ) < #(Φ N) := by exact_mod_cast hpos
      rw [div_lt_one hp] at hN
      push_cast at hN
      linarith
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨z, hz1, hz2⟩ := hnd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz1
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
    exact ⟨(g * x, x), ⟨hz2, hx⟩, by simp⟩
  exact Set.countable_univ_iff.mp (hT.mono huniv)

/-- A set with finite complement has density `1` along any left Følner sequence of an
infinite group. -/
theorem hasDensityAlong_one_of_compl_finite [Infinite G] {Φ : ℕ → Finset G}
    (hΦ : IsLeftFolner Φ) {S : Set G} (hS : Sᶜ.Finite) : HasDensityAlong Φ S 1 := by
  have hc : Tendsto (fun N => ((#(Φ N) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (card_tendsto_atTop hΦ)
  set c : ℕ := #hS.toFinset
  have hlow : Tendsto (fun N => (1 : ℝ) - c / #(Φ N)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hc)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun N => ?_)
    (fun N => ?_)
  · have hp : (0 : ℝ) < #(Φ N) := by exact_mod_cast (hΦ.1 N).card_pos
    have hsplit := Finset.card_filter_add_card_filter_not (s := Φ N) (fun x => x ∈ S)
    have hle : #{x ∈ Φ N | ¬ x ∈ S} ≤ c := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter] at hx
      simpa using hx.2
    unfold relDens
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', one_sub_div hp.ne', div_le_div_iff_of_pos_right hp]
    have : ((#{x ∈ Φ N | x ∈ S} : ℕ) : ℝ) + #{x ∈ Φ N | ¬ x ∈ S} = #(Φ N) := by
      exact_mod_cast hsplit
    have : ((#{x ∈ Φ N | ¬ x ∈ S} : ℕ) : ℝ) ≤ c := by exact_mod_cast hle
    linarith
  · have hp : (0 : ℝ) < #(Φ N) := by exact_mod_cast (hΦ.1 N).card_pos
    unfold relDens
    rw [div_le_one hp]
    exact_mod_cast Finset.card_filter_le _ _

omit [Group G] in
/-- Counting tuples by their last coordinate:
`#{y ∈ s^{k+1} | P (y_last)} = #{h ∈ s | P h} * #s^k`. -/
theorem card_filter_piFinset_last (s : Finset G) (P : G → Prop) [DecidablePred P] (k : ℕ) :
    #{y ∈ Fintype.piFinset (fun _ : Fin (k + 1) => s) | P (y (Fin.last k))} =
      #{h ∈ s | P h} * #s ^ k := by
  have hk : #(Fintype.piFinset (fun _ : Fin k => s)) = #s ^ k := by
    simp [Fintype.card_piFinset]
  rw [← hk, ← Finset.card_product]
  refine Finset.card_nbij' (fun y => (y (Fin.last k), Fin.init y))
    (fun p => (Fin.snoc p.2 p.1 : Fin (k + 1) → G)) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset] at hy
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Set.mem_ofPred_eq,
      Finset.mem_coe, Fintype.mem_piFinset]
    exact ⟨⟨hy.1 _, hy.2⟩, fun i => hy.1 _⟩
  · intro p hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Set.mem_ofPred_eq,
      Finset.mem_coe, Fintype.mem_piFinset] at hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, Fin.snoc_last]
    refine ⟨fun i => ?_, hp.1.2⟩
    induction i using Fin.lastCases with
    | last => simpa using hp.1.1
    | cast j => simpa using hp.2 j
  · intro y _
    simp
  · intro p _
    simp

omit [Group G] in
/-- Counting tuples by their first and last coordinates:
`#{x ∈ s^{k+2} | P (x_0) (x_last)} = #{p ∈ s × s | P p.1 p.2} * #s^k`. -/
theorem card_filter_piFinset_zero_last (s : Finset G) (P : G → G → Prop)
    [∀ a b, Decidable (P a b)] (k : ℕ) :
    #{x ∈ Fintype.piFinset (fun _ : Fin (k + 2) => s) | P (x 0) (x (Fin.last (k + 1)))} =
      #{p ∈ s ×ˢ s | P p.1 p.2} * #s ^ k := by
  have hk : #(Fintype.piFinset (fun _ : Fin k => s)) = #s ^ k := by
    simp [Fintype.card_piFinset]
  rw [← hk, ← Finset.card_product]
  refine Finset.card_nbij' (fun x => ((x 0, x (Fin.last (k + 1))), fun j => x j.castSucc.succ))
    (fun p => (Fin.cons p.1.1 (Fin.snoc p.2 p.1.2 : Fin (k + 1) → G) : Fin (k + 2) → G))
    ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset] at hy
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Set.mem_ofPred_eq,
      Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product]
    exact ⟨⟨⟨hy.1 _, hy.1 _⟩, hy.2⟩, fun i => hy.1 _⟩
  · intro p hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Set.mem_ofPred_eq,
      Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product] at hp
    have hl : (Fin.last (k + 1)) = (Fin.last k).succ := (Fin.succ_last k).symm
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, Fin.cons_zero, hl,
      Fin.cons_succ, Fin.snoc_last]
    refine ⟨fun i => ?_, hp.1.2⟩
    induction i using Fin.cases with
    | zero => simpa using hp.1.1.1
    | succ i =>
      induction i using Fin.lastCases with
      | last => simpa using hp.1.1.2
      | cast j => simpa using hp.2 j
  · intro x _
    simp only
    have hl : (Fin.last (k + 1)) = (Fin.last k).succ := (Fin.succ_last k).symm
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      induction i using Fin.lastCases with
      | last => rw [Fin.cons_succ, Fin.snoc_last, hl]
      | cast j => simp
  · intro p _
    have hl : (Fin.last (k + 1)) = (Fin.last k).succ := (Fin.succ_last k).symm
    rw [hl]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_last, Fin.snoc_castSucc]


omit [Group G] in
/-- For an enumeration `e` of `G`, the ordered pairs in `s × s` whose first entry is earlier
in the enumeration are exactly half of the off-diagonal pairs: `2L + |s| = |s|^2`. -/
theorem two_mul_card_lt_add_card (e : ℕ ≃ G) (s : Finset G) :
    2 * #{p ∈ s ×ˢ s | e.symm p.1 < e.symm p.2} + #s = #s ^ 2 := by
  have h1 := Finset.card_filter_add_card_filter_not (s := s ×ˢ s)
    (fun p : G × G => e.symm p.1 < e.symm p.2)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := {p ∈ s ×ˢ s | ¬ e.symm p.1 < e.symm p.2}) (fun p : G × G => e.symm p.2 < e.symm p.1)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have hR : #{p ∈ s ×ˢ s | ¬ e.symm p.1 < e.symm p.2 ∧ e.symm p.2 < e.symm p.1} =
      #{p ∈ s ×ˢ s | e.symm p.1 < e.symm p.2} := by
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.2⟩
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, not_lt.mpr hp.2.le, hp.2⟩
    · intro p _; simp
    · intro p _; simp
  have hD : #{p ∈ s ×ˢ s | ¬ e.symm p.1 < e.symm p.2 ∧ ¬ e.symm p.2 < e.symm p.1} = #s := by
    refine Finset.card_nbij' (fun p => p.1) (fun x => (x, x)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp
      exact hp.1.1
    · intro x hx
      simp only [Finset.mem_coe] at hx
      simp [hx]
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq] at hp
      have : p.1 = p.2 := e.symm.injective (le_antisymm (not_lt.mp hp.2.2) (not_lt.mp hp.2.1))
      ext <;> simp [this]
    · intro x _; simp
  rw [hR, hD] at h2
  rw [Finset.card_product] at h1
  rw [sq]
  omega

/-- The set `A_d ⊆ G^d` (here `d = k + 2`) of the paper: for an enumeration
`G = {e 0, e 1, e 2, …}` without repetitions, `x ∈ A_d` iff the first coordinate `x_1` comes
strictly earlier in the enumeration than the last coordinate `x_d`. -/
def cornerSet (e : ℕ ≃ G) (k : ℕ) : Set (Fin (k + 2) → G) :=
  {x | e.symm (x 0) < e.symm (x (Fin.last (k + 1)))}

/-- The last-coordinate fibre `{h | (x_1, …, x_{d-1}, h) ∈ A}` of `A ⊆ G^d`, `d = k + 2`,
over `y = (x_1, …, x_{d-1}) ∈ G^{d-1}`. -/
def lastFibre {k : ℕ} (A : Set (Fin (k + 2) → G)) (y : Fin (k + 1) → G) : Set G :=
  {h | (Fin.snoc y h : Fin (k + 2) → G) ∈ A}

/-- The fibre `{y ∈ G^{d-1} | (x_1, y) ∈ A}` of `A ⊆ G^d`, `d = k + 2`, over the first
coordinate `x_1`. -/
def firstFibre {k : ℕ} (A : Set (Fin (k + 2) → G)) (x₁ : G) : Set (Fin (k + 1) → G) :=
  {y | (Fin.cons x₁ y : Fin (k + 2) → G) ∈ A}

/-- The `j`-th point of the `d`-dimensional corner (`d = k + 2`, `0 ≤ j ≤ d`) with base point
`t` along the indices `i_1 < ⋯ < i_d`:
`(b(i_1) t_1, …, b(i_j) t_j, t_{j+1}, …, t_d)`. -/
def cornerPoint {k : ℕ} (t : Fin (k + 2) → G) (b : ℕ → G) (i : Fin (k + 2) → ℕ)
    (j : Fin (k + 3)) : Fin (k + 2) → G :=
  fun l => if (l : ℕ) < (j : ℕ) then b (i l) * t l else t l

/-- `A ⊆ G^d` (`d = k + 2`) contains the corner configuration of the paper with base point `t`
and sequence `b`: for all `i_1 < ⋯ < i_d` all `d + 1` corner points lie in `A`. For `d = 2`
these are the points `(t, s), (b(i) t, s), (b(i) t, b(j) s)` with `i < j`. -/
def HasCorner {k : ℕ} (A : Set (Fin (k + 2) → G)) (t : Fin (k + 2) → G) (b : ℕ → G) : Prop :=
  ∀ i : Fin (k + 2) → ℕ, StrictMono i → ∀ j : Fin (k + 3), cornerPoint t b i j ∈ A

omit [Group G] in
theorem lastFibre_cornerSet (e : ℕ ≃ G) (k : ℕ) (y : Fin (k + 1) → G) :
    lastFibre (cornerSet e k) y = {h | e.symm (y 0) < e.symm h} := by
  ext h
  have h0 : (0 : Fin (k + 2)) = Fin.castSucc 0 := rfl
  simp only [lastFibre, cornerSet, Set.mem_ofPred_eq, Fin.snoc_last]
  rw [h0, Fin.snoc_castSucc]

omit [Group G] in
theorem firstFibre_cornerSet (e : ℕ ≃ G) (k : ℕ) (x₁ : G) :
    firstFibre (cornerSet e k) x₁ = {y | e.symm x₁ < e.symm (y (Fin.last k))} := by
  ext y
  have hl : (Fin.last (k + 1)) = (Fin.last k).succ := (Fin.succ_last k).symm
  simp only [firstFibre, cornerSet, Set.mem_ofPred_eq, Fin.cons_zero]
  rw [hl, Fin.cons_succ]

omit [Group G] in
theorem compl_finite_gt (e : ℕ ≃ G) (n : ℕ) : ({h | n < e.symm h} : Set G)ᶜ.Finite := by
  have : ({h | n < e.symm h} : Set G)ᶜ = e.symm ⁻¹' Set.Iic n := by
    ext h; simp
  rw [this]
  exact (Set.finite_Iic n).preimage e.symm.injective.injOn

theorem hasDensityAlong_gt (e : ℕ ≃ G) {Φ : ℕ → Finset G} (hΦ : IsLeftFolner Φ) (n : ℕ) :
    HasDensityAlong Φ {h | n < e.symm h} 1 := by
  have : Infinite G := Infinite.of_injective e e.injective
  exact hasDensityAlong_one_of_compl_finite hΦ (compl_finite_gt e n)

/-- **Paper, Theorem \ref{G:thm:q523literal}, parts (i)–(iv).** Let `G` be a countably infinite
group, enumerated without repetitions by `e : ℕ ≃ G`, let `d = k + 2 ≥ 2`, and let `Φ` be any
left Følner sequence in `G`. For `A_d = cornerSet e k`:
(i) every last-coordinate fibre is cofinite and has density `1` along `Φ`;
(ii) every fibre over the first coordinate has density `1` along `Φ^{d-1}`;
(iii) `|A_d ∩ Φ_M^d| / |Φ_M|^d → 1/2`;
(iv) for every `t ∈ G^d` the set `{g | (g t_1, t_2, …, t_d) ∈ A_d}` is finite; consequently,
for injective `b`, `(b(i) t_1, t_2, …, t_d) ∈ A_d` holds for only finitely many `i`. -/
theorem q523literal (e : ℕ ≃ G) {Φ : ℕ → Finset G} (hΦ : IsLeftFolner Φ) (k : ℕ) :
    (∀ y : Fin (k + 1) → G, (lastFibre (cornerSet e k) y)ᶜ.Finite ∧
        HasDensityAlong Φ (lastFibre (cornerSet e k) y) 1) ∧
    (∀ x₁ : G, HasDensityAlong (fun M => Fintype.piFinset fun _ : Fin (k + 1) => Φ M)
        (firstFibre (cornerSet e k) x₁) 1) ∧
    HasDensityAlong (fun M => Fintype.piFinset fun _ : Fin (k + 2) => Φ M) (cornerSet e k)
        (1 / 2) ∧
    (∀ t : Fin (k + 2) → G, {g : G | Function.update t 0 (g * t 0) ∈ cornerSet e k}.Finite) ∧
    (∀ (t : Fin (k + 2) → G) (b : ℕ → G), Function.Injective b →
        {i : ℕ | Function.update t 0 (b i * t 0) ∈ cornerSet e k}.Finite) := by
  have : Infinite G := Infinite.of_injective e e.injective
  have hcard := card_tendsto_atTop hΦ
  have hiv : ∀ t : Fin (k + 2) → G,
      {g : G | Function.update t 0 (g * t 0) ∈ cornerSet e k}.Finite := by
    intro t
    have hne : (Fin.last (k + 1)) ≠ 0 := by
      intro h; exact absurd (congrArg Fin.val h) (by simp)
    have : {g : G | Function.update t 0 (g * t 0) ∈ cornerSet e k} =
        (fun g => g * t 0) ⁻¹' (e.symm ⁻¹' Set.Iio (e.symm (t (Fin.last (k + 1))))) := by
      ext g
      simp [cornerSet]
    rw [this]
    exact ((Set.finite_Iio _).preimage e.symm.injective.injOn).preimage
      (mul_left_injective (t 0)).injOn
  refine ⟨fun y => ?_, fun x₁ => ?_, ?_, hiv, fun t b hb => ?_⟩
  · rw [lastFibre_cornerSet]
    exact ⟨compl_finite_gt e _, hasDensityAlong_gt e hΦ _⟩
  · rw [firstFibre_cornerSet]
    refine (hasDensityAlong_gt e hΦ (e.symm x₁)).congr (fun M => ?_)
    have hp : (0 : ℝ) < #(Φ M) := by exact_mod_cast (hΦ.1 M).card_pos
    have h1 := card_filter_piFinset_last (Φ M) (fun h => e.symm x₁ < e.symm h) k
    have h2 : #(Fintype.piFinset fun _ : Fin (k + 1) => Φ M) = #(Φ M) * #(Φ M) ^ k := by
      simp [Fintype.card_piFinset, pow_succ, mul_comm]
    rw [relDens_eq (Φ M) {h | e.symm x₁ < e.symm h} (fun h => e.symm x₁ < e.symm h)
        (fun _ => Iff.rfl),
      relDens_eq _ {y | e.symm x₁ < e.symm (y (Fin.last k))}
        (fun y : Fin (k + 1) → G => e.symm x₁ < e.symm (y (Fin.last k))) (fun _ => Iff.rfl)]
    beta_reduce
    rw [h1, h2]
    push_cast
    rw [mul_div_mul_right _ _ (pow_ne_zero _ hp.ne')]
  · have hlim : Tendsto (fun M => ((1 : ℝ) - ((#(Φ M) : ℕ) : ℝ)⁻¹) / 2) atTop (𝓝 (1 / 2)) := by
      have := tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hcard)
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub this).div_const (2 : ℝ)
    refine hlim.congr (fun M => ?_)
    have hp : (0 : ℝ) < #(Φ M) := by exact_mod_cast (hΦ.1 M).card_pos
    have h1 := card_filter_piFinset_zero_last (Φ M) (fun a b => e.symm a < e.symm b) k
    have h2 : #(Fintype.piFinset fun _ : Fin (k + 2) => Φ M) = #(Φ M) ^ k * #(Φ M) ^ 2 := by
      simp [Fintype.card_piFinset, pow_add]
    have h3 := two_mul_card_lt_add_card e (Φ M)
    rw [relDens_eq _ (cornerSet e k)
        (fun x : Fin (k + 2) → G => e.symm (x 0) < e.symm (x (Fin.last (k + 1))))
        (fun _ => Iff.rfl)]
    beta_reduce
    rw [h1, h2]
    set L := #{p ∈ Φ M ×ˢ Φ M | e.symm p.1 < e.symm p.2}
    set n := #(Φ M)
    have h3' : (2 : ℝ) * L + n = n ^ 2 := by exact_mod_cast h3
    push_cast
    have hk : (0 : ℝ) < (n : ℝ) ^ k := pow_pos hp k
    rw [mul_comm ((n : ℝ) ^ k) _, mul_div_mul_right _ _ hk.ne', eq_div_iff (by positivity)]
    have h4 : (1 - (n : ℝ)⁻¹) / 2 * n ^ 2 = ((n : ℝ) ^ 2 - n) / 2 := by
      field_simp
    rw [h4]
    linarith
  · have : {i : ℕ | Function.update t 0 (b i * t 0) ∈ cornerSet e k} =
        b ⁻¹' {g : G | Function.update t 0 (g * t 0) ∈ cornerSet e k} := rfl
    rw [this]
    exact (hiv t).preimage hb.injOn


/-- The first nontrivial point of a corner is `(b(i_1) t_1, t_2, …, t_d)`. -/
theorem cornerPoint_one {k : ℕ} (t : Fin (k + 2) → G) (b : ℕ → G) (i : Fin (k + 2) → ℕ) :
    cornerPoint t b i 1 = Function.update t 0 (b (i 0) * t 0) := by
  funext l
  by_cases hl : l = 0
  · subst hl; simp [cornerPoint]
  · have : ¬ (l : ℕ) < 1 := by
      intro h; exact hl (Fin.ext (by simpa using h))
    simp [cornerPoint, hl, this]

/-- If `{g | (g t_1, t_2, …, t_d) ∈ A}` is finite for every `t`, then `A` contains no corner
configuration with an injective sequence `b`. -/
theorem not_hasCorner_of_finite {k : ℕ} {A : Set (Fin (k + 2) → G)}
    (hA : ∀ t : Fin (k + 2) → G, {g : G | Function.update t 0 (g * t 0) ∈ A}.Finite)
    (t : Fin (k + 2) → G) (b : ℕ → G) (hb : Function.Injective b) : ¬ HasCorner A t b := by
  intro hc
  have hall : ∀ m : ℕ, b m ∈ {g : G | Function.update t 0 (g * t 0) ∈ A} := by
    intro m
    have hmono : StrictMono (fun l : Fin (k + 2) => m + (l : ℕ)) := by
      intro a a' h
      simp only [Fin.lt_def] at h
      simp only
      omega
    have := hc _ hmono 1
    rw [cornerPoint_one] at this
    simpa using this
  have hinf : (Set.range b).Infinite := Set.infinite_range_of_injective hb
  exact hinf ((hA t).subset (by rintro _ ⟨m, rfl⟩; exact hall m))

/-- **Paper, Theorem \ref{G:thm:q523literal} (negative answer to Question 5.23 and its
`G^d` version, Question §5.4(b)).** Let `G` be an infinite group and `Φ` a left Følner
sequence in `G` (so `G` is countable and amenable), and let `d = k + 2 ≥ 2`. There is a set
`A ⊆ G^d` such that
* condition (I) holds with value `1`: `liminf_{(x_1,…,x_{d-1}) → ∞} liminf_M` of the density
  of the last-coordinate fibre in `Φ_M` equals `1`;
* condition (II) holds with value `1`: `liminf_{x_1 → ∞} liminf_M` of the density of the
  fibre over `x_1` in `Φ_M^{d-1}` equals `1`;
(for `d = 2` both are condition (G:eq:23) of Question 5.23), but for no base point `t` and
no injective `b : ℕ → G` does `A` contain the corner configuration
`(t_1, …, t_d), (b(i_1) t_1, t_2, …), …, (b(i_1) t_1, …, b(i_d) t_d)` for all
`i_1 < ⋯ < i_d`. Here `x → ∞` means convergence along the cofinite filter. -/
theorem q523_negative [Infinite G] {Φ : ℕ → Finset G} (hΦ : IsLeftFolner Φ) (k : ℕ) :
    ∃ A : Set (Fin (k + 2) → G),
      liminf (fun y : Fin (k + 1) → G =>
          liminf (fun M => relDens (Φ M) (lastFibre A y)) atTop) cofinite = 1 ∧
      liminf (fun x₁ : G =>
          liminf (fun M => relDens (Fintype.piFinset fun _ : Fin (k + 1) => Φ M)
            (firstFibre A x₁)) atTop) cofinite = 1 ∧
      ∀ (t : Fin (k + 2) → G) (b : ℕ → G), Function.Injective b → ¬ HasCorner A t b := by
  have : Countable G := countable_of_isLeftFolner hΦ
  obtain ⟨hD⟩ := nonempty_denumerable G
  let e : ℕ ≃ G := (Denumerable.eqv G).symm
  obtain ⟨hi, hii, -, hiv, -⟩ := q523literal e hΦ k
  refine ⟨cornerSet e k, ?_, ?_, not_hasCorner_of_finite hiv⟩
  · have : (fun y : Fin (k + 1) → G =>
        liminf (fun M => relDens (Φ M) (lastFibre (cornerSet e k) y)) atTop) = fun _ => 1 := by
      funext y
      exact (hi y).2.liminf_eq
    rw [this, liminf_const]
  · have : (fun x₁ : G =>
        liminf (fun M => relDens (Fintype.piFinset fun _ : Fin (k + 1) => Φ M)
          (firstFibre (cornerSet e k) x₁)) atTop) = fun _ => 1 := by
      funext x₁
      exact (hii x₁).liminf_eq
    rw [this, liminf_const]

end Kmrr25.Q523
