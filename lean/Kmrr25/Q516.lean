import Kmrr25.Basic

/-!
# Admissible translates for `B ⊕ B + t` in abelian groups (Question 5.16)

Paper, Section \ref{G:sec:translates}: Theorem \ref{G:thm:translates}, Lemmas
\ref{G:lem:density}, \ref{G:lem:pigeon}, \ref{G:lem:move}, and Proposition \ref{G:prop:strict}.

## Conditional result

The existence of *some* admissible translate is a theorem of Charamaras and Mountakis
(*Finding product sets in some classes of amenable groups*, Corollary 1.13), quoted in the paper
as Theorem \ref{G:thm:CM}; it is **not** formalized here. It is the `Prop`
`CharamarasMountakisCor113` below, transcribed from the paper's quotation and quantified over all
countable abelian groups `Γ` (in a fixed universe) with `[Γ : 2Γ] < ∞`. The results of
Theorem \ref{G:thm:translates} that depend on it take it as an explicit hypothesis
`(hCM : CharamarasMountakisCor113)`; it is not an axiom. Everything else (Følner sequences and
their existence, Lemma \ref{G:lem:density}, the two elementary lemmas, the upper bound
`T(A) ⊆ A + 2G`, `R(A) ≠ ∅`, and Proposition \ref{G:prop:strict}) is proved unconditionally.

## Definitions

* `IsFolner Φ`: `Φ_N` finite nonempty with `|Φ_N ∩ (g + Φ_N)| / |Φ_N| → 1` for every `g`.
* `udensAlong Φ A = limsup_N |A ∩ Φ_N| / |Φ_N|`, and `ubd A = sup_Φ udensAlong Φ A` over all
  Følner sequences `Φ` (the paper's definition of `d*`).
* `twoG G = 2G = {g + g}`, `coset2 r = r + 2G`, `addTwoG S = S + 2G`.
* `RestrSumsetIn B t A`: `B ⊕ B + t ⊆ A`, where `B ⊕ B = {b + b' : b ≠ b'}`.
* `admissible A = T(A)`, `posCosets A = R(A) = {r : d*(A ∩ (r + 2G)) > 0}`.
* `Suffices T`, `MeetsAllCosets T`, `IsTransversal T`, `IsUnionOfCosets U`.

## Main results

* `exists_folner`: every countable abelian group has a Følner sequence.
* `tendsto_relDens_coset`, `ubd_coset` — Lemma \ref{G:lem:density}(i): for `[G : H] = ℓ < ∞`,
  `|(r + H) ∩ Φ_N| / |Φ_N| → 1/ℓ` along every Følner sequence, and `d*(r + H) = 1/ℓ`;
  `ubd_union_le` — Lemma \ref{G:lem:density}(ii); `ubd_pos_iff`.
* `lem_pigeon`, `lem_pigeon_mem`, `lem_pigeon_coset` — Lemma \ref{G:lem:pigeon};
  `lem_move` — Lemma \ref{G:lem:move}.
* `thm_translates` — Theorem \ref{G:thm:translates}, all four parts, conditional on
  `CharamarasMountakisCor113`; the parts are also stated separately:
  `thm_translates_union` (a), `posCosets_subset_admissible`, `admissible_subset_addTwoG`,
  `posCosets_nonempty`, `exists_coset_subset_admissible` (b), `thm_translates_realise`,
  `thm_translates_family` (c), `suffices_iff`, `minimal_suffices_iff`,
  `IsTransversal.ncard_eq` (d). Parts (a), the upper bound in (b), `R(A) ≠ ∅` and the
  cardinality of transversals do not use the hypothesis.
* `prop_strict_i`, `prop_strict_ii` — Proposition \ref{G:prop:strict} (unconditional).

## Conventions

* The group is any `AddCommGroup` with `[Countable G]` and `(twoG G).FiniteIndex`; the results
  that use Charamaras–Mountakis also assume `[Infinite G]`, as in the paper (the quoted theorem is
  about infinite groups, and it is false for finite ones).
* "`T` meets every coset of `2G`" is `MeetsAllCosets T`; a transversal meets every coset in
  exactly one point; minimality is Mathlib's `Minimal Suffices T`.
* In Proposition \ref{G:prop:strict}, `ℕ = {1, 2, …}`: `A = 2ℤ ∪ {3^n : n ≥ 1}` and
  `X = {2^i + 2^j + 1 : 1 ≤ i < j}`.

## Remark on proofs

For `d*(X) = 0` in Proposition \ref{G:prop:strict}(ii) we use a different argument from the paper:
`X` lies in at most `(k + 1)^2` residue classes modulo `2^k`, so `d*(X) ≤ (k + 1)^2 / 2^k` by
Lemma \ref{G:lem:density}. In Proposition \ref{G:prop:strict} the inclusion `2ℤ ⊆ T(A)` is proved
directly (with `B = 2ℤ`, `t = 0`), so no appeal to Theorem \ref{G:thm:CM} is needed there.
-/

open Filter Topology Finset
open scoped Classical

noncomputable section

namespace Kmrr25.Q516

/-! ## Følner sequences and upper Banach density -/

section Density

variable {G : Type*} [AddCommGroup G]

/-- A *Følner sequence* in the abelian group `G`: a sequence `Φ_N` of finite nonempty subsets
of `G` such that `|Φ_N ∩ (g + Φ_N)| / |Φ_N| → 1` for every `g ∈ G`. -/
def IsFolner (Φ : ℕ → Finset G) : Prop :=
  (∀ N, (Φ N).Nonempty) ∧
    ∀ g : G, Tendsto (fun N => (#(Φ N ∩ (Φ N).image (g + ·)) : ℝ) / #(Φ N)) atTop (𝓝 1)

/-- The relative density `|A ∩ F| / |F|`. -/
def relDens {α : Type*} (F : Finset α) (A : Set α) : ℝ := (#(F.filter (· ∈ A)) : ℝ) / #F

/-- The upper density along `Φ`: `d̄_Φ(A) = limsup_N |A ∩ Φ_N| / |Φ_N|`. -/
def udensAlong (Φ : ℕ → Finset G) (A : Set G) : ℝ := limsup (fun N => relDens (Φ N) A) atTop

/-- The upper Banach density `d*(A) = sup_Φ d̄_Φ(A)`, the supremum over all Følner sequences
`Φ` in `G`. -/
def ubd (A : Set G) : ℝ := ⨆ Φ : {Φ : ℕ → Finset G // IsFolner Φ}, udensAlong Φ.1 A

lemma relDens_nonneg {α : Type*} (F : Finset α) (A : Set α) : 0 ≤ relDens F A := by
  unfold relDens; positivity

lemma relDens_le_one {α : Type*} (F : Finset α) (A : Set α) : relDens F A ≤ 1 := by
  unfold relDens
  rcases Nat.eq_zero_or_pos #F with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_filter_le _ _

lemma relDens_mono {α : Type*} (F : Finset α) {A B : Set α} (h : A ⊆ B) : relDens F A ≤ relDens F B := by
  unfold relDens
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [Nat.cast_le]
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

lemma relDens_union_le {α : Type*} (F : Finset α) (A B : Set α) :
    relDens F (A ∪ B) ≤ relDens F A + relDens F B := by
  unfold relDens
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Nat.cast_add, Nat.cast_le]
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Set.mem_union, Finset.mem_union] at hx ⊢
  tauto

omit [AddCommGroup G] in
lemma isBoundedUnder_relDens (Φ : ℕ → Finset G) (A : Set G) :
    IsBoundedUnder (· ≤ ·) atTop (fun N => relDens (Φ N) A) :=
  isBoundedUnder_of_eventually_le (a := 1) (Eventually.of_forall fun _ => relDens_le_one _ _)

omit [AddCommGroup G] in
lemma isCoboundedUnder_relDens (Φ : ℕ → Finset G) (A : Set G) :
    IsCoboundedUnder (· ≤ ·) atTop (fun N => relDens (Φ N) A) :=
  isCoboundedUnder_le_of_le atTop (x := 0) fun _ => relDens_nonneg _ _

omit [AddCommGroup G] in
lemma udensAlong_nonneg (Φ : ℕ → Finset G) (A : Set G) : 0 ≤ udensAlong Φ A :=
  le_limsup_of_le (isBoundedUnder_relDens Φ A) fun c hc => by
    obtain ⟨N, hN⟩ := hc.exists
    exact (relDens_nonneg _ _).trans hN

omit [AddCommGroup G] in
lemma udensAlong_le_one (Φ : ℕ → Finset G) (A : Set G) : udensAlong Φ A ≤ 1 :=
  limsup_le_of_le (isCoboundedUnder_relDens Φ A) (Eventually.of_forall fun _ => relDens_le_one _ _)

omit [AddCommGroup G] in
lemma udensAlong_le_of_eventually {Φ : ℕ → Finset G} {A : Set G} {c : ℝ}
    (h : ∀ᶠ N in atTop, relDens (Φ N) A ≤ c) : udensAlong Φ A ≤ c :=
  limsup_le_of_le (isCoboundedUnder_relDens Φ A) h

omit [AddCommGroup G] in
lemma eventually_relDens_lt (Φ : ℕ → Finset G) (A : Set G) {c : ℝ} (hc : udensAlong Φ A < c) :
    ∀ᶠ N in atTop, relDens (Φ N) A < c :=
  eventually_lt_of_limsup_lt hc (isBoundedUnder_relDens Φ A)

omit [AddCommGroup G] in
lemma udensAlong_mono (Φ : ℕ → Finset G) {A B : Set G} (h : A ⊆ B) :
    udensAlong Φ A ≤ udensAlong Φ B :=
  limsup_le_limsup (Eventually.of_forall fun _ => relDens_mono _ h)
    (isCoboundedUnder_relDens Φ A) (isBoundedUnder_relDens Φ B)

omit [AddCommGroup G] in
lemma udensAlong_union_le (Φ : ℕ → Finset G) (A B : Set G) :
    udensAlong Φ (A ∪ B) ≤ udensAlong Φ A + udensAlong Φ B := by
  refine le_of_forall_pos_le_add fun ε hε => udensAlong_le_of_eventually ?_
  filter_upwards [eventually_relDens_lt Φ A (show udensAlong Φ A < udensAlong Φ A + ε / 2 by
    linarith), eventually_relDens_lt Φ B (show udensAlong Φ B < udensAlong Φ B + ε / 2 by
    linarith)] with N hA hB
  linarith [relDens_union_le (Φ N) A B]

lemma bddAbove_udensAlong (A : Set G) :
    BddAbove (Set.range fun Φ : {Φ : ℕ → Finset G // IsFolner Φ} => udensAlong Φ.1 A) :=
  ⟨1, by rintro _ ⟨Φ, rfl⟩; exact udensAlong_le_one _ _⟩

lemma ubd_nonneg (A : Set G) : 0 ≤ ubd A :=
  Real.iSup_nonneg fun _ => udensAlong_nonneg _ _

lemma udensAlong_le_ubd {Φ : ℕ → Finset G} (hΦ : IsFolner Φ) (A : Set G) :
    udensAlong Φ A ≤ ubd A :=
  le_ciSup (bddAbove_udensAlong A) ⟨Φ, hΦ⟩

/-- `d*(A) > 0` if and only if `d̄_Φ(A) > 0` for some Følner sequence `Φ`. -/
theorem ubd_pos_iff (A : Set G) : 0 < ubd A ↔ ∃ Φ, IsFolner Φ ∧ 0 < udensAlong Φ A := by
  constructor
  · intro h
    by_cases hne : Nonempty {Φ : ℕ → Finset G // IsFolner Φ}
    · obtain ⟨Φ, hΦ⟩ := (lt_ciSup_iff (bddAbove_udensAlong A)).mp h
      exact ⟨Φ.1, Φ.2, hΦ⟩
    · rw [not_nonempty_iff] at hne
      simp [ubd, Real.iSup_of_isEmpty] at h
  · rintro ⟨Φ, hΦ, h⟩
    exact h.trans_le (udensAlong_le_ubd hΦ A)

lemma ubd_le_of_forall {A : Set G} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ Φ, IsFolner Φ → udensAlong Φ A ≤ c) : ubd A ≤ c := by
  by_cases hne : Nonempty {Φ : ℕ → Finset G // IsFolner Φ}
  · exact ciSup_le fun Φ => h Φ.1 Φ.2
  · rw [not_nonempty_iff] at hne
    simp only [ubd, Real.iSup_of_isEmpty]
    exact hc

lemma ubd_mono {A B : Set G} (h : A ⊆ B) : ubd A ≤ ubd B :=
  ubd_le_of_forall (ubd_nonneg B) fun Φ hΦ =>
    (udensAlong_mono Φ h).trans (udensAlong_le_ubd hΦ B)

/-- Paper, Lemma \ref{G:lem:density}(ii): `d*(X ∪ Y) ≤ d*(X) + d*(Y)`. -/
theorem ubd_union_le (X Y : Set G) : ubd (X ∪ Y) ≤ ubd X + ubd Y :=
  ubd_le_of_forall (add_nonneg (ubd_nonneg X) (ubd_nonneg Y)) fun Φ hΦ =>
    (udensAlong_union_le Φ X Y).trans
      (add_le_add (udensAlong_le_ubd hΦ X) (udensAlong_le_ubd hΦ Y))

/-- Finite subadditivity of `d*`. -/
theorem ubd_biUnion_le {ι : Type*} (s : Finset ι) (X : ι → Set G) :
    ubd (⋃ i ∈ s, X i) ≤ ∑ i ∈ s, ubd (X i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Finset.sum_empty]
    exact ubd_le_of_forall le_rfl fun Φ _ => udensAlong_le_of_eventually
      (Eventually.of_forall fun _ => by simp [relDens])
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.set_biUnion_insert]
    exact (ubd_union_le _ _).trans (add_le_add le_rfl ih)

end Density

/-! ## Existence of Følner sequences in countable abelian groups -/

section Existence

variable {G : Type*} [AddCommGroup G]

/-- The "box" `{∑_{i < n} a_i s_i : 0 ≤ a_i ≤ M}`. -/
def box (s : ℕ → G) (n M : ℕ) : Finset G :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (M + 1)).image
    fun a => ∑ i : Fin n, a i • s (i : ℕ)

lemma box_nonempty (s : ℕ → G) (n M : ℕ) : (box s n M).Nonempty :=
  ⟨0, Finset.mem_image.mpr ⟨fun _ => 0, by simp, by simp⟩⟩

lemma box_card_le (s : ℕ → G) (n M : ℕ) : #(box s n M) ≤ (M + 1) ^ n := by
  unfold box
  refine Finset.card_image_le.trans ?_
  simp

lemma box_mono (s : ℕ → G) (n M : ℕ) : box s n M ⊆ box s n (M + 1) := by
  intro x hx
  simp only [box, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_range] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, fun i => by have := ha i; omega, rfl⟩

lemma box_add_subset (s : ℕ → G) (n M : ℕ) (j : Fin n) :
    (box s n M).image (s j + ·) ⊆ box s n (M + 1) := by
  intro x hx
  simp only [box, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_range] at hx ⊢
  obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hx
  refine ⟨a + Pi.single j 1, fun i => ?_, ?_⟩
  · have := ha i
    simp only [Pi.add_apply]
    by_cases hij : i = j
    · subst hij; simp; omega
    · rw [Pi.single_eq_of_ne hij]; omega
  · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; rw [Pi.single_eq_of_ne hij, zero_smul]
    · intro h; exact absurd (Finset.mem_univ j) h

/-- Polynomial growth of boxes: for every `δ > 0` some box satisfies
`|box (M + 1)| ≤ (1 + δ) |box M|`. -/
lemma exists_box_good (s : ℕ → G) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M, (#(box s n (M + 1)) : ℝ) ≤ (1 + δ) * #(box s n M) := by
  by_contra hcon
  push Not at hcon
  have hgrow : ∀ M, (1 + δ) ^ M ≤ (#(box s n M) : ℝ) := by
    intro M
    induction M with
    | zero =>
      simp only [pow_zero, Nat.one_le_cast]
      exact (box_nonempty s n 0).card_pos
    | succ M ih =>
      rw [pow_succ]
      have := hcon M
      nlinarith
  have hbound : ∀ M : ℕ, (1 + δ) ^ M ≤ ((M : ℝ) + 1) ^ n := fun M =>
    (hgrow M).trans (by exact_mod_cast box_card_le s n M)
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt n (show 1 < 1 + δ by linarith)).comp
    (tendsto_add_atTop_nat 1)
  obtain ⟨M, hM⟩ := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (1 + δ) by positivity))).exists
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hM
  have hpos : (0 : ℝ) < (1 + δ) ^ (M + 1) := by positivity
  rw [div_lt_iff₀ hpos, pow_succ, one_div, ← mul_assoc, mul_comm _ ((1 + δ) ^ M), mul_assoc,
    inv_mul_cancel₀ (by positivity), mul_one] at hM
  linarith [hbound M]

/-- In a good box, every generator `s_j` (`j < n`) moves the box by a proportion `≤ δ`. -/
lemma box_folner_bound (s : ℕ → G) (n M : ℕ) {δ : ℝ}
    (hM : (#(box s n (M + 1)) : ℝ) ≤ (1 + δ) * #(box s n M)) (j : Fin n) :
    (1 - δ) * #(box s n M) ≤ #(box s n M ∩ (box s n M).image (s j + ·)) := by
  set B := box s n M
  have hinj : #(B.image (s j + ·)) = #B := Finset.card_image_of_injective _ (add_right_injective _)
  have hU : #(B ∪ B.image (s j + ·)) ≤ #(box s n (M + 1)) :=
    Finset.card_le_card (Finset.union_subset (box_mono s n M) (box_add_subset s n M j))
  have h1 := Finset.card_union_add_card_inter B (B.image (s j + ·))
  rw [hinj] at h1
  have h2 : (#(B ∪ B.image (s j + ·)) : ℝ) + #(B ∩ B.image (s j + ·)) = #B + #B := by
    exact_mod_cast h1
  have h3 : (#(B ∪ B.image (s j + ·)) : ℝ) ≤ #(box s n (M + 1)) := by exact_mod_cast hU
  linarith

/-- Every countable abelian group has a Følner sequence. -/
theorem exists_folner [Countable G] : ∃ Φ : ℕ → Finset G, IsFolner Φ := by
  obtain ⟨e, he⟩ := exists_surjective_nat G
  have hM : ∀ N : ℕ, ∃ M, (#(box e N (M + 1)) : ℝ) ≤ (1 + 1 / ((N : ℝ) + 1)) * #(box e N M) :=
    fun N => exists_box_good e N (by positivity)
  choose M hM using hM
  refine ⟨fun N => box e N (M N), fun N => box_nonempty _ _ _, fun g => ?_⟩
  obtain ⟨j, rfl⟩ := he g
  have hlow : Tendsto (fun N : ℕ => 1 - 1 / ((N : ℝ) + 1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop j] with N hN
    have hpos : (0 : ℝ) < #(box e N (M N)) := by exact_mod_cast (box_nonempty _ _ _).card_pos
    rw [le_div_iff₀ hpos]
    exact box_folner_bound e N (M N) (hM N) ⟨j, hN⟩
  · refine Eventually.of_forall fun N => ?_
    have hpos : (0 : ℝ) < #(box e N (M N)) := by exact_mod_cast (box_nonempty _ _ _).card_pos
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left

end Existence

/-! ## Lemma \ref{G:lem:density}(i): cosets of a subgroup of finite index -/

section Cosets

variable {G : Type*} [AddCommGroup G]

omit [AddCommGroup G] in
/-- For finite sets `P, Q` of equal size, `|P ∩ C| ≤ |Q ∩ C| + (|P| - |P ∩ Q|)`. -/
lemma card_filter_le_of_card_eq {P Q : Finset G} (C : Set G) :
    #(P.filter (· ∈ C)) ≤ #(Q.filter (· ∈ C)) + (#P - #(P ∩ Q)) := by
  have h1 : P.filter (· ∈ C) ⊆ Q.filter (· ∈ C) ∪ (P \ Q) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff] at hx ⊢
    by_cases hq : x ∈ Q
    · exact Or.inl ⟨hq, hx.2⟩
    · exact Or.inr ⟨hx.1, hq⟩
  have h2 : #(P \ Q) = #P - #(P ∩ Q) := by
    rw [← Finset.card_sdiff_add_card_inter P Q]; omega
  calc _ ≤ #(Q.filter (· ∈ C) ∪ (P \ Q)) := Finset.card_le_card h1
    _ ≤ #(Q.filter (· ∈ C)) + #(P \ Q) := Finset.card_union_le _ _
    _ = _ := by rw [h2]

/-- Translating a set changes its relative density in a Følner set by `o(1)`:
`|d_{Φ_N}(x + C) - d_{Φ_N}(C)| ≤ 1 - |Φ_N ∩ (-x + Φ_N)| / |Φ_N|`. -/
lemma abs_relDens_translate_sub_le (F : Finset G) (hF : F.Nonempty) (C : Set G) (x : G) :
    |relDens F {g | g - x ∈ C} - relDens F C| ≤
      1 - (#(F ∩ F.image ((-x) + ·)) : ℝ) / #F := by
  set Ψ := F.image ((-x) + ·)
  have hΨ : #Ψ = #F := Finset.card_image_of_injective _ (add_right_injective _)
  -- `|F ∩ (x + C)| = |Ψ ∩ C|`
  have hshift : #(F.filter (· ∈ {g | g - x ∈ C})) = #(Ψ.filter (· ∈ C)) := by
    refine Finset.card_bij (fun g _ => -x + g) ?_ ?_ ?_
    · intro g hg
      simp only [Finset.mem_filter, Set.mem_ofPred_eq] at hg
      simp only [Ψ, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨g, hg.1, rfl⟩, by rw [neg_add_eq_sub]; exact hg.2⟩
    · intro a _ b _ h; exact add_left_cancel h
    · intro y hy
      simp only [Ψ, Finset.mem_filter, Finset.mem_image] at hy
      obtain ⟨⟨g, hg, rfl⟩, hC⟩ := hy
      refine ⟨g, ?_, rfl⟩
      simp only [Finset.mem_filter, Set.mem_ofPred_eq]
      exact ⟨hg, by rw [← neg_add_eq_sub]; exact hC⟩
  have hpos : (0 : ℝ) < #F := by exact_mod_cast hF.card_pos
  have hint : #(F ∩ Ψ) ≤ #F := Finset.card_le_card Finset.inter_subset_left
  have hint' : #(Ψ ∩ F) = #(F ∩ Ψ) := by rw [Finset.inter_comm]
  have a1 := card_filter_le_of_card_eq (P := Ψ) (Q := F) C
  have a2 := card_filter_le_of_card_eq (P := F) (Q := Ψ) C
  rw [hΨ, hint'] at a1
  have b1 : (#(Ψ.filter (· ∈ C)) : ℝ) ≤ #(F.filter (· ∈ C)) + (#F - #(F ∩ Ψ)) := by
    have := Nat.cast_le (α := ℝ) |>.mpr a1
    push_cast [Nat.cast_sub hint] at this
    linarith
  have b2 : (#(F.filter (· ∈ C)) : ℝ) ≤ #(Ψ.filter (· ∈ C)) + (#F - #(F ∩ Ψ)) := by
    have := Nat.cast_le (α := ℝ) |>.mpr a2
    push_cast [Nat.cast_sub hint] at this
    linarith
  unfold relDens
  rw [hshift, ← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, sub_mul, one_mul,
    div_mul_cancel₀ _ hpos.ne', abs_le]
  constructor <;> linarith

lemma tendsto_relDens_translate_sub {Φ : ℕ → Finset G} (hΦ : IsFolner Φ) (C : Set G) (x : G) :
    Tendsto (fun N => relDens (Φ N) {g | g - x ∈ C} - relDens (Φ N) C) atTop (𝓝 0) := by
  have h := hΦ.2 (-x)
  have h0 : Tendsto (fun N => 1 - (#(Φ N ∩ (Φ N).image ((-x) + ·)) : ℝ) / #(Φ N)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  refine squeeze_zero_norm (fun N => ?_) h0
  rw [Real.norm_eq_abs]
  exact abs_relDens_translate_sub_le _ (hΦ.1 N) C x

/-- Paper, Lemma \ref{G:lem:density}(i), first part: if `H ≤ G` has finite index `ℓ`, then for
every Følner sequence `Φ` and every `r ∈ G`, `|(r + H) ∩ Φ_N| / |Φ_N| → 1/ℓ`. -/
theorem tendsto_relDens_coset (H : AddSubgroup G) [H.FiniteIndex] {Φ : ℕ → Finset G}
    (hΦ : IsFolner Φ) (r : G) :
    Tendsto (fun N => relDens (Φ N) {g | g - r ∈ H}) atTop (𝓝 (1 / (H.index : ℝ))) := by
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  set Q := G ⧸ H
  obtain ⟨fib, hfib⟩ : ∃ fib : Q → Set G, fib = fun q => {g : G | (g : Q) = q} := ⟨_, rfl⟩
  have hcoset : {g | g - r ∈ H} = fib (r : Q) := by
    ext g
    simp only [hfib, Set.mem_ofPred_eq]
    rw [QuotientAddGroup.eq, neg_add_eq_sub, ← neg_sub, neg_mem_iff]
  rw [hcoset]
  -- the cosets are translates of each other
  have hx : ∀ q : Q, ∃ x : G, fib q = {g | g - x ∈ fib (r : Q)} := by
    intro q
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (q - (r : Q))
    refine ⟨x, ?_⟩
    ext g
    simp only [hfib, Set.mem_ofPred_eq, QuotientAddGroup.mk_sub, hx]
    constructor
    · intro h; rw [h]; abel
    · intro h; rw [← sub_eq_zero] at h ⊢; rw [← h]; abel
  choose x hx using hx
  -- the densities of the cosets add up to `1`
  have hsum : ∀ N, ∑ q : Q, relDens (Φ N) (fib q) = 1 := by
    intro N
    have hpos : (0 : ℝ) < #(Φ N) := by exact_mod_cast (hΦ.1 N).card_pos
    unfold relDens
    rw [← Finset.sum_div, div_eq_one_iff_eq hpos.ne']
    have := Finset.card_eq_sum_card_fiberwise (f := fun g : G => (g : Q)) (s := Φ N)
      (t := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    rw [this]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    refine congrArg (fun s : Finset G => ((#s : ℕ) : ℝ)) (Finset.ext fun g => ?_)
    simp only [Finset.mem_filter, hfib, Set.mem_ofPred_eq]
  have hdiff : ∀ q : Q, Tendsto (fun N => relDens (Φ N) (fib q) - relDens (Φ N) (fib (r : Q)))
      atTop (𝓝 0) := by
    intro q
    rw [hx q]
    exact tendsto_relDens_translate_sub hΦ _ _
  have hℓ : (Fintype.card Q : ℝ) = H.index := by
    rw [AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hℓpos : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  have key : ∀ N, relDens (Φ N) (fib (r : Q)) =
      (1 - ∑ q : Q, (relDens (Φ N) (fib q) - relDens (Φ N) (fib (r : Q)))) / Fintype.card Q := by
    intro N
    rw [Finset.sum_sub_distrib, hsum N, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  rw [← hℓ]
  have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_finsetSum (Finset.univ : Finset Q) fun q _ => hdiff q)).div_const
    (Fintype.card Q : ℝ)
  rw [Finset.sum_const_zero, sub_zero] at this
  exact this.congr fun N => (key N).symm

/-- Paper, Lemma \ref{G:lem:density}(i), second part: in a countable abelian group,
`d*(r + H) = 1/[G : H]`. -/
theorem ubd_coset [Countable G] (H : AddSubgroup G) [H.FiniteIndex] (r : G) :
    ubd {g | g - r ∈ H} = 1 / (H.index : ℝ) := by
  obtain ⟨Φ₀, hΦ₀⟩ := exists_folner (G := G)
  have : Nonempty {Φ : ℕ → Finset G // IsFolner Φ} := ⟨⟨Φ₀, hΦ₀⟩⟩
  have h : ∀ Φ : {Φ : ℕ → Finset G // IsFolner Φ}, udensAlong Φ.1 {g | g - r ∈ H} =
      1 / (H.index : ℝ) := fun Φ => (tendsto_relDens_coset H Φ.2 r).limsup_eq
  simp only [ubd, h, ciSup_const]

lemma ubd_coset_pos [Countable G] (H : AddSubgroup G) [H.FiniteIndex] (r : G) :
    0 < ubd {g | g - r ∈ H} := by
  rw [ubd_coset]
  have : 0 < H.index := AddSubgroup.FiniteIndex.index_ne_zero.bot_lt
  positivity

end Cosets

/-! ## Admissible translates -/

section Translates

universe u

/-- The subgroup `2G = {g + g : g ∈ G}`. -/
def twoG (G : Type*) [AddCommGroup G] : AddSubgroup G where
  carrier := {x | ∃ g, g + g = x}
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by abel⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, by abel⟩

variable {G : Type*} [AddCommGroup G]

lemma mem_twoG {x : G} : x ∈ twoG G ↔ ∃ g, g + g = x := Iff.rfl

/-- `B ⊕ B + t ⊆ A`, where `B ⊕ B = {b + b' : b, b' ∈ B, b ≠ b'}`. -/
def RestrSumsetIn (B : Set G) (t : G) (A : Set G) : Prop :=
  ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → b + b' + t ∈ A

/-- The set of admissible translates
`T(A) = {t ∈ G : B ⊕ B + t ⊆ A for some infinite B ⊆ G}`. -/
def admissible (A : Set G) : Set G := {t | ∃ B : Set G, B.Infinite ∧ RestrSumsetIn B t A}

/-- The coset `r + 2G`. -/
def coset2 (r : G) : Set G := {g | g - r ∈ twoG G}

/-- `R(A) = {r ∈ G : d*(A ∩ (r + 2G)) > 0}`. -/
def posCosets (A : Set G) : Set G := {r | 0 < ubd (A ∩ coset2 r)}

/-- `S + 2G`. -/
def addTwoG (S : Set G) : Set G := {x | ∃ s ∈ S, x - s ∈ twoG G}

/-- `U` is a union of cosets of `2G`: `U + 2G = U`. -/
def IsUnionOfCosets (U : Set G) : Prop := ∀ u ∈ U, ∀ h ∈ twoG G, u + h ∈ U

/-- A set `T ⊆ G` of translates *suffices* if `T(A) ∩ T ≠ ∅` for every `A ⊆ G` with
`d*(A) > 0`. -/
def Suffices (T : Set G) : Prop := ∀ A : Set G, 0 < ubd A → (admissible A ∩ T).Nonempty

/-- `T` meets every coset of `2G`. -/
def MeetsAllCosets (T : Set G) : Prop := ∀ r : G, ∃ t ∈ T, t - r ∈ twoG G

/-- `T` is a transversal of `2G` in `G`: it meets every coset of `2G` in exactly one point. -/
def IsTransversal (T : Set G) : Prop := ∀ r : G, ∃! t, t ∈ T ∧ t - r ∈ twoG G

/-- Charamaras–Mountakis, Corollary 1.13 (*Finding product sets in some classes of amenable
groups*), as quoted in the paper (Theorem \ref{G:thm:CM}): let `Γ` be a countably infinite abelian
group such that `2Γ` has finite index, and let `A ⊆ Γ` have positive upper Banach density. Then there
are an infinite `B ⊆ A` and `t ∈ Γ` with `B ⊕ B ⊆ A - t`.

This is a hypothesis of the results below that need it; it is not proved in this file. -/
def CharamarasMountakisCor113 : Prop :=
  ∀ (Γ : Type u) [AddCommGroup Γ] [Countable Γ] [Infinite Γ], (twoG Γ).FiniteIndex →
    ∀ A : Set Γ, 0 < ubd A → ∃ B ⊆ A, B.Infinite ∧ ∃ t : Γ, RestrSumsetIn B t A

lemma mem_coset2_self (r : G) : r ∈ coset2 r := by simp [coset2]

lemma coset2_comm {r s : G} : s ∈ coset2 r ↔ r ∈ coset2 s := by
  simp only [coset2, Set.mem_ofPred_eq]
  rw [← neg_mem_iff, neg_sub]

lemma IsUnionOfCosets.coset2_subset {U : Set G} (hU : IsUnionOfCosets U) {u : G} (hu : u ∈ U) :
    coset2 u ⊆ U := fun g hg => by
  have := hU u hu _ hg
  rwa [add_sub_cancel] at this

lemma IsUnionOfCosets.addTwoG_subset {U : Set G} (hU : IsUnionOfCosets U) : addTwoG U ⊆ U := by
  rintro x ⟨s, hs, hx⟩
  have := hU s hs _ hx
  rwa [add_sub_cancel] at this

lemma coset2_isUnionOfCosets (r : G) : IsUnionOfCosets (coset2 r) := by
  intro u hu h hh
  simp only [coset2, Set.mem_ofPred_eq] at hu ⊢
  have : u + h - r = (u - r) + h := by abel
  rw [this]
  exact add_mem hu hh

/-- Paper, Lemma \ref{G:lem:pigeon}, first part: if `[G : 2G] < ∞` and `B` is infinite, then
`(B ⊕ B) ∩ 2G ≠ ∅`. -/
theorem lem_pigeon [(twoG G).FiniteIndex] {B : Set G} (hB : B.Infinite) :
    ∃ b ∈ B, ∃ b' ∈ B, b ≠ b' ∧ b + b' ∈ twoG G := by
  obtain ⟨b, hb, b', hb', hne, he⟩ := hB.exists_ne_map_eq_of_mapsTo
    (f := fun g : G => (g : G ⧸ twoG G)) (Set.mapsTo_univ _ _) Set.finite_univ
  refine ⟨b, hb, b', hb', hne, ?_⟩
  have h1 : -b + b' ∈ twoG G := QuotientAddGroup.eq.mp he
  have h2 : b + b ∈ twoG G := ⟨b, rfl⟩
  have : b + b' = (-b + b') + (b + b) := by abel
  rw [this]
  exact add_mem h1 h2

/-- Paper, Lemma \ref{G:lem:pigeon}, second part: if `B ⊕ B + t ⊆ A` with `B` infinite, then
`t ∈ A + 2G`. -/
theorem lem_pigeon_mem [(twoG G).FiniteIndex] {A B : Set G} {t : G} (hB : B.Infinite)
    (h : RestrSumsetIn B t A) : t ∈ addTwoG A := by
  obtain ⟨b, hb, b', hb', hne, h2⟩ := lem_pigeon hB
  refine ⟨b + b' + t, h b hb b' hb' hne, ?_⟩
  have : t - (b + b' + t) = -(b + b') := by abel
  rw [this]
  exact neg_mem h2

/-- Paper, Lemma \ref{G:lem:pigeon}, third part: if `B ⊕ B + t ⊆ r + 2G` with `B` infinite, then
`t ∈ r + 2G`. -/
theorem lem_pigeon_coset [(twoG G).FiniteIndex] {B : Set G} {t r : G} (hB : B.Infinite)
    (h : RestrSumsetIn B t (coset2 r)) : t ∈ coset2 r := by
  obtain ⟨b, hb, b', hb', hne, h2⟩ := lem_pigeon hB
  have h1 := h b hb b' hb' hne
  simp only [coset2, Set.mem_ofPred_eq] at h1 ⊢
  have : t - r = (b + b' + t - r) - (b + b') := by abel
  rw [this]
  exact sub_mem h1 h2

/-- Paper, Lemma \ref{G:lem:move}: `(B - s) ⊕ (B - s) = B ⊕ B - 2s`; consequently
`T(A) + 2G = T(A)`. -/
theorem lem_move (A : Set G) : IsUnionOfCosets (admissible A) := by
  rintro t ⟨B, hB, hBt⟩ _ ⟨s, rfl⟩
  refine ⟨(fun b => b - s) '' B, hB.image (fun x _ y _ h => sub_left_injective h), ?_⟩
  rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩ hne
  have hne' : b ≠ b' := fun h => hne (by rw [h])
  have : b - s + (b' - s) + (t + (s + s)) = b + b' + t := by abel
  rw [this]
  exact hBt b hb b' hb' hne'

/-- Paper, Theorem \ref{G:thm:translates}\ref{G:it:union}: `T(A)` is a union of cosets of `2G`. -/
theorem thm_translates_union (A : Set G) : IsUnionOfCosets (admissible A) := lem_move A

/-- Paper, Theorem \ref{G:thm:translates}\ref{G:it:sandwich}, upper bound: `T(A) ⊆ A + 2G`. -/
theorem admissible_subset_addTwoG [(twoG G).FiniteIndex] (A : Set G) :
    admissible A ⊆ addTwoG A := by
  rintro t ⟨B, hB, hBt⟩
  exact lem_pigeon_mem hB hBt

/-- Paper, Theorem \ref{G:thm:translates}\ref{G:it:sandwich}, lower bound, **conditional on
Charamaras–Mountakis** (`CharamarasMountakisCor113`): `R(A) ⊆ T(A)`. -/
theorem posCosets_subset_admissible {G : Type u} [AddCommGroup G] [Countable G] [Infinite G]
    [(twoG G).FiniteIndex] (hCM : CharamarasMountakisCor113.{u}) (A : Set G) :
    posCosets A ⊆ admissible A := by
  intro r hr
  obtain ⟨B, hBA, hB, t, hBt⟩ := hCM G inferInstance (A ∩ coset2 r) hr
  have ht : t ∈ admissible A := ⟨B, hB, fun b hb b' hb' hne => (hBt b hb b' hb' hne).1⟩
  have htr : t ∈ coset2 r := lem_pigeon_coset hB fun b hb b' hb' hne => (hBt b hb b' hb' hne).2
  have := lem_move A t ht (r - t) (by
    rw [coset2_comm] at htr
    exact htr)
  rwa [add_sub_cancel] at this

/-- Paper, Theorem \ref{G:thm:translates}\ref{G:it:sandwich}, last part: if `d*(A) > 0`, then
`R(A) ≠ ∅`. -/
theorem posCosets_nonempty [(twoG G).FiniteIndex] {A : Set G} (hA : 0 < ubd A) :
    (posCosets A).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hcon
  have : Fintype (G ⧸ twoG G) := Fintype.ofFinite _
  have hsub : A ⊆ ⋃ q ∈ (Finset.univ : Finset (G ⧸ twoG G)), A ∩ coset2 q.out := by
    intro a ha
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    refine ⟨(a : G ⧸ twoG G), ha, ?_⟩
    simp only [coset2, Set.mem_ofPred_eq]
    have h := QuotientAddGroup.out_eq' (a : G ⧸ twoG G)
    have := QuotientAddGroup.eq.mp h
    rwa [neg_add_eq_sub] at this
  have h1 := (ubd_mono hsub).trans (ubd_biUnion_le _ _)
  have h2 : ∑ q ∈ (Finset.univ : Finset (G ⧸ twoG G)), ubd (A ∩ coset2 q.out) ≤ 0 :=
    Finset.sum_nonpos fun q _ => not_lt.mp (hcon q.out)
  linarith

/-- Paper, Theorem \ref{G:thm:translates}\ref{G:it:sandwich}, **conditional on
Charamaras–Mountakis**: if `d*(A) > 0`, then `T(A)` contains a full coset of `2G`. -/
theorem exists_coset_subset_admissible {G : Type u} [AddCommGroup G] [Countable G] [Infinite G]
    [(twoG G).FiniteIndex] (hCM : CharamarasMountakisCor113.{u}) {A : Set G} (hA : 0 < ubd A) :
    ∃ r, coset2 r ⊆ admissible A := by
  obtain ⟨r, hr⟩ := posCosets_nonempty hA
  exact ⟨r, (thm_translates_union A).coset2_subset (posCosets_subset_admissible hCM A hr)⟩

/-- Paper, Theorem \ref{G:thm:translates}\ref{G:it:realise}, first part, **conditional on
Charamaras–Mountakis**: for every nonempty union `U` of cosets of `2G`, `d*(U) > 0` and
`T(U) = U`. -/
theorem thm_translates_realise {G : Type u} [AddCommGroup G] [Countable G] [Infinite G]
    [(twoG G).FiniteIndex] (hCM : CharamarasMountakisCor113.{u}) {U : Set G}
    (hne : U.Nonempty) (hU : IsUnionOfCosets U) : 0 < ubd U ∧ admissible U = U := by
  obtain ⟨u, hu⟩ := hne
  refine ⟨(ubd_coset_pos (twoG G) u).trans_le (ubd_mono (hU.coset2_subset hu)), ?_⟩
  have hR : U ⊆ posCosets U := by
    intro v hv
    simp only [posCosets, Set.mem_ofPred_eq]
    rw [Set.inter_eq_right.mpr (hU.coset2_subset hv)]
    exact ubd_coset_pos (twoG G) v
  exact Set.Subset.antisymm ((admissible_subset_addTwoG U).trans hU.addTwoG_subset)
    (hR.trans (posCosets_subset_admissible hCM U))

/-- Paper, Theorem \ref{G:thm:translates}\ref{G:it:realise}, "consequently" part,
**conditional on Charamaras–Mountakis**: the family `{T(A) : A ⊆ G, d*(A) > 0}` is exactly the
family of nonempty unions of cosets of `2G`. -/
theorem thm_translates_family {G : Type u} [AddCommGroup G] [Countable G] [Infinite G]
    [(twoG G).FiniteIndex] (hCM : CharamarasMountakisCor113.{u}) (S : Set G) :
    (∃ A : Set G, 0 < ubd A ∧ admissible A = S) ↔ (S.Nonempty ∧ IsUnionOfCosets S) := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨r, hr⟩ := exists_coset_subset_admissible hCM hA
    exact ⟨⟨r, hr (mem_coset2_self r)⟩, thm_translates_union A⟩
  · rintro ⟨hne, hS⟩
    exact ⟨S, (thm_translates_realise hCM hne hS).1, (thm_translates_realise hCM hne hS).2⟩

/-- Paper, Theorem \ref{G:thm:translates}\ref{G:it:suffice}, first part, **conditional on
Charamaras–Mountakis**: a set `T ⊆ G` suffices if and only if `T` meets every coset of `2G`. -/
theorem suffices_iff {G : Type u} [AddCommGroup G] [Countable G] [Infinite G]
    [(twoG G).FiniteIndex] (hCM : CharamarasMountakisCor113.{u}) (T : Set G) :
    Suffices T ↔ MeetsAllCosets T := by
  constructor
  · intro hT r
    by_contra hcon
    push Not at hcon
    obtain ⟨hpos, hadm⟩ := thm_translates_realise hCM ⟨r, mem_coset2_self r⟩
      (coset2_isUnionOfCosets r)
    obtain ⟨t, ht, htT⟩ := hT _ hpos
    rw [hadm] at ht
    exact hcon t htT ht
  · intro hT A hA
    obtain ⟨r, hr⟩ := exists_coset_subset_admissible hCM hA
    obtain ⟨t, htT, htr⟩ := hT r
    exact ⟨t, hr htr, htT⟩

lemma IsTransversal.meetsAllCosets {T : Set G} (hT : IsTransversal T) : MeetsAllCosets T :=
  fun r => by obtain ⟨t, ht, -⟩ := hT r; exact ⟨t, ht⟩

lemma IsTransversal.eq_of_mem {T : Set G} (hT : IsTransversal T) {t t' : G} (ht : t ∈ T)
    (ht' : t' ∈ T) (h : t' - t ∈ twoG G) : t' = t :=
  (hT t).unique ⟨ht', h⟩ ⟨ht, by simp⟩

/-- Paper, Theorem \ref{G:thm:translates}\ref{G:it:suffice}, second part, **conditional on
Charamaras–Mountakis**: the minimal sets that suffice are exactly the transversals of `2G`. -/
theorem minimal_suffices_iff {G : Type u} [AddCommGroup G] [Countable G] [Infinite G]
    [(twoG G).FiniteIndex] (hCM : CharamarasMountakisCor113.{u}) (T : Set G) :
    Minimal Suffices T ↔ IsTransversal T := by
  simp only [Minimal, suffices_iff hCM]
  constructor
  · rintro ⟨hT, hmin⟩ r
    obtain ⟨t, htT, htr⟩ := hT r
    refine ⟨t, ⟨htT, htr⟩, ?_⟩
    rintro t' ⟨ht'T, ht'r⟩
    by_contra hne
    -- removing `t'` leaves a set that still meets every coset
    have hT' : MeetsAllCosets (T \ {t'}) := by
      intro r'
      obtain ⟨s, hsT, hsr⟩ := hT r'
      by_cases hs : s = t'
      · refine ⟨t, ⟨htT, fun h => hne h.symm⟩, ?_⟩
        subst hs
        have : t - r' = (s - r') - (s - r) + (t - r) := by abel
        rw [this]
        exact add_mem (sub_mem hsr ht'r) htr
      · exact ⟨s, ⟨hsT, hs⟩, hsr⟩
    have := hmin hT' Set.sdiff_subset ht'T
    exact this.2 rfl
  · intro hT
    refine ⟨hT.meetsAllCosets, fun T' hT' hsub t ht => ?_⟩
    obtain ⟨t', ht'T', ht't⟩ := hT' t
    have := hT.eq_of_mem ht (hsub ht'T') ht't
    rwa [this] at ht'T'

/-- Paper, Theorem \ref{G:thm:translates}\ref{G:it:suffice}, last part: every transversal of `2G`
has exactly `[G : 2G]` elements. -/
theorem IsTransversal.ncard_eq [(twoG G).FiniteIndex] {T : Set G} (hT : IsTransversal T) :
    T.ncard = (twoG G).index := by
  rw [AddSubgroup.index_eq_card, ← Nat.card_coe_set_eq]
  refine Nat.card_eq_of_bijective (fun t : T => ((t : G) : G ⧸ twoG G)) ⟨?_, ?_⟩
  · rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
    have h1 := QuotientAddGroup.eq.mp h
    rw [neg_add_eq_sub] at h1
    exact Subtype.ext (hT.eq_of_mem ht ht' h1).symm
  · intro q
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨t, ⟨htT, htr⟩, -⟩ := hT r
    refine ⟨⟨t, htT⟩, ?_⟩
    simp only
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_add_eq_sub, neg_sub]
    exact htr

/-- A transversal of `2G` is finite (it has `[G : 2G] ≠ 0` elements). -/
lemma IsTransversal.finite [(twoG G).FiniteIndex] {T : Set G} (hT : IsTransversal T) :
    T.Finite :=
  Set.finite_of_ncard_ne_zero (by rw [hT.ncard_eq]; exact AddSubgroup.FiniteIndex.index_ne_zero)

/-- Paper, Theorem \ref{G:thm:translates} (all parts), **conditional on Charamaras–Mountakis**
(`CharamarasMountakisCor113`). Let `G` be a countably infinite abelian group with
`[G : 2G] < ∞`, and `R(A) = {r : d*(A ∩ (r + 2G)) > 0}`.
* (a) `T(A)` is a union of cosets of `2G`;
* (b) `R(A) ⊆ T(A) ⊆ A + 2G`; if `d*(A) > 0` then `R(A) ≠ ∅` and `T(A)` contains a coset of `2G`;
* (c) every nonempty union `U` of cosets has `d*(U) > 0` and `T(U) = U`; the sets `T(A)` with
  `d*(A) > 0` are exactly the nonempty unions of cosets of `2G`;
* (d) `T` suffices iff `T` meets every coset of `2G`; the minimal sufficient sets are exactly the
  transversals of `2G`, and every transversal has `[G : 2G]` elements. -/
theorem thm_translates {G : Type u} [AddCommGroup G] [Countable G] [Infinite G]
    [(twoG G).FiniteIndex] (hCM : CharamarasMountakisCor113.{u}) :
    (∀ A : Set G, IsUnionOfCosets (admissible A)) ∧
    (∀ A : Set G, posCosets A ⊆ admissible A ∧ admissible A ⊆ addTwoG A) ∧
    (∀ A : Set G, 0 < ubd A → (posCosets A).Nonempty ∧ ∃ r, coset2 r ⊆ admissible A) ∧
    (∀ U : Set G, U.Nonempty → IsUnionOfCosets U → 0 < ubd U ∧ admissible U = U) ∧
    (∀ S : Set G, (∃ A, 0 < ubd A ∧ admissible A = S) ↔ (S.Nonempty ∧ IsUnionOfCosets S)) ∧
    (∀ T : Set G, Suffices T ↔ MeetsAllCosets T) ∧
    (∀ T : Set G, Minimal Suffices T ↔ IsTransversal T) ∧
    (∀ T : Set G, IsTransversal T → T.ncard = (twoG G).index) :=
  ⟨thm_translates_union, fun A => ⟨posCosets_subset_admissible hCM A,
    admissible_subset_addTwoG A⟩, fun _ hA => ⟨posCosets_nonempty hA,
    exists_coset_subset_admissible hCM hA⟩, fun _ hne hU => thm_translates_realise hCM hne hU,
    thm_translates_family hCM, suffices_iff hCM, minimal_suffices_iff hCM,
    fun _ hT => hT.ncard_eq⟩

end Translates

/-! ## Proposition \ref{G:prop:strict}: both inclusions can be strict (`G = ℤ`) -/

section Strict

lemma mem_twoG_int {x : ℤ} : x ∈ twoG ℤ ↔ Even x :=
  ⟨fun ⟨g, h⟩ => ⟨g, h.symm⟩, fun ⟨g, h⟩ => ⟨g, h.symm⟩⟩

lemma twoG_int_eq : twoG ℤ = AddSubgroup.zmultiples 2 := by
  ext x
  rw [mem_twoG_int, Int.mem_zmultiples_iff, even_iff_two_dvd]

instance : (twoG ℤ).FiniteIndex := ⟨by rw [twoG_int_eq, Int.index_zmultiples]; norm_num⟩

instance (k : ℕ) : (AddSubgroup.zmultiples ((2 : ℤ) ^ k)).FiniteIndex :=
  ⟨by rw [Int.index_zmultiples]; positivity⟩

lemma mem_coset2_int {x r : ℤ} : x ∈ coset2 r ↔ Even (x - r) := mem_twoG_int

lemma infinite_evens : {x : ℤ | Even x}.Infinite := by
  have : {x : ℤ | Even x} = Set.range fun n : ℤ => n + n := by
    ext x; simp [Even, eq_comm]
  rw [this]
  exact Set.infinite_range_of_injective fun a b h => by
    have h' : a + a = b + b := h
    omega

/-- If `A` contains all even integers, then `2ℤ ⊆ T(A)` (take `B = 2ℤ`, `t = 0`). -/
lemma evens_subset_admissible {A : Set ℤ} (hA : {x : ℤ | Even x} ⊆ A) :
    {x : ℤ | Even x} ⊆ admissible A := by
  have h0 : (0 : ℤ) ∈ admissible A := by
    refine ⟨{x | Even x}, infinite_evens, fun b hb b' hb' _ => hA ?_⟩
    simp only [add_zero, Set.mem_ofPred_eq]
    exact Even.add hb hb'
  intro x hx
  have := thm_translates_union A 0 h0 x (mem_twoG_int.mpr hx)
  rwa [zero_add] at this

/-- The set `A = 2ℤ ∪ {3^n : n ∈ ℕ}` of Proposition \ref{G:prop:strict}(i). -/
def setA₁ : Set ℤ := {x | Even x} ∪ {x | ∃ n : ℕ, 1 ≤ n ∧ x = 3 ^ n}

lemma odd_not_mem_admissible_setA₁ {t : ℤ} (ht : Odd t) : t ∉ admissible setA₁ := by
  rintro ⟨B, hB, hBt⟩
  -- an infinite subset of `B` of constant parity
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (B ∩ {b | b % 2 = c}).Infinite := by
    by_contra hcon
    push Not at hcon
    apply hB
    have : B ⊆ (B ∩ {b | b % 2 = 0}) ∪ (B ∩ {b | b % 2 = 1}) := by
      intro b hb
      rcases Int.emod_two_eq_zero_or_one b with h | h
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, h⟩
    exact ((hcon 0).union (hcon 1)).subset this
  set B' := B ∩ {b | b % 2 = c}
  obtain ⟨b₁, hb₁, b₂, hb₂, hne⟩ := hc.nontrivial
  wlog hlt : b₁ < b₂ generalizing b₁ b₂
  · exact this b₂ hb₂ b₁ hb₁ hne.symm (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
  have hto : (t % 2) = 1 := Int.odd_iff.mp ht
  -- odd elements of `A` are powers of `3`
  have hpow : ∀ z ∈ setA₁, z % 2 = 1 → ∃ n : ℕ, 1 ≤ n ∧ z = 3 ^ n := by
    rintro z (hz | hz) hz2
    · exact absurd (Int.even_iff.mp hz) (by omega)
    · exact hz
  set D := b₂ - b₁
  have key : ∀ b ∈ B' \ {b₁, b₂}, b₁ + b + t ∈
      (((Finset.range (D.toNat + 1)).image fun n : ℕ => (3 : ℤ) ^ n : Finset ℤ) : Set ℤ) := by
    intro b hb
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
    obtain ⟨⟨hbB, hbc⟩, hb1, hb2⟩ := hb
    have hb₁c : b₁ % 2 = c := hb₁.2
    have hb₂c : b₂ % 2 = c := hb₂.2
    have hbc' : b % 2 = c := hbc
    obtain ⟨n, hn1, hn⟩ := hpow _ (hBt b₁ hb₁.1 b hbB (Ne.symm hb1)) (by omega)
    obtain ⟨m, hm1, hm⟩ := hpow _ (hBt b₂ hb₂.1 b hbB (Ne.symm hb2)) (by omega)
    have hD : (3 : ℤ) ^ m - 3 ^ n = D := by rw [← hm, ← hn]; ring
    have hnm : n < m := by
      have hD0 : 0 < D := by omega
      have : (3 : ℤ) ^ n < 3 ^ m := by linarith
      exact (pow_lt_pow_iff_right₀ (by norm_num)).mp this
    have h3 : (3 : ℤ) ^ n ≤ D := by
      have : (3 : ℤ) ^ (n + 1) ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) hnm
      rw [pow_succ] at this
      have : (0 : ℤ) < 3 ^ n := by positivity
      linarith
    have hnD : (n : ℤ) ≤ D := by
      have : (n : ℤ) < 3 ^ n := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 3)
      linarith
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨n, by omega, hn.symm⟩
  have hfin : (B' \ {b₁, b₂}).Finite :=
    ((Finset.finite_toSet _).image fun z => z - b₁ - t).subset fun b hb =>
      ⟨b₁ + b + t, key b hb, by ring⟩
  exact (hc.sdiff (Set.toFinite {b₁, b₂})) hfin

/-- Paper, Proposition \ref{G:prop:strict}(i): for `A = 2ℤ ∪ {3^n : n ∈ ℕ}` we have
`T(A) = 2ℤ`, while `A + 2ℤ = ℤ`. -/
theorem prop_strict_i : admissible setA₁ = {x : ℤ | Even x} ∧ addTwoG setA₁ = Set.univ := by
  constructor
  · refine Set.Subset.antisymm (fun t ht => ?_) (evens_subset_admissible Set.subset_union_left)
    rcases Int.even_or_odd t with h | h
    · exact h
    · exact absurd ht (odd_not_mem_admissible_setA₁ h)
  · refine Set.eq_univ_of_forall fun x => ?_
    rcases Int.even_or_odd x with h | h
    · exact ⟨0, Or.inl ⟨0, by simp⟩, mem_twoG_int.mpr (by simpa using h)⟩
    · refine ⟨3, Or.inr ⟨1, le_rfl, by norm_num⟩, mem_twoG_int.mpr ?_⟩
      have : Odd (3 : ℤ) := by decide
      exact h.sub_odd this

/-- `X = {2^i + 2^j + 1 : 1 ≤ i < j}`. -/
def setX : Set ℤ := {x | ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ x = 2 ^ i + 2 ^ j + 1}

/-- The set `A = 2ℤ ∪ X` of Proposition \ref{G:prop:strict}(ii). -/
def setA₂ : Set ℤ := {x | Even x} ∪ setX

/-- `X` is contained in at most `(k + 1)^2` residue classes modulo `2^k`, hence
`d*(X) ≤ (k + 1)^2 / 2^k`. -/
lemma ubd_setX_le (k : ℕ) : ubd setX ≤ ((k : ℝ) + 1) ^ 2 / 2 ^ k := by
  set H := AddSubgroup.zmultiples ((2 : ℤ) ^ k)
  set P : Finset ℤ := (Finset.range (k + 1)).image fun i => if i < k then (2 : ℤ) ^ i else 0
  have hP : ∀ i : ℕ, ∃ p ∈ P, (2 : ℤ) ^ i - p ∈ H := by
    intro i
    by_cases hi : i < k
    · exact ⟨2 ^ i, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), by simp [hi]⟩,
        by simp⟩
    · refine ⟨0, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), by simp⟩, ?_⟩
      rw [sub_zero, Int.mem_zmultiples_iff]
      exact pow_dvd_pow 2 (not_lt.mp hi)
  have hsub : setX ⊆ ⋃ pq ∈ P ×ˢ P, {g | g - (pq.1 + pq.2 + 1) ∈ H} := by
    rintro x ⟨i, j, -, -, rfl⟩
    obtain ⟨p, hp, hpi⟩ := hP i
    obtain ⟨q, hq, hqj⟩ := hP j
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    have : (2 : ℤ) ^ i + 2 ^ j + 1 - ((p, q).1 + (p, q).2 + 1) = (2 ^ i - p) + (2 ^ j - q) := by
      simp only; ring
    rw [this]
    exact add_mem hpi hqj
  have hcard : #(P ×ˢ P) ≤ (k + 1) ^ 2 := by
    rw [Finset.card_product, sq]
    have : #P ≤ k + 1 := Finset.card_image_le.trans (by simp)
    exact Nat.mul_le_mul this this
  have hidx : (H.index : ℝ) = 2 ^ k := by
    rw [Int.index_zmultiples]; simp
  calc ubd setX ≤ ∑ pq ∈ P ×ˢ P, ubd {g | g - (pq.1 + pq.2 + 1) ∈ H} :=
        (ubd_mono hsub).trans (ubd_biUnion_le _ _)
    _ = #(P ×ˢ P) * (1 / (2 : ℝ) ^ k) := by
        rw [Finset.sum_congr rfl fun pq _ => (ubd_coset H _).trans (by rw [hidx]),
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k : ℝ) + 1) ^ 2 * (1 / (2 : ℝ) ^ k) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ = ((k : ℝ) + 1) ^ 2 / 2 ^ k := by ring

/-- `d*(X) = 0`. -/
theorem ubd_setX : ubd setX = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (ubd_nonneg _)
  have ht := ((tendsto_pow_const_div_const_pow_of_one_lt 2 (show (1 : ℝ) < 2 by norm_num)).comp
    (tendsto_add_atTop_nat 1)).const_mul 2
  rw [mul_zero] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hk
  have e : 2 * (((k : ℝ) + 1) ^ 2 / 2 ^ (k + 1)) = ((k : ℝ) + 1) ^ 2 / 2 ^ k := by
    field_simp; ring
  rw [e] at hk
  linarith [ubd_setX_le k]

/-- Paper, Proposition \ref{G:prop:strict}(ii): for `A = 2ℤ ∪ X` with
`X = {2^i + 2^j + 1 : 1 ≤ i < j}` we have `R(A) = 2ℤ`, while `T(A) = ℤ`. -/
theorem prop_strict_ii : posCosets setA₂ = {x : ℤ | Even x} ∧ admissible setA₂ = Set.univ := by
  constructor
  · ext r
    simp only [posCosets, Set.mem_ofPred_eq]
    constructor
    · intro hr
      by_contra hodd
      have hsub : setA₂ ∩ coset2 r ⊆ setX := by
        rintro x ⟨hx | hx, hxr⟩
        · exfalso
          have h1 := mem_coset2_int.mp hxr
          have : Even (x - (x - r)) := Even.sub hx h1
          rw [sub_sub_cancel] at this
          exact hodd this
        · exact hx
      have := (ubd_mono hsub).trans_eq ubd_setX
      linarith
    · intro hr
      have : setA₂ ∩ coset2 r = coset2 r := by
        refine Set.inter_eq_right.mpr fun x hx => Or.inl ?_
        have h1 := mem_coset2_int.mp hx
        have := Even.add h1 hr
        rwa [sub_add_cancel] at this
      rw [this]
      exact ubd_coset_pos (twoG ℤ) r
  · have hev := evens_subset_admissible (A := setA₂) Set.subset_union_left
    have h1 : (1 : ℤ) ∈ admissible setA₂ := by
      refine ⟨(fun i : ℕ => (2 : ℤ) ^ i) '' {i | 1 ≤ i}, ?_, ?_⟩
      · refine (Set.Ici_infinite 1).image fun a _ b _ h => ?_
        exact Nat.pow_right_injective le_rfl (by exact_mod_cast h)
      · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hne
        have hij : i ≠ j := fun h => hne (by rw [h])
        right
        rcases lt_or_gt_of_ne hij with h | h
        · exact ⟨i, j, hi, h, rfl⟩
        · exact ⟨j, i, hj, h, by ring⟩
    refine Set.eq_univ_of_forall fun x => ?_
    rcases Int.even_or_odd x with h | h
    · exact hev h
    · have := thm_translates_union setA₂ 1 h1 (x - 1) (mem_twoG_int.mpr (h.sub_odd odd_one))
      rwa [add_sub_cancel] at this

end Strict

end Kmrr25.Q516
