import Kmrr25.Basic

/-!
# Sums of blocks from a density Ramsey family (Question 3.31 and Question §3.6(a))

Paper, Section \ref{IB:sec:q331}: Theorem \ref{IB:thm:dR}, Corollary \ref{IB:cor:331},
Lemmas \ref{IB:lem:folner} and \ref{IB:lem:intersect}.

## Conditional result

The dynamical input of the proof is Proposition \ref{IB:prop:dyn}, which the paper extracts from
Kra, Moreira, Richter and Robertson, *The Density Finite Sums Theorem* (arXiv:2504.06424); it is
**not** formalized here. It is the `Prop` `DynInput` below,
transcribed from the statement of Proposition \ref{IB:prop:dyn}, and it appears as an explicit
hypothesis `(hDyn : DynInput)` of the main theorems. It is not declared as an axiom, and nothing in
this file proves it. Everything else in the section is proved here: the definitions of upper
Banach density, Følner sequences and density Ramsey families, Lemma \ref{IB:lem:folner},
Lemma \ref{IB:lem:intersect} (the intersectivity lemma along a Følner sequence), the inductive
construction of nested boxes and blocks, the chain argument, the passage from `t ≥ 0` to
`t ≥ 1`, and the deduction of Corollary \ref{IB:cor:331}.

## Main results

* `thm_dR` — Theorem \ref{IB:thm:dR}, assuming `DynInput`: if `𝒟` has the density Ramsey
  property, `k ≥ 1` and `d*(A) > 0`, there are `t ≥ 1` and blocks `B_0, B_1, … ∈ 𝒟` with
  `max B_i < min B_{i+1}` such that `B_{i_1} + ⋯ + B_{i_m} ⊆ A - t` for all `1 ≤ m ≤ k` and
  `i_1 < ⋯ < i_m`.
* `cor331` — Corollary \ref{IB:cor:331} in its strong form for Question 3.31 (`k = 2`, with
  `B_i ⊆ A - t` and ordered blocks); `question331_of_dyn : DynInput → Question331` and
  `question36a_of_dyn : DynInput → Question36a` — positive answers to Question 3.31 and
  Question §3.6(a) (Questions \ref{IB:q:331}, \ref{IB:q:36a}).
* `IsFolner.tendsto_card`, `IsFolner.udensAlong_le_ubd` — Lemma \ref{IB:lem:folner}:
  `|Φ_N| → ∞` and `d*(K) ≥ d̄_Φ(K)`.
* `lem_intersect` — Lemma \ref{IB:lem:intersect}.
* `step`, `chain` — the inductive step (properties (I1)–(I3)) and the chain argument
  \eqref{IB:eq:chain} of the proof of Theorem \ref{IB:thm:dR}.

## Conventions

* The paper's `ℕ` is `{1, 2, …}`. Sets `A ⊆ ℕ` are `Set ℕ` (Lean's `ℕ` contains `0`, which
  plays no role: `d*` only counts windows `{M + 1, …, M + N}`); `A - t = {n ≥ 1 : n + t ∈ A}`
  is `shiftSet A t`. Følner sets and members of `𝒟` consist of positive integers.
* `d*(A) = limsup_{N → ∞} sup_{M ≥ 0} |A ∩ {M + 1, …, M + N}| / N` (`ubd`), as in the paper.
  `d̄_Φ(K) = limsup_N |K ∩ Φ_N| / |Φ_N|` (`udensAlong`). These real `limsup`s are of sequences
  in `[0, 1]`, so they are the usual ones.
* Blocks are indexed from `0`: `B i` is the paper's `B_{i+1}`. "`max B_i < min B_{i+1}`" is
  stated elementwise (`∀ x ∈ B i, ∀ y ∈ B (i + 1), x < y`), and
  "`B_{i_1} + ⋯ + B_{i_m} ⊆ A - t`" as: for every strictly increasing `idx : Fin m → ℕ` and every
  choice `b_l ∈ B (idx l)`, `∑ l, b l ∈ A - t`.
* `Question331` and `Question36a` quantify over all `A : Set ℕ`, which includes the paper's
  `A ⊆ {1, 2, …}`. In `DynInput` the set `A` is required to lie in `{1, 2, …}`, exactly as in
  Proposition \ref{IB:prop:dyn}; in `DensityRamsey` likewise.
* `DynInput` asserts more than the proof uses (genericity of `a`, ergodicity of `μ̃`); this is
  deliberate, so that the hypothesis is literally the paper's proposition.

## Remarks on proofs

* For `d*(K) ≥ d̄_Φ(K)` in Lemma \ref{IB:lem:folner} we use an averaging argument instead of the
  paper's decomposition into maximal blocks: for every `L ≥ 1`,
  `L |K ∩ F| ≤ ∑_{h=1}^{L} |{n ∈ F : n + h ∈ K}| + L² |F \ (F + 1)|`, and the sum on the right is
  `∑_{n ∈ F} |K ∩ {n + 1, …, n + L}| ≤ |F| sup_M |K ∩ {M + 1, …, M + L}|`.
* In Lemma \ref{IB:lem:intersect} the reverse Fatou lemma is applied along the whole sequence
  (no subsequence is needed); the hypothesis `δ > 0` is not needed and is omitted.
* In the inductive step the constants `δ = c/8`, `κ = c/4` are used instead of `c/2`, `c/2`;
  the next box is `W = (u_1 ∩ V_1) × ⋯ × (u_k ∩ V_k)` for a product neighbourhood
  `u_0 × ⋯ × u_k ⊆ O` of a point of `supp σ`, which gives (I1) directly.
* Only `d*(A - 1) ≥ d*(A)` is proved (the paper notes equality); this is all that is used.
-/

open Filter Topology Finset
open scoped Classical

noncomputable section

namespace Kmrr25.Q331

/-! ## Densities and Følner sequences -/

/-- `|A ∩ {M + 1, …, M + N}|`. -/
def cnt (A : Set ℕ) (M N : ℕ) : ℕ := #((Ioc M (M + N)).filter (· ∈ A))

/-- The upper Banach density
`d*(A) = limsup_{N → ∞} sup_{M ≥ 0} |A ∩ {M + 1, …, M + N}| / N`. -/
def ubd (A : Set ℕ) : ℝ := limsup (fun N : ℕ => (⨆ M : ℕ, (cnt A M N : ℝ)) / N) atTop

/-- A *Følner sequence* in `ℕ = {1, 2, …}`: finite nonempty sets `Φ_N ⊆ {1, 2, …}` with
`|(Φ_N + 1) ∩ Φ_N| / |Φ_N| → 1`. -/
def IsFolner (Φ : ℕ → Finset ℕ) : Prop :=
  (∀ N, (Φ N).Nonempty) ∧ (∀ N, ∀ n ∈ Φ N, 1 ≤ n) ∧
    Tendsto (fun N => (#((Φ N).image (· + 1) ∩ Φ N) : ℝ) / #(Φ N)) atTop (𝓝 1)

/-- The relative density `|K ∩ F| / |F|`. -/
def relDens (F : Finset ℕ) (K : Set ℕ) : ℝ := (#(F.filter (· ∈ K)) : ℝ) / #F

/-- The upper density along `Φ`: `d̄_Φ(K) = limsup_N |K ∩ Φ_N| / |Φ_N|`. -/
def udensAlong (Φ : ℕ → Finset ℕ) (K : Set ℕ) : ℝ := limsup (fun N => relDens (Φ N) K) atTop

/-! ## Elementary bounds -/

lemma cnt_le (A : Set ℕ) (M N : ℕ) : cnt A M N ≤ N := by
  unfold cnt
  refine (card_filter_le _ _).trans ?_
  simp

/-- `sup_M |A ∩ {M + 1, …, M + N}|`. -/
def winSup (A : Set ℕ) (N : ℕ) : ℝ := ⨆ M : ℕ, (cnt A M N : ℝ)

lemma bddAbove_cnt (A : Set ℕ) (N : ℕ) : BddAbove (Set.range fun M : ℕ => (cnt A M N : ℝ)) :=
  ⟨N, by rintro _ ⟨M, rfl⟩; show (cnt A M N : ℝ) ≤ N; exact_mod_cast cnt_le A M N⟩

lemma cnt_le_winSup (A : Set ℕ) (M N : ℕ) : (cnt A M N : ℝ) ≤ winSup A N :=
  le_ciSup (bddAbove_cnt A N) M

lemma winSup_le (A : Set ℕ) (N : ℕ) : winSup A N ≤ N :=
  ciSup_le fun M => by exact_mod_cast cnt_le A M N

lemma winSup_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ winSup A N :=
  (Nat.cast_nonneg _).trans (cnt_le_winSup A 0 N)

lemma winSup_div_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ winSup A N / N :=
  div_nonneg (winSup_nonneg A N) (Nat.cast_nonneg _)

lemma winSup_div_le_one (A : Set ℕ) (N : ℕ) : winSup A N / N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact winSup_le A N

lemma ubd_eq (A : Set ℕ) : ubd A = limsup (fun N : ℕ => winSup A N / N) atTop := rfl

lemma relDens_nonneg (F : Finset ℕ) (K : Set ℕ) : 0 ≤ relDens F K := by
  unfold relDens; positivity

lemma relDens_le_one (F : Finset ℕ) (K : Set ℕ) : relDens F K ≤ 1 := by
  unfold relDens
  rcases Nat.eq_zero_or_pos #F with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast card_filter_le _ _

lemma bdd_le_one {u : ℕ → ℝ} (h : ∀ n, u n ≤ 1) : IsBoundedUnder (· ≤ ·) atTop u :=
  isBoundedUnder_of ⟨1, h⟩

lemma cobdd_nonneg {u : ℕ → ℝ} (h : ∀ n, 0 ≤ u n) : IsCoboundedUnder (· ≤ ·) atTop u :=
  (isBoundedUnder_of ⟨0, h⟩).isCoboundedUnder_le

lemma limsup_nonneg' {u : ℕ → ℝ} (h0 : ∀ n, 0 ≤ u n) (h1 : ∀ n, u n ≤ 1) :
    0 ≤ limsup u atTop :=
  le_limsup_of_frequently_le (Frequently.of_forall h0) (bdd_le_one h1)

/-- If `u ≥ 0` and eventually `u_n ≤ c + e_n` with `e_n → 0`, then `limsup u ≤ c`. -/
lemma limsup_le_of_le_add {u e : ℕ → ℝ} {c : ℝ} (hu0 : ∀ n, 0 ≤ u n)
    (h : ∀ᶠ n in atTop, u n ≤ c + e n) (he : Tendsto e atTop (𝓝 0)) :
    limsup u atTop ≤ c := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine limsup_le_of_le (cobdd_nonneg hu0) ?_
  filter_upwards [h, he.eventually (gt_mem_nhds hε)] with n h1 h2
  linarith

lemma udensAlong_nonneg (Φ : ℕ → Finset ℕ) (K : Set ℕ) : 0 ≤ udensAlong Φ K :=
  limsup_nonneg' (fun _ => relDens_nonneg _ _) (fun _ => relDens_le_one _ _)

lemma ubd_nonneg (A : Set ℕ) : 0 ≤ ubd A :=
  limsup_nonneg' (fun _ => winSup_div_nonneg _ _) (fun _ => winSup_div_le_one _ _)

/-! ## Lemma \ref{IB:lem:folner} -/

variable {Φ : ℕ → Finset ℕ}

lemma card_image_succ_inter_lt (F : Finset ℕ) (hF : F.Nonempty) :
    #(F.image (· + 1) ∩ F) + 1 ≤ #F := by
  have hinj : Set.InjOn (· + 1 : ℕ → ℕ) F := fun a _ b _ h => by simpa using h
  have hcard : #(F.image (· + 1)) = #F := card_image_of_injOn hinj
  have hmem : F.max' hF + 1 ∈ F.image (· + 1) := mem_image_of_mem _ (max'_mem F hF)
  have hnot : F.max' hF + 1 ∉ F := fun h => by
    have := le_max' F _ h
    omega
  have hsub : F.image (· + 1) ∩ F ⊆ (F.image (· + 1)).erase (F.max' hF + 1) := by
    intro x hx
    rw [mem_inter] at hx
    exact mem_erase.2 ⟨fun h => hnot (h ▸ hx.2), hx.1⟩
  have := card_le_card hsub
  rw [card_erase_of_mem hmem, hcard] at this
  have hpos : 0 < #F := card_pos.2 hF
  omega

/-- The proportion of `Φ_N` not in `Φ_N + 1` tends to `0`. -/
lemma IsFolner.tendsto_sdiff (hΦ : IsFolner Φ) :
    Tendsto (fun N => (#(Φ N \ (Φ N).image (· + 1)) : ℝ) / #(Φ N)) atTop (𝓝 0) := by
  have h := hΦ.2.2
  have h' : Tendsto (fun N => 1 - (#((Φ N).image (· + 1) ∩ Φ N) : ℝ) / #(Φ N)) atTop
      (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  refine h'.congr fun N => ?_
  have hpos : (0 : ℝ) < #(Φ N) := by exact_mod_cast card_pos.2 (hΦ.1 N)
  have e := card_sdiff_add_card_inter (Φ N) ((Φ N).image (· + 1))
  rw [inter_comm] at e
  have e' : ((#(Φ N \ (Φ N).image (· + 1)) : ℕ) : ℝ) =
      #(Φ N) - #((Φ N).image (· + 1) ∩ Φ N) := by
    rw [← e]; push_cast; ring
  rw [e']
  field_simp

/-- Paper, Lemma \ref{IB:lem:folner}, first part: `1 / |Φ_N| → 0`. -/
lemma IsFolner.tendsto_inv_card (hΦ : IsFolner Φ) :
    Tendsto (fun N => (1 : ℝ) / #(Φ N)) atTop (𝓝 0) := by
  have h := hΦ.tendsto_sdiff
  refine squeeze_zero (fun N => div_nonneg zero_le_one (Nat.cast_nonneg _)) (fun N => ?_) h
  have hpos : (0 : ℝ) < #(Φ N) := by exact_mod_cast card_pos.2 (hΦ.1 N)
  refine div_le_div_of_nonneg_right ?_ hpos.le
  have e := card_sdiff_add_card_inter (Φ N) ((Φ N).image (· + 1))
  rw [inter_comm] at e
  have := card_image_succ_inter_lt (Φ N) (hΦ.1 N)
  have : 1 ≤ #(Φ N \ (Φ N).image (· + 1)) := by omega
  exact_mod_cast this

/-- Paper, Lemma \ref{IB:lem:folner}, first part: `|Φ_N| → ∞`. -/
theorem IsFolner.tendsto_card (hΦ : IsFolner Φ) : Tendsto (fun N => #(Φ N)) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  have h := hΦ.tendsto_inv_card.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / ((B : ℝ) + 1) by positivity))
  filter_upwards [h] with N hN
  have hpos : (0 : ℝ) < #(Φ N) := by exact_mod_cast card_pos.2 (hΦ.1 N)
  rw [div_lt_div_iff₀ hpos (by positivity)] at hN
  have : (B : ℝ) ≤ #(Φ N) := by linarith
  exact_mod_cast this

lemma card_sdiff_image_add (F : Finset ℕ) (h : ℕ) :
    #(F \ F.image (· + h)) ≤ h * #(F \ F.image (· + 1)) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hsub : F \ F.image (· + (h + 1)) ⊆
        (F \ F.image (· + h)) ∪ (F \ F.image (· + 1)).image (· + h) := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      by_cases hx' : x ∈ F.image (· + h)
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx'
        refine mem_union_right _ (mem_image.2 ⟨y, mem_sdiff.2 ⟨hy, fun hy1 => ?_⟩, rfl⟩)
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy1
        exact hx.2 (Finset.mem_image.2 ⟨z, hz, by omega⟩)
      · exact mem_union_left _ (mem_sdiff.2 ⟨hx.1, hx'⟩)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    refine (add_le_add ih card_image_le).trans ?_
    rw [add_mul, one_mul]

lemma card_filter_le_shift (F : Finset ℕ) (K : Set ℕ) (h : ℕ) :
    #(F.filter (· ∈ K)) ≤ #(F.filter (fun n => n + h ∈ K)) + #(F \ F.image (· + h)) := by
  have hsub : F.filter (· ∈ K) ⊆
      (F.filter (fun n => n + h ∈ K)).image (· + h) ∪ (F \ F.image (· + h)) := by
    intro x hx
    rw [mem_filter] at hx
    by_cases hx' : x ∈ F.image (· + h)
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx'
      exact mem_union_left _ (mem_image.2 ⟨y, mem_filter.2 ⟨hy, hx.2⟩, rfl⟩)
    · exact mem_union_right _ (mem_sdiff.2 ⟨hx.1, hx'⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add card_image_le le_rfl))

lemma cnt_eq (K : Set ℕ) (n L : ℕ) : cnt K n L = #((Ioc 0 L).filter (fun h => n + h ∈ K)) := by
  unfold cnt
  have : Ioc n (n + L) = (Ioc 0 L).map (addLeftEmbedding n) := by
    rw [map_add_left_Ioc]; simp
  rw [this, filter_map, card_map]
  rfl

lemma sum_card_shift (F : Finset ℕ) (K : Set ℕ) (L : ℕ) :
    ∑ h ∈ Ioc 0 L, #(F.filter (fun n => n + h ∈ K)) = ∑ n ∈ F, cnt K n L := by
  simp only [cnt_eq, card_filter]
  exact sum_comm

/-- The key inequality: `|K ∩ F| ≤ |F| · sup_M |K ∩ {M+1, …, M+L}| / L + L · |F \ (F + 1)|`. -/
lemma card_filter_le_winSup (F : Finset ℕ) (K : Set ℕ) {L : ℕ} (hL : 1 ≤ L) :
    (#(F.filter (· ∈ K)) : ℝ) ≤
      #F * (winSup K L / L) + L * #(F \ F.image (· + 1)) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have h1 : (L : ℝ) * #(F.filter (· ∈ K)) ≤
      ∑ h ∈ Ioc 0 L, ((#(F.filter (fun n => n + h ∈ K)) : ℝ) + L * #(F \ F.image (· + 1))) := by
    have : (L : ℝ) * #(F.filter (· ∈ K)) = ∑ h ∈ Ioc 0 L, (#(F.filter (· ∈ K)) : ℝ) := by
      simp
    rw [this]
    refine sum_le_sum fun h hh => ?_
    have hhL : h ≤ L := (mem_Ioc.1 hh).2
    have a := card_filter_le_shift F K h
    have b := card_sdiff_image_add F h
    have c : (h : ℝ) * #(F \ F.image (· + 1)) ≤ L * #(F \ F.image (· + 1)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hhL) (Nat.cast_nonneg _)
    have a' : (#(F.filter (· ∈ K)) : ℝ) ≤ #(F.filter (fun n => n + h ∈ K)) +
        #(F \ F.image (· + h)) := by exact_mod_cast a
    have b' : (#(F \ F.image (· + h)) : ℝ) ≤ h * #(F \ F.image (· + 1)) := by exact_mod_cast b
    linarith
  rw [sum_add_distrib] at h1
  have h2 : ∑ h ∈ Ioc 0 L, (#(F.filter (fun n => n + h ∈ K)) : ℝ) ≤ #F * winSup K L := by
    have := sum_card_shift F K L
    have e : ∑ h ∈ Ioc 0 L, (#(F.filter (fun n => n + h ∈ K)) : ℝ) =
        ∑ n ∈ F, (cnt K n L : ℝ) := by exact_mod_cast this
    rw [e]
    calc ∑ n ∈ F, (cnt K n L : ℝ) ≤ ∑ n ∈ F, winSup K L :=
          sum_le_sum fun n _ => cnt_le_winSup K n L
      _ = #F * winSup K L := by simp
  have h3 : ∑ h ∈ Ioc 0 L, ((L : ℝ) * #(F \ F.image (· + 1))) =
      L * (L * #(F \ F.image (· + 1))) := by simp
  rw [h3] at h1
  have : (L : ℝ) * #(F.filter (· ∈ K)) ≤ L * (#F * (winSup K L / L) +
      L * #(F \ F.image (· + 1))) := by
    rw [mul_add, mul_div_assoc', mul_comm (L : ℝ) (#F * winSup K L / L), div_mul_cancel₀ _
      hLpos.ne']
    linarith
  exact le_of_mul_le_mul_left this hLpos

/-- Paper, Lemma \ref{IB:lem:folner}, second part: `d*(K) ≥ d̄_Φ(K)` for every `K ⊆ ℕ`. -/
theorem IsFolner.udensAlong_le_ubd (hΦ : IsFolner Φ) (K : Set ℕ) : udensAlong Φ K ≤ ubd K := by
  have hL : ∀ L : ℕ, 1 ≤ L → udensAlong Φ K ≤ winSup K L / L := by
    intro L hL
    refine limsup_le_of_le_add (fun _ => relDens_nonneg _ _) (Eventually.of_forall fun N => ?_)
      ((hΦ.tendsto_sdiff.const_mul (L : ℝ)).congr (fun _ => rfl) |>.trans (by simp))
    have hpos : (0 : ℝ) < #(Φ N) := by exact_mod_cast card_pos.2 (hΦ.1 N)
    have := card_filter_le_winSup (Φ N) K hL
    unfold relDens
    rw [div_le_iff₀ hpos]
    calc (#((Φ N).filter (· ∈ K)) : ℝ) ≤ _ := this
      _ = (winSup K L / L + L * ((#(Φ N \ (Φ N).image (· + 1)) : ℝ) / #(Φ N))) * #(Φ N) := by
        field_simp
  refine le_limsup_of_frequently_le ?_ (bdd_le_one fun _ => winSup_div_le_one _ _)
  rw [frequently_atTop]
  intro L0
  exact ⟨max L0 1, le_max_left _ _, hL _ (le_max_right _ _)⟩

/-! ## Lemma \ref{IB:lem:intersect} -/

open MeasureTheory ENNReal

lemma ofReal_relDens (F : Finset ℕ) (hF : F.Nonempty) (K : Set ℕ) :
    ENNReal.ofReal (relDens F K) = (#F : ℝ≥0∞)⁻¹ * #(F.filter (· ∈ K)) := by
  have hpos : (0 : ℝ) < #F := by exact_mod_cast card_pos.2 hF
  unfold relDens
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    ENNReal.div_eq_inv_mul]

lemma ofReal_udensAlong (Φ : ℕ → Finset ℕ) (K : Set ℕ) :
    ENNReal.ofReal (udensAlong Φ K) =
      limsup (fun N => ENNReal.ofReal (relDens (Φ N) K)) atTop :=
  Monotone.map_limsup_of_continuousAt (fun _ _ h => ENNReal.ofReal_le_ofReal h) _
    ENNReal.continuous_ofReal.continuousAt (bdd_le_one fun _ => relDens_le_one _ _)
    (cobdd_nonneg fun _ => relDens_nonneg _ _)

/-- Paper, Lemma \ref{IB:lem:intersect} (Bergelson's intersectivity lemma along a Følner
sequence). Let `(Ω, ν)` be a probability space, `Φ` a Følner sequence in `ℕ`, and `R ⊆ ℕ` with
`d̄_Φ(R) ≥ δ > 0`. For `n ∈ R` let `O_n ⊆ Ω` be measurable with `ν(O_n) ≥ κ > 0`. Then there is
`K ⊆ R` with `d*(K) ≥ δκ` such that `ν(⋂_{n ∈ F} O_n) > 0` for every finite nonempty `F ⊆ K`. -/
theorem lem_intersect {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {Φ : ℕ → Finset ℕ} (hΦ : IsFolner Φ) {R : Set ℕ} {δ κ : ℝ}
    (hR : δ ≤ udensAlong Φ R) (O : ℕ → Set Ω) (hOm : ∀ n ∈ R, MeasurableSet (O n))
    (hκ : 0 < κ) (hOκ : ∀ n ∈ R, κ ≤ ν.real (O n)) :
    ∃ K ⊆ R, δ * κ ≤ ubd K ∧
      ∀ F : Finset ℕ, F.Nonempty → (F : Set ℕ) ⊆ K → 0 < ν (⋂ n ∈ F, O n) := by
  -- the null set `Z`, the union of all null intersections
  set Z : Set Ω := ⋃ F : Finset ℕ,
    if (F : Set ℕ) ⊆ R ∧ ν (⋂ n ∈ F, O n) = 0 then ⋂ n ∈ F, O n else ∅ with hZ
  have hZm : MeasurableSet Z := by
    refine MeasurableSet.iUnion fun F => ?_
    split_ifs with h
    · exact Finset.measurableSet_biInter F fun n hn => hOm n (h.1 hn)
    · exact MeasurableSet.empty
  have hZ0 : ν Z = 0 := by
    refine measure_iUnion_null fun F => ?_
    split_ifs with h
    · exact h.2
    · exact measure_empty
  -- `K_ω = {n ∈ R : ω ∈ O_n \ Z}` and `f_N(ω) = |K_ω ∩ Φ_N| / |Φ_N|`
  set Kω : Ω → Set ℕ := fun ω => {n | n ∈ R ∧ ω ∈ O n \ Z} with hKω
  set f : ℕ → Ω → ℝ≥0∞ := fun N ω =>
    (#(Φ N) : ℝ≥0∞)⁻¹ * ∑ n ∈ (Φ N).filter (· ∈ R), (O n \ Z).indicator 1 ω with hf
  have hfm : ∀ N, Measurable (f N) := fun N =>
    (Finset.measurable_sum _ fun n hn =>
      measurable_one.indicator ((hOm n (mem_filter.1 hn).2).diff hZm)).const_mul _
  have hfK : ∀ N ω, f N ω = ENNReal.ofReal (relDens (Φ N) (Kω ω)) := by
    intro N ω
    rw [ofReal_relDens _ (hΦ.1 N)]
    simp only [hf]
    congr 1
    simp only [Set.indicator_apply, Pi.one_apply]
    rw [sum_boole, filter_filter]
    congr 2
    ext n
    simp only [mem_filter, hKω, Set.mem_ofPred_eq]
  have hf1 : ∀ N ω, f N ω ≤ 1 := fun N ω => by
    rw [hfK, ENNReal.ofReal_le_one]; exact relDens_le_one _ _
  have hint : ∀ N, ENNReal.ofReal κ * ENNReal.ofReal (relDens (Φ N) R) ≤ ∫⁻ ω, f N ω ∂ν := by
    intro N
    simp only [hf]
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun n hn =>
      measurable_one.indicator ((hOm n (mem_filter.1 hn).2).diff hZm)),
      lintegral_finsetSum _ fun n hn =>
      measurable_one.indicator ((hOm n (mem_filter.1 hn).2).diff hZm),
      ofReal_relDens _ (hΦ.1 N)]
    have : ∀ n ∈ (Φ N).filter (· ∈ R), ENNReal.ofReal κ ≤ ∫⁻ ω, (O n \ Z).indicator 1 ω ∂ν := by
      intro n hn
      have hnR := (mem_filter.1 hn).2
      rw [lintegral_indicator_one ((hOm n hnR).diff hZm), measure_sdiff_null hZ0]
      exact ENNReal.ofReal_le_of_le_toReal (hOκ n hnR)
    calc ENNReal.ofReal κ * ((#(Φ N) : ℝ≥0∞)⁻¹ * #((Φ N).filter (· ∈ R)))
        = (#(Φ N) : ℝ≥0∞)⁻¹ * ∑ n ∈ (Φ N).filter (· ∈ R), ENNReal.ofReal κ := by
          rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := by gcongr with n hn; exact this n hn
  -- reverse Fatou
  have hfatou : ENNReal.ofReal (κ * δ) ≤ ∫⁻ ω, limsup (fun N => f N ω) atTop ∂ν := by
    calc ENNReal.ofReal (κ * δ) = ENNReal.ofReal κ * ENNReal.ofReal δ := ENNReal.ofReal_mul hκ.le
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal (udensAlong Φ R) := by gcongr
      _ = limsup (fun N => ENNReal.ofReal κ * ENNReal.ofReal (relDens (Φ N) R)) atTop := by
          rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top, ofReal_udensAlong]
      _ ≤ limsup (fun N => ∫⁻ ω, f N ω ∂ν) atTop :=
          limsup_le_limsup (Eventually.of_forall hint)
      _ ≤ _ := limsup_lintegral_le 1 hfm (fun N => Eventually.of_forall (hf1 N)) (by simp)
  -- a good point `ω`
  obtain ⟨ω, hω⟩ : ∃ ω, ENNReal.ofReal (κ * δ) ≤ limsup (fun N => f N ω) atTop := by
    by_contra hcon
    push Not at hcon
    have hfi : ∫⁻ ω, limsup (fun N => f N ω) atTop ∂ν ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂ν) (by simp) (lintegral_mono fun ω => ?_)
      exact limsup_le_of_le (h := Eventually.of_forall fun N => hf1 N ω)
    have := lintegral_strict_mono (μ := ν) (IsProbabilityMeasure.ne_zero ν) aemeasurable_const hfi
      (Eventually.of_forall hcon)
    rw [lintegral_const, measure_univ, mul_one] at this
    exact absurd hfatou (not_le.2 this)
  refine ⟨Kω ω, fun n hn => hn.1, ?_, ?_⟩
  · have h1 : ENNReal.ofReal (κ * δ) ≤ ENNReal.ofReal (udensAlong Φ (Kω ω)) := by
      rw [ofReal_udensAlong]
      simpa only [hfK] using hω
    rw [ENNReal.ofReal_le_ofReal_iff (udensAlong_nonneg _ _), mul_comm] at h1
    exact h1.trans (hΦ.udensAlong_le_ubd _)
  · intro F hF hFK
    rw [pos_iff_ne_zero]
    intro h0
    obtain ⟨n, hn⟩ := hF
    have hωZ : ω ∉ Z := (hFK hn).2.2
    apply hωZ
    refine Set.mem_iUnion.2 ⟨F, ?_⟩
    rw [if_pos ⟨fun m hm => (hFK hm).1, h0⟩]
    exact Set.mem_iInter₂.2 fun m hm => (hFK hm).2.1

/-! ## Density Ramsey families and shifts -/

/-- `A - t = {n ∈ ℕ : n + t ∈ A}` with `ℕ = {1, 2, …}`. -/
def shiftSet (A : Set ℕ) (t : ℕ) : Set ℕ := {n | 1 ≤ n ∧ n + t ∈ A}

/-- Survey, Definition 3.29: a collection `𝒟` of finite nonempty subsets of `ℕ = {1, 2, …}`
has the *density Ramsey property* if every `A ⊆ ℕ` with `d*(A) > 0` contains some `X ∈ 𝒟`. -/
def DensityRamsey (𝒟 : Set (Finset ℕ)) : Prop :=
  (∀ F ∈ 𝒟, F.Nonempty ∧ ∀ n ∈ F, 1 ≤ n) ∧
    ∀ A : Set ℕ, (∀ n ∈ A, 1 ≤ n) → 0 < ubd A → ∃ X ∈ 𝒟, (X : Set ℕ) ⊆ A

lemma cnt_le_cnt_shift (A : Set ℕ) (M N : ℕ) : cnt A M N ≤ cnt (shiftSet A 1) M N + 1 := by
  unfold cnt
  have hsub : (Ioc M (M + N)).filter (· ∈ A) ⊆
      insert (M + 1) (((Ioc M (M + N)).filter (· ∈ shiftSet A 1)).image (· + 1)) := by
    intro x hx
    rw [mem_filter, mem_Ioc] at hx
    rcases eq_or_ne x (M + 1) with h | h
    · exact mem_insert.2 (Or.inl h)
    · refine mem_insert.2 (Or.inr (mem_image.2 ⟨x - 1, mem_filter.2 ⟨mem_Ioc.2 ⟨by omega,
        by omega⟩, by omega, ?_⟩, by omega⟩))
      rw [show x - 1 + 1 = x by omega]
      exact hx.2
  refine (card_le_card hsub).trans ((card_insert_le _ _).trans ?_)
  exact Nat.add_le_add_right card_image_le 1

/-- `d*(A) ≤ d*(A - 1)`. -/
lemma ubd_le_ubd_shift (A : Set ℕ) : ubd A ≤ ubd (shiftSet A 1) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1 := eventually_lt_of_limsup_lt (lt_add_of_pos_right (ubd (shiftSet A 1)) hε)
    (bdd_le_one fun _ => winSup_div_le_one _ _)
  refine limsup_le_of_le_add (e := fun N => 1 / (N : ℝ)) (fun _ => winSup_div_nonneg _ _) ?_
    tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [h1, eventually_ge_atTop 1] with N hN hN1
  change winSup (shiftSet A 1) N / N < ubd (shiftSet A 1) + ε at hN
  change winSup A N / N ≤ ubd (shiftSet A 1) + ε + 1 / N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have : winSup A N ≤ winSup (shiftSet A 1) N + 1 :=
    ciSup_le fun M => by
      have h2 : (cnt A M N : ℝ) ≤ cnt (shiftSet A 1) M N + 1 := by
        exact_mod_cast cnt_le_cnt_shift A M N
      linarith [cnt_le_winSup (shiftSet A 1) M N]
  have : winSup A N / N ≤ winSup (shiftSet A 1) N / N + 1 / N := by
    rw [← add_div]; exact div_le_div_of_nonneg_right this hNpos.le
  linarith

/-! ## The dynamical input (Proposition \ref{IB:prop:dyn}) -/

open MeasureTheory

/-- Paper, Proposition \ref{IB:prop:dyn} (Kra–Moreira–Richter–Robertson), transcribed as a
`Prop`. It is a hypothesis of the main theorems below and is **not** proved in this file.

Let `A ⊆ ℕ = {1, 2, …}` with `d*(A) > 0` and `k ∈ ℕ`, `k ≥ 1`. There exist a topological system
`(Y, T)` (a compact metric space `Y`, with its Borel σ-algebra, and a homeomorphism `T`), a point
`a ∈ Y`, an open set `Ẽ ⊆ Y`, a Følner sequence `Φ` in `ℕ` such that `a` is generic along `Φ`
for an ergodic `T`-invariant Borel probability measure `μ̃` on `Y`, a Borel probability measure
`σ` on `Y^{k+1}` and an integer `t ≥ 0` such that
* (i) `A = {n ∈ ℕ : T^n a ∈ Ẽ}`;
* (ii) `σ({a} × Y^k) = 1`;
* (iii) `σ(Y × (T^{-t} Ẽ)^k) > 0`;
* (iv) for all open `U_1, …, U_k ⊆ Y` such that `V = U_1 × ⋯ × U_k` satisfies `σ(Y × V) > 0`,
  `liminf_N (1/|Φ_N|) ∑_{n ∈ Φ_N} σ((Y × V) ∩ T_Δ^{-n}(V × Y)) > 0`, where
  `T_Δ = T × ⋯ × T` (`k + 1` factors).

Coordinates of `Y^{k+1}` are indexed by `Fin (k + 1)`, the first one being `0`; thus
`Y × V = {x : x_{j+1} ∈ U_j for all j < k}` and
`T_Δ^{-n}(V × Y) = {x : T^n x_j ∈ U_j for all j < k}`. The sequence in (iv) takes values in
`[0, 1]`, so its (real) `liminf` is the usual one. Genericity of `a` means
`(1/|Φ_N|) ∑_{n ∈ Φ_N} f(T^n a) → ∫ f dμ̃` for every continuous `f : Y → ℝ`. -/
def DynInput : Prop :=
  ∀ A : Set ℕ, (∀ n ∈ A, 1 ≤ n) → 0 < ubd A → ∀ k : ℕ, 1 ≤ k →
    ∃ (Y : Type) (_ : MetricSpace Y) (_ : CompactSpace Y) (_ : MeasurableSpace Y)
      (_ : BorelSpace Y) (T : Y ≃ₜ Y) (a : Y) (E : Set Y) (Φ : ℕ → Finset ℕ) (μ : Measure Y)
      (σ : Measure (Fin (k + 1) → Y)) (t : ℕ),
      IsOpen E ∧ IsFolner Φ ∧ IsProbabilityMeasure μ ∧ Ergodic T μ ∧
      (∀ f : C(Y, ℝ), Tendsto (fun N => (#(Φ N) : ℝ)⁻¹ * ∑ n ∈ Φ N, f (T^[n] a)) atTop
        (𝓝 (∫ y, f y ∂μ))) ∧
      IsProbabilityMeasure σ ∧
      A = {n | 1 ≤ n ∧ T^[n] a ∈ E} ∧
      σ {x | x 0 = a} = 1 ∧
      0 < σ {x | ∀ j : Fin k, T^[t] (x j.succ) ∈ E} ∧
      ∀ U : Fin k → Set Y, (∀ j, IsOpen (U j)) → 0 < σ {x | ∀ j : Fin k, x j.succ ∈ U j} →
        0 < liminf (fun N => (#(Φ N) : ℝ)⁻¹ * ∑ n ∈ Φ N,
          σ.real {x | (∀ j : Fin k, x j.succ ∈ U j) ∧ ∀ j : Fin k, T^[n] (x j.castSucc) ∈ U j})
          atTop

/-! ## The inductive construction (proof of Theorem \ref{IB:thm:dR}) -/

section Construction

variable {Y : Type*} [TopologicalSpace Y] {k : ℕ}

/-- `Y × V` for a box `V = V_0 × ⋯ × V_{k-1} ⊆ Y^k`. -/
def YV (V : Fin k → Set Y) : Set (Fin (k + 1) → Y) := {x | ∀ j : Fin k, x j.succ ∈ V j}

/-- `O_n = (Y × V) ∩ T_Δ^{-n}(V × Y)`. -/
def Oset (T : Y → Y) (V : Fin k → Set Y) (n : ℕ) : Set (Fin (k + 1) → Y) :=
  {x | (∀ j : Fin k, x j.succ ∈ V j) ∧ ∀ j : Fin k, T^[n] (x j.castSucc) ∈ V j}

lemma isOpen_YV {V : Fin k → Set Y} (hV : ∀ j, IsOpen (V j)) : IsOpen (YV V) := by
  have : YV V = ⋂ j : Fin k, (fun x : Fin (k + 1) → Y => x j.succ) ⁻¹' V j := by
    ext x; simp [YV]
  rw [this]
  exact isOpen_iInter_of_finite fun j => (hV j).preimage (continuous_apply _)

lemma isOpen_Oset {T : Y → Y} (hT : Continuous T) {V : Fin k → Set Y} (hV : ∀ j, IsOpen (V j))
    (n : ℕ) : IsOpen (Oset T V n) := by
  have : Oset T V n = YV V ∩ ⋂ j : Fin k,
      (fun x : Fin (k + 1) → Y => T^[n] (x j.castSucc)) ⁻¹' V j := by
    ext x; simp [Oset, YV]
  rw [this]
  exact (isOpen_YV hV).inter (isOpen_iInter_of_finite fun j =>
    (hV j).preimage ((hT.iterate n).comp (continuous_apply _)))

variable [SecondCountableTopology Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
  (T : Y → Y) (a : Y) (σ : Measure (Fin (k + 1) → Y)) [IsProbabilityMeasure σ]
  (Φ : ℕ → Finset ℕ)

/-- One step of the construction: from a box `V` with `σ(Y × V) > 0` and a bound `M`, a block
`B ∈ 𝒟` with `min B > M` and a smaller box `W` with `σ(Y × W) > 0`, satisfying (I1)–(I3). -/
lemma step {𝒟 : Set (Finset ℕ)} (h𝒟 : DensityRamsey 𝒟) (hk : 0 < k) (hT : Continuous T)
    (hΦ : IsFolner Φ) (ha : σ {x | x 0 = a} = 1)
    (h4 : ∀ U : Fin k → Set Y, (∀ j, IsOpen (U j)) → 0 < σ (YV U) →
      0 < liminf (fun N => (#(Φ N) : ℝ)⁻¹ * ∑ n ∈ Φ N, σ.real (Oset T U n)) atTop)
    (V : Fin k → Set Y) (hVo : ∀ j, IsOpen (V j)) (hVpos : 0 < σ (YV V)) (M : ℕ) :
    ∃ (B : Finset ℕ) (W : Fin k → Set Y), B ∈ 𝒟 ∧ (∀ n ∈ B, M < n) ∧ (∀ j, IsOpen (W j)) ∧
      0 < σ (YV W) ∧ (∀ j, W j ⊆ V j) ∧ ∀ n ∈ B, T^[n] a ∈ V ⟨0, hk⟩ ∧
        ∀ j : Fin k, ∀ hj : j.val + 1 < k, ∀ y ∈ W j, T^[n] y ∈ V ⟨j.val + 1, hj⟩ := by
  set c := liminf (fun N => (#(Φ N) : ℝ)⁻¹ * ∑ n ∈ Φ N, σ.real (Oset T V n)) atTop with hc
  have hcpos : 0 < c := h4 V hVo hVpos
  -- eventually the averages exceed `c / 2`
  have hev := eventually_lt_of_lt_liminf (half_lt_self hcpos)
    (isBoundedUnder_of ⟨0, fun N => mul_nonneg (by positivity)
      (sum_nonneg fun _ _ => measureReal_nonneg)⟩)
  set R : Set ℕ := {n | M < n ∧ c / 4 ≤ σ.real (Oset T V n)} with hR
  clear_value R
  have hmemR : ∀ n, n ∈ R ↔ M < n ∧ c / 4 ≤ σ.real (Oset T V n) := fun n => by rw [hR]; rfl
  -- `d̄_Φ(R) ≥ c / 8`
  have hRdens : c / 8 ≤ udensAlong Φ R := by
    have hsmall := (hΦ.tendsto_inv_card.const_mul ((M : ℝ) + 1)).eventually
      (gt_mem_nhds (show ((M : ℝ) + 1) * 0 < c / 8 by rw [mul_zero]; positivity))
    refine le_limsup_of_frequently_le (Eventually.frequently ?_)
      (bdd_le_one fun _ => relDens_le_one _ _)
    filter_upwards [hev, hsmall] with N h1 h2
    have hpos : (0 : ℝ) < #(Φ N) := by exact_mod_cast card_pos.2 (hΦ.1 N)
    have hpt : ∀ n ∈ Φ N, σ.real (Oset T V n) ≤
        (if n ∈ R then 1 else 0) + c / 4 + (if n ≤ M then 1 else 0) := by
      intro n _
      have h1 : σ.real (Oset T V n) ≤ 1 := measureReal_le_one
      by_cases hnR : n ∈ R
      · rw [if_pos hnR]
        split_ifs <;> linarith
      · rw [if_neg hnR]
        by_cases hnM : n ≤ M
        · rw [if_pos hnM]; linarith
        · rw [if_neg hnM]
          have : ¬ c / 4 ≤ σ.real (Oset T V n) := fun h => hnR ((hmemR n).2 ⟨by omega, h⟩)
          linarith
    have hsum := sum_le_sum hpt
    rw [sum_add_distrib, sum_add_distrib, sum_boole, sum_boole, sum_const, nsmul_eq_mul] at hsum
    have hM : (#((Φ N).filter (· ≤ M)) : ℝ) ≤ M + 1 := by
      have : (Φ N).filter (· ≤ M) ⊆ range (M + 1) := fun x hx => by
        rw [mem_filter] at hx; rw [mem_range]; omega
      have := card_le_card this
      rw [card_range] at this
      exact_mod_cast this
    have e1 : (#(Φ N) : ℝ)⁻¹ * ∑ n ∈ Φ N, σ.real (Oset T V n) ≤
        relDens (Φ N) R + c / 4 + ((M : ℝ) + 1) * (1 / #(Φ N)) := by
      unfold relDens
      rw [inv_mul_le_iff₀ hpos]
      calc ∑ n ∈ Φ N, σ.real (Oset T V n) ≤ _ := hsum
        _ ≤ (#((Φ N).filter (· ∈ R)) : ℝ) + #(Φ N) * (c / 4) + (M + 1) := by
          gcongr
        _ = _ := by field_simp
    have e2 : ((M : ℝ) + 1) * (1 / #(Φ N)) < c / 8 := h2
    linarith
  -- the intersectivity lemma
  obtain ⟨K, hKR, hKd, hKint⟩ := lem_intersect σ hΦ hRdens (Oset T V)
    (fun n _ => (isOpen_Oset hT hVo n).measurableSet) (by positivity : 0 < c / 4)
    (fun n hn => ((hmemR n).1 hn).2)
  have hKpos : 0 < ubd K := lt_of_lt_of_le (by positivity) hKd
  obtain ⟨B, hB𝒟, hBK⟩ := h𝒟.2 K (fun n hn => by have := ((hmemR _).1 (hKR hn)).1; omega) hKpos
  obtain ⟨hBne, -⟩ := h𝒟.1 B hB𝒟
  have hBM : ∀ n ∈ B, M < n := fun n hn => ((hmemR _).1 (hKR (hBK hn))).1
  set O := ⋂ n ∈ B, Oset T V n with hOdef
  have hOpos : 0 < σ O := hKint B hBne hBK
  have hOopen : IsOpen O := isOpen_biInter_finset fun n _ => isOpen_Oset hT hVo n
  -- a point of the support of `σ` in `O`
  obtain ⟨x, hxO, hxs⟩ := Measure.nonempty_inter_support_of_pos hOpos
  have hsupp := (Measure.mem_support_iff_forall x).1 hxs
  have hx0 : x 0 = a := by
    by_contra hne
    have hclosed : IsClosed {y : Fin (k + 1) → Y | y 0 = a} :=
      isClosed_eq (continuous_apply 0) continuous_const
    have hnull : σ {y : Fin (k + 1) → Y | y 0 = a}ᶜ = 0 :=
      (prob_compl_eq_zero_iff hclosed.measurableSet).2 ha
    have := hsupp _ (hclosed.isOpen_compl.mem_nhds hne)
    rw [hnull] at this
    exact lt_irrefl _ this
  have hxOn : ∀ n ∈ B, x ∈ Oset T V n := fun n hn => Set.mem_iInter₂.1 hxO n hn
  obtain ⟨n0, hn0⟩ := hBne
  -- a box around `x` inside `O`
  obtain ⟨u, hu, hpi⟩ := isOpen_pi_iff'.1 hOopen x hxO
  set W : Fin k → Set Y := fun j => u j.succ ∩ V j with hW
  have hWo : ∀ j, IsOpen (W j) := fun j => (hu j.succ).1.inter (hVo j)
  refine ⟨B, W, hB𝒟, hBM, hWo, ?_, fun j => Set.inter_subset_right, fun n hn => ⟨?_, ?_⟩⟩
  · refine hsupp _ ((isOpen_YV hWo).mem_nhds fun j => ⟨(hu j.succ).2, (hxOn n0 hn0).1 j⟩)
  · have := (hxOn n hn).2 ⟨0, hk⟩
    have e : (Fin.castSucc ⟨0, hk⟩ : Fin (k + 1)) = 0 := Fin.ext rfl
    rwa [e, hx0] at this
  · intro j hj y hy
    set z := Function.update x j.succ y with hz
    have hzpi : z ∈ Set.univ.pi u := by
      intro i _
      by_cases hi : i = j.succ
      · subst hi; rw [hz, Function.update_self]; exact hy.1
      · rw [hz, Function.update_of_ne hi]; exact (hu i).2
    have hzO : z ∈ Oset T V n := Set.mem_iInter₂.1 (hpi hzpi) n hn
    have := hzO.2 ⟨j.val + 1, hj⟩
    have e : (Fin.castSucc ⟨j.val + 1, hj⟩ : Fin (k + 1)) = j.succ := Fin.ext rfl
    rwa [e, hz, Function.update_self] at this

end Construction

/-- The chain argument: if `i_0 < ⋯ < i_m` (`m < k`) and `b_l ∈ B_{i_l}`, then
`T^{b_0 + ⋯ + b_m} a ∈ V_{i_0}^{(m)}` (paper, formula \eqref{IB:eq:chain}, with blocks and
coordinates indexed from `0`). -/
lemma chain {Y : Type*} (T : Y → Y) (a : Y) {k : ℕ} (hk : 0 < k) (box : ℕ → Fin k → Set Y)
    (blk : ℕ → Finset ℕ) (hanti : ∀ i i', i ≤ i' → ∀ j, box i' j ⊆ box i j)
    (hI2 : ∀ i, ∀ n ∈ blk i, T^[n] a ∈ box i ⟨0, hk⟩ ∧
      ∀ j : Fin k, ∀ hj : j.val + 1 < k, ∀ y ∈ box (i + 1) j, T^[n] y ∈ box i ⟨j.val + 1, hj⟩) :
    ∀ m (hm : m < k) (idx : Fin (m + 1) → ℕ), StrictMono idx → ∀ b : Fin (m + 1) → ℕ,
      (∀ l, b l ∈ blk (idx l)) → T^[∑ l, b l] a ∈ box (idx 0) ⟨m, hm⟩ := by
  intro m
  induction m with
  | zero =>
    intro hm idx _ b hb
    rw [Fin.sum_univ_one]
    exact (hI2 _ _ (hb 0)).1
  | succ m ih =>
    intro hm idx hidx b hb
    have h1 := ih (by omega) (Fin.tail idx) (hidx.comp (Fin.strictMono_succ)) (Fin.tail b)
      (fun l => hb l.succ)
    have h01 : idx 0 + 1 ≤ Fin.tail idx 0 := hidx (Fin.succ_pos 0)
    have h2 := hanti _ _ h01 _ h1
    have h3 := (hI2 (idx 0) (b 0) (hb 0)).2 ⟨m, by omega⟩ hm _ h2
    rw [Fin.sum_univ_succ, Function.iterate_add_apply]
    exact h3

/-- Paper, Theorem \ref{IB:thm:dR}, **conditional on Proposition \ref{IB:prop:dyn}**
(`DynInput`). Let `𝒟` have the density Ramsey property, `k ≥ 1` and `d*(A) > 0`. Then there are
`t ≥ 1` and `B_0, B_1, … ∈ 𝒟` with `max B_i < min B_{i+1}` such that
`B_{i_1} + ⋯ + B_{i_m} ⊆ A - t` for all `1 ≤ m ≤ k` and all `i_1 < ⋯ < i_m`. -/
theorem thm_dR (hDyn : DynInput) {𝒟 : Set (Finset ℕ)} (h𝒟 : DensityRamsey 𝒟) {k : ℕ}
    (hk : 1 ≤ k) {A : Set ℕ} (hA : 0 < ubd A) :
    ∃ t : ℕ, 1 ≤ t ∧ ∃ B : ℕ → Finset ℕ, (∀ i, B i ∈ 𝒟) ∧
      (∀ i, ∀ x ∈ B i, ∀ y ∈ B (i + 1), x < y) ∧
      ∀ m, 1 ≤ m → m ≤ k → ∀ idx : Fin m → ℕ, StrictMono idx →
        ∀ b : Fin m → ℕ, (∀ l, b l ∈ B (idx l)) → ∑ l, b l ∈ shiftSet A t := by
  -- pass to `A' = A - 1`, so that the shift `t' ≥ 0` becomes `t' + 1 ≥ 1`
  set A' := shiftSet A 1 with hA'def
  have hA' : 0 < ubd A' := hA.trans_le (ubd_le_ubd_shift A)
  obtain ⟨Y, _, _, _, _, T, a, E, Φ, μ, σ, t, hE, hΦ, -, -, -, hσ, hAE, h2, h3, h4⟩ :=
    hDyn A' (fun n hn => hn.1) hA' k hk
  have hk0 : 0 < k := hk
  have hT : Continuous T := T.continuous
  have h4' : ∀ U : Fin k → Set Y, (∀ j, IsOpen (U j)) → 0 < σ (YV U) →
      0 < liminf (fun N => (#(Φ N) : ℝ)⁻¹ * ∑ n ∈ Φ N, σ.real (Oset (⇑T) U n)) atTop := h4
  choose! Bf Wf hBW using fun (V : Fin k → Set Y) (hV : (∀ j, IsOpen (V j)) ∧ 0 < σ (YV V))
    (M : ℕ) => step (⇑T) a σ Φ h𝒟 hk0 hT hΦ h2 h4' V hV.1 hV.2 M
  -- the sequence of boxes `V_i` and bounds `max B_{i-1}`
  let st : ℕ → (Fin k → Set Y) × ℕ := fun i => Nat.rec ((fun _ => T^[t] ⁻¹' E), 0)
    (fun _ p => (Wf p.1 p.2, (Bf p.1 p.2).sup id)) i
  have hst : ∀ i, st (i + 1) = (Wf (st i).1 (st i).2, (Bf (st i).1 (st i).2).sup id) :=
    fun i => rfl
  set box : ℕ → Fin k → Set Y := fun i => (st i).1 with hbox
  set blk : ℕ → Finset ℕ := fun i => Bf (st i).1 (st i).2 with hblk
  have hgood : ∀ i, (∀ j, IsOpen (box i j)) ∧ 0 < σ (YV (box i)) := by
    intro i
    induction i with
    | zero => exact ⟨fun _ => hE.preimage (hT.iterate t), h3⟩
    | succ i ih =>
      obtain ⟨-, -, hWo, hWpos, -⟩ := hBW _ ih (st i).2
      simp only [hbox, hst]
      exact ⟨hWo, hWpos⟩
  have hspec := fun i => hBW _ (hgood i) (st i).2
  have hanti1 : ∀ i j, box (i + 1) j ⊆ box i j := by
    intro i j
    simp only [hbox, hst]
    exact (hspec i).2.2.2.2.1 j
  have hanti : ∀ i i', i ≤ i' → ∀ j, box i' j ⊆ box i j := by
    intro i i' hii'
    induction i', hii' using Nat.le_induction with
    | base => exact fun j => le_rfl
    | succ i' _ ih => exact fun j => (hanti1 i' j).trans (ih j)
  have hI2 : ∀ i, ∀ n ∈ blk i, T^[n] a ∈ box i ⟨0, hk0⟩ ∧
      ∀ j : Fin k, ∀ hj : j.val + 1 < k, ∀ y ∈ box (i + 1) j, T^[n] y ∈ box i ⟨j.val + 1, hj⟩ := by
    intro i n hn
    have := (hspec i).2.2.2.2.2 n hn
    simp only [hbox, hst]
    exact this
  have hpos : ∀ i, ∀ n ∈ blk i, 1 ≤ n := fun i n hn => by
    have := (hspec i).2.1 n hn; omega
  refine ⟨t + 1, by omega, blk, fun i => (hspec i).1, ?_, ?_⟩
  · intro i x hx y hy
    have h1 : x ≤ (blk i).sup id := le_sup (f := id) hx
    have h2 : (st (i + 1)).2 < y := (hspec (i + 1)).2.1 y hy
    rw [hst] at h2
    exact lt_of_le_of_lt h1 h2
  · intro m hm1 hmk idx hidx b hb
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hc := chain (⇑T) a hk0 box blk hanti hI2 m' (by omega) idx hidx b hb
    have hc0 : T^[∑ l, b l] a ∈ T^[t] ⁻¹' E := hanti 0 (idx 0) (Nat.zero_le _) _ hc
    have hsum : 1 ≤ ∑ l, b l :=
      (hpos _ _ (hb 0)).trans (single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (mem_univ 0))
    have hmem : t + ∑ l, b l ∈ A' := by
      rw [hAE]
      refine ⟨by omega, ?_⟩
      rw [Function.iterate_add_apply]
      exact hc0
    refine ⟨hsum, ?_⟩
    have := hmem.2
    rwa [show t + ∑ l, b l + 1 = ∑ l, b l + (t + 1) by ring] at this

/-! ## Corollary \ref{IB:cor:331}: Questions 3.31 and §3.6(a) -/

/-- Question 3.31 of the survey (Question \ref{IB:q:331}): if `𝒟` has the density Ramsey
property, then for every `A ⊆ ℕ` with `d*(A) > 0` there are `t ∈ ℕ = {1, 2, …}` and pairwise
disjoint `B_0, B_1, … ∈ 𝒟` such that `B_i + B_j ⊆ A - t` for all `i ≠ j`. -/
def Question331 : Prop :=
  ∀ 𝒟 : Set (Finset ℕ), DensityRamsey 𝒟 → ∀ A : Set ℕ, 0 < ubd A →
    ∃ t : ℕ, 1 ≤ t ∧ ∃ B : ℕ → Finset ℕ, (∀ i, B i ∈ 𝒟) ∧ Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      ∀ i j, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, x + y ∈ shiftSet A t

/-- Question §3.6(a) (Question \ref{IB:q:36a}), the `k`-fold analogue: if `𝒟` has the density
Ramsey property, `k ∈ ℕ` and `d*(A) > 0`, then there are `t ∈ ℕ` and pairwise disjoint
`B_0, B_1, … ∈ 𝒟` such that `B_{i_1} + ⋯ + B_{i_k} ⊆ A - t` for all pairwise distinct
`i_1, …, i_k`, i.e. for every injective `idx : Fin k → ℕ` and every choice `b_l ∈ B_{idx l}`,
`b_1 + ⋯ + b_k ∈ A - t`. -/
def Question36a : Prop :=
  ∀ 𝒟 : Set (Finset ℕ), DensityRamsey 𝒟 → ∀ k : ℕ, 1 ≤ k → ∀ A : Set ℕ, 0 < ubd A →
    ∃ t : ℕ, 1 ≤ t ∧ ∃ B : ℕ → Finset ℕ, (∀ i, B i ∈ 𝒟) ∧ Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      ∀ idx : Fin k → ℕ, Function.Injective idx → ∀ b : Fin k → ℕ, (∀ l, b l ∈ B (idx l)) →
        ∑ l, b l ∈ shiftSet A t

/-- Consecutively ordered nonempty blocks are ordered: `i < j` implies `B_i < B_j` elementwise. -/
lemma lt_of_ordered {B : ℕ → Finset ℕ} (hne : ∀ i, (B i).Nonempty)
    (h : ∀ i, ∀ x ∈ B i, ∀ y ∈ B (i + 1), x < y) :
    ∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact h i
  | succ j hj ih =>
    intro x hx y hy
    obtain ⟨z, hz⟩ := hne j
    exact (ih x hx z hz).trans (h j z hz y hy)

lemma pairwise_disjoint_of_ordered {B : ℕ → Finset ℕ} (hne : ∀ i, (B i).Nonempty)
    (h : ∀ i, ∀ x ∈ B i, ∀ y ∈ B (i + 1), x < y) : Pairwise (fun i j => Disjoint (B i) (B j)) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact lt_irrefl x (lt_of_ordered hne h i j hlt x hxi x hxj)
  · exact lt_irrefl x (lt_of_ordered hne h j i hlt x hxj x hxi)

/-- Paper, Corollary \ref{IB:cor:331}, strong form of the answer to Question 3.31,
**conditional on Proposition \ref{IB:prop:dyn}** (`DynInput`): there are `t ≥ 1` and
`B_0, B_1, … ∈ 𝒟` with `max B_i < min B_{i+1}`, `B_i ⊆ A - t` for all `i`, and
`B_i + B_j ⊆ A - t` for all `i ≠ j`. -/
theorem cor331 (hDyn : DynInput) {𝒟 : Set (Finset ℕ)} (h𝒟 : DensityRamsey 𝒟) {A : Set ℕ}
    (hA : 0 < ubd A) :
    ∃ t : ℕ, 1 ≤ t ∧ ∃ B : ℕ → Finset ℕ, (∀ i, B i ∈ 𝒟) ∧
      (∀ i, ∀ x ∈ B i, ∀ y ∈ B (i + 1), x < y) ∧ (∀ i, (B i : Set ℕ) ⊆ shiftSet A t) ∧
      ∀ i j, i ≠ j → ∀ x ∈ B i, ∀ y ∈ B j, x + y ∈ shiftSet A t := by
  obtain ⟨t, ht, B, hB𝒟, hord, hsum⟩ := thm_dR hDyn h𝒟 (k := 2) (by norm_num) hA
  refine ⟨t, ht, B, hB𝒟, hord, fun i x hx => ?_, ?_⟩
  · have := hsum 1 le_rfl (by norm_num) (fun _ => i) (fun a b hab => absurd hab (by
      simp [Subsingleton.elim a b])) (fun _ => x) (fun _ => hx)
    simpa using this
  · have hlt : ∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x + y ∈ shiftSet A t := by
      intro i j hij x hx y hy
      have hmono : StrictMono ![i, j] := by
        rw [Fin.strictMono_iff_lt_succ]
        intro l
        fin_cases l
        simpa using hij
      have := hsum 2 (by norm_num) le_rfl ![i, j] hmono ![x, y] (fun l => by
        fin_cases l <;> simpa)
      simpa [Fin.sum_univ_two] using this
    intro i j hij x hx y hy
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlt i j h x hx y hy
    · rw [add_comm]; exact hlt j i h y hy x hx

/-- Paper, Corollary \ref{IB:cor:331}: Question 3.31 has a positive answer,
**conditional on Proposition \ref{IB:prop:dyn}** (`DynInput`). -/
theorem question331_of_dyn (hDyn : DynInput) : Question331 := by
  intro 𝒟 h𝒟 A hA
  obtain ⟨t, ht, B, hB𝒟, hord, -, hsum⟩ := cor331 hDyn h𝒟 hA
  exact ⟨t, ht, B, hB𝒟, pairwise_disjoint_of_ordered (fun i => (h𝒟.1 _ (hB𝒟 i)).1) hord, hsum⟩

/-- Paper, Corollary \ref{IB:cor:331}: Question §3.6(a) has a positive answer,
**conditional on Proposition \ref{IB:prop:dyn}** (`DynInput`). Sums over distinct indices are
rewritten as sums over increasing indices. -/
theorem question36a_of_dyn (hDyn : DynInput) : Question36a := by
  intro 𝒟 h𝒟 k hk A hA
  obtain ⟨t, ht, B, hB𝒟, hord, hsum⟩ := thm_dR hDyn h𝒟 hk hA
  refine ⟨t, ht, B, hB𝒟, pairwise_disjoint_of_ordered (fun i => (h𝒟.1 _ (hB𝒟 i)).1) hord, ?_⟩
  intro idx hidx b hb
  set p := Tuple.sort idx
  have hmono : StrictMono (idx ∘ p) :=
    (Tuple.monotone_sort idx).strictMono_of_injective (hidx.comp p.injective)
  have := hsum k hk le_rfl (idx ∘ p) hmono (b ∘ p) (fun l => hb (p l))
  rwa [show ∑ l, (b ∘ p) l = ∑ l, b l from Equiv.sum_comp p b] at this

end Kmrr25.Q331
