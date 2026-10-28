import Kmrr25.ThmKDefs

/-!
# Theorem K: Følner sequences, generic points and supports

Paper, Section \ref{K:ssec:prelim}: Lemma \ref{K:lem:folner-grow}, facts (G1)–(G3),
Lemma \ref{K:lem:wiener}(a), and elementary facts about supports and ergodicity.
-/

open Filter Topology Finset MeasureTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

open Q516

/-! ## Averages -/

section Avg

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma avg_def (F : Finset ι) (f : ι → E) : avg F f = (#F : ℝ)⁻¹ • ∑ i ∈ F, f i := rfl

lemma avg_add (F : Finset ι) (f g : ι → E) : avg F (f + g) = avg F f + avg F g := by
  simp [avg, Finset.sum_add_distrib, smul_add]

lemma avg_add' (F : Finset ι) (f g : ι → E) :
    avg F (fun i => f i + g i) = avg F f + avg F g := avg_add F f g

lemma avg_sub' (F : Finset ι) (f g : ι → E) :
    avg F (fun i => f i - g i) = avg F f - avg F g := by
  simp [avg, Finset.sum_sub_distrib, smul_sub]

lemma avg_smul (F : Finset ι) (c : ℝ) (f : ι → E) : avg F (fun i => c • f i) = c • avg F f := by
  simp [avg, ← Finset.smul_sum, smul_comm c]

lemma avg_const {F : Finset ι} (hF : F.Nonempty) (c : E) : avg F (fun _ => c) = c := by
  have : (#F : ℝ) ≠ 0 := by exact_mod_cast hF.card_pos.ne'
  simp [avg, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ this]

lemma norm_avg_le {F : Finset ι} (f : ι → E) {B : ℝ} (hB : ∀ i ∈ F, ‖f i‖ ≤ B) (hB0 : 0 ≤ B) :
    ‖avg F f‖ ≤ B := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simpa [avg] using hB0
  have hc : (0 : ℝ) < #F := by exact_mod_cast hF.card_pos
  rw [avg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc, inv_mul_le_iff₀ hc]
  calc ‖∑ i ∈ F, f i‖ ≤ ∑ i ∈ F, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ F, B := Finset.sum_le_sum hB
    _ = #F * B := by simp

lemma norm_avg_le_avg_norm (F : Finset ι) (f : ι → E) : ‖avg F f‖ ≤ avg F fun i => ‖f i‖ := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp [avg]
  have hc : (0 : ℝ) < #F := by exact_mod_cast hF.card_pos
  rw [avg, avg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

lemma avg_real_mono {F : Finset ι} {f g : ι → ℝ} (h : ∀ i ∈ F, f i ≤ g i) :
    avg F f ≤ avg F g := by
  simp only [avg, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (by positivity)

lemma avg_real_nonneg {F : Finset ι} {f : ι → ℝ} (h : ∀ i ∈ F, 0 ≤ f i) : 0 ≤ avg F f := by
  simp only [avg, smul_eq_mul]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg h)

/-- The relative density of a set is the average of its indicator. -/
lemma relDens_eq_avg (F : Finset ι) (A : Set ι) :
    relDens F A = avg F fun i => if i ∈ A then (1 : ℝ) else 0 := by
  simp [relDens, avg, div_eq_inv_mul]

end Avg

/-! ## Følner sequences -/

section Folner

variable {Γ : Type*} [AddCommGroup Γ]

lemma _root_.Kmrr25.Q516.IsFolner.card_pos {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) (N : ℕ) : (0 : ℝ) < #(Φ N) := by
  exact_mod_cast (hΦ.1 N).card_pos

/-- A subsequence of a Følner sequence is a Følner sequence. -/
lemma _root_.Kmrr25.Q516.IsFolner.comp {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsFolner (Φ ∘ φ) :=
  ⟨fun N => hΦ.1 _, fun g => (hΦ.2 g).comp hφ.tendsto_atTop⟩

lemma card_inter_image_add_right (F : Finset Γ) (g h : Γ) :
    #(F.image (· + h) ∩ (F.image (· + h)).image (g + ·)) = #(F ∩ F.image (g + ·)) := by
  have : F.image (· + h) ∩ (F.image (· + h)).image (g + ·) = (F ∩ F.image (g + ·)).image (· + h) := by
    rw [Finset.image_inter_of_injOn _ _ ((add_left_injective h).injOn)]
    congr 1
    rw [Finset.image_image, Finset.image_image]
    congr 1
    funext x
    simp [add_comm, add_left_comm]
  rw [this, Finset.card_image_of_injective _ (add_left_injective h)]

/-- Translates `Φ_N + h_N` of a Følner sequence form a Følner sequence. -/
lemma _root_.Kmrr25.Q516.IsFolner.translate {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) (h : ℕ → Γ) :
    IsFolner fun N => (Φ N).image (· + h N) := by
  refine ⟨fun N => (hΦ.1 N).image _, fun g => ?_⟩
  refine (hΦ.2 g).congr fun N => ?_
  rw [card_inter_image_add_right, Finset.card_image_of_injective _ (add_left_injective _)]

/-- The defect `|Φ_N ∖ (g + Φ_N)| / |Φ_N|` of a Følner sequence tends to `0`. -/
lemma _root_.Kmrr25.Q516.IsFolner.tendsto_defect {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) (g : Γ) :
    Tendsto (fun N => (#(Φ N \ (Φ N).image (g + ·)) : ℝ) / #(Φ N)) atTop (𝓝 0) := by
  have h := (hΦ.2 g).const_sub 1
  rw [sub_self] at h
  refine h.congr fun N => ?_
  have hc := hΦ.card_pos N
  have := Finset.card_sdiff_add_card_inter (Φ N) ((Φ N).image (g + ·))
  have h' : (#(Φ N \ (Φ N).image (g + ·)) : ℝ) + #(Φ N ∩ (Φ N).image (g + ·)) = #(Φ N) := by
    exact_mod_cast this
  rw [show (#(Φ N \ (Φ N).image (g + ·)) : ℝ) = #(Φ N) - #(Φ N ∩ (Φ N).image (g + ·)) by linarith,
    sub_div, div_self hc.ne']

/-- Shifting the averaged function by `g` changes Følner averages by `o(1)`. -/
lemma norm_avg_shift_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Finset Γ) (hF : F.Nonempty) (f : Γ → E) {B : ℝ} (hB : ∀ γ, ‖f γ‖ ≤ B) (g : Γ) :
    ‖avg F (fun γ => f (g + γ)) - avg F f‖ ≤ 2 * B * ((#(F \ F.image (g + ·)) : ℝ) / #F) := by
  have hc : (0 : ℝ) < #F := by exact_mod_cast hF.card_pos
  have hsum : ∑ γ ∈ F, f (g + γ) = ∑ δ ∈ F.image (g + ·), f δ := by
    rw [Finset.sum_image fun x _ y _ h => add_left_cancel h]
  have hcard : #(F.image (g + ·) \ F) = #(F \ F.image (g + ·)) := by
    have h1 := Finset.card_sdiff_add_card_inter (F.image (g + ·)) F
    have h2 := Finset.card_sdiff_add_card_inter F (F.image (g + ·))
    rw [Finset.card_image_of_injective _ (add_right_injective g), Finset.inter_comm] at h1
    omega
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [avg, avg, ← smul_sub, hsum, ← Finset.sum_sdiff_sub_sum_sdiff, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hc]
  calc (#F : ℝ)⁻¹ * ‖∑ x ∈ F.image (g + ·) \ F, f x - ∑ x ∈ F \ F.image (g + ·), f x‖
      ≤ (#F : ℝ)⁻¹ * (B * #(F.image (g + ·) \ F) + B * #(F \ F.image (g + ·))) := by
        gcongr
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_sum fun x _ => hB x).trans ?_
          simp [mul_comm]
        · refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_sum fun x _ => hB x).trans ?_
          simp [mul_comm]
    _ = 2 * B * ((#(F \ F.image (g + ·)) : ℝ) / #F) := by
        rw [hcard]; field_simp; ring

lemma _root_.Kmrr25.Q516.IsFolner.tendsto_avg_shift_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) (f : Γ → E) {B : ℝ} (hB : ∀ γ, ‖f γ‖ ≤ B) (g : Γ) :
    Tendsto (fun N => avg (Φ N) (fun γ => f (g + γ)) - avg (Φ N) f) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (hΦ.tendsto_defect g).const_mul (2 * B)
  rw [mul_zero] at h
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun N => norm_avg_shift_sub_le _ (hΦ.1 N) f hB g) h

/-- Paper, Lemma \ref{K:lem:wiener}(a): Følner averages of a nontrivial character tend to `0`. -/
lemma _root_.Kmrr25.Q516.IsFolner.tendsto_avg_character {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) (ψ : Γ → ℂ)
    (hψ : ∀ a b, ψ (a + b) = ψ a * ψ b) (hψ1 : ∀ a, ‖ψ a‖ = 1) {g : Γ} (hg : ψ g ≠ 1) :
    Tendsto (fun N => avg (Φ N) ψ) atTop (𝓝 0) := by
  have h := hΦ.tendsto_avg_shift_sub ψ (B := 1) (fun γ => (hψ1 γ).le) g
  have hsh : ∀ N, avg (Φ N) (fun γ => ψ (g + γ)) - avg (Φ N) ψ = (ψ g - 1) * avg (Φ N) ψ := by
    intro N
    simp only [hψ, avg]
    rw [sub_mul, one_mul, ← Finset.mul_sum]
    simp only [Complex.real_smul]
    ring
  simp only [hsh] at h
  have h2 := h.const_mul (ψ g - 1)⁻¹
  rw [mul_zero] at h2
  refine h2.congr fun N => ?_
  rw [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hg), one_mul]

/-- Paper, Lemma \ref{K:lem:folner-grow}: in an infinite group, `|Φ_N| → ∞`. -/
lemma _root_.Kmrr25.Q516.IsFolner.tendsto_card [Infinite Γ] {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) :
    Tendsto (fun N => (#(Φ N) : ℝ)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  obtain ⟨F, hF⟩ := Infinite.exists_superset_card_eq (∅ : Finset Γ) (⌈b⌉₊ + 1) (by simp)
  have hsum : Tendsto (fun N => ∑ g ∈ F, (#(Φ N ∩ (Φ N).image (g + ·)) : ℝ) / #(Φ N)) atTop
      (𝓝 (∑ _g ∈ F, (1 : ℝ))) := tendsto_finsetSum _ fun g _ => hΦ.2 g
  simp only [Finset.sum_const, hF.2, nsmul_eq_mul, mul_one] at hsum
  have hlt : (⌈b⌉₊ : ℝ) < ((⌈b⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
  filter_upwards [hsum.eventually (lt_mem_nhds hlt)] with N hN
  have hc := hΦ.card_pos N
  -- counting: `∑_g |Φ ∩ (g + Φ)| ≤ |Φ|²`
  have hcount : ∑ g ∈ F, (#(Φ N ∩ (Φ N).image (g + ·)) : ℝ) ≤ #(Φ N) * #(Φ N) := by
    have : ∑ g ∈ F, #(Φ N ∩ (Φ N).image (g + ·)) ≤ ∑ x ∈ Φ N, #(F.filter fun g => x - g ∈ Φ N) := by
      rw [← Finset.card_sigma, ← Finset.card_sigma]
      refine Finset.card_le_card_of_injOn (fun p => ⟨p.2, p.1⟩) ?_ ?_
      · rintro ⟨g, x⟩ hp
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_inter, Finset.mem_image] at hp ⊢
        obtain ⟨hg, hx, y, hy, rfl⟩ := hp
        refine ⟨hx, Finset.mem_filter.2 ⟨hg, by simpa using hy⟩⟩
      · rintro ⟨g, x⟩ _ ⟨g', x'⟩ _ h
        simp only [Sigma.mk.inj_iff] at h
        obtain ⟨rfl, h2⟩ := h
        simp_all
    have h2 : ∑ x ∈ Φ N, #(F.filter fun g => x - g ∈ Φ N) ≤ ∑ _x ∈ Φ N, #(Φ N) := by
      refine Finset.sum_le_sum fun x _ => ?_
      refine Finset.card_le_card_of_injOn (fun g => x - g) (fun g hg => ?_) (fun g _ g' _ h => ?_)
      · exact (Finset.mem_filter.1 hg).2
      · simpa using h
    have := this.trans h2
    simp only [Finset.sum_const, smul_eq_mul] at this
    exact_mod_cast this
  rw [← Finset.sum_div, lt_div_iff₀ hc] at hN
  have : (⌈b⌉₊ : ℝ) < #(Φ N) := by nlinarith
  exact (Nat.le_ceil b).trans this.le

end Folner

/-! ## Generic points: facts (G1)–(G3) -/

section Generic

variable {Γ : Type*} [AddCommGroup Γ]
variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y]

/-- Genericity also holds for complex-valued continuous functions. -/
lemma IsGeneric.tendsto_complex {ν : Measure Y} [IsFiniteMeasure ν] [CompactSpace Y]
    {Φ : ℕ → Finset Γ} {y : Y} (hy : IsGeneric ν Φ y) (f : C(Y, ℂ)) :
    Tendsto (fun N => avg (Φ N) fun γ => f (γ +ᵥ y)) atTop (𝓝 (∫ x, f x ∂ν)) := by
  let fr : C(Y, ℝ) := ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(Y, ℝ) := ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
  have hr := hy fr
  have hi := hy fi
  have hf : Integrable (fun x => f x) ν :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint : ∫ x, f x ∂ν = ((∫ x, fr x ∂ν : ℝ) : ℂ) + ((∫ x, fi x ∂ν : ℝ) : ℂ) * Complex.I := by
    have hfr : Integrable (fun x => fr x) ν :=
      fr.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hfi : Integrable (fun x => fi x) ν :=
      fi.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_mul_const,
      ← integral_add hfr.ofReal (hfi.ofReal.mul_const _)]
    congr 1
    funext x
    simp [fr, fi, Complex.re_add_im]
  rw [hint]
  have := ((Complex.continuous_ofReal.tendsto _).comp hr).add
    (((Complex.continuous_ofReal.tendsto _).comp hi).mul_const Complex.I)
  refine this.congr fun N => ?_
  simp only [Function.comp, avg, fr, fi, ContinuousMap.coe_mk, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum, Complex.ofReal_natCast]
  rw [mul_assoc, ← mul_add, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Complex.re_add_im]

end Generic

section GenericFacts

variable {Γ : Type*} [AddCommGroup Γ]
variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y]

/-- Fact (G1): if `y` is generic for `ν` and `O` is open with `ν O > c`, then the return times
of `y` to `O` eventually have relative density `> c` in `Φ_N`. -/
lemma IsGeneric.eventually_lt_relDens [CompactSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    {ν : Measure Y} [IsFiniteMeasure ν] {Φ : ℕ → Finset Γ} {y : Y} (hy : IsGeneric ν Φ y)
    {O : Set Y} (hO : IsOpen O) {c : ℝ} (hc : ENNReal.ofReal c < ν O) :
    ∀ᶠ N in atTop, c < relDens (Φ N) {γ | γ +ᵥ y ∈ O} := by
  obtain ⟨F, hFO, hFc, hcF⟩ := hO.exists_lt_isClosed hc
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hO.isClosed_compl hFc
    (Set.disjoint_compl_left_iff_subset.2 hFO)
  have hint : c < ∫ x, f x ∂ν := by
    have h1 : ν.real F ≤ ∫ x, f x ∂ν := by
      rw [← integral_indicator_one hFc.measurableSet]
      refine integral_mono ((integrable_const 1).indicator hFc.measurableSet)
        (f.continuous.integrable_of_hasCompactSupport ?_) fun x => ?_
      · exact HasCompactSupport.of_compactSpace _
      · by_cases hx : x ∈ F
        · simp [hx, hf1 hx]
        · simp [hx, (hf01 x).1]
    have h2 : c < ν.real F := by
      rcases lt_or_ge c 0 with h | h
      · exact h.trans_le measureReal_nonneg
      · rw [measureReal_def]
        exact (ENNReal.ofReal_lt_iff_lt_toReal h (measure_ne_top _ _)).1 hcF
    linarith
  filter_upwards [(hy f).eventually (lt_mem_nhds hint)] with N hN
  refine hN.trans_le ?_
  rw [relDens_eq_avg]
  refine avg_real_mono fun γ _ => ?_
  by_cases h : γ +ᵥ y ∈ O
  · simp only [Set.mem_ofPred_eq, h, if_true]; exact (hf01 _).2
  · simp only [Set.mem_ofPred_eq, h, if_false]
    have := hf0 (show γ +ᵥ y ∈ Oᶜ from h)
    simp only [Pi.zero_apply] at this
    rw [this]

/-- Fact (G1), qualitative form: return times to an open set of positive measure have positive
lower density along `Φ`. -/
lemma IsGeneric.exists_eventually_lt_relDens [CompactSpace Y]
    [TopologicalSpace.PseudoMetrizableSpace Y]
    {ν : Measure Y} [IsFiniteMeasure ν] {Φ : ℕ → Finset Γ} {y : Y} (hy : IsGeneric ν Φ y)
    {O : Set Y} (hO : IsOpen O) (hpos : 0 < ν O) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in atTop, c < relDens (Φ N) {γ | γ +ᵥ y ∈ O} := by
  have hfin : ν O ≠ ⊤ := measure_ne_top _ _
  have hr : 0 < (ν O).toReal := ENNReal.toReal_pos hpos.ne' hfin
  refine ⟨(ν O).toReal / 2, by positivity, hy.eventually_lt_relDens hO ?_⟩
  rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hfin]
  linarith

/-- A set with relative density bounded below along a Følner sequence of an infinite group is
infinite. -/
lemma infinite_of_eventually_lt_relDens [Infinite Γ] {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ)
    {R : Set Γ} {c : ℝ} (hc : 0 < c) (h : ∀ᶠ N in atTop, c < relDens (Φ N) R) : R.Infinite := by
  intro hR
  have hlim : Tendsto (fun N => (hR.toFinset.card : ℝ) / #(Φ N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hΦ.tendsto_card
  obtain ⟨N, hN1, hN2⟩ := (h.and (hlim.eventually (gt_mem_nhds hc))).exists
  refine absurd hN1 (not_lt.2 (le_trans ?_ hN2.le))
  unfold relDens
  gcongr
  intro x hx
  simpa using (Finset.mem_filter.1 hx).2

/-- Fact (G2): the support of `ν` lies in the orbit closure of any point generic for `ν`. -/
lemma IsGeneric.support_subset [CompactSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    {ν : Measure Y} [IsFiniteMeasure ν] {Φ : ℕ → Finset Γ} {y : Y} (hy : IsGeneric ν Φ y) :
    ν.support ⊆ closure (Set.range fun γ : Γ => γ +ᵥ y) := by
  intro p hp
  rw [mem_closure_iff]
  intro O hO hpO
  have hpos : 0 < ν O := (Measure.mem_support_iff_forall p).1 hp O (hO.mem_nhds hpO)
  obtain ⟨c, hc, hev⟩ := hy.exists_eventually_lt_relDens hO hpos
  obtain ⟨N, hN⟩ := hev.exists
  have hpos' : 0 < #((Φ N).filter (fun γ => γ ∈ {γ | γ +ᵥ y ∈ O})) := by
    by_contra h0
    push_neg at h0
    unfold relDens at hN
    rw [Nat.le_zero.1 h0, Nat.cast_zero, zero_div] at hN
    linarith
  obtain ⟨γ, hγ⟩ := Finset.card_pos.1 hpos'
  exact ⟨γ +ᵥ y, (Finset.mem_filter.1 hγ).2, γ, rfl⟩

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [AddAction Γ Z]

/-- Fact (G3): continuous equivariant maps send generic points to generic points. -/
lemma IsGeneric.map {ν : Measure Y} {Φ : ℕ → Finset Γ} {y : Y} (hy : IsGeneric ν Φ y)
    {P : Y → Z} (hP : Continuous P) (hPe : ∀ (γ : Γ) x, P (γ +ᵥ x) = γ +ᵥ P x) :
    IsGeneric (ν.map P) Φ (P y) := by
  intro f
  rw [integral_map hP.aemeasurable f.continuous.aestronglyMeasurable]
  simpa [hPe] using hy (f.comp ⟨P, hP⟩)

/-- Images of support points under continuous maps lie in the support of the image measure. -/
lemma image_support_subset_support_map {ν : Measure Y} {P : Y → Z} (hP : Continuous P) :
    P '' ν.support ⊆ (ν.map P).support := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Measure.mem_support_iff_forall] at hx ⊢
  intro U hU
  exact (hx _ (hP.continuousAt.preimage_mem_nhds hU)).trans_le
    (Measure.le_map_apply hP.aemeasurable U)

end GenericFacts

/-! ## Ergodicity -/

section Ergodic

variable {Γ : Type*} [AddCommGroup Γ]
variable {Y : Type*} [MeasurableSpace Y] [AddAction Γ Y]

/-- For an ergodic measure, an a.e. invariant measurable map into a countably separated space is
a.e. constant. -/
lemma ErgodicVAdd.ae_eq_const {ν : Measure Y} [ErgodicVAdd Γ Y ν] {Z : Type*} [Nonempty Z]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] {g : Y → Z} (hg : Measurable g)
    (hinv : ∀ γ : Γ, (fun y => g (γ +ᵥ y)) =ᵐ[ν] g) : ∃ c : Z, g =ᵐ[ν] fun _ => c := by
  refine exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU => ?_
  have h := ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := Γ) (μ := ν) (hg hU)
    fun γ => (hinv γ).mono fun y hy => by
      have hy' : g (γ +ᵥ y) = g y := hy
      show (g (γ +ᵥ y) ∈ U) = (g y ∈ U)
      rw [hy']
  exact eventuallyConst_set.1 h

variable {Z : Type*} [MeasurableSpace Z] [AddAction Γ Z]

/-- A factor of an ergodic measure (under an everywhere equivariant measurable map) is ergodic. -/
lemma ErgodicVAdd.map {ν : Measure Y} [ErgodicVAdd Γ Y ν] {P : Y → Z} (hP : Measurable P)
    (hPe : ∀ (γ : Γ) x, P (γ +ᵥ x) = γ +ᵥ P x) [MeasurableConstVAdd Γ Y]
    [MeasurableConstVAdd Γ Z] : ErgodicVAdd Γ Z (ν.map P) where
  measure_preimage_vadd γ s hs := by
    rw [Measure.map_apply hP (hs.preimage (measurable_const_vadd γ)), Measure.map_apply hP hs]
    have : P ⁻¹' ((γ +ᵥ ·) ⁻¹' s) = (γ +ᵥ ·) ⁻¹' (P ⁻¹' s) := by
      ext x; simp [hPe]
    rw [this]
    exact VAddInvariantMeasure.measure_preimage_vadd (μ := ν) γ (hP hs)
  aeconst_of_forall_preimage_vadd_ae_eq {s} hs hinv := by
    have h := ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := Γ) (μ := ν) (hP hs)
      fun γ => by
        have h2 : ((γ +ᵥ ·) ⁻¹' s) ∘ P =ᵐ[ν] s ∘ P := ae_eq_comp hP.aemeasurable (hinv γ)
        refine EventuallyEq.trans (Eventually.of_forall fun x => ?_) h2
        show (P (γ +ᵥ x) ∈ s) = (γ +ᵥ P x ∈ s)
        rw [hPe]
    rw [eventuallyConst_set] at h ⊢
    rcases h with h | h
    · exact Or.inl ((ae_map_iff hP.aemeasurable hs).2 h)
    · exact Or.inr ((ae_map_iff hP.aemeasurable hs.compl).2 h)

end Ergodic

end Kmrr25.ThmK
