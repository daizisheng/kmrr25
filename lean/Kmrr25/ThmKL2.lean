import Kmrr25.ThmKGeneric

/-!
# Theorem K: correlations, double averages and weak mixing

Elementary Hilbert-space facts used in Section \ref{K:sec:main}, phrased for functions:

* `norm_integral_mul_conj_sq_le`: the Cauchy–Schwarz inequality in `L²`;
* `integral_normSq_sum`: `∫ |∑ a_γ v∘T^γ|² = ∑_{γ,δ} a_γ ā_δ ⟨v∘T^{γ-δ}, v⟩`;
* `tendsto_double_avg`: if `𝔼_{β ∈ Θ_M} |c(β)| → 0` along *every* Følner sequence, then the
  double averages `𝔼_{γ,δ ∈ Φ_N} |c(γ - δ)|` tend to `0` (translates of Følner sequences are
  Følner);
* consequences for a *weakly mixing* function `v` (one whose self-correlations have vanishing
  Cesàro averages along every Følner sequence): weighted averages of `v ∘ T^γ` tend to `0` in
  `L²` (`WeakMixing.tendsto_l2_avg`), the correlations with any bounded `g` have vanishing
  Cesàro averages (paper, Lemma \ref{K:lem:wiener}(d)), and `v` is orthogonal to every
  eigenfunction (`WeakMixing.orthogonal_eigen`).
-/

open Filter Topology Finset MeasureTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

open Q516

/-! ## Bounded measurable functions -/

/-- A bounded measurable complex function. -/
structure Bdd {Y : Type*} [MeasurableSpace Y] (f : Y → ℂ) : Prop where
  meas : Measurable f
  bound : ∃ C, ∀ y, ‖f y‖ ≤ C

namespace Bdd

variable {Y : Type*} [MeasurableSpace Y] {f g : Y → ℂ}

lemma exists_bound_nonneg (hf : Bdd f) : ∃ C, 0 ≤ C ∧ ∀ y, ‖f y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.bound
  exact ⟨max C 0, le_max_right _ _, fun y => (hC y).trans (le_max_left _ _)⟩

lemma add (hf : Bdd f) (hg : Bdd g) : Bdd (fun y => f y + g y) := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨D, hD⟩ := hg.bound
  exact ⟨hf.meas.add hg.meas, C + D, fun y => (norm_add_le _ _).trans (add_le_add (hC y) (hD y))⟩

lemma sub (hf : Bdd f) (hg : Bdd g) : Bdd (fun y => f y - g y) := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨D, hD⟩ := hg.bound
  exact ⟨hf.meas.sub hg.meas, C + D, fun y => (norm_sub_le _ _).trans (add_le_add (hC y) (hD y))⟩

lemma mul (hf : Bdd f) (hg : Bdd g) : Bdd (fun y => f y * g y) := by
  obtain ⟨C, hC0, hC⟩ := hf.exists_bound_nonneg
  obtain ⟨D, hD⟩ := hg.bound
  refine ⟨hf.meas.mul hg.meas, C * D, fun y => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC y) (hD y) (norm_nonneg _) hC0

lemma const_mul (hf : Bdd f) (c : ℂ) : Bdd (fun y => c * f y) := by
  obtain ⟨C, hC⟩ := hf.bound
  refine ⟨hf.meas.const_mul c, ‖c‖ * C, fun y => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)

lemma conj' (hf : Bdd f) : Bdd (fun y => conj (f y)) := by
  obtain ⟨C, hC⟩ := hf.bound
  exact ⟨Complex.continuous_conj.measurable.comp hf.meas, C, fun y => by simpa using hC y⟩

lemma const (c : ℂ) : Bdd (fun _ : Y => c) := ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

lemma comp {Z : Type*} [MeasurableSpace Z] {f : Z → ℂ} (hf : Bdd f) {P : Y → Z}
    (hP : Measurable P) : Bdd (f ∘ P) :=
  ⟨hf.meas.comp hP, by obtain ⟨C, hC⟩ := hf.bound; exact ⟨C, fun y => hC (P y)⟩⟩

lemma indicator {s : Set Y} (hs : MeasurableSet s) : Bdd (s.indicator fun _ => (1 : ℂ)) :=
  ⟨measurable_const.indicator hs, 1, fun y => by
    by_cases h : y ∈ s <;> simp [h]⟩

lemma sum {ι : Type*} (F : Finset ι) {f : ι → Y → ℂ} (hf : ∀ i ∈ F, Bdd (f i)) :
    Bdd (fun y => ∑ i ∈ F, f i y) := by
  induction F using Finset.induction_on with
  | empty => simpa using const (Y := Y) 0
  | insert a F ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma smul_real (hf : Bdd f) (c : ℝ) : Bdd (fun y => c • f y) := by
  simpa [Complex.real_smul] using hf.const_mul (c : ℂ)

lemma avg {ι : Type*} (F : Finset ι) {f : ι → Y → ℂ} (hf : ∀ i ∈ F, Bdd (f i)) :
    Bdd (fun y => ThmK.avg F fun i => f i y) := by
  simp only [ThmK.avg]
  exact (sum F hf).smul_real _

variable {μ : Measure Y}

lemma integrable [IsFiniteMeasure μ] (hf : Bdd f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hf.bound
  exact Integrable.of_bound hf.meas.aestronglyMeasurable C (Eventually.of_forall hC)

lemma memLp [IsFiniteMeasure μ] (hf : Bdd f) (p : ENNReal) : MemLp f p μ := by
  obtain ⟨C, hC⟩ := hf.bound
  exact MemLp.of_bound hf.meas.aestronglyMeasurable C (Eventually.of_forall hC)

lemma norm_integral_le [IsProbabilityMeasure μ] {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ‖∫ y, f y ∂μ‖ ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
    (Eventually.of_forall hC)
  simpa using this

end Bdd

lemma avg_ofReal {ι : Type*} (F : Finset ι) (f : ι → ℝ) :
    (avg F fun i => ((f i : ℝ) : ℂ)) = ((avg F f : ℝ) : ℂ) := by
  simp [avg, Complex.ofReal_sum]

/-! ## Cauchy–Schwarz -/

section CS

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

/-- Real Cauchy–Schwarz inequality for integrals. -/
lemma integral_mul_sq_le {F G : Y → ℝ} (hF : Integrable (fun y => F y ^ 2) μ)
    (hG : Integrable (fun y => G y ^ 2) μ) (hFG : Integrable (fun y => F y * G y) μ) :
    (∫ y, F y * G y ∂μ) ^ 2 ≤ (∫ y, F y ^ 2 ∂μ) * ∫ y, G y ^ 2 ∂μ := by
  have h : ∀ t : ℝ, 0 ≤ (∫ y, G y ^ 2 ∂μ) * (t * t) + (-2 * ∫ y, F y * G y ∂μ) * t +
      ∫ y, F y ^ 2 ∂μ := by
    intro t
    have hint : ∫ y, (F y - t * G y) ^ 2 ∂μ = (∫ y, G y ^ 2 ∂μ) * (t * t) +
        (-2 * ∫ y, F y * G y ∂μ) * t + ∫ y, F y ^ 2 ∂μ := by
      have : (fun y => (F y - t * G y) ^ 2) =
          fun y => F y ^ 2 + (-(2 * t) * (F y * G y) + t ^ 2 * G y ^ 2) := by
        funext y; ring
      have h2 : Integrable (fun y => -(2 * t) * (F y * G y) + t ^ 2 * G y ^ 2) μ :=
        (hFG.const_mul _).add (hG.const_mul _)
      rw [this, integral_add hF h2,
        integral_add (hFG.const_mul _) (hG.const_mul _), integral_const_mul, integral_const_mul]
      ring
    rw [← hint]
    exact integral_nonneg fun y => sq_nonneg _
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith

/-- Pointwise bound making products of `L²` functions integrable. -/
lemma integrable_norm_mul_norm {f g : Y → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun y => ‖f y‖ * ‖g y‖) μ := by
  have hf2 := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  refine Integrable.mono' ((hf2.add hg2).div_const 2)
    (hf.1.norm.mul hg.1.norm) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  show ‖f y‖ * ‖g y‖ ≤ (‖f y‖ ^ 2 + ‖g y‖ ^ 2) / 2
  nlinarith [sq_nonneg (‖f y‖ - ‖g y‖)]

lemma integrable_mul_conj {f g : Y → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun y => f y * conj (g y)) μ := by
  refine (integrable_norm_mul_norm hf hg).mono' (hf.1.mul hg.1.star) ?_
  exact Eventually.of_forall fun y => by simp

/-- Cauchy–Schwarz in `L²(μ)`: `|⟨f, g⟩|² ≤ ‖f‖₂² ‖g‖₂²`. -/
lemma norm_integral_mul_conj_sq_le {f g : Y → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ y, f y * conj (g y) ∂μ‖ ^ 2 ≤ (∫ y, ‖f y‖ ^ 2 ∂μ) * ∫ y, ‖g y‖ ^ 2 ∂μ := by
  have h1 : ‖∫ y, f y * conj (g y) ∂μ‖ ≤ ∫ y, ‖f y‖ * ‖g y‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext y; simp
  have h2 := integral_mul_sq_le (μ := μ) (F := fun y => ‖f y‖) (G := fun y => ‖g y‖)
    ((memLp_two_iff_integrable_sq_norm hf.1).1 hf) ((memLp_two_iff_integrable_sq_norm hg.1).1 hg)
    (integrable_norm_mul_norm hf hg)
  calc ‖∫ y, f y * conj (g y) ∂μ‖ ^ 2 ≤ (∫ y, ‖f y‖ * ‖g y‖ ∂μ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- `∫ |f + g|² ≤ 2 ∫ |f|² + 2 ∫ |g|²`. -/
lemma integral_norm_add_sq_le {f g : Y → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ y, ‖f y + g y‖ ^ 2 ∂μ ≤ 2 * ∫ y, ‖f y‖ ^ 2 ∂μ + 2 * ∫ y, ‖g y‖ ^ 2 ∂μ := by
  have hf2 := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hf2.const_mul _)
    (hg2.const_mul _)]
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity)
    ((hf2.const_mul _).add (hg2.const_mul _)) (Eventually.of_forall fun y => ?_)
  have := norm_add_le (f y) (g y)
  nlinarith [sq_nonneg (‖f y‖ - ‖g y‖), norm_nonneg (f y + g y)]

end CS

/-! ## Correlations -/

section Corr

variable {Γ : Type*} [AddCommGroup Γ]
variable {Y : Type*} [MeasurableSpace Y] [AddAction Γ Y] [MeasurableConstVAdd Γ Y]

/-- The correlation `⟨v ∘ T^β, v⟩_μ`. -/
def corr (μ : Measure Y) (v : Y → ℂ) (β : Γ) : ℂ := ∫ y, v (β +ᵥ y) * conj (v y) ∂μ

variable {μ : Measure Y} [VAddInvariantMeasure Γ Y μ]

lemma integral_vadd (F : Y → ℂ) (c : Γ) : ∫ y, F (c +ᵥ y) ∂μ = ∫ y, F y ∂μ :=
  integral_vadd_eq_self F

lemma integral_shift_mul_conj (v : Y → ℂ) (γ δ : Γ) :
    ∫ y, v (γ +ᵥ y) * conj (v (δ +ᵥ y)) ∂μ = corr μ v (γ - δ) := by
  rw [corr, ← integral_vadd (μ := μ) _ (-δ)]
  congr 1; funext y
  simp only [vadd_vadd, sub_eq_add_neg, add_neg_cancel, zero_vadd]

/-- `∫ |∑_{γ∈F} a_γ v(T^γ y)|² dμ = ∑_{γ,δ ∈ F} a_γ ā_δ ⟨v∘T^{γ-δ}, v⟩`. -/
lemma integral_normSq_sum [IsFiniteMeasure μ] {v : Y → ℂ} (hv : Bdd v) (F : Finset Γ)
    (a : Γ → ℂ) :
    ((∫ y, ‖∑ γ ∈ F, a γ * v (γ +ᵥ y)‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ∑ γ ∈ F, ∑ δ ∈ F, a γ * conj (a δ) * corr μ v (γ - δ) := by
  have hb : ∀ γ : Γ, Bdd fun y => v (γ +ᵥ y) := fun γ => hv.comp (measurable_const_vadd γ)
  rw [← integral_complex_ofReal]
  have : (fun y => ((‖∑ γ ∈ F, a γ * v (γ +ᵥ y)‖ ^ 2 : ℝ) : ℂ)) =
      fun y => ∑ γ ∈ F, ∑ δ ∈ F, a γ * conj (a δ) * (v (γ +ᵥ y) * conj (v (δ +ᵥ y))) := by
    funext y
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
    simp only [map_mul]; ring
  rw [this, integral_finsetSum]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun δ _ => ?_
      rw [integral_const_mul, integral_shift_mul_conj]
    · intro δ _
      exact (((hb γ).mul (hb δ).conj').integrable).const_mul _
  · intro γ _
    refine integrable_finsetSum _ fun δ _ => ?_
    exact (((hb γ).mul (hb δ).conj').integrable).const_mul _

lemma norm_corr_le [IsProbabilityMeasure μ] {v : Y → ℂ} {C : ℝ} (hv : ∀ y, ‖v y‖ ≤ C) (β : Γ) :
    ‖corr μ v β‖ ≤ C ^ 2 := by
  have : ∀ y, ‖v (β +ᵥ y) * conj (v y)‖ ≤ C ^ 2 := fun y => by
    rw [norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul (hv _) (hv _) (norm_nonneg _) ((norm_nonneg (v y)).trans (hv y))
  exact Bdd.norm_integral_le (μ := μ) this

end Corr

/-! ## Double averages -/

section DoubleAvg

variable {Γ : Type*} [AddCommGroup Γ]

lemma avg_comm {ι : Type*} (F : Finset ι) (g : ι → ι → ℝ) :
    (avg F fun i => avg F fun j => g i j) = avg F fun j => avg F fun i => g i j := by
  simp only [avg, smul_eq_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]

lemma avg_comp_sub (F : Finset Γ) (f : Γ → ℝ) (δ : Γ) :
    (avg F fun γ => f (γ - δ)) = avg (F.image (· + (-δ))) f := by
  simp only [avg]
  rw [Finset.sum_image fun x _ y _ h => add_right_cancel h,
    Finset.card_image_of_injective _ (add_left_injective _)]
  simp [sub_eq_add_neg]

/-- If `𝔼_{β∈Θ_M} c(β) → 0` along every Følner sequence (with `c ≥ 0`), then the double averages
`𝔼_{γ,δ ∈ Φ_N} c(γ - δ)` tend to `0` along every Følner sequence. -/
theorem tendsto_double_avg {c : Γ → ℝ} (hc0 : ∀ β, 0 ≤ c β)
    (hc : ∀ Θ : ℕ → Finset Γ, IsFolner Θ → Tendsto (fun M => avg (Θ M) c) atTop (𝓝 0))
    {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) :
    Tendsto (fun N => avg (Φ N) fun γ => avg (Φ N) fun δ => c (γ - δ)) atTop (𝓝 0) := by
  have hmax : ∀ N, ∃ δ ∈ Φ N, ∀ δ' ∈ Φ N,
      (avg (Φ N) fun γ => c (γ - δ')) ≤ avg (Φ N) fun γ => c (γ - δ) :=
    fun N => Finset.exists_max_image _ _ (hΦ.1 N)
  choose δ hδ hδmax using hmax
  have ht := hc _ (hΦ.translate fun N => -δ N)
  refine squeeze_zero (fun N => avg_real_nonneg fun γ _ => avg_real_nonneg fun δ _ => hc0 _)
    (fun N => ?_) ht
  rw [avg_comm, ← avg_comp_sub]
  calc (avg (Φ N) fun δ' => avg (Φ N) fun γ => c (γ - δ'))
      ≤ avg (Φ N) fun _ => avg (Φ N) fun γ => c (γ - δ N) := avg_real_mono fun δ' h => hδmax N δ' h
    _ = _ := avg_const (hΦ.1 N) _

end DoubleAvg

/-! ## Weak mixing -/

section WeakMixing

variable (Γ : Type*) [AddCommGroup Γ]
variable {Y : Type*} [MeasurableSpace Y] [AddAction Γ Y] [MeasurableConstVAdd Γ Y]

/-- `v` is *weakly mixing* for `μ`: its self-correlations have vanishing Cesàro averages along
every Følner sequence. (By `WienerKoopman`, this holds for every `v` orthogonal to all
eigenfunctions.) -/
def WeakMixing (μ : Measure Y) (v : Y → ℂ) : Prop :=
  ∀ Θ : ℕ → Finset Γ, IsFolner Θ →
    Tendsto (fun M => avg (Θ M) fun β => ‖corr (Γ := Γ) μ v β‖) atTop (𝓝 0)

variable {Γ} {μ : Measure Y} [IsProbabilityMeasure μ] [VAddInvariantMeasure Γ Y μ]

lemma integral_norm_avg_sq (F : Finset Γ) (f : Γ → Y → ℂ) :
    (∫ y, ‖avg F (fun γ => f γ y)‖ ^ 2 ∂μ) =
      ((#F : ℝ)⁻¹) ^ 2 * ∫ y, ‖∑ γ ∈ F, f γ y‖ ^ 2 ∂μ := by
  rw [← integral_const_mul]
  congr 1; funext y
  rw [avg, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, Nat.abs_cast]

/-- Weighted Følner averages of translates of a weakly mixing function tend to `0` in `L²`. -/
theorem WeakMixing.tendsto_l2_avg {v : Y → ℂ} (hv : Bdd v) (hwm : WeakMixing Γ μ v)
    {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) (a : ℕ → Γ → ℂ) (ha : ∀ N γ, ‖a N γ‖ ≤ 1) :
    Tendsto (fun N => ∫ y, ‖avg (Φ N) (fun γ => a N γ * v (γ +ᵥ y))‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hd := tendsto_double_avg (c := fun β => ‖corr (Γ := Γ) μ v β‖) (fun _ => norm_nonneg _)
    hwm hΦ
  refine squeeze_zero (fun N => integral_nonneg fun y => by positivity) (fun N => ?_) hd
  rw [integral_norm_avg_sq]
  have hc := hΦ.card_pos N
  have key := integral_normSq_sum (μ := μ) hv (Φ N) (a N)
  have h1 : (∫ y, ‖∑ γ ∈ Φ N, a N γ * v (γ +ᵥ y)‖ ^ 2 ∂μ) ≤
      ∑ γ ∈ Φ N, ∑ δ ∈ Φ N, ‖corr (Γ := Γ) μ v (γ - δ)‖ := by
    have h0 : 0 ≤ ∫ y, ‖∑ γ ∈ Φ N, a N γ * v (γ +ᵥ y)‖ ^ 2 ∂μ :=
      integral_nonneg fun y => by positivity
    calc (∫ y, ‖∑ γ ∈ Φ N, a N γ * v (γ +ᵥ y)‖ ^ 2 ∂μ)
        = ‖((∫ y, ‖∑ γ ∈ Φ N, a N γ * v (γ +ᵥ y)‖ ^ 2 ∂μ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      _ = ‖∑ γ ∈ Φ N, ∑ δ ∈ Φ N, a N γ * conj (a N δ) * corr μ v (γ - δ)‖ := by rw [key]
      _ ≤ ∑ γ ∈ Φ N, ∑ δ ∈ Φ N, ‖a N γ * conj (a N δ) * corr μ v (γ - δ)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun γ _ => norm_sum_le _ _)
      _ ≤ _ := by
          refine Finset.sum_le_sum fun γ _ => Finset.sum_le_sum fun δ _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj]
          have := ha N γ; have := ha N δ
          have h3 : ‖a N γ‖ * ‖a N δ‖ ≤ 1 := by nlinarith [norm_nonneg (a N γ), norm_nonneg (a N δ)]
          nlinarith [norm_nonneg (corr (Γ := Γ) μ v (γ - δ)), norm_nonneg (a N γ),
            norm_nonneg (a N δ)]
  calc ((#(Φ N) : ℝ)⁻¹) ^ 2 * ∫ y, ‖∑ γ ∈ Φ N, a N γ * v (γ +ᵥ y)‖ ^ 2 ∂μ
      ≤ ((#(Φ N) : ℝ)⁻¹) ^ 2 * ∑ γ ∈ Φ N, ∑ δ ∈ Φ N, ‖corr (Γ := Γ) μ v (γ - δ)‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by
        simp only [avg, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
        ring

/-- The phase `z̄ / |z|` (equal to `0` at `z = 0`), so that `phase z * z = |z|`. -/
def phase (z : ℂ) : ℂ := conj z / (‖z‖ : ℂ)

lemma norm_phase_le (z : ℂ) : ‖phase z‖ ≤ 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [phase]
  · rw [phase, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 hz)]

lemma phase_mul_self (z : ℂ) : phase z * z = (‖z‖ : ℂ) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [phase]
  · have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
    rw [phase, div_mul_eq_mul_div, mul_comm, Complex.mul_conj', div_eq_iff this]
    push_cast; ring

/-- The integral `∫ (𝔼_γ a_γ v∘T^γ) ḡ` is the average of the weighted correlations. -/
lemma integral_avg_mul_conj {v g : Y → ℂ} (hv : Bdd v) (hg : Bdd g) (F : Finset Γ) (a : Γ → ℂ) :
    ∫ y, avg F (fun γ => a γ * v (γ +ᵥ y)) * conj (g y) ∂μ =
      avg F fun γ => a γ * ∫ y, v (γ +ᵥ y) * conj (g y) ∂μ := by
  simp only [avg, Finset.smul_sum, Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    have : (fun y => (#F : ℝ)⁻¹ • (a γ * v (γ +ᵥ y)) * conj (g y)) =
        fun y => ((#F : ℝ)⁻¹ * a γ : ℂ) * (v (γ +ᵥ y) * conj (g y)) := by
      funext y; simp only [Complex.real_smul]; ring
    rw [this, integral_const_mul, Complex.real_smul]
    push_cast
    ring
  · intro γ _
    have : Bdd fun y => (#F : ℝ)⁻¹ • (a γ * v (γ +ᵥ y)) * conj (g y) :=
      (((hv.comp (measurable_const_vadd γ)).const_mul (a γ)).smul_real _).mul hg.conj'
    exact this.integrable

/-- Paper, Lemma \ref{K:lem:wiener}(d): correlations of a weakly mixing function with any bounded
function have vanishing Cesàro averages. -/
theorem WeakMixing.tendsto_avg_norm_inner {v : Y → ℂ} (hv : Bdd v) (hwm : WeakMixing Γ μ v)
    {g : Y → ℂ} (hg : Bdd g) {Θ : ℕ → Finset Γ} (hΘ : IsFolner Θ) :
    Tendsto (fun M => avg (Θ M) fun β => ‖∫ y, v (β +ᵥ y) * conj (g y) ∂μ‖) atTop (𝓝 0) := by
  set z : Γ → ℂ := fun β => ∫ y, v (β +ᵥ y) * conj (g y) ∂μ
  have hl2 := hwm.tendsto_l2_avg hv hΘ (fun _ β => phase (z β)) fun _ _ => norm_phase_le _
  obtain ⟨C, hC0, hC⟩ := hg.exists_bound_nonneg
  have hgl2 : ∫ y, ‖g y‖ ^ 2 ∂μ ≤ C ^ 2 := by
    calc ∫ y, ‖g y‖ ^ 2 ∂μ ≤ ∫ _y, C ^ 2 ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity)
            (integrable_const _) (Eventually.of_forall fun y => pow_le_pow_left₀ (norm_nonneg _) (hC y) 2)
      _ = C ^ 2 := by simp
  -- squared averages are bounded by `‖𝔼 a v∘T‖₂² ‖g‖₂²`
  have hsq : ∀ M, (avg (Θ M) fun β => ‖z β‖) ^ 2 ≤
      C ^ 2 * ∫ y, ‖avg (Θ M) (fun γ => phase (z γ) * v (γ +ᵥ y))‖ ^ 2 ∂μ := by
    intro M
    have h1 : ((avg (Θ M) fun β => ‖z β‖ : ℝ) : ℂ) =
        ∫ y, avg (Θ M) (fun γ => phase (z γ) * v (γ +ᵥ y)) * conj (g y) ∂μ := by
      rw [integral_avg_mul_conj hv hg]
      have : (fun γ => phase (z γ) * ∫ y, v (γ +ᵥ y) * conj (g y) ∂μ) =
          fun γ => ((‖z γ‖ : ℝ) : ℂ) := funext fun γ => phase_mul_self (z γ)
      rw [this, avg_ofReal]
    have hmem : MemLp (fun y => avg (Θ M) (fun γ => phase (z γ) * v (γ +ᵥ y))) 2 μ :=
      (Bdd.avg (Θ M) fun γ _ => (hv.comp (measurable_const_vadd γ)).const_mul _).memLp 2
    have h2 := norm_integral_mul_conj_sq_le hmem (hg.memLp 2)
    rw [← h1, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h2
    calc _ ≤ _ := h2
      _ ≤ (∫ y, ‖avg (Θ M) (fun γ => phase (z γ) * v (γ +ᵥ y))‖ ^ 2 ∂μ) * C ^ 2 :=
          mul_le_mul_of_nonneg_left hgl2 (integral_nonneg fun y => by positivity)
      _ = _ := mul_comm _ _
  have hlim : Tendsto (fun M => (avg (Θ M) fun β => ‖z β‖) ^ 2) atTop (𝓝 0) := by
    have := hl2.const_mul (C ^ 2)
    rw [mul_zero] at this
    exact squeeze_zero (fun M => sq_nonneg _) hsq this
  have hnn : ∀ M, 0 ≤ avg (Θ M) fun β => ‖z β‖ := fun M => avg_real_nonneg fun β _ => norm_nonneg _
  have := (Real.continuous_sqrt.tendsto 0).comp hlim
  simp only [Function.comp, Real.sqrt_zero] at this
  refine this.congr fun M => ?_
  simp only [Function.comp_apply]
  rw [Real.sqrt_sq (hnn M)]

/-- A weakly mixing bounded function is orthogonal to every `L²` eigenfunction. -/
theorem WeakMixing.orthogonal_eigen [Countable Γ] {v : Y → ℂ} (hv : Bdd v)
    (hwm : WeakMixing Γ μ v) {h : Y → ℂ} (hh : MemLp h 2 μ) (he : IsEigenfunction (Γ := Γ) μ h) :
    ∫ y, v y * conj (h y) ∂μ = 0 := by
  obtain ⟨ψ, hψ⟩ := he
  set A := ∫ y, ‖h y‖ ^ 2 ∂μ
  have hA0 : 0 ≤ A := integral_nonneg fun y => by positivity
  rcases hA0.eq_or_lt with hA | hA
  · -- `h = 0` a.e.
    have hh2 := (memLp_two_iff_integrable_sq_norm hh.1).1 hh
    have h0 : (fun y => ‖h y‖ ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y => by positivity) hh2).1 hA.symm
    rw [integral_eq_zero_of_ae]
    filter_upwards [h0] with y hy
    have : h y = 0 := by simpa using hy
    simp [this]
  -- `|ψ γ| = 1`
  have hψ1 : ∀ γ, ‖ψ γ‖ = 1 := by
    intro γ
    have h1 : ∫ y, ‖h (γ +ᵥ y)‖ ^ 2 ∂μ = A := integral_vadd_eq_self (fun y => ‖h y‖ ^ 2)
    have h2 : ∫ y, ‖h (γ +ᵥ y)‖ ^ 2 ∂μ = ‖ψ γ‖ ^ 2 * A := by
      rw [← integral_const_mul]
      refine integral_congr_ae ((hψ γ).mono fun y hy => ?_)
      simp only [hy, norm_mul, mul_pow]
    have : ‖ψ γ‖ ^ 2 = 1 := by
      have := h1.symm.trans h2
      field_simp at this
      linarith
    have h0 := norm_nonneg (ψ γ)
    refine le_antisymm ?_ ?_ <;> nlinarith
  have hb : ∀ γ : Γ, Bdd fun y => v (γ +ᵥ y) := fun γ => hv.comp (measurable_const_vadd γ)
  have hI : ∀ γ, ∫ y, v (γ +ᵥ y) * conj (h y) ∂μ = ψ γ * ∫ y, v y * conj (h y) ∂μ := by
    intro γ
    have e1 : ∫ y, v y * conj (h y) ∂μ = conj (ψ γ) * ∫ y, v (γ +ᵥ y) * conj (h y) ∂μ := by
      rw [← integral_vadd_eq_self (μ := μ) (fun y => v y * conj (h y)) (g := γ),
        ← integral_const_mul]
      refine integral_congr_ae ((hψ γ).mono fun y hy => ?_)
      simp only [hy, map_mul]; ring
    rw [e1, ← mul_assoc, Complex.mul_conj', hψ1]; simp
  obtain ⟨Φ, hΦ⟩ := Q516.exists_folner (G := Γ)
  have hl2 := hwm.tendsto_l2_avg hv hΦ (fun _ γ => conj (ψ γ)) fun _ γ => by
    rw [Complex.norm_conj, hψ1]
  have hbound : ∀ N, ‖∫ y, v y * conj (h y) ∂μ‖ ^ 2 ≤
      (∫ y, ‖avg (Φ N) (fun γ => conj (ψ γ) * v (γ +ᵥ y))‖ ^ 2 ∂μ) * A := by
    intro N
    have hmem : MemLp (fun y => avg (Φ N) (fun γ => conj (ψ γ) * v (γ +ᵥ y))) 2 μ :=
      (Bdd.avg (Φ N) fun γ _ => (hb γ).const_mul _).memLp 2
    have e2 : ∫ y, avg (Φ N) (fun γ => conj (ψ γ) * v (γ +ᵥ y)) * conj (h y) ∂μ =
        ∫ y, v y * conj (h y) ∂μ := by
      simp only [avg, Finset.smul_sum, Finset.sum_mul]
      rw [integral_finsetSum]
      · have : ∀ γ ∈ Φ N, ∫ y, (#(Φ N) : ℝ)⁻¹ • (conj (ψ γ) * v (γ +ᵥ y)) * conj (h y) ∂μ =
            (#(Φ N) : ℝ)⁻¹ • ∫ y, v y * conj (h y) ∂μ := by
          intro γ _
          have : (fun y => (#(Φ N) : ℝ)⁻¹ • (conj (ψ γ) * v (γ +ᵥ y)) * conj (h y)) =
              fun y => ((#(Φ N) : ℝ)⁻¹ * conj (ψ γ) : ℂ) * (v (γ +ᵥ y) * conj (h y)) := by
            funext y; simp only [Complex.real_smul]; ring
          rw [this, integral_const_mul, hI, Complex.real_smul, ← mul_assoc, mul_assoc _ _ (ψ γ),
            mul_comm (conj (ψ γ)), Complex.mul_conj', hψ1]
          simp
        rw [Finset.sum_congr rfl this, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
          mul_inv_cancel₀ (hΦ.card_pos N).ne', one_smul]
      · intro γ _
        exact integrable_mul_conj (((hb γ).const_mul _).smul_real _ |>.memLp 2) hh
    have := norm_integral_mul_conj_sq_le hmem hh
    rwa [e2] at this
  have hlim : Tendsto (fun N => (∫ y, ‖avg (Φ N) (fun γ => conj (ψ γ) * v (γ +ᵥ y))‖ ^ 2 ∂μ) * A)
      atTop (𝓝 0) := by simpa using hl2.mul_const A
  have h5 : ‖∫ y, v y * conj (h y) ∂μ‖ ^ 2 ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hbound)
  have : ‖∫ y, v y * conj (h y) ∂μ‖ = 0 := by
    nlinarith [norm_nonneg (∫ y, v y * conj (h y) ∂μ)]
  exact norm_eq_zero.1 this

end WeakMixing

end Kmrr25.ThmK
