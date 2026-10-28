import Kmrr25.ThmKDisint

/-!
# Theorem K: the Kronecker factor and weak mixing

Paper, Lemma \ref{K:lem:kron}(c) and its consequences, in the form used later:

* `IsKroneckerMap.weakMixing_sub_tilde`: for a Kronecker map `κ` of `μ` and bounded `f`, the
  function `f - 𝔼(f | κ) = f - f̃ ∘ κ` is weakly mixing (this uses the classical input
  `WienerKoopman` and the eigenfunction property of `κ`);
* `WeakMixing.tilde_ae_eq_zero`: conversely, a weakly mixing function has `𝔼(v | κ) = 0` for
  every rotation factor `κ` (the characters of `K` composed with `κ` are eigenfunctions, and
  trigonometric polynomials are dense in `L²(m_K)`);
* `WeakMixing.comp`: weak mixing passes to pull-backs under factor maps.

We also record that compact metrizable spaces are Polish, so that disintegrations exist.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

universe u

/-- A compact metrizable space is Polish. -/
instance (priority := 50) polishSpace_of_compact_metrizable {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y] : PolishSpace Y := by
  let _ := TopologicalSpace.metrizableSpaceMetric Y
  have : CompleteSpace Y := complete_of_compact
  infer_instance

section Kron

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}
variable {Y : Type*} [MeasurableSpace Y] [AddAction Γ Y]
variable {μ : Measure Y} {κ : Y → KG α}

/-- Characters of `K` composed with a rotation factor are eigenfunctions. -/
lemma IsRotFactor.isEigenfunction_char (h : IsRotFactor μ α κ) {χ : C(KG α, ℂ)}
    (hχ : χ ∈ Chars α) : IsEigenfunction (Γ := Γ) μ (fun y => χ (κ y)) :=
  ⟨fun γ => χ (kα α γ), fun γ => (h.ae_equivariant γ).mono fun y hy => by
    simp only [hy, Chars.map_add hχ, mul_comm]⟩

variable [StandardBorelSpace Y] [Nonempty Y] [IsProbabilityMeasure μ]

lemma tilde_sub {F G : Y → ℂ} (hF : Bdd F) (hG : Bdd G) (z : KG α) :
    tilde μ κ (fun y => F y - G y) z = tilde μ κ F z - tilde μ κ G z :=
  integral_sub hF.integrable hG.integrable

lemma IsRotFactor.tilde_comp_tilde (h : IsRotFactor μ α κ) {F : Y → ℂ} :
    tilde μ κ (fun y => tilde μ κ F (κ y)) =ᵐ[haarK α] tilde μ κ F := by
  filter_upwards [h.ae_ae_fiber] with z hz
  unfold tilde
  rw [integral_congr_ae (hz.mono fun y hy => by rw [hy])]
  simp

/-- The function `f - f̃ ∘ κ` has vanishing conditional expectation. -/
lemma IsRotFactor.tilde_sub_tilde (h : IsRotFactor μ α κ) {F : Y → ℂ} (hF : Bdd F) :
    tilde μ κ (fun y => F y - tilde μ κ F (κ y)) =ᵐ[haarK α] 0 := by
  filter_upwards [h.tilde_comp_tilde (F := F)] with z hz
  rw [tilde_sub (G := fun y => tilde μ κ F (κ y)) hF (hF.tilde.comp h.measurable), hz, sub_self]
  rfl

/-- Paper, Lemma \ref{K:lem:kron}(c), the direction used: for a Kronecker map `κ`, the function
`f - 𝔼(f | κ)` is orthogonal to all eigenfunctions, hence weakly mixing. -/
theorem IsKroneckerMap.weakMixing_sub_tilde {Γ Y : Type u} [AddCommGroup Γ] [Countable Γ]
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [AddAction Γ Y] [ContinuousConstVAdd Γ Y] [Nonempty Y] {α : Γ →+ Torus}
    {μ : Measure Y} [IsProbabilityMeasure μ] [VAddInvariantMeasure Γ Y μ] {κ : Y → KG α}
    (hW : WienerKoopman.{u}) (h : IsKroneckerMap μ α κ) {F : Y → ℂ} (hF : Bdd F) :
    WeakMixing Γ μ (fun y => F y - tilde μ κ F (κ y)) := by
  have hv : Bdd fun y => F y - tilde μ κ F (κ y) := hF.sub (hF.tilde.comp h.measurable)
  have horth : ∀ g : Y → ℂ, MemLp g 2 μ → IsEigenfunction (Γ := Γ) μ g →
      ∫ y, (F y - tilde μ κ F (κ y)) * conj (g y) ∂μ = 0 := by
    intro g hg he
    obtain ⟨G, hGm, hgG⟩ := h.eigen g hg he
    have hGl2 : MemLp G 2 (haarK α) := by
      rw [← h.map_eq]
      exact (memLp_map_measure_iff hGm.aestronglyMeasurable h.measurable.aemeasurable).2
        (hg.ae_eq hgG)
    have hGint : Integrable (fun z => conj (G z)) (haarK α) :=
      (hGl2.integrable one_le_two).norm.mono'
        (Complex.continuous_conj.comp_aestronglyMeasurable hGm.aestronglyMeasurable)
        (Eventually.of_forall fun z => by simp)
    rw [integral_congr_ae (hgG.mono fun y hy => by rw [hy])]
    have := h.toRotFactor.integral_comp_mul_tilde (G := fun z => conj (G z))
      (Complex.continuous_conj.measurable.comp hGm) hGint hv
    simp only [Function.comp]
    rw [show (fun y => (F y - tilde μ κ F (κ y)) * conj (G (κ y))) =
        fun y => conj (G (κ y)) * (F y - tilde μ κ F (κ y)) from funext fun y => mul_comm _ _, this]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h.toRotFactor.tilde_sub_tilde hF] with z hz
    simp [hz]
  intro Θ hΘ
  exact hW Γ Y μ (fun y => F y - tilde μ κ F (κ y)) (hv.memLp 2) horth Θ hΘ

variable [MeasurableConstVAdd Γ Y] [VAddInvariantMeasure Γ Y μ]

/-- A weakly mixing function has vanishing conditional expectation onto any rotation factor
(paper, Lemma \ref{K:lem:kron}(c), the converse direction). -/
theorem WeakMixing.tilde_ae_eq_zero [Countable Γ] {v : Y → ℂ} (hv : Bdd v)
    (hwm : WeakMixing Γ μ v) (h : IsRotFactor μ α κ) : tilde μ κ v =ᵐ[haarK α] 0 := by
  have hwb : Bdd (tilde μ κ v) := hv.tilde
  -- `w` is orthogonal to every character
  have horth : ∀ χ ∈ Chars α, ∫ z, conj (χ z) * tilde μ κ v z ∂haarK α = 0 := by
    intro χ hχ
    have hχb : Bdd fun z : KG α => χ z := ⟨χ.continuous.measurable, 1,
      fun z => (Chars.norm_eq hχ z).le⟩
    have h1 := hwm.orthogonal_eigen hv ((hχb.comp h.measurable).memLp 2)
      (h.isEigenfunction_char hχ)
    have h2 := h.integral_comp_mul_tilde (G := fun z => conj (χ z))
      (Complex.continuous_conj.measurable.comp χ.continuous.measurable) hχb.conj'.integrable hv
    rw [← h2, ← h1]
    congr 1; funext y; rw [mul_comm]; rfl
  -- hence orthogonal to every trigonometric polynomial
  have horthP : ∀ P, IsTrig α P → ∫ z, conj (P z) * tilde μ κ v z ∂haarK α = 0 := by
    rintro _ ⟨t, c, ht, rfl⟩
    have hb : ∀ χ ∈ t, Bdd fun z => conj (c χ * χ z) * tilde μ κ v z := fun χ hχ =>
      ((Bdd.const (c χ)).mul ⟨χ.continuous.measurable, 1,
        fun z => (Chars.norm_eq (ht hχ) z).le⟩).conj'.mul hwb
    simp only [map_sum, Finset.sum_mul]
    rw [integral_finsetSum _ fun χ hχ => (hb χ hχ).integrable]
    refine Finset.sum_eq_zero fun χ hχ => ?_
    simp only [map_mul, mul_assoc]
    rw [integral_const_mul, horth χ (ht hχ), mul_zero]
  -- conclude by density
  have hA : ∫ z, ‖tilde μ κ v z‖ ^ 2 ∂haarK α = 0 := by
    set A := ∫ z, ‖tilde μ κ v z‖ ^ 2 ∂haarK α
    have hA0 : 0 ≤ A := integral_nonneg fun z => by positivity
    have key : ∀ ε > 0, A ^ 2 ≤ ε * A := by
      intro ε hε
      obtain ⟨P, hP, hwP⟩ := exists_trig_l2_approx hwb hε
      have e1 : ((A : ℝ) : ℂ) = ∫ z, conj (tilde μ κ v z - P z) * tilde μ κ v z ∂haarK α := by
        rw [← integral_complex_ofReal]
        have : (fun z => ((‖tilde μ κ v z‖ ^ 2 : ℝ) : ℂ)) =
            fun z => conj (tilde μ κ v z - P z) * tilde μ κ v z + conj (P z) * tilde μ κ v z := by
          funext z; rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sub]; ring
        rw [this, integral_add ((hwb.sub hP.bdd).conj'.mul hwb).integrable
          (hP.bdd.conj'.mul hwb).integrable, horthP P hP, add_zero]
      have hcs := norm_integral_mul_conj_sq_le (μ := haarK α) (hwb.memLp 2)
        ((hwb.sub hP.bdd).memLp 2)
      have : ∫ z, tilde μ κ v z * conj (tilde μ κ v z - P z) ∂haarK α = ((A : ℝ) : ℂ) := by
        rw [e1]; congr 1; funext z; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hcs
      calc A ^ 2 ≤ A * ∫ z, ‖tilde μ κ v z - P z‖ ^ 2 ∂haarK α := hcs
        _ ≤ A * ε := mul_le_mul_of_nonneg_left hwP.le hA0
        _ = ε * A := mul_comm _ _
    by_contra hne
    have hpos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hne)
    have := key (A / 2) (half_pos hpos)
    nlinarith
  have hint2 : Integrable (fun z => ‖tilde μ κ v z‖ ^ 2) (haarK α) :=
    (memLp_two_iff_integrable_sq_norm hwb.meas.aestronglyMeasurable).1 (hwb.memLp 2)
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun z => by positivity) hint2).1 hA] with z hz
  simpa using hz

end Kron

/-! ## Weak mixing and factor maps -/

section Factor

variable {Γ : Type*} [AddCommGroup Γ]
variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [AddAction Γ Y] [AddAction Γ Z]
  [MeasurableConstVAdd Γ Y] [MeasurableConstVAdd Γ Z]

omit [MeasurableConstVAdd Γ Y] in
lemma corr_comp {μ : Measure Y} {P : Y → Z} (hP : Measurable P)
    (hPe : ∀ (γ : Γ) y, P (γ +ᵥ y) = γ +ᵥ P y) {v : Z → ℂ} (hv : Measurable v) (β : Γ) :
    corr μ (fun y => v (P y)) β = corr (μ.map P) v β := by
  rw [corr, corr, integral_map hP.aemeasurable]
  · simp [hPe]
  · exact ((hv.comp (measurable_const_vadd β)).mul (Complex.continuous_conj.measurable.comp hv))
      |>.aestronglyMeasurable

lemma WeakMixing.comp {μ : Measure Y} {P : Y → Z} (hP : Measurable P)
    (hPe : ∀ (γ : Γ) y, P (γ +ᵥ y) = γ +ᵥ P y) {v : Z → ℂ} (hv : Measurable v)
    (hwm : WeakMixing Γ (μ.map P) v) : WeakMixing Γ μ (fun y => v (P y)) := by
  intro Θ hΘ
  simpa only [corr_comp hP hPe hv] using hwm Θ hΘ

end Factor

end Kmrr25.ThmK
