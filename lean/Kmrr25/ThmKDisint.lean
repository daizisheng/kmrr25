import Kmrr25.ThmKHaar

/-!
# Theorem K: disintegration over a rotation factor and relative products

Paper, Section \ref{K:ssec:prelim} (*Disintegrations*) and Definition \ref{K:def:J},
Lemma \ref{K:lem:J}(a),(b).

Let `κ : Y → K` be a measurable map with `κ_* μ = m_K` which is a.e. equivariant
(`IsRotFactor`). The disintegration `z ↦ μ_z` is Mathlib's conditional kernel of the joint law of
`(κ, id)` (`dis`), and `f̃(z) = ∫ f dμ_z` (`tilde`). We prove

* `integral_comp_mul_tilde`: `∫ G(κ y) f(y) dμ = ∫ G f̃ dm_K` (so `f̃ ∘ κ = 𝔼(f | κ)`);
* `ae_tilde_vadd`: `(f ∘ T^γ)~ = f̃(· + α γ)` a.e.;
* the relative products `J t = ∫ μ_z ⊗ μ_{z+t} dm_K(z)` (`relJ`): the product formula
  (Lemma \ref{K:lem:J}(a)), both marginals equal `μ`, invariance under the diagonal action,
  and concentration on `{κ y' = κ y + t}` (Lemma \ref{K:lem:J}(b)).
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

/-! ## Two measure-theoretic tools -/

/-- Two finite measures on a product space which agree on measurable rectangles are equal. -/
lemma measure_prod_ext {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {μ ν : Measure (Y × Z)} [IsFiniteMeasure μ]
    (h : ∀ A B, MeasurableSet A → MeasurableSet B → μ (A ×ˢ B) = ν (A ×ˢ B)) : μ = ν := by
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact h A B hA hB
  · rw [← Set.univ_prod_univ]
    exact h _ _ MeasurableSet.univ MeasurableSet.univ

/-- Two bounded measurable functions whose integrals against every bounded measurable function
agree are a.e. equal. -/
lemma ae_eq_of_forall_integral_mul_eq {K : Type*} [MeasurableSpace K] {m : Measure K}
    [IsFiniteMeasure m] {h1 h2 : K → ℂ} (hb1 : Bdd h1) (hb2 : Bdd h2)
    (h : ∀ G : K → ℂ, Bdd G → ∫ z, G z * h1 z ∂m = ∫ z, G z * h2 z ∂m) : h1 =ᵐ[m] h2 := by
  have hd := (hb1.sub hb2)
  have h0 := h (fun z => conj (h1 z - h2 z)) hd.conj'
  have hint : ∫ z, ((‖h1 z - h2 z‖ ^ 2 : ℝ) : ℂ) ∂m = 0 := by
    have : (fun z => ((‖h1 z - h2 z‖ ^ 2 : ℝ) : ℂ)) =
        fun z => conj (h1 z - h2 z) * h1 z - conj (h1 z - h2 z) * h2 z := by
      funext z
      rw [Complex.ofReal_pow, ← Complex.mul_conj', mul_comm, mul_sub]
    rw [this, integral_sub (hd.conj'.mul hb1).integrable (hd.conj'.mul hb2).integrable, h0,
      sub_self]
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hint
  have hint2 : Integrable (fun z => ‖h1 z - h2 z‖ ^ 2) m :=
    (memLp_two_iff_integrable_sq_norm hd.meas.aestronglyMeasurable).1 (hd.memLp 2)
  have := (integral_eq_zero_iff_of_nonneg (fun z => by positivity) hint2).1 hint
  filter_upwards [this] with z hz
  have : ‖h1 z - h2 z‖ = 0 := by simpa using hz
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-! ## Rotation factors and disintegration -/

section Disint

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}
variable {Y : Type*} [MeasurableSpace Y] [AddAction Γ Y]

/-- `κ : Y → K` is a *rotation factor* of `μ`: measurable, `κ_* μ = m_K`, and a.e.
equivariant. -/
structure IsRotFactor (μ : Measure Y) (α : Γ →+ Torus) (κ : Y → KG α) : Prop where
  measurable : Measurable κ
  map_eq : μ.map κ = haarK α
  ae_equivariant : ∀ γ : Γ, ∀ᵐ y ∂μ, κ (γ +ᵥ y) = κ y + kα α γ

lemma IsKroneckerMap.toRotFactor {μ : Measure Y} {κ : Y → KG α} (h : IsKroneckerMap μ α κ) :
    IsRotFactor μ α κ := ⟨h.measurable, h.map_eq, h.ae_equivariant⟩

variable [StandardBorelSpace Y] [Nonempty Y]

/-- The disintegration `z ↦ μ_z` of `μ` over `κ`. -/
def dis (μ : Measure Y) [IsFiniteMeasure μ] (κ : Y → KG α) : Kernel (KG α) Y :=
  (μ.map fun y => (κ y, y)).condKernel

instance (μ : Measure Y) [IsFiniteMeasure μ] (κ : Y → KG α) : IsMarkovKernel (dis μ κ) := by
  unfold dis; infer_instance

/-- `f̃(z) = ∫ f dμ_z`. -/
def tilde (μ : Measure Y) [IsFiniteMeasure μ] (κ : Y → KG α) (F : Y → ℂ) (z : KG α) : ℂ :=
  ∫ y, F y ∂(dis μ κ z)

variable {μ : Measure Y} [IsProbabilityMeasure μ] {κ : Y → KG α}

lemma IsRotFactor.graph_eq (h : IsRotFactor μ α κ) :
    μ.map (fun y => (κ y, y)) = haarK α ⊗ₘ dis μ κ := by
  have := Measure.disintegrate (μ.map fun y => (κ y, y)) ((μ.map fun y => (κ y, y)).condKernel)
  rw [Measure.fst_map_prodMk (X := κ) (Y := fun y => y) measurable_id', h.map_eq] at this
  exact this.symm

lemma Bdd.tilde {F : Y → ℂ} (hF : Bdd F) : Bdd (tilde μ κ F) := by
  obtain ⟨C, hC⟩ := hF.bound
  refine ⟨(hF.meas.stronglyMeasurable.integral_kernel (κ := dis μ κ)).measurable, C, fun z => ?_⟩
  exact Bdd.norm_integral_le (μ := dis μ κ z) hC

/-- The defining property of the disintegration: `∫ G(κ y) f(y) dμ = ∫ G f̃ dm_K`. -/
theorem IsRotFactor.integral_comp_mul_tilde (h : IsRotFactor μ α κ) {G : KG α → ℂ}
    (hGm : Measurable G) (hG : Integrable G (haarK α)) {F : Y → ℂ} (hF : Bdd F) :
    ∫ y, G (κ y) * F y ∂μ = ∫ z, G z * tilde μ κ F z ∂haarK α := by
  have hm : Measurable fun p : KG α × Y => G p.1 * F p.2 :=
    (hGm.comp measurable_fst).mul (hF.meas.comp measurable_snd)
  have e1 : ∫ y, G (κ y) * F y ∂μ = ∫ p, G p.1 * F p.2 ∂(μ.map fun y => (κ y, y)) :=
    (integral_map (h.measurable.prodMk measurable_id').aemeasurable
      hm.aestronglyMeasurable).symm
  obtain ⟨C, hC0, hC⟩ := hF.exists_bound_nonneg
  have hint : Integrable (fun p : KG α × Y => G p.1 * F p.2) (haarK α ⊗ₘ dis μ κ) := by
    have h1 : Integrable (fun p : KG α × Y => G p.1) (haarK α ⊗ₘ dis μ κ) := by
      have : (haarK α ⊗ₘ dis μ κ).map Prod.fst = haarK α := Measure.fst_compProd _ _
      rw [← this] at hG
      exact (integrable_map_measure hGm.aestronglyMeasurable measurable_fst.aemeasurable).1 hG
    refine (h1.norm.const_mul C).mono' hm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  rw [e1, h.graph_eq, Measure.integral_compProd hint]
  simp only [integral_const_mul]
  rfl

lemma IsRotFactor.integral_comp (h : IsRotFactor μ α κ) {G : KG α → ℂ} (hGm : Measurable G) :
    ∫ y, G (κ y) ∂μ = ∫ z, G z ∂haarK α := by
  rw [← h.map_eq, integral_map h.measurable.aemeasurable hGm.aestronglyMeasurable]

lemma IsRotFactor.integral_tilde (h : IsRotFactor μ α κ) {F : Y → ℂ} (hF : Bdd F) :
    ∫ z, tilde μ κ F z ∂haarK α = ∫ y, F y ∂μ := by
  have := h.integral_comp_mul_tilde (G := fun _ => 1) measurable_const (integrable_const _) hF
  simpa using this.symm

/-- `f - f̃ ∘ κ` is orthogonal to every bounded function of `κ`. -/
lemma IsRotFactor.integral_mul_sub_tilde (h : IsRotFactor μ α κ) {G : KG α → ℂ} (hG : Bdd G)
    {F : Y → ℂ} (hF : Bdd F) :
    ∫ y, G (κ y) * (F y - tilde μ κ F (κ y)) ∂μ = 0 := by
  have h1 := h.integral_comp_mul_tilde hG.meas hG.integrable hF
  have h2 := h.integral_comp (G := fun z => G z * tilde μ κ F z) (hG.meas.mul hF.tilde.meas)
  have e : (fun y => G (κ y) * (F y - tilde μ κ F (κ y))) =
      fun y => G (κ y) * F y - G (κ y) * tilde μ κ F (κ y) := by funext y; ring
  have i1 : Integrable (fun y => G (κ y) * F y) μ := ((hG.comp h.measurable).mul hF).integrable
  have i2 : Integrable (fun y => G (κ y) * tilde μ κ F (κ y)) μ :=
    ((hG.mul hF.tilde).comp h.measurable).integrable
  rw [e, integral_sub i1 i2, h1, h2, sub_self]

variable [MeasurableConstVAdd Γ Y] [VAddInvariantMeasure Γ Y μ]

/-- Equivariance of the disintegration: `(f ∘ T^γ)~ = f̃(· + α γ)` a.e. -/
theorem IsRotFactor.ae_tilde_vadd (h : IsRotFactor μ α κ) {F : Y → ℂ} (hF : Bdd F) (γ : Γ) :
    tilde μ κ (fun y => F (γ +ᵥ y)) =ᵐ[haarK α] fun z => tilde μ κ F (z + kα α γ) := by
  have hFγ : Bdd fun y => F (γ +ᵥ y) := hF.comp (measurable_const_vadd γ)
  refine ae_eq_of_forall_integral_mul_eq hFγ.tilde (hF.tilde.comp (measurable_add_const _))
    fun G hG => ?_
  rw [← h.integral_comp_mul_tilde hG.meas hG.integrable hFγ]
  have e1 : ∫ z, G z * tilde μ κ F (z + kα α γ) ∂haarK α =
      ∫ z, G (z - kα α γ) * tilde μ κ F z ∂haarK α := by
    rw [← integral_haarK_add (fun z => G (z - kα α γ) * tilde μ κ F z) (kα α γ)]
    simp
  rw [e1, ← h.integral_comp_mul_tilde (G := fun z => G (z - kα α γ))
    (hG.meas.comp (measurable_sub_const _)) (hG.comp (measurable_sub_const _)).integrable hF]
  rw [← integral_vadd_eq_self (μ := μ) (fun y => G (κ y - kα α γ) * F y) (g := γ)]
  refine integral_congr_ae ((h.ae_equivariant γ).mono fun y hy => ?_)
  simp [hy]

omit [MeasurableConstVAdd Γ Y] [VAddInvariantMeasure Γ Y μ] in
/-- `μ_z` is concentrated on the fibre `κ⁻¹(z)` for a.e. `z`. -/
lemma IsRotFactor.ae_ae_fiber (h : IsRotFactor μ α κ) :
    ∀ᵐ z ∂haarK α, ∀ᵐ y ∂(dis μ κ z), κ y = z := by
  have hmeas : MeasurableSet {p : KG α × Y | κ p.2 = p.1} :=
    (isClosed_diagonal (X := KG α)).measurableSet.preimage
      ((h.measurable.comp measurable_snd).prodMk measurable_fst)
  have h1 : ∀ᵐ p ∂(μ.map fun y => (κ y, y)), κ p.2 = p.1 := by
    rw [ae_map_iff (h.measurable.prodMk measurable_id').aemeasurable hmeas]
    exact Eventually.of_forall fun y => rfl
  rw [h.graph_eq] at h1
  exact Measure.ae_ae_of_ae_compProd h1

end Disint

/-! ## Relative products -/

section RelProd

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}
variable {Y : Type*} [MeasurableSpace Y] [AddAction Γ Y] [StandardBorelSpace Y] [Nonempty Y]
variable (μ : Measure Y) [IsProbabilityMeasure μ] (κ : Y → KG α)

/-- The kernel `z ↦ μ_z ⊗ μ_{z+t}`. -/
def relK (t : KG α) : Kernel (KG α) (Y × Y) :=
  Kernel.prod (dis μ κ) ((dis μ κ).comap (· + t) (measurable_add_const t))

instance (t : KG α) : IsMarkovKernel (relK μ κ t) := by unfold relK; infer_instance

omit [AddAction Γ Y] in
lemma relK_apply (t z : KG α) : relK μ κ t z = (dis μ κ z).prod (dis μ κ (z + t)) := by
  simp [relK, Kernel.prod_apply, Kernel.comap_apply]

/-- Paper, Definition \ref{K:def:J}: the relative product
`J^μ_t = ∫_K μ_z ⊗ μ_{z+t} dm_K(z)` with parameter `t`. -/
def relJ (t : KG α) : Measure (Y × Y) := (haarK α ⊗ₘ relK μ κ t).snd

instance (t : KG α) : IsProbabilityMeasure (relJ μ κ t) := by unfold relJ; infer_instance

variable {μ κ}

lemma integral_relJ {F : Y × Y → ℂ} (hF : Bdd F) (t : KG α) :
    ∫ p, F p ∂relJ μ κ t = ∫ z, ∫ p, F p ∂((dis μ κ z).prod (dis μ κ (z + t))) ∂haarK α := by
  have hb : Bdd fun x : KG α × (Y × Y) => F x.2 := hF.comp measurable_snd
  rw [relJ, Measure.snd, integral_map measurable_snd.aemeasurable hF.meas.aestronglyMeasurable,
    Measure.integral_compProd hb.integrable]
  simp [relK_apply]

/-- Paper, Lemma \ref{K:lem:J}(a): `∫ f ⊗ g dJ_t = ∫ f̃(z) g̃(z + t) dm_K(z)`. -/
theorem integral_relJ_mul {f g : Y → ℂ} (hf : Bdd f) (hg : Bdd g) (t : KG α) :
    ∫ p, f p.1 * g p.2 ∂relJ μ κ t = ∫ z, tilde μ κ f z * tilde μ κ g (z + t) ∂haarK α := by
  have hb : Bdd fun p : Y × Y => f p.1 * g p.2 := (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  rw [integral_relJ hb t]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  exact integral_prod_mul (μ := dis μ κ z) (ν := dis μ κ (z + t)) f g

lemma relJ_real_prod {A B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) (t : KG α) :
    (((relJ μ κ t).real (A ×ˢ B) : ℝ) : ℂ) =
      ∫ z, tilde μ κ (A.indicator fun _ => (1 : ℂ)) z *
        tilde μ κ (B.indicator fun _ => (1 : ℂ)) (z + t) ∂haarK α := by
  rw [← integral_relJ_mul (Bdd.indicator hA) (Bdd.indicator hB), ← integral_indicator_one
    (hA.prod hB), ← integral_complex_ofReal]
  congr 1; funext p
  by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;>
    simp [Set.indicator, Set.mem_prod, h1, h2]

lemma measure_eq_of_real_eq {X X' : Type*} [MeasurableSpace X] [MeasurableSpace X']
    {μ : Measure X} {ν : Measure X'} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {s : Set X} {s' : Set X'} (h : μ.real s = ν.real s') : μ s = ν s' :=
  (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h

lemma tilde_one (z : KG α) : tilde μ κ (fun _ => (1 : ℂ)) z = 1 := by simp [tilde]

lemma tilde_indicator_univ (z : KG α) :
    tilde μ κ ((Set.univ : Set Y).indicator fun _ => (1 : ℂ)) z = 1 := by
  simp [tilde]

lemma indicator_comp_vadd (A : Set Y) (γ : Γ) :
    (fun y => A.indicator (fun _ => (1 : ℂ)) (γ +ᵥ y)) = ((γ +ᵥ ·) ⁻¹' A).indicator fun _ => 1 := by
  funext y; simp [Set.indicator]

variable (h : IsRotFactor μ α κ)
include h

/-- Paper, Lemma \ref{K:lem:J}(b): the first marginal of `J_t` is `μ`. -/
theorem IsRotFactor.relJ_map_fst (t : KG α) : (relJ μ κ t).map Prod.fst = μ := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, ← Set.prod_univ]
  apply measure_eq_of_real_eq
  apply Complex.ofReal_injective
  rw [relJ_real_prod hA MeasurableSet.univ]
  simp only [tilde_indicator_univ (μ := μ) (κ := κ), mul_one]
  rw [h.integral_tilde (Bdd.indicator hA), ← integral_indicator_one hA, ← integral_complex_ofReal]
  congr 1; funext y; by_cases hy : y ∈ A <;> simp [hy]

/-- Paper, Lemma \ref{K:lem:J}(b): the second marginal of `J_t` is `μ`. -/
theorem IsRotFactor.relJ_map_snd (t : KG α) : (relJ μ κ t).map Prod.snd = μ := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB, ← Set.univ_prod]
  apply measure_eq_of_real_eq
  apply Complex.ofReal_injective
  rw [relJ_real_prod MeasurableSet.univ hB]
  simp only [tilde_indicator_univ (μ := μ) (κ := κ), one_mul]
  rw [integral_haarK_add (fun z => tilde μ κ (B.indicator fun _ => (1 : ℂ)) z) t,
    h.integral_tilde (Bdd.indicator hB), ← integral_indicator_one hB, ← integral_complex_ofReal]
  congr 1; funext y; by_cases hy : y ∈ B <;> simp [hy]

/-- Paper, Lemma \ref{K:lem:J}(b): `J_t` is concentrated on `{(y, y') : κ y' = κ y + t}`. -/
theorem IsRotFactor.ae_relJ (t : KG α) : ∀ᵐ p ∂relJ μ κ t, κ p.2 = κ p.1 + t := by
  have hc : Continuous fun q : KG α × KG α => (q.2, q.1 + t) :=
    continuous_snd.prodMk (continuous_fst.add continuous_const)
  have hmeasK : MeasurableSet {q : KG α × KG α | q.2 = q.1 + t} := by
    have : {q : KG α × KG α | q.2 = q.1 + t} = (fun q => (q.2, q.1 + t)) ⁻¹' Set.diagonal (KG α) := by
      ext q; simp [Set.diagonal]
    rw [this]
    exact (isClosed_diagonal.preimage hc).measurableSet
  have hmeas : MeasurableSet {p : Y × Y | κ p.2 = κ p.1 + t} :=
    hmeasK.preimage ((h.measurable.comp measurable_fst).prodMk (h.measurable.comp measurable_snd))
  have hf := h.ae_ae_fiber
  have hf' : ∀ᵐ z ∂haarK α, ∀ᵐ y ∂(dis μ κ (z + t)), κ y = z + t :=
    (measurePreserving_add_right (haarK α) t).quasiMeasurePreserving.ae
      (p := fun w => ∀ᵐ y ∂(dis μ κ w), κ y = w) hf
  have hcp : ∀ᵐ x ∂(haarK α ⊗ₘ relK μ κ t), κ x.2.2 = κ x.2.1 + t := by
    refine Measure.ae_compProd_of_ae_ae (p := fun x : KG α × (Y × Y) => κ x.2.2 = κ x.2.1 + t)
      (measurable_snd hmeas) ?_
    filter_upwards [hf, hf'] with z h1 h2
    rw [relK_apply]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1,
      Measure.quasiMeasurePreserving_snd.ae h2] with q hq1 hq2
    rw [hq2, hq1]
  exact (ae_map_iff measurable_snd.aemeasurable hmeas).2 hcp

variable [MeasurableConstVAdd Γ Y] [VAddInvariantMeasure Γ Y μ]

/-- Paper, Lemma \ref{K:lem:J}(b): `J_t` is invariant under the diagonal action. -/
theorem IsRotFactor.relJ_map_vadd (t : KG α) (γ : Γ) :
    (relJ μ κ t).map (γ +ᵥ ·) = relJ μ κ t := by
  have hmv : Measurable fun p : Y × Y => γ +ᵥ p :=
    (measurable_const_vadd γ |>.comp measurable_fst).prodMk
      (measurable_const_vadd γ |>.comp measurable_snd)
  refine (measure_prod_ext fun A B hA hB => ?_).symm
  rw [Measure.map_apply hmv (hA.prod hB)]
  have hpre : (fun p : Y × Y => γ +ᵥ p) ⁻¹' (A ×ˢ B) = ((γ +ᵥ ·) ⁻¹' A) ×ˢ ((γ +ᵥ ·) ⁻¹' B) := by
    ext p; simp [Prod.vadd_def]
  rw [hpre]
  have hA' : MeasurableSet ((γ +ᵥ ·) ⁻¹' A) := measurable_const_vadd γ hA
  have hB' : MeasurableSet ((γ +ᵥ ·) ⁻¹' B) := measurable_const_vadd γ hB
  apply measure_eq_of_real_eq
  apply Complex.ofReal_injective
  rw [relJ_real_prod hA hB, relJ_real_prod hA' hB', ← indicator_comp_vadd, ← indicator_comp_vadd]
  have e1 := h.ae_tilde_vadd (Bdd.indicator hA) γ
  have e2 := (measurePreserving_add_right (haarK α) t).quasiMeasurePreserving.ae
    (h.ae_tilde_vadd (Bdd.indicator hB) γ)
  have e3 : (fun z => tilde μ κ (fun y => A.indicator (fun _ => (1 : ℂ)) (γ +ᵥ y)) z *
      tilde μ κ (fun y => B.indicator (fun _ => (1 : ℂ)) (γ +ᵥ y)) (z + t)) =ᵐ[haarK α]
      fun z => tilde μ κ (A.indicator fun _ => (1 : ℂ)) (z + kα α γ) *
        tilde μ κ (B.indicator fun _ => (1 : ℂ)) (z + t + kα α γ) := by
    filter_upwards [e1, e2] with z hz1 hz2
    rw [hz1, hz2]
  rw [integral_congr_ae e3, ← integral_haarK_add (fun z => tilde μ κ (A.indicator fun _ => (1 : ℂ)) z *
    tilde μ κ (B.indicator fun _ => (1 : ℂ)) (z + t)) (kα α γ)]
  congr 1; funext z
  rw [add_right_comm z t]

end RelProd

end Kmrr25.ThmK
