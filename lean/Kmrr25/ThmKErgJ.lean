import Kmrr25.ThmKSupport

/-!
# Theorem K: ergodicity of almost every relative product

Paper, Lemma \ref{K:lem:J}(c): `J^λ_t` is ergodic for `m_K`-almost every `t`.

We follow the structure of the paper's proof but avoid invariant projections:

* `integral_prod_eq_integral_relJ`: `∫ Φ d(λ × λ) = ∫_K ∫ Φ dJ_t dm_K(t)` (Step 1);
* `tendsto_l2_relJ_avg`: for bounded `f, g`, the averages `𝔼_{γ∈Φ_N} f(T^γ y) g(T^γ y')`
  converge in `L²(λ × λ)` to `J_{κ y' - κ y}(f ⊗ g)` (this replaces Step 2: the weakly mixing
  parts are handled by `WeakMixing.tendsto_l2_avg`, the Kronecker part by the mean ergodic theorem
  for the rotation);
* Step 3 via Fatou's lemma, applied to rectangles from a countable generating π-system.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

open Q516

universe u

/-! ## A countable generating π-system -/

section PiFam

variable {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
  [BorelSpace Y]

/-- Finite intersections of members of the countable basis of `Y`. -/
def piFam (Y : Type*) [TopologicalSpace Y] [SecondCountableTopology Y] : Set (Set Y) :=
  {s | ∃ T : Set (Set Y), T.Finite ∧ T ⊆ TopologicalSpace.countableBasis Y ∧ s = ⋂₀ T}

lemma piFam_countable : (piFam Y).Countable := by
  have h := Set.countable_setOf_finite_subset (TopologicalSpace.countable_countableBasis Y)
  refine (h.image fun T => ⋂₀ T).mono ?_
  rintro _ ⟨T, hT, hTB, rfl⟩
  exact ⟨T, ⟨hT, hTB⟩, rfl⟩

lemma isPiSystem_piFam : IsPiSystem (piFam Y) := by
  rintro _ ⟨T₁, h₁, hB₁, rfl⟩ _ ⟨T₂, h₂, hB₂, rfl⟩ _
  exact ⟨T₁ ∪ T₂, h₁.union h₂, Set.union_subset hB₁ hB₂, (Set.sInter_union _ _).symm⟩

lemma univ_mem_piFam : (Set.univ : Set Y) ∈ piFam Y :=
  ⟨∅, Set.finite_empty, Set.empty_subset _, Set.sInter_empty.symm⟩

lemma measurableSet_of_mem_piFam {s : Set Y} (hs : s ∈ piFam Y) : MeasurableSet s := by
  obtain ⟨T, hT, hTB, rfl⟩ := hs
  exact MeasurableSet.sInter hT.countable fun t ht =>
    (TopologicalSpace.isOpen_of_mem_countableBasis (hTB ht)).measurableSet

lemma generateFrom_piFam : MeasurableSpace.generateFrom (piFam Y) = ‹MeasurableSpace Y› := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun s hs => measurableSet_of_mem_piFam hs
  · rw [BorelSpace.measurable_eq (α := Y), (TopologicalSpace.isBasis_countableBasis Y).borel_eq_generateFrom]
    refine MeasurableSpace.generateFrom_mono fun s hs => ⟨{s}, Set.finite_singleton s,
      Set.singleton_subset_iff.2 hs, (Set.sInter_singleton s).symm⟩

/-- Finite measures on `Y × Y` agreeing on rectangles from `piFam` are equal. -/
lemma measure_ext_piFam {μ ν : Measure (Y × Y)} [IsFiniteMeasure μ]
    (h : ∀ A ∈ piFam Y, ∀ B ∈ piFam Y, μ (A ×ˢ B) = ν (A ×ˢ B)) : μ = ν := by
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (Y × Y)) =
      MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) (piFam Y) (piFam Y)) := by
    have hsp : IsCountablySpanning (piFam Y) :=
      ⟨fun _ => Set.univ, fun _ => univ_mem_piFam, Set.iUnion_const _⟩
    have := generateFrom_prod_eq hsp hsp
    rw [generateFrom_piFam] at this
    exact this
  refine ext_of_generate_finite _ hgen (isPiSystem_piFam.prod isPiSystem_piFam) ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact h A hA B hB
  · rw [← Set.univ_prod_univ]
    exact h _ univ_mem_piFam _ univ_mem_piFam

end PiFam

/-! ## Step 1: `λ × λ` is the integral of the relative products -/

section Step1

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}
variable {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable {μ : Measure Y} [IsProbabilityMeasure μ] {κ : Y → KG α}

/-- The kernel `(z, z') ↦ μ_z ⊗ μ_{z'}`. -/
def disPair (μ : Measure Y) [IsProbabilityMeasure μ] (κ : Y → KG α) :
    Kernel (KG α × KG α) (Y × Y) :=
  Kernel.prod ((dis μ κ).comap Prod.fst measurable_fst) ((dis μ κ).comap Prod.snd measurable_snd)

instance : IsMarkovKernel (disPair μ κ) := by unfold disPair; infer_instance

lemma disPair_apply (q : KG α × KG α) : disPair μ κ q = (dis μ κ q.1).prod (dis μ κ q.2) := by
  simp [disPair, Kernel.prod_apply, Kernel.comap_apply]

lemma IsRotFactor.bind_dis [AddAction Γ Y] (h : IsRotFactor μ α κ) :
    (haarK α).bind (dis μ κ) = μ := by
  have h1 : (μ.map fun y => (κ y, y)).snd = μ := by
    rw [Measure.snd, Measure.map_map measurable_snd (h.measurable.prodMk measurable_id')]
    exact Measure.map_id
  rw [h.graph_eq, Measure.snd_compProd] at h1
  exact h1

lemma IsRotFactor.bind_disPair [AddAction Γ Y] (h : IsRotFactor μ α κ) :
    ((haarK α).prod (haarK α)).bind (disPair μ κ) = μ.prod μ := by
  refine (measure_prod_ext fun A B hA hB => ?_)
  rw [Measure.bind_apply (hA.prod hB) (disPair μ κ).aemeasurable, Measure.prod_prod]
  simp only [disPair_apply, Measure.prod_prod]
  rw [lintegral_prod_mul ((dis μ κ).measurable_coe hA).aemeasurable
    ((dis μ κ).measurable_coe hB).aemeasurable]
  have e : ∀ S, MeasurableSet S → ∫⁻ z, dis μ κ z S ∂haarK α = μ S := fun S hS => by
    conv_rhs => rw [← h.bind_dis]
    rw [Measure.bind_apply hS (dis μ κ).aemeasurable]
  rw [e A hA, e B hB]

/-- Paper, proof of Lemma \ref{K:lem:J}(c), Step 1:
`∫ Φ d(μ × μ) = ∫_K (∫ Φ dJ_t) dm_K(t)` for bounded measurable `Φ`. -/
theorem IsRotFactor.integral_prod_eq_integral_relJ [AddAction Γ Y] (h : IsRotFactor μ α κ)
    {Φ : Y × Y → ℂ} (hΦ : Bdd Φ) :
    ∫ p, Φ p ∂(μ.prod μ) = ∫ t, ∫ p, Φ p ∂relJ μ κ t ∂haarK α := by
  set G : KG α × KG α → ℂ := fun q => ∫ p, Φ p ∂(disPair μ κ q) with hG
  have hGb : Bdd G := ⟨(hΦ.meas.stronglyMeasurable.integral_kernel (κ := disPair μ κ)).measurable,
    by obtain ⟨C, hC⟩ := hΦ.bound; exact ⟨C, fun q => Bdd.norm_integral_le hC⟩⟩
  -- integrate over the bind
  have hint : Integrable (fun x : (KG α × KG α) × (Y × Y) => Φ x.2)
      (((haarK α).prod (haarK α)) ⊗ₘ disPair μ κ) := (hΦ.comp measurable_snd).integrable
  have e1 : ∫ p, Φ p ∂(μ.prod μ) = ∫ q, G q ∂((haarK α).prod (haarK α)) := by
    calc ∫ p, Φ p ∂(μ.prod μ)
        = ∫ x, Φ x.2 ∂(((haarK α).prod (haarK α)) ⊗ₘ disPair μ κ) := by
          rw [← h.bind_disPair, ← Measure.snd_compProd, Measure.snd,
            integral_map measurable_snd.aemeasurable hΦ.meas.aestronglyMeasurable]
      _ = ∫ q, ∫ p, Φ p ∂(disPair μ κ q) ∂((haarK α).prod (haarK α)) :=
          Measure.integral_compProd (f := fun x => Φ x.2) hint
  rw [e1, integral_prod G hGb.integrable]
  -- substitute `z' = z + t`
  have e2 : ∀ z : KG α, ∫ z', G (z, z') ∂haarK α = ∫ t, G (z, z + t) ∂haarK α := fun z => by
    rw [← integral_haarK_add (fun z' => G (z, z')) z]
    simp [add_comm]
  simp only [e2]
  have hGt : Bdd fun q : KG α × KG α => G (q.1, q.1 + q.2) :=
    hGb.comp (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  rw [integral_integral_swap (f := fun z t => G (z, z + t)) hGt.integrable]
  congr 1; funext t
  rw [integral_relJ hΦ t]
  congr 1; funext z
  simp [hG, disPair_apply]

end Step1

/-! ## Products of weakly mixing functions -/

section ProdWM

variable {Γ : Type*} [AddCommGroup Γ]
variable {Y : Type*} [MeasurableSpace Y] [AddAction Γ Y] [MeasurableConstVAdd Γ Y]
variable {μ : Measure Y} [IsProbabilityMeasure μ] [VAddInvariantMeasure Γ Y μ]

instance prod_vaddInvariant : VAddInvariantMeasure Γ (Y × Y) (μ.prod μ) := by
  refine ⟨fun γ S hS => ?_⟩
  have hm : Measurable fun p : Y × Y => γ +ᵥ p := measurable_const_vadd γ
  have : (μ.prod μ).map (fun p : Y × Y => γ +ᵥ p) = μ.prod μ := by
    have e : (fun p : Y × Y => γ +ᵥ p) = Prod.map (γ +ᵥ ·) (γ +ᵥ ·) := by
      funext p; rfl
    rw [e, ← Measure.map_prod_map _ _ (measurable_const_vadd γ) (measurable_const_vadd γ),
      (measurePreserving_vadd γ μ).map_eq]
  rw [← Measure.map_apply hm hS, this]

lemma corr_prod {f g : Y → ℂ} (β : Γ) :
    corr (μ.prod μ) (fun p : Y × Y => f p.1 * g p.2) β = corr μ f β * corr μ g β := by
  simp only [corr]
  rw [← integral_prod_mul (μ := μ) (ν := μ)]
  congr 1; funext p
  simp only [Prod.vadd_def, map_mul]
  ring

lemma WeakMixing.prod_right {f g : Y → ℂ} (hf : Bdd f) (hg : WeakMixing Γ μ g) :
    WeakMixing Γ (μ.prod μ) (fun p : Y × Y => f p.1 * g p.2) := by
  intro Θ hΘ
  obtain ⟨C, hC0, hC⟩ := hf.exists_bound_nonneg
  have h := (hg Θ hΘ).const_mul (C ^ 2)
  rw [mul_zero] at h
  refine squeeze_zero (fun M => avg_real_nonneg fun _ _ => norm_nonneg _) (fun M => ?_) h
  rw [← smul_eq_mul, ← avg_smul]
  refine avg_real_mono fun β _ => ?_
  rw [corr_prod, norm_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_right (norm_corr_le hC β) (norm_nonneg _)

lemma WeakMixing.prod_left {f g : Y → ℂ} (hf : WeakMixing Γ μ f) (hg : Bdd g) :
    WeakMixing Γ (μ.prod μ) (fun p : Y × Y => f p.1 * g p.2) := by
  intro Θ hΘ
  obtain ⟨C, hC0, hC⟩ := hg.exists_bound_nonneg
  have h := (hf Θ hΘ).const_mul (C ^ 2)
  rw [mul_zero] at h
  refine squeeze_zero (fun M => avg_real_nonneg fun _ _ => norm_nonneg _) (fun M => ?_) h
  rw [← smul_eq_mul, ← avg_smul]
  refine avg_real_mono fun β _ => ?_
  rw [corr_prod, norm_mul, smul_eq_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_corr_le hC β) (norm_nonneg _)

end ProdWM

/-! ## The `L²` convergence of averages on `λ × λ` -/

section L2

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}

lemma norm_add4_sq_le {E : Type*} [NormedAddCommGroup E] (a b c d : E) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h1 : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
      _ ≤ ‖a + b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖a‖ - ‖d‖),
    sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖b‖ - ‖d‖), sq_nonneg (‖c‖ - ‖d‖)]

/-- The two-variable form of the mean ergodic theorem for the rotation. -/
theorem tendsto_l2_rotation_pair {Fa Fb : KG α → ℂ} (ha : Bdd Fa) (hb : Bdd Fb)
    {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) :
    Tendsto (fun N => ∫ q, ‖avg (Φ N) (fun γ => Fa (q.1 + kα α γ) * Fb (q.2 + kα α γ)) -
      ∫ u, Fa u * Fb (u + (q.2 - q.1)) ∂haarK α‖ ^ 2 ∂((haarK α).prod (haarK α))) atTop
      (𝓝 0) := by
  set H : KG α → KG α → ℂ := fun t u => Fa u * Fb (u + t) with hH
  have hHb : ∀ t, Bdd (H t) := fun t => ha.mul (hb.comp (measurable_add_const t))
  obtain ⟨Ca, hCa0, hCa⟩ := ha.exists_bound_nonneg
  obtain ⟨Cb, hCb0, hCb⟩ := hb.exists_bound_nonneg
  have hHC : ∀ t u, ‖H t u‖ ≤ Ca * Cb := fun t u => by
    simp only [hH, norm_mul]
    exact mul_le_mul (hCa u) (hCb _) (norm_nonneg _) hCa0
  set Q : ℕ → KG α × KG α → ℂ := fun N q =>
    avg (Φ N) (fun γ => Fa (q.1 + kα α γ) * Fb (q.2 + kα α γ)) -
      ∫ u, Fa u * Fb (u + (q.2 - q.1)) ∂haarK α with hQ
  set I : ℕ → KG α → ℝ := fun N t =>
    ∫ z, ‖avg (Φ N) (fun γ => H t (z + kα α γ)) - ∫ u, H t u ∂haarK α‖ ^ 2 ∂haarK α with hI
  -- measurability
  have hQm : ∀ N, Measurable (Q N) := by
    intro N
    have h1 : Measurable fun q : KG α × KG α =>
        avg (Φ N) (fun γ => Fa (q.1 + kα α γ) * Fb (q.2 + kα α γ)) :=
      (Bdd.avg (Φ N) fun γ _ => (ha.comp (measurable_fst.add_const _)).mul
        (hb.comp (measurable_snd.add_const _))).meas
    have h2 : StronglyMeasurable fun q : KG α × KG α => ∫ u, Fa u * Fb (u + (q.2 - q.1)) ∂haarK α :=
      (((ha.meas.comp measurable_snd).mul (hb.meas.comp (measurable_snd.add
        ((measurable_snd.comp measurable_fst).sub (measurable_fst.comp measurable_fst)))))
        |>.stronglyMeasurable).integral_prod_right'
    exact h1.sub h2.measurable
  have hQb : ∀ N q, ‖Q N q‖ ≤ 2 * (Ca * Cb) := by
    intro N q
    refine (norm_sub_le _ _).trans ?_
    have e1 : ‖avg (Φ N) (fun γ => Fa (q.1 + kα α γ) * Fb (q.2 + kα α γ))‖ ≤ Ca * Cb :=
      norm_avg_le _ (fun γ _ => by
        rw [norm_mul]; exact mul_le_mul (hCa _) (hCb _) (norm_nonneg _) hCa0) (by positivity)
    have e2 : ‖∫ u, Fa u * Fb (u + (q.2 - q.1)) ∂haarK α‖ ≤ Ca * Cb :=
      Bdd.norm_integral_le fun u => by
        rw [norm_mul]; exact mul_le_mul (hCa _) (hCb _) (norm_nonneg _) hCa0
    linarith
  -- rewrite the double integral
  have hsq : ∀ N, Bdd fun q => ((‖Q N q‖ ^ 2 : ℝ) : ℂ) := fun N =>
    ⟨Complex.continuous_ofReal.measurable.comp ((hQm N).norm.pow_const 2),
      (2 * (Ca * Cb)) ^ 2, fun q => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hQb N q) 2⟩
  have hsqr : ∀ N, Integrable (fun q => ‖Q N q‖ ^ 2) ((haarK α).prod (haarK α)) := fun N =>
    Integrable.of_bound ((hQm N).norm.pow_const 2).aestronglyMeasurable ((2 * (Ca * Cb)) ^ 2)
      (Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hQb N q) 2)
  have he : ∀ N, ∫ q, ‖Q N q‖ ^ 2 ∂((haarK α).prod (haarK α)) = ∫ t, I N t ∂haarK α := by
    intro N
    rw [integral_prod _ (hsqr N)]
    have e2 : ∀ z : KG α, ∫ z', ‖Q N (z, z')‖ ^ 2 ∂haarK α =
        ∫ t, ‖Q N (z, z + t)‖ ^ 2 ∂haarK α := fun z => by
      rw [← integral_haarK_add_real (fun z' => ‖Q N (z, z')‖ ^ 2) z]
      simp [add_comm]
    simp only [e2]
    have hint : Integrable (fun q : KG α × KG α => ‖Q N (q.1, q.1 + q.2)‖ ^ 2)
        ((haarK α).prod (haarK α)) :=
      Integrable.of_bound (((hQm N).comp (measurable_fst.prodMk
        (measurable_fst.add measurable_snd))).norm.pow_const 2).aestronglyMeasurable
        ((2 * (Ca * Cb)) ^ 2) (Eventually.of_forall fun q => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hQb N _) 2)
    rw [integral_integral_swap (f := fun z t => ‖Q N (z, z + t)‖ ^ 2) hint]
    congr 1; funext t
    simp only [hI, hQ, hH]
    congr 1; funext z
    simp only [add_right_comm z t, add_sub_cancel_left]
  refine Tendsto.congr (fun N => (he N).symm) ?_
  -- dominated convergence
  have hIm : ∀ N, AEStronglyMeasurable (I N) (haarK α) := by
    intro N
    have : StronglyMeasurable fun q : KG α × KG α =>
        ‖avg (Φ N) (fun γ => H q.1 (q.2 + kα α γ)) - ∫ u, H q.1 u ∂haarK α‖ ^ 2 := by
      have h1 : Measurable fun q : KG α × KG α => avg (Φ N) (fun γ => H q.1 (q.2 + kα α γ)) :=
        (Bdd.avg (Φ N) fun γ _ => (ha.comp (measurable_snd.add_const _)).mul
          (hb.comp ((measurable_snd.add_const _).add measurable_fst))).meas
      have h2 : StronglyMeasurable fun q : KG α × KG α => ∫ u, H q.1 u ∂haarK α := by
        have : StronglyMeasurable fun p : (KG α × KG α) × KG α => H p.1.1 p.2 :=
          ((ha.meas.comp measurable_snd).mul (hb.meas.comp (measurable_snd.add
            (measurable_fst.comp measurable_fst)))).stronglyMeasurable
        exact this.integral_prod_right' (ν := haarK α)
      exact ((h1.sub h2.measurable).norm.pow_const 2).stronglyMeasurable
    exact (this.integral_prod_right' (ν := haarK α)).aestronglyMeasurable
  have hbound : ∀ N, ∀ᵐ t ∂haarK α, ‖I N t‖ ≤ (2 * (Ca * Cb)) ^ 2 := by
    intro N
    refine Eventually.of_forall fun t => ?_
    have h0 : 0 ≤ I N t := integral_nonneg fun z => by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    calc I N t ≤ ∫ _z, (2 * (Ca * Cb)) ^ 2 ∂haarK α := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
            (integrable_const _) (Eventually.of_forall fun z => ?_)
          refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
          have e1 := norm_avg_le (F := Φ N) (fun γ => H t (z + kα α γ)) (fun γ _ => hHC t _)
            (by positivity)
          have e2 : ‖∫ u, H t u ∂haarK α‖ ≤ Ca * Cb := Bdd.norm_integral_le (hHC t)
          linarith
      _ = (2 * (Ca * Cb)) ^ 2 := by simp
  have hlim : ∀ᵐ t ∂haarK α, Tendsto (fun N => I N t) atTop (𝓝 0) :=
    Eventually.of_forall fun t => tendsto_rotation_avg_l2 (hHb t) hΦ
  have := tendsto_integral_of_dominated_convergence (fun _ => (2 * (Ca * Cb)) ^ 2) hIm
    (integrable_const _) hbound hlim
  simpa using this

/-- `c_{f,g}(t) = J_t(f ⊗ g) = ∫ f̃(z) g̃(z + t) dm_K(z)`. -/
def cJ {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (κ : Y → KG α) (f g : Y → ℂ) (t : KG α) : ℂ :=
  ∫ z, tilde μ κ f z * tilde μ κ g (z + t) ∂haarK α

lemma Bdd.cJ {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] [AddAction Γ Y]
    {μ : Measure Y}
    [IsProbabilityMeasure μ] {κ : Y → KG α} {f g : Y → ℂ} (hf : Bdd f) (hg : Bdd g) :
    Bdd (cJ μ κ f g) := by
  obtain ⟨Ca, hCa0, hCa⟩ := hf.tilde (μ := μ) (κ := κ) |>.exists_bound_nonneg
  obtain ⟨Cb, hCb0, hCb⟩ := hg.tilde (μ := μ) (κ := κ) |>.exists_bound_nonneg
  refine ⟨?_, Ca * Cb, fun t => Bdd.norm_integral_le fun z => ?_⟩
  · have : StronglyMeasurable fun p : KG α × KG α =>
        Kmrr25.ThmK.tilde μ κ f p.2 * Kmrr25.ThmK.tilde μ κ g (p.2 + p.1) :=
      ((hf.tilde.meas.comp measurable_snd).mul (hg.tilde.meas.comp
        (measurable_snd.add measurable_fst))).stronglyMeasurable
    exact (this.integral_prod_right' (ν := haarK α)).measurable
  · rw [norm_mul]; exact mul_le_mul (hCa _) (hCb _) (norm_nonneg _) hCa0

/-- The averages `𝔼_{γ∈Φ_N} f(T^γ y) g(T^γ y')` converge in `L²(λ × λ)` to
`J_{κ y' - κ y}(f ⊗ g)`. -/
theorem IsKroneckerMap.tendsto_l2_prod_avg {Γ Y : Type u} [AddCommGroup Γ] [Countable Γ]
    {α : Γ →+ Torus} [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y] [ContinuousConstVAdd Γ Y] [Nonempty Y]
    {μ : Measure Y} [IsProbabilityMeasure μ] [VAddInvariantMeasure Γ Y μ] {κ : Y → KG α}
    (hW : WienerKoopman.{u}) (hκ : IsKroneckerMap μ α κ) {f g : Y → ℂ} (hf : Bdd f) (hg : Bdd g)
    {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) :
    Tendsto (fun N => ∫ p, ‖avg (Φ N) (fun γ => f (γ +ᵥ p.1) * g (γ +ᵥ p.2)) -
      cJ μ κ f g (κ p.2 - κ p.1)‖ ^ 2 ∂(μ.prod μ)) atTop (𝓝 0) := by
  have hR := hκ.toRotFactor
  set f₀ : Y → ℂ := fun y => tilde μ κ f (κ y) with hf₀
  set g₀ : Y → ℂ := fun y => tilde μ κ g (κ y) with hg₀
  set f₁ : Y → ℂ := fun y => f y - f₀ y with hf₁
  set g₁ : Y → ℂ := fun y => g y - g₀ y with hg₁
  have bf₀ : Bdd f₀ := hf.tilde.comp hκ.measurable
  have bg₀ : Bdd g₀ := hg.tilde.comp hκ.measurable
  have bf₁ : Bdd f₁ := hf.sub bf₀
  have bg₁ : Bdd g₁ := hg.sub bg₀
  have wf₁ : WeakMixing Γ μ f₁ := hκ.weakMixing_sub_tilde hW hf
  have wg₁ : WeakMixing Γ μ g₁ := hκ.weakMixing_sub_tilde hW hg
  -- the three weakly mixing terms
  have hT : ∀ {v : Y × Y → ℂ}, Bdd v → WeakMixing Γ (μ.prod μ) v →
      Tendsto (fun N => ∫ p, ‖avg (Φ N) (fun γ => v (γ +ᵥ p))‖ ^ 2 ∂(μ.prod μ)) atTop (𝓝 0) := by
    intro v hv hwm
    have := hwm.tendsto_l2_avg hv hΦ (fun _ _ => 1) fun _ _ => by simp
    simpa using this
  have h01 := hT ((bf₀.comp measurable_fst).mul (bg₁.comp measurable_snd)) (wg₁.prod_right bf₀)
  have h10 := hT ((bf₁.comp measurable_fst).mul (bg₀.comp measurable_snd)) (wf₁.prod_left bg₀)
  have h11 := hT ((bf₁.comp measurable_fst).mul (bg₁.comp measurable_snd)) (wf₁.prod_left bg₁)
  -- the Kronecker term
  have hrot := tendsto_l2_rotation_pair (hf.tilde (μ := μ) (κ := κ)) (hg.tilde (μ := μ) (κ := κ)) hΦ
  have hae : ∀ᵐ p ∂(μ.prod μ), ∀ γ : Γ, κ (γ +ᵥ p.1) = κ p.1 + kα α γ ∧
      κ (γ +ᵥ p.2) = κ p.2 + kα α γ := by
    rw [ae_all_iff]
    intro γ
    exact (Measure.quasiMeasurePreserving_fst.ae (hκ.ae_equivariant γ)).and
      (Measure.quasiMeasurePreserving_snd.ae (hκ.ae_equivariant γ))
  have hmap : (μ.prod μ).map (Prod.map κ κ) = (haarK α).prod (haarK α) := by
    rw [← Measure.map_prod_map _ _ hκ.measurable hκ.measurable, hκ.map_eq]
  have h00 : Tendsto (fun N => ∫ p, ‖avg (Φ N) (fun γ => f₀ (γ +ᵥ p.1) * g₀ (γ +ᵥ p.2)) -
      cJ μ κ f g (κ p.2 - κ p.1)‖ ^ 2 ∂(μ.prod μ)) atTop (𝓝 0) := by
    refine hrot.congr fun N => ?_
    rw [← hmap, integral_map (hκ.measurable.prodMap hκ.measurable).aemeasurable]
    · refine integral_congr_ae (hae.mono fun p hp => ?_)
      simp only [hf₀, hg₀, cJ, Prod.map_fst, Prod.map_snd, (hp _).1, (hp _).2]
    · refine (Measurable.aestronglyMeasurable ?_)
      refine (Measurable.pow_const (Measurable.norm (Measurable.sub ?_ ?_)) 2)
      · exact (Bdd.avg (Φ N) fun γ _ => (hf.tilde.comp (measurable_fst.add_const _)).mul
          (hg.tilde.comp (measurable_snd.add_const _))).meas
      · have : StronglyMeasurable fun x : (KG α × KG α) × KG α =>
            tilde μ κ f x.2 * tilde μ κ g (x.2 + (x.1.2 - x.1.1)) :=
          ((hf.tilde.meas.comp measurable_snd).mul (hg.tilde.meas.comp (measurable_snd.add
            ((measurable_snd.comp measurable_fst).sub (measurable_fst.comp measurable_fst)))))
            |>.stronglyMeasurable
        exact (this.integral_prod_right' (ν := haarK α)).measurable
  -- combine
  have hsum := ((h00.add h01).add h10).add h11
  simp only [add_zero] at hsum
  have hsum4 := hsum.const_mul 4
  rw [mul_zero] at hsum4
  refine squeeze_zero (fun N => integral_nonneg fun p => by positivity) (fun N => ?_) hsum4
  -- pointwise decomposition
  have hdec : ∀ p : Y × Y, avg (Φ N) (fun γ => f (γ +ᵥ p.1) * g (γ +ᵥ p.2)) -
      cJ μ κ f g (κ p.2 - κ p.1) =
      (avg (Φ N) (fun γ => f₀ (γ +ᵥ p.1) * g₀ (γ +ᵥ p.2)) - cJ μ κ f g (κ p.2 - κ p.1)) +
      avg (Φ N) (fun γ => f₀ (γ +ᵥ p.1) * g₁ (γ +ᵥ p.2)) +
      avg (Φ N) (fun γ => f₁ (γ +ᵥ p.1) * g₀ (γ +ᵥ p.2)) +
      avg (Φ N) (fun γ => f₁ (γ +ᵥ p.1) * g₁ (γ +ᵥ p.2)) := by
    intro p
    simp only [avg, ← smul_add]
    rw [sub_add_eq_add_sub, sub_add_eq_add_sub, sub_add_eq_add_sub, ← smul_add, ← smul_add,
      ← smul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 2
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [hf₁, hg₁]; ring
  have hb : ∀ {v : Y × Y → ℂ}, Bdd v → Integrable (fun p => ‖v p‖ ^ 2) (μ.prod μ) := by
    intro v hv
    exact (memLp_two_iff_integrable_sq_norm hv.meas.aestronglyMeasurable).1 (hv.memLp 2)
  have hA00 : Bdd fun p : Y × Y => avg (Φ N) (fun γ => f₀ (γ +ᵥ p.1) * g₀ (γ +ᵥ p.2)) -
      cJ μ κ f g (κ p.2 - κ p.1) :=
    (Bdd.avg _ fun γ _ => (bf₀.comp ((measurable_const_vadd γ).comp measurable_fst)).mul
      (bg₀.comp ((measurable_const_vadd γ).comp measurable_snd))).sub
      ((hf.cJ hg).comp ((hκ.measurable.comp measurable_snd).sub
        (hκ.measurable.comp measurable_fst)))
  have hAv : ∀ {a b : Y → ℂ}, Bdd a → Bdd b →
      Bdd fun p : Y × Y => avg (Φ N) (fun γ => a (γ +ᵥ p.1) * b (γ +ᵥ p.2)) := by
    intro a b ha hb'
    exact Bdd.avg _ fun γ _ => (ha.comp ((measurable_const_vadd γ).comp measurable_fst)).mul
      (hb'.comp ((measurable_const_vadd γ).comp measurable_snd))
  calc ∫ p, ‖avg (Φ N) (fun γ => f (γ +ᵥ p.1) * g (γ +ᵥ p.2)) -
        cJ μ κ f g (κ p.2 - κ p.1)‖ ^ 2 ∂(μ.prod μ)
      ≤ ∫ p, 4 * (‖avg (Φ N) (fun γ => f₀ (γ +ᵥ p.1) * g₀ (γ +ᵥ p.2)) -
          cJ μ κ f g (κ p.2 - κ p.1)‖ ^ 2 +
          ‖avg (Φ N) (fun γ => f₀ (γ +ᵥ p.1) * g₁ (γ +ᵥ p.2))‖ ^ 2 +
          ‖avg (Φ N) (fun γ => f₁ (γ +ᵥ p.1) * g₀ (γ +ᵥ p.2))‖ ^ 2 +
          ‖avg (Φ N) (fun γ => f₁ (γ +ᵥ p.1) * g₁ (γ +ᵥ p.2))‖ ^ 2) ∂(μ.prod μ) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun p => by positivity)
          ((((hb hA00).add (hb (hAv bf₀ bg₁))).add (hb (hAv bf₁ bg₀))).add
            (hb (hAv bf₁ bg₁)) |>.const_mul 4) (Eventually.of_forall fun p => ?_)
        dsimp only
        rw [hdec p]
        exact norm_add4_sq_le _ _ _ _
    _ = _ := by
        rw [integral_const_mul]
        congr 1
        rw [integral_add, integral_add, integral_add] <;>
          first
          | rfl
          | exact hb hA00
          | exact hb (hAv bf₀ bg₁)
          | exact hb (hAv bf₁ bg₀)
          | exact hb (hAv bf₁ bg₁)
          | exact (hb hA00).add (hb (hAv bf₀ bg₁))
          | exact ((hb hA00).add (hb (hAv bf₀ bg₁))).add (hb (hAv bf₁ bg₀))

end L2

/-! ## Step 3: ergodicity of almost every `J_t` -/

section Step3

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}

lemma ind_prod_inter {Y : Type*} (A B : Set Y) (S : Set (Y × Y)) (p : Y × Y) :
    A.indicator (fun _ => (1 : ℂ)) p.1 * B.indicator (fun _ => 1) p.2 * S.indicator (fun _ => 1) p =
      ((((A ×ˢ B) ∩ S).indicator (1 : Y × Y → ℝ) p : ℝ) : ℂ) := by
  by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;> by_cases h3 : p ∈ S <;>
    simp [Set.indicator, h1, h2, h3, Set.mem_prod]

lemma measurable_integral_relJ {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [AddAction Γ Y] {μ : Measure Y} [IsProbabilityMeasure μ] {κ : Y → KG α} {Φ : Y × Y → ℂ}
    (hΦ : Bdd Φ) : Measurable fun t => ∫ p, Φ p ∂relJ μ κ t := by
  have hG : StronglyMeasurable fun q : KG α × KG α => ∫ p, Φ p ∂(disPair μ κ q) :=
    hΦ.meas.stronglyMeasurable.integral_kernel (κ := disPair μ κ)
  have hG' : StronglyMeasurable fun q : KG α × KG α => ∫ p, Φ p ∂(disPair μ κ (q.2, q.2 + q.1)) :=
    (hG.measurable.comp (measurable_snd.prodMk (measurable_snd.add measurable_fst))).stronglyMeasurable
  have := (hG'.integral_prod_right' (ν := haarK α)).measurable
  convert this using 1
  funext t
  rw [integral_relJ hΦ t]
  congr 1; funext z
  rw [disPair_apply]

/-- Paper, Lemma \ref{K:lem:J}(c): `J^λ_t` is ergodic for `m_K`-almost every `t`. -/
theorem IsKroneckerMap.ae_ergodic_relJ {Γ Y : Type u} [AddCommGroup Γ] [Countable Γ]
    {α : Γ →+ Torus} [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y] [ContinuousConstVAdd Γ Y] [Nonempty Y]
    {μ : Measure Y} [IsProbabilityMeasure μ] [VAddInvariantMeasure Γ Y μ] {κ : Y → KG α}
    (hW : WienerKoopman.{u}) (hκ : IsKroneckerMap μ α κ) :
    ∀ᵐ t ∂haarK α, ErgodicVAdd Γ (Y × Y) (relJ μ κ t) := by
  have hR := hκ.toRotFactor
  obtain ⟨Φ, hΦ⟩ := Q516.exists_folner (G := Γ)
  -- the countable family of rectangles
  have hfam : Countable (piFam Y × piFam Y) := by
    have := (piFam_countable (Y := Y)).to_subtype; infer_instance
  -- for each rectangle: `a_N(t) → 0` along a subsequence, for a.e. `t`
  set F : piFam Y × piFam Y → Y × Y → ℂ := fun o p =>
    (o.1 : Set Y).indicator (fun _ => (1 : ℂ)) p.1 * (o.2 : Set Y).indicator (fun _ => 1) p.2
    with hFdef
  have hFb : ∀ o, Bdd (F o) := fun o =>
    ((Bdd.indicator (measurableSet_of_mem_piFam o.1.2)).comp measurable_fst).mul
      ((Bdd.indicator (measurableSet_of_mem_piFam o.2.2)).comp measurable_snd)
  set c : piFam Y × piFam Y → KG α → ℂ := fun o =>
    cJ μ κ ((o.1 : Set Y).indicator fun _ => (1 : ℂ)) ((o.2 : Set Y).indicator fun _ => 1)
    with hcdef
  have hcb : ∀ o, Bdd (c o) := fun o =>
    (Bdd.indicator (measurableSet_of_mem_piFam o.1.2)).cJ
      (Bdd.indicator (measurableSet_of_mem_piFam o.2.2))
  set Ψ : piFam Y × piFam Y → ℕ → Y × Y → ℝ := fun o N p =>
    ‖avg (Φ N) (fun γ => F o (γ +ᵥ p)) - c o (κ p.2 - κ p.1)‖ ^ 2 with hΨdef
  have hΨb : ∀ o N, Bdd fun p => ((Ψ o N p : ℝ) : ℂ) := by
    intro o N
    have hv : Bdd fun p : Y × Y => avg (Φ N) (fun γ => F o (γ +ᵥ p)) - c o (κ p.2 - κ p.1) :=
      (Bdd.avg _ fun γ _ => (hFb o).comp (measurable_const_vadd γ)).sub
        ((hcb o).comp ((hκ.measurable.comp measurable_snd).sub (hκ.measurable.comp measurable_fst)))
    obtain ⟨C, hC0, hC⟩ := hv.exists_bound_nonneg
    exact ⟨Complex.continuous_ofReal.measurable.comp (hv.meas.norm.pow_const 2), C ^ 2,
      fun p => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC p) 2⟩
  set a : piFam Y × piFam Y → ℕ → KG α → ℝ := fun o N t => ∫ p, Ψ o N p ∂relJ μ κ t with hadef
  have ha_meas : ∀ o N, Measurable (a o N) := by
    intro o N
    have := measurable_integral_relJ (μ := μ) (κ := κ) (hΨb o N)
    have := Complex.measurable_re.comp this
    convert this using 1
    funext t
    simp only [Function.comp, hadef, integral_complex_ofReal, Complex.ofReal_re]
  have ha_nonneg : ∀ o N t, 0 ≤ a o N t := fun o N t => integral_nonneg fun p => by positivity
  have ha_int : ∀ o N, ∫ t, a o N t ∂haarK α = ∫ p, Ψ o N p ∂(μ.prod μ) := by
    intro o N
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal, ← integral_complex_ofReal,
      hR.integral_prod_eq_integral_relJ (hΨb o N)]
    congr 1; funext t
    rw [integral_complex_ofReal]
  have ha_lim : ∀ o, Tendsto (fun N => ∫ t, a o N t ∂haarK α) atTop (𝓝 0) := by
    intro o
    simp only [ha_int]
    exact hκ.tendsto_l2_prod_avg hW (Bdd.indicator (measurableSet_of_mem_piFam o.1.2))
      (Bdd.indicator (measurableSet_of_mem_piFam o.2.2)) hΦ
  -- Fatou: `liminf a_N(t) = 0` for a.e. `t`
  have hfatou : ∀ o, ∀ᵐ t ∂haarK α,
      liminf (fun N => ENNReal.ofReal (a o N t)) atTop = 0 := by
    intro o
    have hle := lintegral_liminf_le (μ := haarK α) (u := atTop)
      (fun N => ENNReal.measurable_ofReal.comp (ha_meas o N))
    have hlim0 : liminf (fun N => ∫⁻ t, ENNReal.ofReal (a o N t) ∂haarK α) atTop = 0 := by
      have e : ∀ N, ∫⁻ t, ENNReal.ofReal (a o N t) ∂haarK α =
          ENNReal.ofReal (∫ t, a o N t ∂haarK α) := fun N => by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · obtain ⟨C, hC⟩ := (hΨb o N).bound
          refine Integrable.of_bound (ha_meas o N).aestronglyMeasurable C
            (Eventually.of_forall fun t => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (ha_nonneg o N t)]
          calc a o N t ≤ ∫ _p, C ∂relJ μ κ t :=
                integral_mono_of_nonneg (Eventually.of_forall fun p => by positivity)
                  (integrable_const _) (Eventually.of_forall fun p => by
                    have := hC p
                    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this)
            _ = C := by simp
        · exact Eventually.of_forall (ha_nonneg o N)
      simp only [e]
      have := (ENNReal.continuous_ofReal.tendsto 0).comp (ha_lim o)
      rw [ENNReal.ofReal_zero] at this
      exact this.liminf_eq
    have h0 : ∫⁻ t, liminf (fun N => ENNReal.ofReal (a o N t)) atTop ∂haarK α = 0 :=
      le_antisymm (hle.trans hlim0.le) bot_le
    have hmeas : Measurable fun t => liminf (fun N => ENNReal.ofReal (a o N t)) atTop :=
      Measurable.liminf fun N => ENNReal.measurable_ofReal.comp (ha_meas o N)
    rw [lintegral_eq_zero_iff hmeas] at h0
    exact h0
  rw [← ae_all_iff] at hfatou
  filter_upwards [hfatou] with t ht
  set J := relJ μ κ t with hJ
  have hinv : VAddInvariantMeasure Γ (Y × Y) J :=
    ⟨fun γ S hS => by
      rw [← Measure.map_apply (measurable_const_vadd γ) hS, hJ, hR.relJ_map_vadd t γ]⟩
  refine { toVAddInvariantMeasure := hinv, aeconst_of_forall_preimage_vadd_ae_eq := ?_ }
  intro S hS hSinv
  have hconc := hR.ae_relJ t
  -- the factorisation `J(R ∩ S) = J(R) J(S)` on rectangles
  have hfact : ∀ o : piFam Y × piFam Y,
      J.real (((o.1 : Set Y) ×ˢ (o.2 : Set Y)) ∩ S) =
        J.real ((o.1 : Set Y) ×ˢ (o.2 : Set Y)) * J.real S := by
    intro o
    have hA := measurableSet_of_mem_piFam o.1.2
    have hB := measurableSet_of_mem_piFam o.2.2
    have hSb : Bdd (S.indicator fun _ => (1 : ℂ)) := Bdd.indicator hS
    set X : ℂ := ∫ p, F o p * S.indicator (fun _ => (1 : ℂ)) p ∂J with hX
    have hXr : X = (J.real (((o.1 : Set Y) ×ˢ (o.2 : Set Y)) ∩ S) : ℂ) := by
      rw [hX, ← integral_indicator_one ((hA.prod hB).inter hS), ← integral_complex_ofReal]
      congr 1; funext p
      exact ind_prod_inter _ _ _ p
    have hcr : c o t = (J.real ((o.1 : Set Y) ×ˢ (o.2 : Set Y)) : ℂ) := by
      rw [hJ, relJ_real_prod hA hB]; rfl
    have hSr : ∫ p, S.indicator (fun _ => (1 : ℂ)) p ∂J = (J.real S : ℂ) := by
      rw [← integral_indicator_one hS, ← integral_complex_ofReal]
      congr 1; funext p; by_cases h : p ∈ S <;> simp [h]
    -- invariance of `X`
    have hXγ : ∀ γ : Γ, ∫ p, F o (γ +ᵥ p) * S.indicator (fun _ => (1 : ℂ)) p ∂J = X := by
      intro γ
      rw [hX, ← integral_vadd_eq_self (μ := J) (fun p => F o p * S.indicator (fun _ => (1 : ℂ)) p)
        (g := γ)]
      refine integral_congr_ae ((hSinv γ).mono fun p hp => ?_)
      have hp' : (γ +ᵥ p ∈ S) = (p ∈ S) := hp
      simp only [Set.indicator, hp']
    -- the estimate
    have hest : ∀ N, ‖X - c o t * J.real S‖ ^ 2 ≤ a o N t := by
      intro N
      have hb1 : Bdd fun p : Y × Y => avg (Φ N) (fun γ => F o (γ +ᵥ p)) - c o t :=
        (Bdd.avg _ fun γ _ => (hFb o).comp (measurable_const_vadd γ)).sub (Bdd.const _)
      have e1 : X - c o t * J.real S =
          ∫ p, (avg (Φ N) (fun γ => F o (γ +ᵥ p)) - c o t) * conj (S.indicator (fun _ => 1) p) ∂J := by
        have : (fun p => (avg (Φ N) (fun γ => F o (γ +ᵥ p)) - c o t) *
            conj (S.indicator (fun _ => (1 : ℂ)) p)) = fun p =>
            avg (Φ N) (fun γ => F o (γ +ᵥ p) * S.indicator (fun _ => (1 : ℂ)) p) -
              c o t * S.indicator (fun _ => (1 : ℂ)) p := by
          funext p
          have hc : conj (S.indicator (fun _ => (1 : ℂ)) p) = S.indicator (fun _ => 1) p := by
            by_cases h : p ∈ S <;> simp [h]
          rw [hc, sub_mul]
          congr 1
          simp only [avg, Complex.real_smul, Finset.sum_mul, mul_assoc]
        rw [this, integral_sub, integral_const_mul, hSr]
        · congr 1
          simp only [avg]
          rw [integral_smul, integral_finsetSum]
          · simp only [hXγ, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
            rw [inv_mul_cancel₀ (hΦ.card_pos N).ne', one_smul]
          · intro γ _
            exact (((hFb o).comp (measurable_const_vadd γ)).mul hSb).integrable
        · exact (Bdd.avg _ fun γ _ => ((hFb o).comp (measurable_const_vadd γ)).mul hSb).integrable
        · exact (hSb.const_mul _).integrable
      rw [e1]
      have hcs := norm_integral_mul_conj_sq_le (μ := J) (hb1.memLp 2) (hSb.memLp 2)
      have hS1 : ∫ p, ‖S.indicator (fun _ => (1 : ℂ)) p‖ ^ 2 ∂J ≤ 1 := by
        calc ∫ p, ‖S.indicator (fun _ => (1 : ℂ)) p‖ ^ 2 ∂J ≤ ∫ _p, (1 : ℝ) ∂J :=
              integral_mono_of_nonneg (Eventually.of_forall fun p => by positivity)
                (integrable_const _) (Eventually.of_forall fun p => by
                  by_cases h : p ∈ S <;> simp [h])
          _ = 1 := by simp
      have ha : ∫ p, ‖avg (Φ N) (fun γ => F o (γ +ᵥ p)) - c o t‖ ^ 2 ∂J = a o N t := by
        rw [hadef]
        refine integral_congr_ae (hconc.mono fun p hp => ?_)
        simp only [hΨdef]
        rw [hp, add_sub_cancel_left]
      rw [ha] at hcs
      calc _ ≤ a o N t * ∫ p, ‖S.indicator (fun _ => (1 : ℂ)) p‖ ^ 2 ∂J := hcs
        _ ≤ a o N t * 1 := mul_le_mul_of_nonneg_left hS1 (ha_nonneg o N t)
        _ = a o N t := mul_one _
    -- conclude `X = c J(S)`
    have hzero : ‖X - c o t * J.real S‖ ^ 2 = 0 := by
      refine le_antisymm ?_ (sq_nonneg _)
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hfreq : ∃ᶠ N in atTop, ENNReal.ofReal (a o N t) < ENNReal.ofReal ε := by
        refine frequently_lt_of_liminf_lt (by isBoundedDefault) ?_
        rw [ht o]; exact ENNReal.ofReal_pos.2 hε
      obtain ⟨N, hN⟩ := hfreq.exists
      have := (ENNReal.ofReal_lt_ofReal_iff hε).1 hN
      linarith [hest N]
    have : X = c o t * J.real S := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hzero
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    rw [hXr, hcr] at this
    exact_mod_cast this
  -- hence `J|_S = J(S) J`
  have hmeas_eq : J.restrict S = J S • J := by
    refine measure_ext_piFam fun A hA B hB => ?_
    have hAB := (measurableSet_of_mem_piFam hA).prod (measurableSet_of_mem_piFam hB)
    rw [Measure.restrict_apply hAB, Measure.smul_apply, smul_eq_mul]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1
    have := hfact (⟨A, hA⟩, ⟨B, hB⟩)
    simp only [measureReal_def] at this
    rw [this, ENNReal.toReal_mul, mul_comm]
  have hSS := congrArg (fun ν : Measure (Y × Y) => ν S) hmeas_eq
  simp only [Measure.restrict_apply hS, Set.inter_self, Measure.smul_apply, smul_eq_mul] at hSS
  rw [eventuallyConst_set]
  have hfin : J S ≠ ⊤ := measure_ne_top _ _
  rcases eq_or_ne (J S) 0 with h0 | h0
  · right
    exact measure_eq_zero_iff_ae_notMem.1 h0
  · left
    have h1 : J S = 1 := by
      have := hSS
      calc J S = J S * J S / J S := by rw [ENNReal.mul_div_cancel_right h0 hfin]
        _ = J S / J S := by rw [← this]
        _ = 1 := ENNReal.div_self h0 hfin
    have hc : J Sᶜ = 0 := by
      rw [measure_compl hS hfin, h1, measure_univ, tsub_self]
    exact measure_eq_zero_iff_ae_notMem.1 hc |>.mono fun p hp => by simpa using hp

end Step3

end Kmrr25.ThmK
