import Kmrr25.ThmKPairs

/-!
# Theorem K: the cube criterion

Paper, Proposition \ref{K:prop:criterion}. We prove it for an abstract system `Y` (a compact
metric `Γ`-system) with a finite family of "faces" `L_i, U_i : Y → Y`; in
`Kmrr25.ThmKStep` it is applied to the cube spaces `X^{[m]}` with the (duplicating) lower and
upper faces.

* `claimB` — Claim B of the paper (directions `i ≤ m`), via the decomposition of `1_S` into its
  Kronecker part and its weakly mixing part, continuity of translation on the Kronecker group of
  the face measure, and the phase returns of Lemma \ref{K:lem:phase};
* `cube_criterion` — the nested-boxes construction.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

open Q516

universe u

section ClaimBParts

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}
variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [AddAction Γ Y] [AddAction Γ Z]
  [StandardBorelSpace Z] [Nonempty Z]
variable {μ : Measure Y} [IsProbabilityMeasure μ] {ν : Measure Z} [IsProbabilityMeasure ν]
  {ι : Z → KG α}

/-- Positivity (paper, proof of Claim B, using \cite[Remark 2.2]{kra2026short}):
`∫_V ν_{ι(U x)}(S) dλ(x) > 0` when `U(V) ⊆ S` and `λ(V) > 0`. -/
lemma pos_integral_tR [TopologicalSpace Z] [BorelSpace Z] (hι : IsRotFactor ν α ι)
    {U : Y → Z} (hUm : Measurable U) (hUν : μ.map U = ν) {S : Set Z} (hSm : MeasurableSet S)
    {V : Set Y} (hVm : MeasurableSet V) (hVpos : 0 < μ V) (hVS : ∀ x ∈ V, U x ∈ S) :
    0 < ∫ x, V.indicator (fun _ => (1 : ℝ)) x * tR ν ι S (ι (U x)) ∂μ := by
  set G : KG α → ℝ := tR ν ι S with hGdef
  have hGm : Measurable G := measurable_tR hSm
  have hG0 : ∀ ξ, 0 ≤ G ξ := tR_nonneg S
  have hG1 : ∀ ξ, G ξ ≤ 1 := tR_le_one S
  set B := {ξ : KG α | G ξ ≤ 0} with hB
  have hBm : MeasurableSet B := measurableSet_le hGm measurable_const
  have hnull : ν (S ∩ ι ⁻¹' B) = 0 := by
    have h1 := graph_real_prod hι hSm hBm
    have h2 : (graphMeasure ν ι) (S ×ˢ B) = ν (S ∩ ι ⁻¹' B) := by
      rw [graphMeasure, Measure.map_apply (measurable_id'.prodMk hι.measurable) (hSm.prod hBm)]
      rfl
    have h3 : ∫ ξ, B.indicator (fun _ => (1 : ℝ)) ξ * tR ν ι S ξ ∂haarK α = 0 := by
      refine integral_eq_zero_of_ae (Eventually.of_forall fun ξ => ?_)
      simp only [Set.indicator, hB, Set.mem_setOf_eq, Pi.zero_apply]
      split_ifs with h
      · have := hG0 ξ; simp only [hGdef] at h this ⊢; linarith
      · simp
    have : IsProbabilityMeasure (graphMeasure ν ι) := isProbabilityMeasure_graphMeasure hι.measurable
    rw [h3, measureReal_eq_zero_iff, h2] at h1
    exact h1
  have hnullμ : μ (U ⁻¹' (S ∩ ι ⁻¹' B)) = 0 := by
    rw [← Measure.map_apply hUm (hSm.inter (hι.measurable hBm)), hUν, hnull]
  have hint : Integrable (fun x => V.indicator (fun _ => (1 : ℝ)) x * G (ι (U x))) μ :=
    Integrable.of_bound ((measurable_const.indicator hVm).mul
      (hGm.comp (hι.measurable.comp hUm))).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_one₀ ?_ (abs_nonneg _) ?_
        · by_cases h : x ∈ V <;> simp [h]
        · rw [abs_of_nonneg (hG0 _)]; exact hG1 _)
  rw [integral_pos_iff_support_of_nonneg (fun x => mul_nonneg
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hG0 _)) hint]
  refine hVpos.trans_le (le_trans ?_ (measure_mono (s := V \ U ⁻¹' (S ∩ ι ⁻¹' B)) ?_))
  · rw [measure_diff_null hnullμ]
  · intro x ⟨hxV, hxN⟩
    simp only [Function.mem_support, Set.indicator, hxV, if_true, one_mul]
    have hxS := hVS x hxV
    have : ¬ G (ι (U x)) ≤ 0 := fun h => hxN ⟨hxS, h⟩
    intro h0
    exact this (le_of_eq h0)

/-- The Kronecker estimate of Claim B: if `α β - r` is close to `0`, then
`∫_V G(ι(L(T^β x))) dλ` is close to `∫_V G(ι(U x)) dλ`. -/
lemma kronecker_estimate [MeasurableConstVAdd Γ Y] {L U : Y → Z}
    (hL : IsFactorMap (Γ := Γ) μ ν L) (hι : IsRotFactor ν α ι) {r : KG α}
    (hr : ∀ᵐ x ∂μ, ι (U x) = ι (L x) + r) {G : KG α → ℝ} (hGm : Measurable G)
    (hGb : ∀ ξ, |G ξ| ≤ 1) {V : Set Y} (hVm : MeasurableSet V) (β : Γ) :
    |(∫ x, V.indicator (fun _ => (1 : ℝ)) x * G (ι (L (β +ᵥ x))) ∂μ) -
      ∫ x, V.indicator (fun _ => (1 : ℝ)) x * G (ι (U x)) ∂μ| ≤
      ∫ z, |G (z + (kα α β - r)) - G z| ∂haarK α := by
  have hmapιL : μ.map (fun x => ι (L x)) = haarK α := by
    rw [show (fun x => ι (L x)) = ι ∘ L from rfl, ← Measure.map_map hι.measurable hL.measurable,
      hL.map_eq, hι.map_eq]
  have hiV : ∀ x, |V.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := fun x => by
    by_cases h : x ∈ V <;> simp [h]
  have hbd : ∀ (H : Y → ℝ), Measurable H → (∀ x, |H x| ≤ 1) → Integrable H μ := fun H hH hb =>
    Integrable.of_bound hH.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hb x)
  have e1 : (∫ x, V.indicator (fun _ => (1 : ℝ)) x * G (ι (L (β +ᵥ x))) ∂μ) =
      ∫ x, V.indicator (fun _ => (1 : ℝ)) x * G (ι (L x) + kα α β) ∂μ :=
    integral_congr_ae ((hL.ae_equivariant_comp hι β).mono fun x hx => by simp only [hx])
  have e2 : (∫ x, V.indicator (fun _ => (1 : ℝ)) x * G (ι (U x)) ∂μ) =
      ∫ x, V.indicator (fun _ => (1 : ℝ)) x * G (ι (L x) + r) ∂μ :=
    integral_congr_ae (hr.mono fun x hx => by simp only [hx])
  have hm1 : Measurable fun x => V.indicator (fun _ => (1 : ℝ)) x * G (ι (L x) + kα α β) :=
    (measurable_const.indicator hVm).mul (hGm.comp ((hι.measurable.comp hL.measurable).add_const _))
  have hm2 : Measurable fun x => V.indicator (fun _ => (1 : ℝ)) x * G (ι (L x) + r) :=
    (measurable_const.indicator hVm).mul (hGm.comp ((hι.measurable.comp hL.measurable).add_const _))
  rw [e1, e2, ← integral_sub (hbd _ hm1 fun x => by
    rw [abs_mul]; exact mul_le_one₀ (hiV x) (abs_nonneg _) (hGb _))
    (hbd _ hm2 fun x => by rw [abs_mul]; exact mul_le_one₀ (hiV x) (abs_nonneg _) (hGb _))]
  refine abs_integral_le_integral_abs.trans ?_
  have hm3 : Measurable fun z : KG α => |G (z + kα α β) - G (z + r)| :=
    ((hGm.comp (measurable_add_const _)).sub (hGm.comp (measurable_add_const _))).abs
  calc ∫ x, |V.indicator (fun _ => (1 : ℝ)) x * G (ι (L x) + kα α β) -
        V.indicator (fun _ => (1 : ℝ)) x * G (ι (L x) + r)| ∂μ
      ≤ ∫ x, |G (ι (L x) + kα α β) - G (ι (L x) + r)| ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) ?_
          (Eventually.of_forall fun x => ?_)
        · refine Integrable.of_bound (hm3.comp (hι.measurable.comp hL.measurable)).aestronglyMeasurable
            2 (Eventually.of_forall fun x => ?_)
          rw [Real.norm_eq_abs, abs_abs]
          have := hGb (ι (L x) + kα α β); have := hGb (ι (L x) + r)
          calc |G (ι (L x) + kα α β) - G (ι (L x) + r)| ≤ |G (ι (L x) + kα α β)| + |G (ι (L x) + r)| :=
                abs_sub _ _
            _ ≤ 2 := by linarith
        · dsimp only
          rw [← mul_sub, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hiV x)
    _ = ∫ z, |G (z + kα α β) - G (z + r)| ∂haarK α := by
        rw [← hmapιL, integral_map (φ := fun x => ι (L x))
          (hι.measurable.comp hL.measurable).aemeasurable hm3.aestronglyMeasurable]
    _ = ∫ z, |G (z + (kα α β - r)) - G z| ∂haarK α := by
        rw [← integral_haarK_add_real (fun z => |G (z + (kα α β - r)) - G z|) r]
        congr 1; funext z
        rw [show z + r + (kα α β - r) = z + kα α β by abel]

/-- The weakly mixing part `(1_S - 𝔼(1_S | ι)) ∘ L` of Claim B. -/
def faceWM (ν : Measure Z) [IsProbabilityMeasure ν] (ι : Z → KG α) (S : Set Z) (L : Y → Z)
    (x : Y) : ℂ :=
  S.indicator (fun _ => (1 : ℂ)) (L x) - tilde ν ι (S.indicator fun _ => (1 : ℂ)) (ι (L x))

lemma faceWM_bdd (hι : Measurable ι) {S : Set Z} (hS : MeasurableSet S) {L : Y → Z}
    (hL : Measurable L) : Bdd (faceWM ν ι S L) :=
  ((Bdd.indicator hS).sub ((Bdd.indicator hS).tilde.comp hι)).comp hL

end ClaimBParts

lemma faceWM_weakMixing {Γ Y Z : Type u} [AddCommGroup Γ] [Countable Γ] {α : Γ →+ Torus}
    [MeasurableSpace Y] [AddAction Γ Y] [MeasurableConstVAdd Γ Y]
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddAction Γ Z] [ContinuousConstVAdd Γ Z] [Nonempty Z]
    {μ : Measure Y} {ν : Measure Z} [IsProbabilityMeasure ν] [VAddInvariantMeasure Γ Z ν]
    {ι : Z → KG α} (hW : WienerKoopman.{u}) (hι : IsKroneckerMap ν α ι) {L : Y → Z}
    (hL : IsFactorMap (Γ := Γ) μ ν L) {S : Set Z} (hS : MeasurableSet S) :
    WeakMixing Γ μ (faceWM ν ι S L) := by
  have hwmν := hι.weakMixing_sub_tilde hW (Bdd.indicator hS)
  have hv : Measurable fun z => S.indicator (fun _ => (1 : ℂ)) z -
      tilde ν ι (S.indicator fun _ => (1 : ℂ)) (ι z) :=
    ((Bdd.indicator hS).sub ((Bdd.indicator hS).tilde.comp hι.measurable)).meas
  have := WeakMixing.comp hL.measurable hL.equivariant hv (by rw [hL.map_eq]; exact hwmν)
  exact this

section ClaimB


variable {Γ Y Z : Type u} [AddCommGroup Γ] [Countable Γ] [Infinite Γ]
variable [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y]
  [ContinuousConstVAdd Γ Y]
variable [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [AddAction Γ Z] [ContinuousConstVAdd Γ Z]

/-- Paper, proof of Proposition \ref{K:prop:criterion}, Claim B. -/
theorem claimB (hG : GenericPointsExist.{u}) (hK : DiscreteSpectrumThm.{u})
    (hW : WienerKoopman.{u}) {μ : Measure Y} [IsProbabilityMeasure μ] [ErgodicVAdd Γ Y μ]
    {Ψ : ℕ → Finset Γ} {w : Y} (hw : IsGeneric μ Ψ w) {L U : Y → Z} (hLc : Continuous L)
    (hUc : Continuous U) (hLe : ∀ (γ : Γ) y, L (γ +ᵥ y) = γ +ᵥ L y)
    (hUe : ∀ (γ : Γ) y, U (γ +ᵥ y) = γ +ᵥ U y) (hface : μ.map L = μ.map U)
    (hsupp : U w ∈ (μ.map U).support) {V : Set Y} (hVo : IsOpen V) (hVpos : 0 < μ V)
    {S : Set Z} (hSo : IsOpen S) (hVS : ∀ x ∈ V, U x ∈ S) {V' : Set Z} (hV'o : IsOpen V')
    (hwV' : U w ∈ V') (F : Finset Γ) :
    ∃ β : Γ, β ∉ F ∧ β +ᵥ L w ∈ V' ∧ 0 < μ (V ∩ {x | β +ᵥ L x ∈ S}) := by
  have : IsProbabilityMeasure (μ.map U) :=
    Measure.isProbabilityMeasure_map hUc.measurable.aemeasurable
  have : ErgodicVAdd Γ Z (μ.map U) := ErgodicVAdd.map hUc.measurable hUe
  have : Nonempty Z := ⟨U w⟩
  obtain ⟨α, ι, hι⟩ := hK Γ Z (μ.map U)
  have hιR := hι.toRotFactor
  have hLf : IsFactorMap (Γ := Γ) μ (μ.map U) L := ⟨hLc.measurable, hLe, hface⟩
  have hUf : IsFactorMap (Γ := Γ) μ (μ.map U) U := ⟨hUc.measurable, hUe, rfl⟩
  obtain ⟨r, hr⟩ := phase_const hLf hUf hιR
  have hSm := hSo.measurableSet
  have hVm := hVo.measurableSet
  have hGm : Measurable (tR (μ.map U) ι S) := measurable_tR hSm
  have hGb : ∀ ξ, |tR (μ.map U) ι S ξ| ≤ 1 := abs_tR_le S
  have hGc : Bdd fun ξ => (tR (μ.map U) ι S ξ : ℂ) :=
    ⟨Complex.continuous_ofReal.measurable.comp hGm, 1, fun ξ => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hGb ξ⟩
  have hηpos := pos_integral_tR hιR hUc.measurable rfl hSm hVm hVpos hVS
  set ηV := ∫ x, V.indicator (fun _ => (1 : ℝ)) x * tR (μ.map U) ι S (ι (U x)) ∂μ with hηV
  -- the neighbourhood `O`
  obtain ⟨O, hOsub, hOo, hO0⟩ := eventually_nhds_iff.1
    (eventually_integral_norm_translate_sub_lt hGc (show 0 < ηV / 4 by positivity))
  -- phase returns
  obtain ⟨Ω, hΩ, c0, hc0, hR⟩ := phase_returns hG hw hLc hUc hLf hUf hιR hr hsupp hV'o hwV'
    hOo hO0
  -- the weakly mixing part
  have hhb : Bdd (faceWM (μ.map U) ι S L) := faceWM_bdd hιR.measurable hSm hLc.measurable
  have hwmμ : WeakMixing Γ μ (faceWM (μ.map U) ι S L) := faceWM_weakMixing hW hι hLf hSm
  have hVb : Bdd (V.indicator fun _ => (1 : ℂ)) := Bdd.indicator hVm
  have hwmlim := hwmμ.tendsto_avg_norm_inner hhb hVb hΩ
  set R := {γ : Γ | γ +ᵥ L w ∈ V' ∧ kα α γ - r ∈ O} with hRdef
  set R' := {γ : Γ | ηV / 4 ≤
    ‖∫ x, faceWM (μ.map U) ι S L (γ +ᵥ x) * conj (V.indicator (fun _ => (1 : ℂ)) x) ∂μ‖}
    with hR'def
  have hR'lim : ∀ᶠ M in atTop, relDens (Ω M) R' < c0 / 2 := by
    have hlim := hwmlim.const_mul (4 / ηV)
    rw [mul_zero] at hlim
    refine (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < c0 / 2 by positivity))).mono
      fun M hM => lt_of_le_of_lt ?_ hM
    rw [relDens_eq_avg, ← smul_eq_mul, ← avg_smul]
    refine avg_real_mono fun γ _ => ?_
    simp only [hR'def, Set.mem_setOf_eq, smul_eq_mul]
    split_ifs with hγ
    · have e : 4 / ηV * (ηV / 4) = 1 := by field_simp
      calc (1 : ℝ) = 4 / ηV * (ηV / 4) := e.symm
        _ ≤ 4 / ηV * _ := mul_le_mul_of_nonneg_left hγ (by positivity)
    · positivity
  -- `R ∖ R'` is infinite
  have hRR' : ∀ᶠ M in atTop, c0 / 2 < relDens (Ω M) (R \ R') := by
    filter_upwards [hR, hR'lim] with M h1 h2
    have := relDens_union_le (Ω M) (R \ R') R'
    have hsub : relDens (Ω M) R ≤ relDens (Ω M) ((R \ R') ∪ R') :=
      relDens_mono _ (fun γ hγ => by by_cases h' : γ ∈ R' <;> simp [h', hγ])
    linarith
  have hinf := infinite_of_eventually_lt_relDens hΩ (half_pos hc0) hRR'
  obtain ⟨β, ⟨⟨hβV', hβO⟩, hβR'⟩, hβF⟩ := (hinf.diff F.finite_toSet).nonempty
  refine ⟨β, hβF, hβV', ?_⟩
  -- the final estimate
  have hkr := kronecker_estimate hLf hιR hr hGm hGb hVm β
  have hO' : ∫ z, |tR (μ.map U) ι S (z + (kα α β - r)) - tR (μ.map U) ι S z| ∂haarK α < ηV / 4 := by
    have := hOsub _ hβO
    simpa [← Complex.ofReal_sub, Complex.norm_real] using this
  have hR'β : ‖∫ x, faceWM (μ.map U) ι S L (β +ᵥ x) * conj (V.indicator (fun _ => (1 : ℂ)) x) ∂μ‖ <
      ηV / 4 :=
    lt_of_not_ge hβR'
  -- decomposition of `λ(V ∩ {T^β L x ∈ S})`
  have hdec : ((μ.real (V ∩ {x | β +ᵥ L x ∈ S}) : ℝ) : ℂ) =
      ((∫ x, V.indicator (fun _ => (1 : ℝ)) x * tR (μ.map U) ι S (ι (L (β +ᵥ x))) ∂μ : ℝ) : ℂ) +
        ∫ x, faceWM (μ.map U) ι S L (β +ᵥ x) * conj (V.indicator (fun _ => (1 : ℂ)) x) ∂μ := by
    have hmS : MeasurableSet {x | β +ᵥ L x ∈ S} :=
      hSm.preimage ((continuous_const_vadd β).comp hLc).measurable
    have hpt : ∀ x, ((((V ∩ {x | β +ᵥ L x ∈ S}).indicator (1 : Y → ℝ) x : ℝ)) : ℂ) =
        ((V.indicator (fun _ => (1 : ℝ)) x * tR (μ.map U) ι S (ι (L (β +ᵥ x))) : ℝ) : ℂ) +
          faceWM (μ.map U) ι S L (β +ᵥ x) * conj (V.indicator (fun _ => (1 : ℂ)) x) := by
      intro x
      simp only [faceWM, tilde_indicator_eq hSm, hLe]
      by_cases hV : x ∈ V <;> by_cases hS' : β +ᵥ L x ∈ S <;>
        simp [Set.indicator, hV, hS', Set.mem_inter_iff]
    have i1 : Integrable (fun x => ((V.indicator (fun _ => (1 : ℝ)) x *
        tR (μ.map U) ι S (ι (L (β +ᵥ x))) : ℝ) : ℂ)) μ := by
      refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun x => ?_)
      · exact (Complex.continuous_ofReal.measurable.comp ((measurable_const.indicator hVm).mul
          (hGm.comp (hιR.measurable.comp (hLc.measurable.comp (measurable_const_vadd β))))))
          |>.aestronglyMeasurable
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
        refine mul_le_one₀ ?_ (abs_nonneg _) (hGb _)
        by_cases h : x ∈ V <;> simp [h]
    have i2 : Integrable (fun x => faceWM (μ.map U) ι S L (β +ᵥ x) *
        conj (V.indicator (fun _ => (1 : ℂ)) x)) μ :=
      ((hhb.comp (measurable_const_vadd β)).mul hVb.conj').integrable
    rw [← integral_indicator_one (hVm.inter hmS), ← integral_complex_ofReal,
      ← integral_complex_ofReal, ← integral_add i1 i2]
    congr 1; funext x; exact hpt x
  have hre := congrArg Complex.re hdec
  simp only [Complex.ofReal_re, Complex.add_re] at hre
  have h1 := Complex.re_le_norm (∫ x, faceWM (μ.map U) ι S L (β +ᵥ x) * conj (V.indicator (fun _ => (1 : ℂ)) x) ∂μ)
  have h2 := neg_abs_le (∫ x, faceWM (μ.map U) ι S L (β +ᵥ x) * conj (V.indicator (fun _ => (1 : ℂ)) x) ∂μ).re
  have h3 := Complex.abs_re_le_norm (∫ x, faceWM (μ.map U) ι S L (β +ᵥ x) * conj (V.indicator (fun _ => (1 : ℂ)) x) ∂μ)
  have hk := abs_sub_lt_iff.1 (lt_of_le_of_lt hkr hO')
  have hpos : 0 < μ.real (V ∩ {x | β +ᵥ L x ∈ S}) := by linarith [hk.1, hk.2]
  rw [measureReal_def] at hpos
  exact (ENNReal.toReal_pos_iff.1 hpos).1

end ClaimB

/-! ## The nested-boxes construction -/

section Nested

variable {Γ Y : Type u} [AddCommGroup Γ] [Countable Γ] [Infinite Γ]
variable [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y]
  [ContinuousConstVAdd Γ Y]

/-- Every open set of positive measure contains a small closed ball whose open ball has positive
measure. -/
lemma exists_ball_pos {μ : Measure Y} {W : Set Y} (hW : IsOpen W) (hpos : 0 < μ W) {ε : ℝ}
    (hε : 0 < ε) : ∃ c : Y, ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧ Metric.closedBall c r ⊆ W ∧
      0 < μ (Metric.ball c r) := by
  have hrad : ∀ x : W, ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧ Metric.closedBall (x : Y) r ⊆ W := by
    intro x
    obtain ⟨s, hs, hsW⟩ := Metric.isOpen_iff.1 hW x x.2
    refine ⟨min (s / 2) ε, lt_min (half_pos hs) hε, min_le_right _ _, ?_⟩
    exact (Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hs))).trans
      hsW
  choose r hr0 hrε hrW using hrad
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : W => Metric.ball (x : Y) (r x)) fun x => Metric.isOpen_ball
  have hcover : W = ⋃ x ∈ T, Metric.ball (x : Y) (r x) := by
    rw [hTU]
    ext y; constructor
    · intro hy; exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (hr0 _)⟩
    · intro hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.1 hy
      exact hrW x (Metric.ball_subset_closedBall hx)
  by_contra hne
  push_neg at hne
  have : μ W = 0 := by
    rw [hcover]
    refine (measure_biUnion_null_iff hTc).2 fun x _ => ?_
    exact le_antisymm (hne x (r x) (hr0 x) (hrε x) (hrW x)) bot_le
  exact hpos.ne' this

/-- One step of the nested construction. -/
lemma nested_step (hG : GenericPointsExist.{u}) (hK : DiscreteSpectrumThm.{u})
    (hW : WienerKoopman.{u}) {μ : Measure Y} [IsProbabilityMeasure μ] [ErgodicVAdd Γ Y μ]
    {Ψ : ℕ → Finset Γ} (hΨ : IsFolner Ψ) {w : Y} (hw : IsGeneric μ Ψ w) {m : ℕ}
    (L U : Fin m → Y → Y) (hLc : ∀ i, Continuous (L i)) (hUc : ∀ i, Continuous (U i))
    (hLe : ∀ i (γ : Γ) y, L i (γ +ᵥ y) = γ +ᵥ L i y)
    (hUe : ∀ i (γ : Γ) y, U i (γ +ᵥ y) = γ +ᵥ U i y)
    (hUlip : ∀ i x y, dist (U i x) (U i y) ≤ dist x y) (hface : ∀ i, μ.map (L i) = μ.map (U i))
    (hsupp : ∀ i, U i w ∈ (μ.map (U i)).support) (n : ℕ) (d : Fin (m + 1)) (c : Y) (r : ℝ)
    (hr : 0 < μ (Metric.ball c r)) (F : Finset Γ) :
    ∃ β : Γ, β ∉ F ∧ ∃ c' : Y, ∃ r' : ℝ, 0 < r' ∧ r' ≤ 1 / ((n : ℝ) + 1) ∧
      Metric.closedBall c' r' ⊆ Metric.ball c r ∧ 0 < μ (Metric.ball c' r') ∧
      (d = Fin.last m → β +ᵥ w ∈ Metric.ball c r) ∧
      (∀ i : Fin m, d = Fin.castSucc i → dist (β +ᵥ L i w) (U i w) < 1 / ((n : ℝ) + 1) ∧
        ∀ x ∈ Metric.ball c' r', dist (β +ᵥ L i x) (U i x) < 1 / ((n : ℝ) + 1) + 2 * r) := by
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  induction d using Fin.lastCases with
  | last =>
    obtain ⟨c0, hc0, hev⟩ := hw.exists_eventually_lt_relDens Metric.isOpen_ball hr
    have hinf := infinite_of_eventually_lt_relDens hΨ hc0 hev
    obtain ⟨β, hβ, hβF⟩ := (hinf.diff F.finite_toSet).nonempty
    obtain ⟨c', r', hr'0, hr'n, hcl, hpos⟩ := exists_ball_pos Metric.isOpen_ball hr hδ
    refine ⟨β, hβF, c', r', hr'0, hr'n, hcl, hpos, fun _ => hβ, fun i hi => ?_⟩
    exact absurd hi.symm (Fin.castSucc_ne_last i)
  | cast i =>
    set S := Metric.thickening (1 / ((n : ℝ) + 1)) (U i '' Metric.ball c r) with hS
    have hVS : ∀ x ∈ Metric.ball c r, U i x ∈ S := fun x hx =>
      Metric.self_subset_thickening hδ _ ⟨x, hx, rfl⟩
    obtain ⟨β, hβF, hβV', hβpos⟩ := claimB hG hK hW hw (hLc i) (hUc i) (hLe i) (hUe i)
      (hface i) (hsupp i) Metric.isOpen_ball hr Metric.isOpen_thickening hVS
      (Metric.isOpen_ball (x := U i w) (ε := 1 / ((n : ℝ) + 1))) (Metric.mem_ball_self hδ) F
    have hWo : IsOpen (Metric.ball c r ∩ {x | β +ᵥ L i x ∈ S}) :=
      Metric.isOpen_ball.inter (Metric.isOpen_thickening.preimage
        ((continuous_const_vadd β).comp (hLc i)))
    obtain ⟨c', r', hr'0, hr'n, hcl, hpos⟩ := exists_ball_pos hWo hβpos hδ
    refine ⟨β, hβF, c', r', hr'0, hr'n, hcl.trans Set.inter_subset_left, hpos,
      fun h => absurd h (Fin.castSucc_ne_last i), fun i' hi' => ?_⟩
    have hii : i = i' := Fin.castSucc_injective _ hi'
    subst hii
    refine ⟨hβV', fun x hx => ?_⟩
    have hxW := hcl (Metric.ball_subset_closedBall hx)
    obtain ⟨z, ⟨v, hv, rfl⟩, hz⟩ := Metric.mem_thickening_iff.1 hxW.2
    have h1 : dist (U i v) (U i x) < 2 * r := by
      refine (hUlip i v x).trans_lt ?_
      have := dist_triangle v c x
      rw [Metric.mem_ball] at hv
      have hx' : dist x c < r := hxW.1
      rw [dist_comm c x] at this
      linarith
    calc dist (β +ᵥ L i x) (U i x) ≤ dist (β +ᵥ L i x) (U i v) + dist (U i v) (U i x) :=
          dist_triangle _ _ _
      _ < 1 / ((n : ℝ) + 1) + 2 * r := add_lt_add hz h1

/-- Paper, Proposition \ref{K:prop:criterion} (cube criterion), abstract form: for a cube datum
there is a point `x ∈ V₀` such that `(w, x)` satisfies all the Erdős-cube conditions. -/
theorem cube_criterion (hG : GenericPointsExist.{u}) (hK : DiscreteSpectrumThm.{u})
    (hW : WienerKoopman.{u}) {μ : Measure Y} [IsProbabilityMeasure μ] [ErgodicVAdd Γ Y μ]
    {Ψ : ℕ → Finset Γ} (hΨ : IsFolner Ψ) {w : Y} (hw : IsGeneric μ Ψ w) {m : ℕ}
    (L U : Fin m → Y → Y) (hLc : ∀ i, Continuous (L i)) (hUc : ∀ i, Continuous (U i))
    (hLe : ∀ i (γ : Γ) y, L i (γ +ᵥ y) = γ +ᵥ L i y)
    (hUe : ∀ i (γ : Γ) y, U i (γ +ᵥ y) = γ +ᵥ U i y)
    (hUlip : ∀ i x y, dist (U i x) (U i y) ≤ dist x y) (hface : ∀ i, μ.map (L i) = μ.map (U i))
    (hsupp : ∀ i, U i w ∈ (μ.map (U i)).support) {V0 : Set Y} (hV0o : IsOpen V0)
    (hV0 : 0 < μ V0) :
    ∃ x ∈ V0, (∃ β : ℕ → Γ, Function.Injective β ∧ Tendsto (fun n => β n +ᵥ w) atTop (𝓝 x)) ∧
      ∀ i : Fin m, ∃ β : ℕ → Γ, Function.Injective β ∧
        Tendsto (fun n => β n +ᵥ L i w) atTop (𝓝 (U i w)) ∧
        Tendsto (fun n => β n +ᵥ L i x) atTop (𝓝 (U i x)) := by
  have hstep := nested_step hG hK hW hΨ hw L U hLc hUc hLe hUe hUlip hface hsupp
  choose β hβF c' r' hr'0 hr'n hcl hpos hlast hfaceP using hstep
  obtain ⟨c0, r0, hr00, hr01, hcl0, hpos0⟩ := exists_ball_pos hV0o hV0 one_pos
  let dir : ℕ → Fin (m + 1) := fun n => ⟨n % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
  let St := {p : Y × ℝ × Finset Γ // 0 < μ (Metric.ball p.1 p.2.1)}
  let next : ℕ → St → St := fun n p =>
    ⟨(c' n (dir n) p.1.1 p.1.2.1 p.2 p.1.2.2, r' n (dir n) p.1.1 p.1.2.1 p.2 p.1.2.2,
      insert (β n (dir n) p.1.1 p.1.2.1 p.2 p.1.2.2) p.1.2.2), hpos n (dir n) _ _ p.2 _⟩
  let seq : ℕ → St := fun n => Nat.rec ⟨(c0, r0, ∅), hpos0⟩ (fun n p => next n p) n
  have hseq : ∀ n, seq (n + 1) = next n (seq n) := fun n => rfl
  let cc : ℕ → Y := fun n => (seq n).1.1
  let rr : ℕ → ℝ := fun n => (seq n).1.2.1
  let used : ℕ → Finset Γ := fun n => (seq n).1.2.2
  let bb : ℕ → Γ := fun n => β n (dir n) (cc n) (rr n) (seq n).2 (used n)
  have hcc : ∀ n, cc (n + 1) = c' n (dir n) (cc n) (rr n) (seq n).2 (used n) := fun n => rfl
  have hrr : ∀ n, rr (n + 1) = r' n (dir n) (cc n) (rr n) (seq n).2 (used n) := fun n => rfl
  have hused : ∀ n, used (n + 1) = insert (bb n) (used n) := fun n => rfl
  have hnest : ∀ n, Metric.closedBall (cc (n + 1)) (rr (n + 1)) ⊆ Metric.ball (cc n) (rr n) :=
    fun n => by rw [hcc, hrr]; exact hcl _ _ _ _ _ _
  have hrr_le : ∀ n, rr (n + 1) ≤ 1 / ((n : ℝ) + 1) := fun n => by rw [hrr]; exact hr'n _ _ _ _ _ _
  have hrr_pos : ∀ n, 0 < rr n := by
    intro n; cases n with
    | zero => exact hr00
    | succ n => rw [hrr]; exact hr'0 _ _ _ _ _ _
  -- the radii tend to `0`
  have hrr_lim : Tendsto rr atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    exact squeeze_zero (fun n => (hrr_pos (n + 1)).le) hrr_le tendsto_one_div_add_atTop_nhds_zero_nat
  -- the chosen group elements are distinct
  have hused_mono : ∀ n n', n ≤ n' → used n ⊆ used n' := by
    intro n n' h
    induction n', h using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => rw [hused]; exact ih.trans (Finset.subset_insert _ _)
  have hbb_inj : Function.Injective bb := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : bb a ∈ used b := hused_mono (a + 1) b h (by rw [hused]; exact Finset.mem_insert_self _ _)
      exact hβF b (dir b) (cc b) (rr b) (seq b).2 (used b) (show bb b ∈ used b by rw [← hab]; exact h1)
    · have h1 : bb b ∈ used a := hused_mono (b + 1) a h (by rw [hused]; exact Finset.mem_insert_self _ _)
      exact hβF a (dir a) (cc a) (rr a) (seq a).2 (used a) (show bb a ∈ used a by rw [hab]; exact h1)
  -- the limit point
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => Metric.closedBall (cc n) (rr n))
    (fun n => (hnest n).trans Metric.ball_subset_closedBall)
    (fun n => ⟨cc n, Metric.mem_closedBall_self (hrr_pos n).le⟩)
    (Metric.isClosed_closedBall).isCompact (fun n => Metric.isClosed_closedBall)
  rw [Set.mem_iInter] at hx
  have hxball : ∀ n, x ∈ Metric.ball (cc n) (rr n) := fun n => hnest n (hx (n + 1))
  -- the subsequences
  let idx : Fin (m + 1) → ℕ → ℕ := fun j k => (m + 1) * k + j.val
  have hdir : ∀ j k, dir (idx j k) = j := by
    intro j k; ext
    simp only [dir, idx]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]
  have hidx_inj : ∀ j, Function.Injective (idx j) := by
    intro j a b h
    simp only [idx] at h
    have : (m + 1) * a = (m + 1) * b := by omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) this
  have hidx_lim : ∀ j, Tendsto (idx j) atTop atTop := fun j =>
    tendsto_atTop_mono (fun k => show k ≤ (m + 1) * k + j.val by nlinarith) tendsto_id
  have hlimr : ∀ j, Tendsto (fun k => rr (idx j k)) atTop (𝓝 0) := fun j =>
    hrr_lim.comp (hidx_lim j)
  have hlim1 : ∀ j, Tendsto (fun k => 1 / ((idx j k : ℝ) + 1)) atTop (𝓝 0) := fun j =>
    tendsto_one_div_add_atTop_nhds_zero_nat.comp (hidx_lim j)
  refine ⟨x, hcl0 (hx 0), ⟨fun k => bb (idx (Fin.last m) k),
    hbb_inj.comp (hidx_inj _), ?_⟩, fun i => ⟨fun k => bb (idx (Fin.castSucc i) k),
    hbb_inj.comp (hidx_inj _), ?_, ?_⟩⟩
  · -- the new direction
    rw [tendsto_iff_dist_tendsto_zero]
    have h2 : Tendsto (fun k => 2 * rr (idx (Fin.last m) k)) atTop (𝓝 0) := by
      simpa using (hlimr (Fin.last m)).const_mul 2
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) h2
    set n := idx (Fin.last m) k
    have h1 : bb n +ᵥ w ∈ Metric.ball (cc n) (rr n) := hlast n (dir n) (cc n) (rr n) (seq n).2
      (used n) (hdir _ _)
    have h3 := hxball n
    rw [Metric.mem_ball] at h1 h3
    have := dist_triangle (bb n +ᵥ w) (cc n) x
    rw [dist_comm (cc n) x] at this
    linarith
  · -- face `i`, the point `w`
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) (hlim1 (Fin.castSucc i))
    set n := idx (Fin.castSucc i) k
    exact ((hfaceP n (dir n) (cc n) (rr n) (seq n).2 (used n) i (hdir _ _)).1).le
  · -- face `i`, the point `x`
    rw [tendsto_iff_dist_tendsto_zero]
    have h2 : Tendsto (fun k => 1 / ((idx (Fin.castSucc i) k : ℝ) + 1) +
        2 * rr (idx (Fin.castSucc i) k)) atTop (𝓝 0) := by
      simpa using (hlim1 (Fin.castSucc i)).add ((hlimr (Fin.castSucc i)).const_mul 2)
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) h2
    set n := idx (Fin.castSucc i) k
    have hxn : x ∈ Metric.ball (c' n (dir n) (cc n) (rr n) (seq n).2 (used n))
        (r' n (dir n) (cc n) (rr n) (seq n).2 (used n)) := by
      have := hxball (n + 1); rw [hcc, hrr] at this; exact this
    exact ((hfaceP n (dir n) (cc n) (rr n) (seq n).2 (used n) i (hdir _ _)).2 x hxn).le

end Nested

end Kmrr25.ThmK
