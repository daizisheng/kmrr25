import Kmrr25.ThmKKron

/-!
# Theorem K: Kronecker factors of factors

Paper, Lemma \ref{K:lem:factor}. Let `P : Y → Z` be an equivariant measurable map with
`P_* μ = ν`, let `κ : Y → K` be a Kronecker map of `μ` and `ι : Z → K'` one of `ν`.

* (b) There is a continuous `χ̄ : K → K'` with `χ̄ ∘ α = α'` (`exists_isFactorHom_of_factor`);
  it is unique (`IsFactorHom.unique`) and additive (`IsFactorHom.map_add`), and
  `ι ∘ P = χ̄ ∘ κ + c` a.e. for some `c` (`IsFactorMap.exists_affine`).
  Instead of Pontryagin duality we use that the coordinates of `K'` are characters: the
  eigenfunctions `e_j ∘ ι ∘ P` of `μ` are functions `g_j ∘ κ`, and continuity of translation in
  `L¹(m_K)` gives continuity of `α γ ↦ α' γ` at `0`.
* (a) `𝔼_μ(f ∘ P | κ) = 𝔼_ν(f | ι) ∘ P`, i.e. `(f ∘ P)~ = f̃(χ̄ · + c)` a.e.
  (`IsFactorMap.tilde_comp_ae_eq`).
* (c) `(P × P)_* J^μ_s = J^ν_{χ̄ s}` for every `s` (`IsFactorMap.map_relJ`).
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

universe u

/-! ## Continuous homomorphisms between Kronecker groups -/

section FactorHom

variable {Γ : Type*} [AddCommGroup Γ] {α α' : Γ →+ Torus}

/-- `χ̄ : K → K'` is continuous with `χ̄ ∘ α = α'`. -/
structure IsFactorHom (α α' : Γ →+ Torus) (χ : KG α → KG α') : Prop where
  continuous : Continuous χ
  comp_eq : ∀ γ, χ (kα α γ) = kα α' γ

lemma IsFactorHom.map_add {χ : KG α → KG α'} (h : IsFactorHom α α' χ) (a b : KG α) :
    χ (a + b) = χ a + χ b := by
  have hd : DenseRange (Prod.map (kα α) (kα α)) := (denseRange_kα α).prodMap (denseRange_kα α)
  have key : (fun p : KG α × KG α => χ (p.1 + p.2)) = fun p => χ p.1 + χ p.2 :=
    hd.equalizer (h.continuous.comp continuous_add)
      ((h.continuous.comp continuous_fst).add (h.continuous.comp continuous_snd))
      (funext fun p => by
        simp only [Function.comp, Prod.map]
        rw [← (kα α).map_add, h.comp_eq, h.comp_eq, h.comp_eq, (kα α').map_add])
  exact congrFun key (a, b)

lemma IsFactorHom.map_zero {χ : KG α → KG α'} (h : IsFactorHom α α' χ) : χ 0 = 0 := by
  have := h.map_add 0 0
  simpa using this

lemma IsFactorHom.map_sub {χ : KG α → KG α'} (h : IsFactorHom α α' χ) (a b : KG α) :
    χ (a - b) = χ a - χ b := by
  have := h.map_add (a - b) b
  rw [sub_add_cancel] at this
  rw [this]; abel

lemma IsFactorHom.unique {χ χ' : KG α → KG α'} (h : IsFactorHom α α' χ)
    (h' : IsFactorHom α α' χ') : χ = χ' :=
  (denseRange_kα α).equalizer h.continuous h'.continuous
    (funext fun γ => by simp [h.comp_eq, h'.comp_eq])

lemma isFactorHom_id : IsFactorHom α α id := ⟨continuous_id, fun _ => rfl⟩

/-- Extension of `α γ ↦ α' γ` from the dense subgroup `α Γ` to `K`. -/
lemma exists_isFactorHom_of_tendsto
    (hc : Tendsto (fun γ => kα α' γ) (comap (kα α) (𝓝 0)) (𝓝 0)) :
    ∃ χ, IsFactorHom α α' χ := by
  letI : UniformSpace Γ := UniformSpace.comap (kα α) inferInstance
  haveI : IsUniformAddGroup Γ := IsUniformAddGroup.comap (kα α)
  have he : IsUniformInducing (kα α) := ⟨rfl⟩
  have hf : UniformContinuous (kα α') := by
    refine uniformContinuous_of_continuousAt_zero (kα α') ?_
    rw [ContinuousAt, map_zero, he.isInducing.nhds_eq_comap, map_zero]
    exact hc
  refine ⟨IsDenseInducing.extend (he.isDenseInducing (denseRange_kα α)) (kα α'),
    (uniformContinuous_uniformly_extend he (denseRange_kα α) hf).continuous,
    uniformly_extend_of_ind he (denseRange_kα α) hf⟩

end FactorHom

/-! ## Factor maps -/

section Factor

variable {Γ : Type*} [AddCommGroup Γ] {α α' : Γ →+ Torus}
variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [AddAction Γ Y] [AddAction Γ Z]

/-- `P : Y → Z` is a factor map from `μ` to `ν`: measurable, everywhere equivariant, `P_* μ = ν`. -/
structure IsFactorMap (μ : Measure Y) (ν : Measure Z) (P : Y → Z) : Prop where
  measurable : Measurable P
  equivariant : ∀ (γ : Γ) y, P (γ +ᵥ y) = γ +ᵥ P y
  map_eq : μ.map P = ν

variable {μ : Measure Y} {ν : Measure Z} {κ : Y → KG α} {ι : Z → KG α'} {P : Y → Z}

lemma IsFactorMap.ae_comp (hP : IsFactorMap (Γ := Γ) μ ν P) {p : Z → Prop} (h : ∀ᵐ z ∂ν, p z) :
    ∀ᵐ y ∂μ, p (P y) := by
  rw [← hP.map_eq] at h
  exact ae_of_ae_map hP.measurable.aemeasurable h

lemma IsFactorMap.ae_equivariant_comp (hP : IsFactorMap (Γ := Γ) μ ν P)
    (hι : IsRotFactor ν α' ι) (γ : Γ) : ∀ᵐ y ∂μ, ι (P (γ +ᵥ y)) = ι (P y) + kα α' γ := by
  filter_upwards [hP.ae_comp (hι.ae_equivariant γ)] with y hy
  rw [hP.equivariant, hy]

/-- The key continuity statement behind Lemma \ref{K:lem:factor}(b): `α γ → 0` forces
`α' γ → 0`. -/
theorem IsFactorMap.tendsto_kα [MeasurableConstVAdd Γ Y] [IsProbabilityMeasure μ]
    [VAddInvariantMeasure Γ Y μ] (hP : IsFactorMap (Γ := Γ) μ ν P) (hκ : IsKroneckerMap μ α κ)
    (hι : IsRotFactor ν α' ι) :
    Tendsto (fun γ => kα α' γ) (comap (kα α) (𝓝 0)) (𝓝 0) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  intro j
  set e : C(KG α', ℂ) := charC α' (Finsupp.single j 1) with he_def
  have he : e ∈ Chars α' := ⟨_, rfl⟩
  have he_apply : ∀ w : KG α', e w = (AddCircle.toCircle ((w : Torus) j) : ℂ) := fun w => by
    simp [he_def, tchr_single]
  -- the eigenfunction `e ∘ ι ∘ P` of `μ`
  set h : Y → ℂ := fun y => e (ι (P y)) with h_def
  have hmeasι : Measurable ι := hι.measurable
  have hhb : Bdd h := ⟨e.continuous.measurable.comp (hι.measurable.comp hP.measurable), 1,
    fun y => (Chars.norm_eq he _).le⟩
  have heig : IsEigenfunction (Γ := Γ) μ h := ⟨fun γ => e (kα α' γ), fun γ =>
    (hP.ae_equivariant_comp hι γ).mono fun y hy => by
      simp only [h_def, hy, Chars.map_add he, mul_comm]⟩
  obtain ⟨g, hgm, hhg⟩ := hκ.eigen h (hhb.memLp 2) heig
  -- a bounded version of `g`
  set g' : KG α → ℂ := fun z => if ‖g z‖ ≤ 1 then g z else 0 with g'_def
  have hg'm : Measurable g' :=
    Measurable.ite (measurableSet_le hgm.norm measurable_const) hgm measurable_const
  have hg'b : Bdd g' := ⟨hg'm, 1, fun z => by
    simp only [g'_def]; split_ifs with h1
    · exact h1
    · simp⟩
  have hhg' : ∀ᵐ y ∂μ, h y = g' (κ y) := by
    filter_upwards [hhg] with y hy
    have h1 : ‖g (κ y)‖ ≤ 1 := by
      rw [← show h y = g (κ y) from hy]; exact (Chars.norm_eq he _).le
    simp only [g'_def, h1, if_true]
    exact hy
  have hmS : ∀ {S : Set (KG α)}, MeasurableSet S → (∀ᵐ y ∂μ, κ y ∈ S) → ∀ᵐ z ∂haarK α, z ∈ S :=
    fun hS hy => by
      rw [← hκ.map_eq]; exact (ae_map_iff hκ.measurable.aemeasurable hS).2 hy
  -- `|g'| = 1` a.e.
  have hnorm : ∀ᵐ z ∂haarK α, ‖g' z‖ = 1 := by
    refine hmS (S := {z | ‖g' z‖ = 1}) (measurableSet_eq_fun hg'm.norm measurable_const) ?_
    filter_upwards [hhg'] with y hy
    show ‖g' (κ y)‖ = 1
    rw [← hy]; exact Chars.norm_eq he _
  -- the translation rule
  have htrans : ∀ γ, ∀ᵐ z ∂haarK α, g' (z + kα α γ) = e (kα α' γ) * g' z := by
    intro γ
    refine hmS (S := {z | g' (z + kα α γ) = e (kα α' γ) * g' z})
      (measurableSet_eq_fun (hg'm.comp (measurable_add_const _)) (hg'm.const_mul _)) ?_
    have hT : ∀ᵐ y ∂μ, h (γ +ᵥ y) = g' (κ (γ +ᵥ y)) :=
      (measurePreserving_vadd γ μ).quasiMeasurePreserving.ae (p := fun y => h y = g' (κ y)) hhg'
    filter_upwards [hT, hhg', hκ.ae_equivariant γ, hP.ae_equivariant_comp hι γ]
      with y h1 h2 h3 h4
    show g' (κ y + kα α γ) = e (kα α' γ) * g' (κ y)
    rw [← h3, ← h1, ← h2]
    simp only [h_def, h4, Chars.map_add he, mul_comm]
  -- the characters `e (α' γ)` tend to `1`
  have hlim : Tendsto (fun γ => e (kα α' γ)) (comap (kα α) (𝓝 0)) (𝓝 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hev := (eventually_integral_norm_translate_sub_lt hg'b hε).comap (kα α)
    filter_upwards [hev] with γ hγ
    have : ∫ z, ‖g' (z + kα α γ) - g' z‖ ∂haarK α = ‖e (kα α' γ) - 1‖ := by
      rw [integral_congr_ae (g := fun _ => ‖e (kα α' γ) - 1‖)]
      · simp
      · filter_upwards [htrans γ, hnorm] with z h1 h2
        rw [h1, ← sub_one_mul, norm_mul, h2, mul_one]
    rw [dist_eq_norm]
    linarith
  -- convert to the coordinate
  have hlim' : Tendsto (fun γ => AddCircle.homeomorphCircle (T := 1) one_ne_zero
      ((kα α' γ : Torus) j)) (comap (kα α) (𝓝 0)) (𝓝 1) := by
    have hind : Topology.IsInducing ((↑) : Circle → ℂ) := Topology.IsInducing.subtypeVal
    refine hind.tendsto_nhds_iff.2 ?_
    simp only [Function.comp_def, AddCircle.homeomorphCircle_apply]
    refine hlim.congr fun γ => ?_
    rw [he_apply]
    rfl
  have h0 : (AddCircle.homeomorphCircle (T := 1) one_ne_zero).symm 1 = 0 := by
    rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply]
    simp
  have := ((AddCircle.homeomorphCircle (T := 1) one_ne_zero).symm.continuous.tendsto 1).comp
    hlim'
  rw [h0] at this
  simpa [Function.comp_def, Homeomorph.symm_apply_apply] using this

/-- Paper, Lemma \ref{K:lem:factor}(b), existence of `χ̄`. -/
theorem IsFactorMap.exists_isFactorHom [MeasurableConstVAdd Γ Y] [IsProbabilityMeasure μ]
    [VAddInvariantMeasure Γ Y μ] (hP : IsFactorMap (Γ := Γ) μ ν P) (hκ : IsKroneckerMap μ α κ)
    (hι : IsRotFactor ν α' ι) : ∃ χ, IsFactorHom α α' χ :=
  exists_isFactorHom_of_tendsto (hP.tendsto_kα hκ hι)

/-- Paper, Lemma \ref{K:lem:factor}(b): `ι ∘ P = χ̄ ∘ κ + c` a.e. -/
theorem IsFactorMap.exists_affine [MeasurableConstVAdd Γ Y] [ErgodicVAdd Γ Y μ]
    (hP : IsFactorMap (Γ := Γ) μ ν P) (hκ : IsRotFactor μ α κ) (hι : IsRotFactor ν α' ι)
    {χ : KG α → KG α'} (hχ : IsFactorHom α α' χ) :
    ∃ c, ∀ᵐ y ∂μ, ι (P y) = χ (κ y) + c := by
  have hg : Measurable fun y => ι (P y) - χ (κ y) :=
    (hι.measurable.comp hP.measurable).sub (hχ.continuous.measurable.comp hκ.measurable)
  obtain ⟨c, hc⟩ := ErgodicVAdd.ae_eq_const (Γ := Γ) hg fun γ => by
    filter_upwards [hP.ae_equivariant_comp hι γ, hκ.ae_equivariant γ] with y h1 h2
    simp only [h1, h2, hχ.map_add, hχ.comp_eq]
    abel
  exact ⟨c, hc.mono fun y hy => by
    have hy' : ι (P y) - χ (κ y) = c := hy
    rw [← hy']; abel⟩

end Factor

/-! ## Conditional expectations under factor maps -/

section Tilde

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}
variable {Y : Type*} [MeasurableSpace Y] [AddAction Γ Y] [StandardBorelSpace Y] [Nonempty Y]
variable {μ : Measure Y} [IsProbabilityMeasure μ] {κ : Y → KG α}

lemma tilde_add {F G : Y → ℂ} (hF : Bdd F) (hG : Bdd G) (z : KG α) :
    tilde μ κ (fun y => F y + G y) z = tilde μ κ F z + tilde μ κ G z :=
  integral_add hF.integrable hG.integrable

/-- `𝔼(H ∘ κ | κ) = H`. -/
lemma IsRotFactor.tilde_comp (h : IsRotFactor μ α κ) (H : KG α → ℂ) :
    tilde μ κ (fun y => H (κ y)) =ᵐ[haarK α] H := by
  filter_upwards [h.ae_ae_fiber] with z hz
  unfold tilde
  rw [integral_congr_ae (hz.mono fun y hy => by rw [hy])]
  simp

/-- `f̃` only depends on the `μ`-a.e. class of `f`. -/
lemma IsRotFactor.tilde_congr_ae (h : IsRotFactor μ α κ) {F G : Y → ℂ} (hF : Measurable F)
    (hG : Measurable G) (hFG : F =ᵐ[μ] G) : tilde μ κ F =ᵐ[haarK α] tilde μ κ G := by
  have hmeas : MeasurableSet {p : KG α × Y | F p.2 = G p.2} :=
    measurableSet_eq_fun (hF.comp measurable_snd) (hG.comp measurable_snd)
  have h1 : ∀ᵐ p ∂(μ.map fun y => (κ y, y)), F p.2 = G p.2 := by
    rw [ae_map_iff (h.measurable.prodMk measurable_id').aemeasurable hmeas]
    exact hFG
  rw [h.graph_eq] at h1
  filter_upwards [Measure.ae_ae_of_ae_compProd h1] with z hz
  exact integral_congr_ae hz

end Tilde

section FactorTilde

variable {Γ : Type*} [AddCommGroup Γ] {α α' : Γ →+ Torus}
variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] [AddAction Γ Y] [AddAction Γ Z]
variable [StandardBorelSpace Y] [Nonempty Y] [StandardBorelSpace Z] [Nonempty Z]
variable {μ : Measure Y} {ν : Measure Z} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {κ : Y → KG α} {ι : Z → KG α'} {P : Y → Z}

/-- The push-forward of `m_K` under `z ↦ χ̄ z + c` is `m_{K'}`. -/
lemma IsFactorMap.map_affine_haarK (hP : IsFactorMap (Γ := Γ) μ ν P) (hκ : IsRotFactor μ α κ)
    (hι : IsRotFactor ν α' ι) {χ : KG α → KG α'} (hχ : IsFactorHom α α' χ) {c : KG α'}
    (hc : ∀ᵐ y ∂μ, ι (P y) = χ (κ y) + c) :
    (haarK α).map (fun z => χ z + c) = haarK α' := by
  have hm : Measurable fun z : KG α => χ z + c := hχ.continuous.measurable.add_const c
  rw [← hκ.map_eq, Measure.map_map hm hκ.measurable, ← hι.map_eq, ← hP.map_eq,
    Measure.map_map hι.measurable hP.measurable]
  exact Measure.map_congr (hc.mono fun y hy => hy.symm)

/-- Paper, Lemma \ref{K:lem:factor}(a): `𝔼_μ(f ∘ P | κ) = 𝔼_ν(f | ι) ∘ P`, in the form
`(f ∘ P)~ = f̃(χ̄ · + c)`. -/
theorem IsFactorMap.tilde_comp_ae_eq {Γ Y Z : Type u} [AddCommGroup Γ] [Countable Γ]
    {α α' : Γ →+ Torus} [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y] [ContinuousConstVAdd Γ Y] [Nonempty Y]
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddAction Γ Z] [ContinuousConstVAdd Γ Z] [Nonempty Z]
    {μ : Measure Y} {ν : Measure Z} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [VAddInvariantMeasure Γ Y μ] [VAddInvariantMeasure Γ Z ν]
    {κ : Y → KG α} {ι : Z → KG α'} {P : Y → Z}
    (hW : WienerKoopman.{u}) (hP : IsFactorMap (Γ := Γ) μ ν P) (hκ : IsRotFactor μ α κ)
    (hι : IsKroneckerMap ν α' ι) {χ : KG α → KG α'} (hχ : IsFactorHom α α' χ) {c : KG α'}
    (hc : ∀ᵐ y ∂μ, ι (P y) = χ (κ y) + c) {F : Z → ℂ} (hF : Bdd F) :
    tilde μ κ (fun y => F (P y)) =ᵐ[haarK α] fun z => tilde ν ι F (χ z + c) := by
  set v : Z → ℂ := fun z => F z - tilde ν ι F (ι z) with hv_def
  have hv : Bdd v := hF.sub (hF.tilde.comp hι.measurable)
  have hwm : WeakMixing Γ ν v := hι.weakMixing_sub_tilde hW hF
  have hwm' : WeakMixing Γ μ (fun y => v (P y)) :=
    WeakMixing.comp hP.measurable hP.equivariant hv.meas (by rw [hP.map_eq]; exact hwm)
  have h0 := hwm'.tilde_ae_eq_zero (v := fun y => v (P y)) (hv.comp hP.measurable) hκ
  set H : KG α → ℂ := fun z => tilde ν ι F (χ z + c) with hH_def
  have hHb : Bdd H := hF.tilde.comp (hχ.continuous.measurable.add_const c)
  have hsplit : ∀ y, F (P y) = v (P y) + tilde ν ι F (ι (P y)) := fun y => by
    simp [hv_def]
  have hae : (fun y => tilde ν ι F (ι (P y))) =ᵐ[μ] fun y => H (κ y) :=
    hc.mono fun y hy => by simp only [hH_def, hy]
  have h2 := hκ.tilde_congr_ae (F := fun y => tilde ν ι F (ι (P y))) (G := fun y => H (κ y))
    ((hF.tilde.comp hι.measurable).comp hP.measurable).meas (hHb.comp hκ.measurable).meas hae
  filter_upwards [h0, h2, hκ.tilde_comp H] with z hz0 hz2 hz3
  have : tilde μ κ (fun y => F (P y)) z = tilde μ κ (fun y => v (P y)) z +
      tilde μ κ (fun y => tilde ν ι F (ι (P y))) z := by
    rw [← tilde_add (F := fun y => v (P y)) (G := fun y => tilde ν ι F (ι (P y)))
      (hv.comp hP.measurable) ((hF.tilde.comp hι.measurable).comp hP.measurable)]
    congr 1; funext y; exact hsplit y
  rw [this, hz0, hz2, hz3]
  simp [hH_def]

/-- Paper, Lemma \ref{K:lem:factor}(c): `(P × P)_* J^μ_s = J^ν_{χ̄ s}` for every `s`. -/
theorem IsFactorMap.map_relJ {Γ Y Z : Type u} [AddCommGroup Γ] [Countable Γ]
    {α α' : Γ →+ Torus} [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y] [ContinuousConstVAdd Γ Y] [Nonempty Y]
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] [AddAction Γ Z] [ContinuousConstVAdd Γ Z] [Nonempty Z]
    {μ : Measure Y} {ν : Measure Z} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [VAddInvariantMeasure Γ Y μ] [VAddInvariantMeasure Γ Z ν]
    {κ : Y → KG α} {ι : Z → KG α'} {P : Y → Z}
    (hW : WienerKoopman.{u}) (hP : IsFactorMap (Γ := Γ) μ ν P) (hκ : IsRotFactor μ α κ)
    (hι : IsKroneckerMap ν α' ι) {χ : KG α → KG α'} (hχ : IsFactorHom α α' χ) {c : KG α'}
    (hc : ∀ᵐ y ∂μ, ι (P y) = χ (κ y) + c) (s : KG α) :
    (relJ μ κ s).map (Prod.map P P) = relJ ν ι (χ s) := by
  have hPP : Measurable (Prod.map P P) := hP.measurable.prodMap hP.measurable
  refine measure_prod_ext fun A B hA hB => ?_
  rw [Measure.map_apply hPP (hA.prod hB), Set.preimage_prod_map_prod]
  apply measure_eq_of_real_eq
  apply Complex.ofReal_injective
  rw [relJ_real_prod (hP.measurable hA) (hP.measurable hB), relJ_real_prod hA hB]
  have hiA : (P ⁻¹' A).indicator (fun _ => (1 : ℂ)) = fun y => A.indicator (fun _ => 1) (P y) := by
    funext y; simp [Set.indicator]
  have hiB : (P ⁻¹' B).indicator (fun _ => (1 : ℂ)) = fun y => B.indicator (fun _ => 1) (P y) := by
    funext y; simp [Set.indicator]
  rw [hiA, hiB]
  have eA := hP.tilde_comp_ae_eq hW hκ hι hχ hc (Bdd.indicator hA)
  have eB := (measurePreserving_add_right (haarK α) s).quasiMeasurePreserving.ae
    (p := fun z => tilde μ κ (fun y => B.indicator (fun _ => (1 : ℂ)) (P y)) z =
      tilde ν ι (B.indicator fun _ => 1) (χ z + c))
    (hP.tilde_comp_ae_eq hW hκ hι hχ hc (Bdd.indicator hB))
  have e3 : (fun z => tilde μ κ (fun y => A.indicator (fun _ => (1 : ℂ)) (P y)) z *
      tilde μ κ (fun y => B.indicator (fun _ => (1 : ℂ)) (P y)) (z + s)) =ᵐ[haarK α]
      fun z => tilde ν ι (A.indicator fun _ => 1) (χ z + c) *
        tilde ν ι (B.indicator fun _ => 1) (χ (z + s) + c) := by
    filter_upwards [eA, eB] with z h1 h2
    rw [h1, h2]
  rw [integral_congr_ae e3]
  have hG : Measurable fun u => tilde ν ι (A.indicator fun _ => (1 : ℂ)) u *
      tilde ν ι (B.indicator fun _ => (1 : ℂ)) (u + χ s) :=
    (Bdd.indicator hA).tilde.meas.mul ((Bdd.indicator hB).tilde.meas.comp (measurable_add_const _))
  rw [← hP.map_affine_haarK hκ hι.toRotFactor hχ hc,
    integral_map (hχ.continuous.measurable.add_const c).aemeasurable hG.aestronglyMeasurable]
  congr 1; funext z
  rw [hχ.map_add]; congr 2; abel

end FactorTilde

end Kmrr25.ThmK
