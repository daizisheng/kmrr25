import Kmrr25.ThmKFactor

/-!
# Theorem K: re-basing and the support lemmas

Paper, Section \ref{K:ssec:support}: Lemma \ref{K:lem:rebase} (re-basing),
Lemma \ref{K:lem:stab} (support of the graph measure), Lemma \ref{K:lem:phase}
(phase returns) and Lemma \ref{K:lem:PS} (pointwise support).

`Γ` acts on the Kronecker group `K = KG α` by `γ +ᵥ k = α γ + k`, and diagonally on products
`Y × K`. For a measure `λ` on `Y` and a measurable `κ : Y → K`, `graphMeasure λ κ` is
`(id, κ)_* λ` on `Y × K`.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

open Q516

universe u

/-! ## The rotation action on `K` -/

section Rotation

variable {Γ : Type*} [AddCommGroup Γ] (α : Γ →+ Torus)

/-- The rotation action `γ +ᵥ k = α γ + k` of `Γ` on `K`. -/
instance instAddActionKG : AddAction Γ (KG α) := AddAction.compHom (KG α) (kα α)

variable {α}

lemma vadd_kg (γ : Γ) (k : KG α) : γ +ᵥ k = kα α γ + k := rfl

instance : ContinuousConstVAdd Γ (KG α) :=
  ⟨fun γ => by simp only [vadd_kg]; exact continuous_const.add continuous_id⟩

instance : MeasurableConstVAdd Γ (KG α) := ⟨fun γ => (continuous_const_vadd γ).measurable⟩

end Rotation

/-- The diagonal action on a product of measurable actions is measurable. -/
instance prodMeasurableConstVAdd {Γ A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [VAdd Γ A] [VAdd Γ B] [MeasurableConstVAdd Γ A] [MeasurableConstVAdd Γ B] :
    MeasurableConstVAdd Γ (A × B) :=
  ⟨fun γ => ((measurable_const_vadd γ).comp measurable_fst).prodMk
    ((measurable_const_vadd γ).comp measurable_snd)⟩

/-! ## Graph measures -/

section Graph

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}
variable {Y : Type*} [MeasurableSpace Y] [AddAction Γ Y] [MeasurableConstVAdd Γ Y]

/-- The graph measure `(id, κ)_* λ` on `Y × K`. -/
def graphMeasure (μ : Measure Y) (κ : Y → KG α) : Measure (Y × KG α) := μ.map fun y => (y, κ y)

omit [AddAction Γ Y] [MeasurableConstVAdd Γ Y] in
instance (μ : Measure Y) [IsProbabilityMeasure μ] (κ : Y → KG α) [Fact (Measurable κ)] :
    IsProbabilityMeasure (graphMeasure μ κ) :=
  Measure.isProbabilityMeasure_map (measurable_id'.prodMk Fact.out).aemeasurable

omit [AddAction Γ Y] [MeasurableConstVAdd Γ Y] in
lemma isProbabilityMeasure_graphMeasure {μ : Measure Y} [IsProbabilityMeasure μ] {κ : Y → KG α}
    (hκ : Measurable κ) : IsProbabilityMeasure (graphMeasure μ κ) :=
  Measure.isProbabilityMeasure_map (measurable_id'.prodMk hκ).aemeasurable

omit [MeasurableConstVAdd Γ Y] in
/-- A factor of an ergodic measure under an a.e. equivariant measurable map is ergodic. -/
lemma ErgodicVAdd.map_ae {Z : Type*} [MeasurableSpace Z] [AddAction Γ Z] [MeasurableConstVAdd Γ Z]
    {μ : Measure Y} [ErgodicVAdd Γ Y μ] {P : Y → Z} (hP : Measurable P)
    (hPe : ∀ γ : Γ, ∀ᵐ x ∂μ, P (γ +ᵥ x) = γ +ᵥ P x) : ErgodicVAdd Γ Z (μ.map P) where
  measure_preimage_vadd γ s hs := by
    rw [Measure.map_apply hP (hs.preimage (measurable_const_vadd γ)), Measure.map_apply hP hs]
    have h1 : P ⁻¹' ((γ +ᵥ ·) ⁻¹' s) =ᵐ[μ] (γ +ᵥ ·) ⁻¹' (P ⁻¹' s) :=
      (hPe γ).mono fun x hx => by
        show (γ +ᵥ P x ∈ s) = (P (γ +ᵥ x) ∈ s)
        rw [hx]
    rw [measure_congr h1]
    exact VAddInvariantMeasure.measure_preimage_vadd (μ := μ) γ (hP hs)
  aeconst_of_forall_preimage_vadd_ae_eq {s} hs hinv := by
    have h := ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := Γ) (μ := μ) (hP hs)
      fun γ => by
        have h2 : ((γ +ᵥ ·) ⁻¹' s) ∘ P =ᵐ[μ] s ∘ P := ae_eq_comp hP.aemeasurable (hinv γ)
        refine EventuallyEq.trans ((hPe γ).mono fun x hx => ?_) h2
        show (P (γ +ᵥ x) ∈ s) = (γ +ᵥ P x ∈ s)
        rw [hx]
    rw [eventuallyConst_set] at h ⊢
    rcases h with h | h
    · exact Or.inl ((ae_map_iff hP.aemeasurable hs).2 h)
    · exact Or.inr ((ae_map_iff hP.aemeasurable hs.compl).2 h)

omit [MeasurableConstVAdd Γ Y] in
lemma ae_graph_equivariant {μ : Measure Y} {κ : Y → KG α}
    (hκe : ∀ γ : Γ, ∀ᵐ y ∂μ, κ (γ +ᵥ y) = κ y + kα α γ) (γ : Γ) :
    ∀ᵐ y ∂μ, (fun y => (y, κ y)) (γ +ᵥ y) = γ +ᵥ (fun y => (y, κ y)) y := by
  filter_upwards [hκe γ] with y hy
  simp [Prod.vadd_def, hy, vadd_kg, add_comm]

lemma graphMeasure_ergodic {μ : Measure Y} [ErgodicVAdd Γ Y μ] {κ : Y → KG α}
    (hκ : Measurable κ) (hκe : ∀ γ : Γ, ∀ᵐ y ∂μ, κ (γ +ᵥ y) = κ y + kα α γ) :
    ErgodicVAdd Γ (Y × KG α) (graphMeasure μ κ) :=
  ErgodicVAdd.map_ae (measurable_id'.prodMk hκ) (ae_graph_equivariant hκe)

end Graph

/-! ## Re-basing -/

section Rebase

lemma avg_image_add {Γ E : Type*} [AddCommGroup Γ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Finset Γ) (f : Γ → E) (c : Γ) :
    avg (F.image (· + c)) f = avg F fun γ => f (γ + c) := by
  simp only [avg]
  rw [Finset.sum_image fun x _ y _ h => add_right_cancel h,
    Finset.card_image_of_injective _ (add_left_injective _)]

/-- Paper, Lemma \ref{K:lem:rebase} (re-basing): if `w` has dense orbit in a closed set carrying
the ergodic measure `λ`, and `κ : W → K` is a.e. equivariant, then for some `d ∈ K` and some Følner
sequence `Ψ`, the decorated point `(w, d)` is generic for the graph measure `(id, κ)_* λ`. -/
theorem rebase {Γ W : Type u} [AddCommGroup Γ] [Countable Γ] [MetricSpace W] [CompactSpace W]
    [MeasurableSpace W] [BorelSpace W] [AddAction Γ W] [ContinuousConstVAdd Γ W]
    (hG : GenericPointsExist.{u}) {μ : Measure W} [IsProbabilityMeasure μ] [ErgodicVAdd Γ W μ]
    {w : W} (hw : μ.support ⊆ closure (Set.range fun γ : Γ => γ +ᵥ w)) {α : Γ →+ Torus}
    {κ : W → KG α} (hκ : Measurable κ) (hκe : ∀ γ : Γ, ∀ᵐ y ∂μ, κ (γ +ᵥ y) = κ y + kα α γ) :
    ∃ d : KG α, ∃ Ψ : ℕ → Finset Γ, IsFolner Ψ ∧ IsGeneric (graphMeasure μ κ) Ψ (w, d) := by
  obtain ⟨Φ, hΦ⟩ := Q516.exists_folner (G := Γ)
  have := graphMeasure_ergodic hκ hκe
  have := isProbabilityMeasure_graphMeasure (μ := μ) hκ
  obtain ⟨φ, hφ, hgen⟩ := hG Γ (W × KG α) (graphMeasure μ κ) Φ hΦ
  set C := closure (Set.range fun γ : Γ => γ +ᵥ w)
  have hC : ∀ᵐ p ∂graphMeasure μ κ, p.1 ∈ C := by
    rw [graphMeasure, ae_map_iff (measurable_id'.prodMk hκ).aemeasurable
      (isClosed_closure.measurableSet.preimage measurable_fst)]
    exact Filter.mem_of_superset Measure.support_mem_ae hw
  obtain ⟨⟨x1, z1⟩, hgen1, hx1⟩ := (hgen.and hC).exists
  -- approximate the orbit of `x1` by the orbit of `w`
  have happrox : ∀ N, ∃ h : Γ, ∀ γ ∈ Φ (φ N), dist (γ +ᵥ (h +ᵥ w)) (γ +ᵥ x1) < 1 / (N + 1) := by
    intro N
    set U := {x : W | ∀ γ ∈ Φ (φ N), dist (γ +ᵥ x) (γ +ᵥ x1) < 1 / (N + 1)}
    have hUo : IsOpen U := by
      have : U = ⋂ γ ∈ Φ (φ N), {x : W | dist (γ +ᵥ x) (γ +ᵥ x1) < 1 / (N + 1)} := by
        ext x; simp [U]
      rw [this]
      exact isOpen_biInter_finset fun γ _ =>
        isOpen_lt ((continuous_const_vadd γ).dist continuous_const) continuous_const
    have hx1U : x1 ∈ U := fun γ _ => by simp; positivity
    obtain ⟨_, hy, h, rfl⟩ := mem_closure_iff.1 hx1 U hUo hx1U
    exact ⟨h, hy⟩
  choose h hh using happrox
  obtain ⟨u, ψ, hψ, hu⟩ := CompactSpace.tendsto_subseq (fun N => kα α (h N))
  refine ⟨z1 - u, fun j => (Φ (φ (ψ j))).image (· + h (ψ j)), ?_, ?_⟩
  · exact (hΦ.comp (hφ.comp hψ)).translate (fun j => h (ψ j))
  intro F
  have hb : Tendsto (fun j => avg (Φ (φ (ψ j))) fun γ => F (γ +ᵥ (x1, z1))) atTop
      (𝓝 (∫ x, F x ∂graphMeasure μ κ)) := (hgen1 F).comp hψ.tendsto_atTop
  -- uniform continuity of `F`
  have hFu : UniformContinuous F := CompactSpace.uniformContinuous_of_continuous F.continuous
  have hdiff : Tendsto (fun j => (avg ((Φ (φ (ψ j))).image (· + h (ψ j))) fun γ =>
      F (γ +ᵥ (w, z1 - u))) - avg (Φ (φ (ψ j))) fun γ => F (γ +ᵥ (x1, z1))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hT := hFu (Metric.dist_mem_uniformity (half_pos hε))
    rw [uniformity_prod_eq_prod] at hT
    obtain ⟨V1, hV1, V2, hV2, hV⟩ := Filter.mem_prod_iff.1 (Filter.mem_map.1 hT)
    obtain ⟨δ, hδ, hδV⟩ := Metric.mem_uniformity_dist.1 hV1
    rw [uniformity_eq_comap_nhds_zero (KG α), mem_comap] at hV2
    obtain ⟨U, hU, hUV⟩ := hV2
    have hev1 : ∀ᶠ j in atTop, 1 / ((ψ j : ℝ) + 1) < δ := by
      have : Tendsto (fun j => 1 / ((ψ j : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop
      exact this.eventually (gt_mem_nhds hδ)
    have hev2 : ∀ᶠ j in atTop, kα α (h (ψ j)) - u ∈ U := by
      have : Tendsto (fun j => kα α (h (ψ j)) - u) atTop (𝓝 0) := by
        simpa using hu.sub_const u
      exact this.eventually hU
    obtain ⟨J, hJ⟩ := (hev1.and hev2).exists_forall_of_atTop
    refine ⟨J, fun j hj => ?_⟩
    obtain ⟨h1, h2⟩ := hJ j hj
    rw [avg_image_add, dist_zero_right, ← avg_sub']
    refine (norm_avg_le _ (B := ε / 2) (fun γ hγ => ?_) (by positivity)).trans_lt (half_lt_self hε)
    have hpair : ((γ +ᵥ (x1, z1)), ((γ + h (ψ j)) +ᵥ (w, z1 - u))) ∈
        (fun p : (W × KG α) × (W × KG α) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ⁻¹'
          (V1 ×ˢ V2) := by
      refine ⟨hδV ?_, hUV ?_⟩
      · simp only [Prod.vadd_def, Prod.fst]
        rw [add_vadd, dist_comm]
        exact (hh (ψ j) γ hγ).trans h1
      · simp only [Prod.vadd_def, Set.mem_preimage, vadd_kg, map_add]
        convert h2 using 1
        abel
    have := hV hpair
    simp only [Set.mem_setOf_eq] at this
    rw [Real.norm_eq_abs, ← Real.dist_eq, dist_comm]
    exact this.le
  have := hb.add hdiff
  simp only [add_sub_cancel, add_zero] at this
  exact this

end Rebase

/-! ## The stabiliser argument -/

section Stab

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}
variable {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [AddAction Γ Z] [ContinuousConstVAdd Γ Z]

/-- The support of an invariant measure is invariant. -/
lemma vadd_mem_support {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddAction Γ X] [ContinuousConstVAdd Γ X] {ρ : Measure X} [VAddInvariantMeasure Γ X ρ]
    {x : X} (hx : x ∈ ρ.support) (γ : Γ) : γ +ᵥ x ∈ ρ.support := by
  have := image_support_subset_support_map (ν := ρ) (continuous_const_vadd γ) ⟨x, hx, rfl⟩
  rwa [(measurePreserving_vadd γ ρ).map_eq] at this

/-- Paper, Lemma \ref{K:lem:stab}: if `(p, θ)` is generic for the graph measure `ρ = (id, ι)_* ν`
and `p ∈ supp ν`, then `(p, θ) ∈ supp ρ`. -/
theorem mem_support_graph_of_isGeneric {ν : Measure Z} [IsProbabilityMeasure ν]
    [ErgodicVAdd Γ Z ν] {ι : Z → KG α} (hι : Measurable ι)
    (hιe : ∀ γ : Γ, ∀ᵐ z ∂ν, ι (γ +ᵥ z) = ι z + kα α γ) {Ψ : ℕ → Finset Γ} {p : Z}
    {θ : KG α} (hgen : IsGeneric (graphMeasure ν ι) Ψ (p, θ)) (hp : p ∈ ν.support) :
    (p, θ) ∈ (graphMeasure ν ι).support := by
  set ρ := graphMeasure ν ι with hρ
  have herg : ErgodicVAdd Γ (Z × KG α) ρ := graphMeasure_ergodic hι hιe
  have : IsProbabilityMeasure ρ := isProbabilityMeasure_graphMeasure hι
  set Sg := ρ.support with hSgdef
  have hSgc : IsClosed Sg := Measure.isClosed_support
  -- a point of `Σ` above `p`
  have hproj : ν.support ⊆ Prod.fst '' Sg := by
    have hcl : IsClosed (Prod.fst '' Sg) :=
      (hSgc.isCompact.image continuous_fst).isClosed
    refine Measure.support_subset_of_isClosed hcl ?_
    have hmap : ρ.map Prod.fst = ν := by
      rw [hρ, graphMeasure, Measure.map_map measurable_fst (measurable_id'.prodMk hι)]
      exact Measure.map_id
    rw [← hmap]
    refine (ae_map_iff measurable_fst.aemeasurable hcl.measurableSet).2 ?_
    exact Filter.mem_of_superset Measure.support_mem_ae fun x hx => ⟨x, hx, rfl⟩
  obtain ⟨⟨p', θ0⟩, hθ0, rfl⟩ := hproj hp
  set ζ := θ - θ0 with hζ
  set S : KG α → Z × KG α → Z × KG α := fun u x => (x.1, x.2 + u) with hS
  have hScont : Continuous fun q : KG α × (Z × KG α) => S q.1 q.2 :=
    (continuous_snd.fst).prodMk (continuous_snd.snd.add continuous_fst)
  have hSvadd : ∀ (u : KG α) (γ : Γ) x, γ +ᵥ S u x = S u (γ +ᵥ x) := by
    intro u γ x
    simp only [hS, Prod.vadd_def, vadd_kg]
    ext <;> simp [add_assoc]
  -- `S_ζ Σ` is closed, invariant, and contains the orbit of `(p, θ)`
  set Sgz := S ζ '' Sg
  have hSgzc : IsClosed Sgz := by
    have : Sgz = (Homeomorph.prodCongr (Homeomorph.refl Z) (Homeomorph.addRight ζ)) '' Sg := rfl
    rw [this]
    exact (Homeomorph.isClosed_image _).2 hSgc
  have hmem : (p', θ) ∈ Sgz := ⟨(p', θ0), hθ0, by simp [hS, hζ]⟩
  have horbit : closure (Set.range fun γ : Γ => γ +ᵥ (p', θ)) ⊆ Sgz := by
    refine closure_minimal ?_ hSgzc
    rintro _ ⟨γ, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hmem
    exact ⟨γ +ᵥ x, vadd_mem_support hx γ, by rw [← hSvadd, hxe]⟩
  have hsub : ∀ x ∈ Sg, S (-ζ) x ∈ Sg := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := horbit (hgen.support_subset hx)
    rw [← hyx]
    simpa [hS] using hy
  have hiter : ∀ n : ℕ, ∀ x ∈ Sg, S (-(n • ζ)) x ∈ Sg := by
    intro n
    induction n with
    | zero => intro x hx; simpa [hS] using hx
    | succ n ih =>
      intro x hx
      have := hsub _ (ih x hx)
      have e : -((n + 1) • ζ) = -(n • ζ) + -ζ := by rw [succ_nsmul, neg_add]
      simp only [hS] at this ⊢
      rw [e, ← add_assoc]
      exact this
  -- compactness: `-(q_l ζ) → ζ` with `q_l ≥ 1`
  obtain ⟨ζs, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq (fun n : ℕ => n • ζ)
  set q : ℕ → ℕ := fun l => φ (2 * l + 2) - φ (2 * l) - 1 with hq
  have hq1 : ∀ l, φ (2 * l + 2) = φ (2 * l) + q l + 1 := by
    intro l
    have h1 : φ (2 * l) < φ (2 * l + 1) := hφ (by omega)
    have h2 : φ (2 * l + 1) < φ (2 * l + 2) := hφ (by omega)
    simp only [hq]; omega
  have hconv : Tendsto (fun l => -(q l • ζ)) atTop (𝓝 ζ) := by
    have h2 : Tendsto (fun l => φ (2 * l + 2) • ζ - φ (2 * l) • ζ) atTop (𝓝 (ζs - ζs)) := by
      refine (hlim.comp ?_).sub (hlim.comp ?_)
      · exact tendsto_atTop_mono (fun l => show l ≤ 2 * l + 2 by omega) tendsto_id
      · exact tendsto_atTop_mono (fun l => show l ≤ 2 * l by omega) tendsto_id
    rw [sub_self] at h2
    have h3 : (fun l => -(q l • ζ)) = fun l => ζ - (φ (2 * l + 2) • ζ - φ (2 * l) • ζ) := by
      funext l
      rw [hq1 l, add_smul, add_smul, one_smul]
      abel
    rw [h3]
    simpa using (tendsto_const_nhds (x := ζ)).sub h2
  have hlimS : Tendsto (fun l => S (-(q l • ζ)) (p', θ0)) atTop (𝓝 (S ζ (p', θ0))) :=
    (hScont.tendsto (ζ, (p', θ0))).comp (hconv.prodMk_nhds tendsto_const_nhds)
  have := hSgc.mem_of_tendsto hlimS (Eventually.of_forall fun l => hiter _ _ hθ0)
  simpa [hS, hζ] using this

end Stab

/-! ## Phase returns -/

section Phase

/-- Paper, Lemma \ref{K:lem:phase}(a): `ι ∘ U = ι ∘ L + r` a.e. -/
theorem phase_const {Γ W Z : Type*} [AddCommGroup Γ] [MeasurableSpace W] [MeasurableSpace Z]
    [AddAction Γ W] [AddAction Γ Z] [MeasurableConstVAdd Γ W] {α : Γ →+ Torus}
    {μ : Measure W} [ErgodicVAdd Γ W μ] {ν : Measure Z} {L U : W → Z}
    (hL : IsFactorMap (Γ := Γ) μ ν L) (hU : IsFactorMap (Γ := Γ) μ ν U) {ι : Z → KG α}
    (hι : IsRotFactor ν α ι) : ∃ r, ∀ᵐ x ∂μ, ι (U x) = ι (L x) + r := by
  have hg : Measurable fun x => ι (U x) - ι (L x) :=
    (hι.measurable.comp hU.measurable).sub (hι.measurable.comp hL.measurable)
  obtain ⟨r, hr⟩ := ErgodicVAdd.ae_eq_const (Γ := Γ) hg fun γ => by
    filter_upwards [hU.ae_equivariant_comp hι γ, hL.ae_equivariant_comp hι γ] with y h1 h2
    simp only [h1, h2]
    abel
  exact ⟨r, hr.mono fun y hy => by
    have hy' : ι (U y) - ι (L y) = r := hy
    rw [← hy']; abel⟩

/-- Paper, Lemma \ref{K:lem:phase}(b): if `U w ∈ supp ν`, then for all neighbourhoods `V` of
`U w` and `O` of `0 ∈ K`, the phase returns `{γ : T^γ L(w) ∈ V, α γ ∈ r + O}` have positive lower
density along some Følner sequence. -/
theorem phase_returns {Γ W Z : Type u} [AddCommGroup Γ] [Countable Γ] [MetricSpace W]
    [CompactSpace W] [MeasurableSpace W] [BorelSpace W] [AddAction Γ W] [ContinuousConstVAdd Γ W]
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [AddAction Γ Z] [ContinuousConstVAdd Γ Z]
    (hG : GenericPointsExist.{u}) {μ : Measure W} [IsProbabilityMeasure μ] [ErgodicVAdd Γ W μ]
    {Ψ : ℕ → Finset Γ} {w : W} (hw : IsGeneric μ Ψ w) {ν : Measure Z} [IsProbabilityMeasure ν]
    [ErgodicVAdd Γ Z ν] {L U : W → Z} (hLc : Continuous L) (hUc : Continuous U)
    (hL : IsFactorMap (Γ := Γ) μ ν L) (hU : IsFactorMap (Γ := Γ) μ ν U) {α : Γ →+ Torus}
    {ι : Z → KG α} (hι : IsRotFactor ν α ι) {r : KG α} (hr : ∀ᵐ x ∂μ, ι (U x) = ι (L x) + r)
    (hUw : U w ∈ ν.support) {V : Set Z} (hV : IsOpen V) (hwV : U w ∈ V) {O : Set (KG α)}
    (hO : IsOpen O) (hO0 : (0 : KG α) ∈ O) :
    ∃ Ω : ℕ → Finset Γ, IsFolner Ω ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ M in atTop, c < relDens (Ω M) {γ | γ +ᵥ L w ∈ V ∧ kα α γ - r ∈ O} := by
  have hsupp := hw.support_subset
  set κ' : W → KG α := fun x => ι (L x) with hκ'
  have hκ'm : Measurable κ' := hι.measurable.comp hL.measurable
  have hκ'e : ∀ γ : Γ, ∀ᵐ y ∂μ, κ' (γ +ᵥ y) = κ' y + kα α γ := hL.ae_equivariant_comp hι
  obtain ⟨d, Ω, hΩ, hgen⟩ := rebase hG hsupp hκ'm hκ'e
  -- the two projections to `Z × K`
  set ΦL : W × KG α → Z × KG α := fun x => (L x.1, x.2)
  set ΦU : W × KG α → Z × KG α := fun x => (U x.1, x.2 + r)
  have hΦLc : Continuous ΦL := (hLc.comp continuous_fst).prodMk continuous_snd
  have hΦUc : Continuous ΦU := (hUc.comp continuous_fst).prodMk (continuous_snd.add continuous_const)
  have hΦLe : ∀ (γ : Γ) x, ΦL (γ +ᵥ x) = γ +ᵥ ΦL x := fun γ x => by
    simp [ΦL, Prod.vadd_def, hL.equivariant]
  have hΦUe : ∀ (γ : Γ) x, ΦU (γ +ᵥ x) = γ +ᵥ ΦU x := fun γ x => by
    simp [ΦU, Prod.vadd_def, hU.equivariant, vadd_kg, add_assoc]
  have hmapL : (graphMeasure μ κ').map ΦL = graphMeasure ν ι := by
    rw [graphMeasure, graphMeasure, Measure.map_map hΦLc.measurable (measurable_id'.prodMk hκ'm),
      ← hL.map_eq, Measure.map_map (measurable_id'.prodMk hι.measurable) hL.measurable]
    rfl
  have hmapU : (graphMeasure μ κ').map ΦU = graphMeasure ν ι := by
    rw [graphMeasure, graphMeasure, Measure.map_map hΦUc.measurable (measurable_id'.prodMk hκ'm),
      ← hU.map_eq, Measure.map_map (measurable_id'.prodMk hι.measurable) hU.measurable]
    refine Measure.map_congr (hr.mono fun x hx => ?_)
    simp [ΦU, hκ', hx]
  have hgL : IsGeneric (graphMeasure ν ι) Ω (L w, d) := by
    have := hgen.map hΦLc hΦLe; rwa [hmapL] at this
  have hgU : IsGeneric (graphMeasure ν ι) Ω (U w, d + r) := by
    have := hgen.map hΦUc hΦUe; rwa [hmapU] at this
  have hmemU := mem_support_graph_of_isGeneric hι.measurable hι.ae_equivariant hgU hUw
  -- the open set `V × (d + r + O)`
  set S : Set (Z × KG α) := {x | x.1 ∈ V ∧ x.2 - (d + r) ∈ O}
  have hSo : IsOpen S := (hV.preimage continuous_fst).inter
    (hO.preimage (continuous_snd.sub continuous_const))
  have hSmem : (U w, d + r) ∈ S := ⟨hwV, by simpa using hO0⟩
  have hpos : 0 < graphMeasure ν ι S :=
    (Measure.mem_support_iff_forall _).1 hmemU S (hSo.mem_nhds hSmem)
  have : IsProbabilityMeasure (graphMeasure ν ι) := isProbabilityMeasure_graphMeasure hι.measurable
  obtain ⟨c, hc, hev⟩ := hgL.exists_eventually_lt_relDens hSo hpos
  refine ⟨Ω, hΩ, c, hc, hev.mono fun M hM => ?_⟩
  convert hM using 2
  ext γ
  simp only [S, Set.mem_setOf_eq, Prod.vadd_def, vadd_kg]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> convert h2 using 1 <;> abel

end Phase

/-! ## Pointwise support -/

section PS

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}

/-- Continuity of `t ↦ ∫ f(ξ) g(ξ + t) dm_K` for bounded measurable `f, g`. -/
lemma continuous_integral_mul_translate {f g : KG α → ℝ} (hf : Measurable f) (hg : Measurable g)
    {Cf Cg : ℝ} (hCf : ∀ ξ, |f ξ| ≤ Cf) (hCg : ∀ ξ, |g ξ| ≤ Cg) :
    Continuous fun t => ∫ ξ, f ξ * g (ξ + t) ∂haarK α := by
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf 0)
  have hgc : Bdd fun ξ => (g ξ : ℂ) := ⟨Complex.continuous_ofReal.measurable.comp hg, Cg,
    fun ξ => by simpa using hCg ξ⟩
  have hint : ∀ t, Integrable (fun ξ => f ξ * g (ξ + t)) (haarK α) := fun t =>
    Integrable.of_bound (hf.mul (hg.comp (measurable_add_const t))).aestronglyMeasurable (Cf * Cg)
      (Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hCf ξ) (hCg _) (abs_nonneg _) hCf0)
  rw [continuous_iff_continuousAt]
  intro t0
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (Cf + 1) := by positivity
  have hev := eventually_integral_norm_translate_sub_lt hgc hδ
  have hev' := (tendsto_sub_nhds_zero_iff.2 (tendsto_id (x := 𝓝 t0))).eventually hev
  filter_upwards [hev'] with t hk
  rw [Real.dist_eq, ← integral_sub (hint t) (hint t0)]
  have hb : ∫ ξ, |g (ξ + t) - g (ξ + t0)| ∂haarK α < ε / (Cf + 1) := by
    have e := integral_haarK_add_real (fun ξ => |g (ξ + (t - t0)) - g ξ|) t0
    simp only [show ∀ ξ, ξ + t0 + (t - t0) = ξ + t from fun ξ => by abel] at e
    rw [e]
    simpa [← Complex.ofReal_sub, Complex.norm_real] using hk
  have hi2 : Integrable (fun ξ => |g (ξ + t) - g (ξ + t0)|) (haarK α) :=
    Integrable.of_bound (((hg.comp (measurable_add_const t)).sub
      (hg.comp (measurable_add_const t0))).abs.aestronglyMeasurable) (2 * Cg)
      (Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_abs]
        calc |g (ξ + t) - g (ξ + t0)| ≤ |g (ξ + t)| + |g (ξ + t0)| := abs_sub _ _
          _ ≤ 2 * Cg := by linarith [hCg (ξ + t), hCg (ξ + t0)])
  calc |∫ ξ, (f ξ * g (ξ + t) - f ξ * g (ξ + t0)) ∂haarK α|
      ≤ ∫ ξ, |f ξ * g (ξ + t) - f ξ * g (ξ + t0)| ∂haarK α := abs_integral_le_integral_abs
    _ ≤ ∫ ξ, Cf * |g (ξ + t) - g (ξ + t0)| ∂haarK α := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hi2.const_mul _) (Eventually.of_forall fun ξ => ?_)
        show |f ξ * g (ξ + t) - f ξ * g (ξ + t0)| ≤ Cf * |g (ξ + t) - g (ξ + t0)|
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_right (hCf ξ) (abs_nonneg _)
    _ = Cf * ∫ ξ, |g (ξ + t) - g (ξ + t0)| ∂haarK α := integral_const_mul _ _
    _ ≤ Cf * (ε / (Cf + 1)) := mul_le_mul_of_nonneg_left hb.le hCf0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] [AddAction Γ Z]
variable {ν : Measure Z} [IsProbabilityMeasure ν] {ι : Z → KG α}

/-- `ν_ξ(S)` as a real number. -/
def tR (ν : Measure Z) [IsProbabilityMeasure ν] (ι : Z → KG α) (S : Set Z) (ξ : KG α) : ℝ :=
  (dis ν ι ξ).real S

omit [AddAction Γ Z] in
lemma tR_nonneg (S : Set Z) (ξ : KG α) : 0 ≤ tR ν ι S ξ := measureReal_nonneg

omit [AddAction Γ Z] in
lemma tR_le_one (S : Set Z) (ξ : KG α) : tR ν ι S ξ ≤ 1 := by
  unfold tR; exact measureReal_le_one

omit [AddAction Γ Z] in
lemma abs_tR_le (S : Set Z) (ξ : KG α) : |tR ν ι S ξ| ≤ 1 := by
  rw [abs_of_nonneg (tR_nonneg S ξ)]; exact tR_le_one S ξ

omit [AddAction Γ Z] in
lemma measurable_tR {S : Set Z} (hS : MeasurableSet S) : Measurable (tR ν ι S) :=
  ((dis ν ι).measurable_coe hS).ennreal_toReal

omit [AddAction Γ Z] in
lemma tilde_indicator_eq {S : Set Z} (hS : MeasurableSet S) (ξ : KG α) :
    tilde ν ι (S.indicator fun _ => (1 : ℂ)) ξ = (tR ν ι S ξ : ℂ) := by
  have : (S.indicator fun _ => (1 : ℂ)) = fun z => ((S.indicator (1 : Z → ℝ) z : ℝ) : ℂ) := by
    funext z; by_cases h : z ∈ S <;> simp [h]
  rw [tilde, this, integral_complex_ofReal, integral_indicator_one hS]
  rfl

lemma relJ_real_prod_tR {A B : Set Z} (hA : MeasurableSet A) (hB : MeasurableSet B) (t : KG α) :
    (relJ ν ι t).real (A ×ˢ B) = ∫ ξ, tR ν ι A ξ * tR ν ι B (ξ + t) ∂haarK α := by
  apply Complex.ofReal_injective
  rw [relJ_real_prod hA hB, ← integral_complex_ofReal]
  congr 1; funext ξ
  rw [tilde_indicator_eq hA, tilde_indicator_eq hB]
  push_cast; rfl

lemma graph_real_prod (hι : IsRotFactor ν α ι) {S : Set Z} {O : Set (KG α)} (hS : MeasurableSet S)
    (hO : MeasurableSet O) :
    (graphMeasure ν ι).real (S ×ˢ O) = ∫ ξ, O.indicator (fun _ => (1 : ℝ)) ξ * tR ν ι S ξ ∂haarK α := by
  apply Complex.ofReal_injective
  have h1 := hι.integral_comp_mul_tilde (G := O.indicator fun _ => (1 : ℂ))
    (measurable_const.indicator hO) ((Bdd.indicator hO).integrable) (Bdd.indicator hS)
  rw [← integral_complex_ofReal]
  have e2 : (fun ξ => ((O.indicator (fun _ => (1 : ℝ)) ξ * tR ν ι S ξ : ℝ) : ℂ)) =
      fun ξ => O.indicator (fun _ => (1 : ℂ)) ξ * tilde ν ι (S.indicator fun _ => 1) ξ := by
    funext ξ; rw [tilde_indicator_eq hS]; by_cases h : ξ ∈ O <;> simp [h]
  rw [e2, ← h1, graphMeasure, measureReal_def,
    Measure.map_apply (measurable_id'.prodMk hι.measurable) (hS.prod hO), ← measureReal_def,
    ← integral_indicator_one (measurable_id'.prodMk hι.measurable (hS.prod hO)),
    ← integral_complex_ofReal]
  congr 1; funext z
  by_cases h1 : z ∈ S <;> by_cases h2 : ι z ∈ O <;> simp [Set.indicator, h1, h2, Set.mem_prod]

/-- The key estimate of Lemma \ref{K:lem:PS}: if `(p, θ) ∈ supp ρ` and `O₁ ∋ p`, `O₂` are open,
then `ρ(O₂ × C) = 0` where `C = {φ : J_{φ-θ}(O₁ × O₂) = 0}`. -/
lemma IsRotFactor.graph_null_of_mem_support [TopologicalSpace Z] [BorelSpace Z]
    (hι : IsRotFactor ν α ι) {p : Z} {θ : KG α} (hpθ : (p, θ) ∈ (graphMeasure ν ι).support)
    {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hp : p ∈ O₁) (hO₂ : IsOpen O₂) :
    graphMeasure ν ι (O₂ ×ˢ {φ | (relJ ν ι (φ - θ)).real (O₁ ×ˢ O₂) = 0}) = 0 := by
  have hm₁ := hO₁.measurableSet
  have hm₂ := hO₂.measurableSet
  set f := tR ν ι O₁
  set g := tR ν ι O₂
  have hfm : Measurable f := measurable_tR hm₁
  have hgm : Measurable g := measurable_tR hm₂
  set F : KG α → ℝ := fun t => ∫ ξ, f ξ * g (ξ + t) ∂haarK α with hF
  have hFc : Continuous F :=
    continuous_integral_mul_translate hfm hgm (abs_tR_le O₁) (abs_tR_le O₂)
  have hJF : ∀ t, (relJ ν ι t).real (O₁ ×ˢ O₂) = F t := fun t => relJ_real_prod_tR hm₁ hm₂ t
  set C := {φ : KG α | F (φ - θ) = 0} with hCdef
  have hCset : {φ | (relJ ν ι (φ - θ)).real (O₁ ×ˢ O₂) = 0} = C := by
    ext φ; simp [hCdef, hJF]
  rw [hCset]
  have hCc : IsClosed C := isClosed_eq (hFc.comp (continuous_id.sub continuous_const))
    continuous_const
  have hCm := hCc.measurableSet
  have : IsProbabilityMeasure (graphMeasure ν ι) := isProbabilityMeasure_graphMeasure hι.measurable
  rw [← measureReal_eq_zero_iff, graph_real_prod hι hm₂ hCm]
  set h : KG α → ℝ := fun φ => C.indicator (fun _ => (1 : ℝ)) φ * g φ with hh
  have hhm : Measurable h := (measurable_const.indicator hCm).mul hgm
  have hh0 : ∀ φ, 0 ≤ h φ := fun φ => mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (tR_nonneg _ _)
  have hh1 : ∀ φ, |h φ| ≤ 1 := fun φ => by
    rw [abs_of_nonneg (hh0 φ)]
    simp only [hh, Set.indicator]
    split_ifs
    · simpa using tR_le_one (ν := ν) (ι := ι) O₂ φ
    · simp
  have hint_h : Integrable h (haarK α) :=
    Integrable.of_bound hhm.aestronglyMeasurable 1 (Eventually.of_forall fun φ => by
      simpa [Real.norm_eq_abs] using hh1 φ)
  by_contra hne
  have hI : 0 < ∫ φ, h φ ∂haarK α :=
    lt_of_le_of_ne (integral_nonneg hh0) (Ne.symm hne)
  -- `R k = ∫ h(φ) g(φ + k - θ) dφ`
  set R0 : KG α → ℝ := fun s => ∫ φ, h φ * g (φ + s) ∂haarK α with hR0
  have hR0c : Continuous R0 := continuous_integral_mul_translate hhm hgm hh1 (abs_tR_le O₂)
  set R : KG α → ℝ := fun k => R0 (k - θ) with hR
  have hRc : Continuous R := hR0c.comp (continuous_id.sub continuous_const)
  have hR_nonneg : ∀ k, 0 ≤ R k := fun k =>
    integral_nonneg fun φ => mul_nonneg (hh0 φ) (tR_nonneg _ _)
  have hRθ : 0 < R θ := by
    have e : R θ = ∫ φ, h φ ^ 2 ∂haarK α := by
      simp only [hR, hR0, sub_self, add_zero]
      congr 1; funext φ
      simp only [hh, Set.indicator]; split_ifs <;> ring
    have hcs := integral_mul_sq_le (μ := haarK α) (F := h) (G := fun _ => 1)
      (Integrable.of_bound (hhm.pow_const 2).aestronglyMeasurable 1
        (Eventually.of_forall fun φ => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_one₀ (abs_nonneg _) (hh1 φ)))
      (integrable_const _) (by simpa using hint_h)
    have e2 : ∫ _φ, (1 : ℝ) ^ 2 ∂haarK α = 1 := by simp
    simp only [mul_one] at hcs
    rw [e2, mul_one] at hcs
    rw [e]
    nlinarith
  -- the open neighbourhood `N` of `θ`
  set N := {k : KG α | R θ / 2 < R k}
  have hNo : IsOpen N := isOpen_lt continuous_const hRc
  have hθN : θ ∈ N := by simp [N]; linarith
  have hpos : 0 < (graphMeasure ν ι).real (O₁ ×ˢ N) := by
    have := (Measure.mem_support_iff_forall _).1 hpθ _
      ((hO₁.prod hNo).mem_nhds ⟨hp, hθN⟩)
    exact ENNReal.toReal_pos this.ne' (measure_ne_top _ _)
  rw [graph_real_prod hι hm₁ hNo.measurableSet] at hpos
  -- lower bound for `∫ f R`
  have hfR_int : Integrable (fun k => f k * R k) (haarK α) := by
    refine Integrable.of_bound (hfm.mul hRc.measurable).aestronglyMeasurable 1
      (Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hR1 : |R k| ≤ 1 := by
      rw [abs_of_nonneg (hR_nonneg k)]
      calc R k ≤ ∫ _φ, (1 : ℝ) ∂haarK α := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun φ =>
              mul_nonneg (hh0 φ) (tR_nonneg _ _)) (integrable_const _)
              (Eventually.of_forall fun φ => ?_)
            have := hh1 φ
            have := tR_le_one (ν := ν) (ι := ι) O₂ (φ + (k - θ))
            have := tR_nonneg (ν := ν) (ι := ι) O₂ (φ + (k - θ))
            rw [abs_of_nonneg (hh0 φ)] at *
            nlinarith
        _ = 1 := by simp
    exact (mul_le_mul (abs_tR_le O₁ k) hR1 (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hlow : (R θ / 2) * ∫ k, N.indicator (fun _ => (1 : ℝ)) k * f k ∂haarK α ≤
      ∫ k, f k * R k ∂haarK α := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun k => ?_) hfR_int
      (Eventually.of_forall fun k => ?_)
    · show 0 ≤ R θ / 2 * (N.indicator (fun _ => (1 : ℝ)) k * f k)
      have := tR_nonneg (ν := ν) (ι := ι) O₁ k
      have hi : 0 ≤ N.indicator (fun _ => (1 : ℝ)) k :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
      exact mul_nonneg (by linarith) (mul_nonneg hi this)
    · show R θ / 2 * (N.indicator (fun _ => (1 : ℝ)) k * f k) ≤ f k * R k
      simp only [Set.indicator]
      split_ifs with hk
      · have hk' : R θ / 2 < R k := hk
        have := tR_nonneg (ν := ν) (ι := ι) O₁ k
        nlinarith
      · simp only [zero_mul, mul_zero]
        exact mul_nonneg (tR_nonneg _ _) (hR_nonneg k)
  -- Fubini: `∫ f R = ∫ h(φ) F(φ - θ) dφ = 0`
  have hfub : ∫ k, f k * R k ∂haarK α = ∫ φ, h φ * F (φ - θ) ∂haarK α := by
    have hprod : Integrable (Function.uncurry fun k φ => f k * (h φ * g (φ + (k - θ))))
        ((haarK α).prod (haarK α)) := by
      refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun q => ?_)
      · exact ((hfm.comp measurable_fst).mul ((hhm.comp measurable_snd).mul
          (hgm.comp (measurable_snd.add (measurable_fst.sub_const θ))))).aestronglyMeasurable
      · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
        have h1 := abs_tR_le (ν := ν) (ι := ι) O₁ q.1
        have h2 := hh1 q.2
        have h3 := abs_tR_le (ν := ν) (ι := ι) O₂ (q.2 + (q.1 - θ))
        exact mul_le_one₀ h1 (by positivity) (mul_le_one₀ h2 (abs_nonneg _) h3)
    calc ∫ k, f k * R k ∂haarK α
        = ∫ k, ∫ φ, f k * (h φ * g (φ + (k - θ))) ∂haarK α ∂haarK α := by
          congr 1; funext k
          simp only [hR, hR0]
          rw [integral_const_mul]
      _ = ∫ φ, ∫ k, f k * (h φ * g (φ + (k - θ))) ∂haarK α ∂haarK α :=
          integral_integral_swap hprod
      _ = ∫ φ, h φ * F (φ - θ) ∂haarK α := by
          congr 1; funext φ
          rw [hF, ← integral_const_mul]
          congr 1; funext k
          rw [show φ + (k - θ) = k + (φ - θ) by abel]
          ring
  have hzero : ∫ φ, h φ * F (φ - θ) ∂haarK α = 0 := by
    refine integral_eq_zero_of_ae (Eventually.of_forall fun φ => ?_)
    simp only [hh, Set.indicator, Pi.zero_apply]
    split_ifs with hφ
    · have : F (φ - θ) = 0 := hφ
      rw [this, mul_zero]
    · simp
  have hintN : 0 < ∫ k, N.indicator (fun _ => (1 : ℝ)) k * f k ∂haarK α := hpos
  have : 0 < (R θ / 2) * ∫ k, N.indicator (fun _ => (1 : ℝ)) k * f k ∂haarK α :=
    mul_pos (half_pos hRθ) hintN
  linarith [hlow, hfub, hzero, this]

/-- Paper, Lemma \ref{K:lem:PS} (pointwise support): if `(p, θ) ∈ supp ρ` then for `ρ`-a.e.
`(q, φ)`, `(p, q) ∈ supp J_{φ - θ}`. -/
theorem IsRotFactor.ae_mem_support_relJ [TopologicalSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z] (hι : IsRotFactor ν α ι) {p : Z} {θ : KG α}
    (hpθ : (p, θ) ∈ (graphMeasure ν ι).support) :
    ∀ᵐ x ∂graphMeasure ν ι, (p, x.1) ∈ (relJ ν ι (x.2 - θ)).support := by
  set B := TopologicalSpace.countableBasis Z
  have hB := TopologicalSpace.isBasis_countableBasis Z
  have hBc : B.Countable := TopologicalSpace.countable_countableBasis Z
  have : Countable (B × B) := by
    have := hBc.to_subtype; infer_instance
  have hnull : ∀ᵐ x ∂graphMeasure ν ι, ∀ o : B × B, p ∈ (o.1 : Set Z) →
      x ∉ (o.2 : Set Z) ×ˢ {φ | (relJ ν ι (φ - θ)).real ((o.1 : Set Z) ×ˢ (o.2 : Set Z)) = 0} := by
    rw [ae_all_iff]
    intro o
    by_cases hpo : p ∈ (o.1 : Set Z)
    · have h0 := hι.graph_null_of_mem_support hpθ (hB.isOpen o.1.2) hpo (hB.isOpen o.2.2)
      exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun x hx _ => hx
    · exact Eventually.of_forall fun x h => absurd h hpo
  filter_upwards [hnull] with x hx
  by_contra hns
  rw [Measure.notMem_support_iff_exists] at hns
  obtain ⟨U, hU, hU0⟩ := hns
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hU
  obtain ⟨O₁, hO₁B, hpO₁, hO₁u⟩ := hB.mem_nhds_iff.1 hu
  obtain ⟨O₂, hO₂B, hqO₂, hO₂v⟩ := hB.mem_nhds_iff.1 hv
  have hJ0 : (relJ ν ι (x.2 - θ)).real (O₁ ×ˢ O₂) = 0 := by
    rw [measureReal_eq_zero_iff]
    exact measure_mono_null ((Set.prod_mono hO₁u hO₂v).trans huv) hU0
  exact hx (⟨O₁, hO₁B⟩, ⟨O₂, hO₂B⟩) hpO₁ ⟨hqO₂, hJ0⟩

end PS

end Kmrr25.ThmK
