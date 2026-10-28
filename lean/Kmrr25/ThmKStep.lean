import Kmrr25.ThmKCriterion
import Kmrr25.ThmKCube

/-!
# Theorem K: cube spaces, cube data and the induction step

Paper, Section \ref{K:ssec:criterion} (Definition \ref{K:def:datum}) and
Proposition \ref{K:prop:step}.

* `CubeSp X m = X^{[m]} = (Fin m → Bool) → X` with the diagonal action. The lower and upper
  `i`-faces are realised as the *duplicating* maps `cL i y = y ∘ update · i false` and
  `cU i y = y ∘ update · i true` from `X^{[m]}` to itself; they carry the same information as
  the paper's faces `L_i, U_i : X^{[m]} → X^{[m-1]}` (the coordinates of `cL i y` are the vertices
  of the lower face, each listed twice).
* `merge : X^{[m]} × X^{[m]} → X^{[m+1]}` splits off the last digit; `dup y = merge (y, y)`.
* `CubeDatum` — Definition \ref{K:def:datum}, with (D2) replaced by the only consequence used,
  `(top vertex)_* λ = μ`.
* `CubeDatum.exists_erdosCube` — Proposition \ref{K:prop:criterion}.
* `CubeDatum.succ` — Proposition \ref{K:prop:step}.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

open Q516

universe u

/-! ## Cube spaces -/

section CubeSp

variable {X : Type*}

/-- The cube space `X^{[m]}`. -/
abbrev CubeSp (X : Type*) (m : ℕ) := (Fin m → Bool) → X

variable {m : ℕ}

/-- The (duplicating) lower `i`-face. -/
def cL (i : Fin m) (y : CubeSp X m) : CubeSp X m := fun ε => y (Function.update ε i false)

/-- The (duplicating) upper `i`-face. -/
def cU (i : Fin m) (y : CubeSp X m) : CubeSp X m := fun ε => y (Function.update ε i true)

/-- The top vertex `y_{1⋯1}`. -/
def topV (y : CubeSp X m) : X := y fun _ => true

/-- The bottom vertex `y_{0⋯0}`. -/
def botV (y : CubeSp X m) : X := y fun _ => false

/-- `X^{[m]} × X^{[m]} → X^{[m+1]}`: the last digit selects the component. -/
def merge (p : CubeSp X m × CubeSp X m) : CubeSp X (m + 1) := fun ε =>
  if ε (Fin.last m) then p.2 (Fin.init ε) else p.1 (Fin.init ε)

/-- `dup y = merge (y, y)`. -/
def dup (y : CubeSp X m) : CubeSp X (m + 1) := merge (y, y)

variable [TopologicalSpace X]

lemma continuous_cL (i : Fin m) : Continuous (cL (X := X) i) :=
  continuous_pi fun _ => continuous_apply _

lemma continuous_cU (i : Fin m) : Continuous (cU (X := X) i) :=
  continuous_pi fun _ => continuous_apply _

lemma continuous_topV : Continuous (topV (X := X) (m := m)) := continuous_apply _

lemma continuous_botV : Continuous (botV (X := X) (m := m)) := continuous_apply _

lemma continuous_merge : Continuous (merge (X := X) (m := m)) := by
  refine continuous_pi fun ε => ?_
  by_cases h : ε (Fin.last m)
  · simp only [merge, h, if_true]; exact (continuous_apply _).comp continuous_snd
  · simp only [merge, h]; exact (continuous_apply _).comp continuous_fst

lemma continuous_dup : Continuous (dup (X := X) (m := m)) :=
  continuous_merge.comp (continuous_id.prodMk continuous_id)

variable {Γ : Type*} [AddCommGroup Γ] [AddAction Γ X]

lemma cL_vadd (i : Fin m) (γ : Γ) (y : CubeSp X m) : cL i (γ +ᵥ y) = γ +ᵥ cL i y := rfl

lemma cU_vadd (i : Fin m) (γ : Γ) (y : CubeSp X m) : cU i (γ +ᵥ y) = γ +ᵥ cU i y := rfl

lemma topV_vadd (γ : Γ) (y : CubeSp X m) : topV (γ +ᵥ y) = γ +ᵥ topV y := rfl

lemma merge_vadd (γ : Γ) (p : CubeSp X m × CubeSp X m) : merge (γ +ᵥ p) = γ +ᵥ merge p := by
  funext ε
  simp only [merge, Pi.vadd_apply, Prod.vadd_fst, Prod.vadd_snd]
  split_ifs <;> rfl

lemma dup_vadd (γ : Γ) (y : CubeSp X m) : dup (γ +ᵥ y) = γ +ᵥ dup y := merge_vadd γ (y, y)

/-! ### Faces of `merge` -/

lemma cL_castSucc_merge (j : Fin m) (p : CubeSp X m × CubeSp X m) :
    cL (Fin.castSucc j) (merge p) = merge (cL j p.1, cL j p.2) := by
  funext ε
  simp only [cL, merge, Function.update_of_ne (Fin.castSucc_ne_last j).symm, Fin.init_update_castSucc]

lemma cU_castSucc_merge (j : Fin m) (p : CubeSp X m × CubeSp X m) :
    cU (Fin.castSucc j) (merge p) = merge (cU j p.1, cU j p.2) := by
  funext ε
  simp only [cU, merge, Function.update_of_ne (Fin.castSucc_ne_last j).symm, Fin.init_update_castSucc]

lemma cL_last_merge (p : CubeSp X m × CubeSp X m) : cL (Fin.last m) (merge p) = dup p.1 := by
  funext ε
  simp only [cL, merge, dup, Function.update_self, Fin.init_update_last, Bool.false_eq_true,
    if_false, ite_self]

lemma cU_last_merge (p : CubeSp X m × CubeSp X m) : cU (Fin.last m) (merge p) = dup p.2 := by
  funext ε
  simp only [cU, merge, dup, Function.update_self, Fin.init_update_last, if_true, ite_self]

lemma botV_merge (p : CubeSp X m × CubeSp X m) : botV (merge p) = botV p.1 := by
  simp only [botV, merge]; rfl

lemma topV_merge (p : CubeSp X m × CubeSp X m) : topV (merge p) = topV p.2 := by
  simp only [topV, merge, if_true]; rfl

/-- Face convergence implies the Erdős cube property. -/
lemma isErdosCube_of_faces {y : CubeSp X m}
    (h : ∀ i : Fin m, ∃ β : ℕ → Γ, Function.Injective β ∧
      Tendsto (fun n => β n +ᵥ cL i y) atTop (𝓝 (cU i y))) :
    IsErdosCube (Γ := Γ) y := by
  intro i
  obtain ⟨β, hβ, hlim⟩ := h i
  refine ⟨β, hβ, fun ε hε => ?_⟩
  have := (tendsto_pi_nhds.1 hlim) ε
  simp only [cL, cU, Pi.vadd_apply] at this
  rwa [Function.update_eq_self_iff.2 hε.symm] at this

end CubeSp

lemma dist_cU_le {X : Type*} [MetricSpace X] {m : ℕ} (i : Fin m) (x y : CubeSp X m) :
    dist (cU i x) (cU i y) ≤ dist x y :=
  (dist_pi_le_iff dist_nonneg).2 fun ε => dist_le_pi_dist x y (Function.update ε i true)

/-! ## Cube data and the cube criterion -/

section Datum

variable {Γ X : Type u} [AddCommGroup Γ] [Countable Γ] [Infinite Γ]
variable [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [AddAction Γ X]
  [ContinuousConstVAdd Γ X]

/-- Paper, Definition \ref{K:def:datum}: an `m`-dimensional cube datum `(w, λ, Ψ)` for the
system `(X, μ)` and the point `a`. Condition (D2) is replaced by `(top vertex)_* λ = μ`, which is
the only consequence of (D2) used in the proof. -/
structure CubeDatum (Γ : Type u) [AddCommGroup Γ] [AddAction Γ X] (μX : Measure X) (a : X)
    (m : ℕ) (w : CubeSp X m) (lam : Measure (CubeSp X m)) (Ψ : ℕ → Finset Γ) : Prop where
  prob : IsProbabilityMeasure lam
  erg : ErgodicVAdd Γ (CubeSp X m) lam
  folner : IsFolner Ψ
  gen : IsGeneric lam Ψ w
  bot : botV w = a
  top : lam.map topV = μX
  face : ∀ i : Fin m, lam.map (cL i) = lam.map (cU i)
  supp : ∀ i : Fin m, cU i w ∈ (lam.map (cU i)).support

/-- Paper, Proposition \ref{K:prop:criterion} (cube criterion): an `m`-dimensional cube datum
yields an `(m+1)`-dimensional Erdős cube with bottom vertex `a` and top vertex in `E`. -/
theorem CubeDatum.exists_erdosCube (hG : GenericPointsExist.{u}) (hK : DiscreteSpectrumThm.{u})
    (hW : WienerKoopman.{u}) {μX : Measure X} {a : X} {m : ℕ} {w : CubeSp X m}
    {lam : Measure (CubeSp X m)} {Ψ : ℕ → Finset Γ} (hd : CubeDatum Γ μX a m w lam Ψ)
    {E : Set X} (hEo : IsOpen E) (hE : 0 < μX E) :
    ∃ y : CubeSp X (m + 1), IsErdosCube (Γ := Γ) y ∧ botV y = a ∧ topV y ∈ E := by
  have := hd.prob
  have := hd.erg
  have hV0o : IsOpen (topV ⁻¹' E : Set (CubeSp X m)) := hEo.preimage continuous_topV
  have hV0 : 0 < lam (topV ⁻¹' E) := by
    rw [← Measure.map_apply continuous_topV.measurable hEo.measurableSet, hd.top]; exact hE
  obtain ⟨x, hxV0, ⟨β, hβ, hlim⟩, hfaces⟩ := cube_criterion hG hK hW hd.folner hd.gen
    (fun i => cL i) (fun i => cU i) (fun i => continuous_cL i) (fun i => continuous_cU i)
    (fun i γ y => cL_vadd i γ y) (fun i γ y => cU_vadd i γ y) (fun i => dist_cU_le i)
    hd.face hd.supp hV0o hV0
  refine ⟨merge (w, x), isErdosCube_of_faces fun i => ?_, by rw [botV_merge]; exact hd.bot,
    by rw [topV_merge]; exact hxV0⟩
  induction i using Fin.lastCases with
  | last =>
    refine ⟨β, hβ, ?_⟩
    rw [cL_last_merge, cU_last_merge]
    have := (continuous_dup.tendsto x).comp hlim
    refine this.congr fun n => ?_
    simp only [Function.comp, dup_vadd]
  | cast j =>
    obtain ⟨β', hβ', h1, h2⟩ := hfaces j
    refine ⟨β', hβ', ?_⟩
    rw [cL_castSucc_merge, cU_castSucc_merge]
    have := (continuous_merge.tendsto (cU j w, cU j x)).comp (h1.prodMk_nhds h2)
    refine this.congr fun n => ?_
    simp only [Function.comp, ← merge_vadd]
    rfl

end Datum

/-! ## The graph measure of a Kronecker map -/

section GraphKron

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}
variable {Y : Type*} [MeasurableSpace Y] [AddAction Γ Y] [MeasurableConstVAdd Γ Y]
variable {μ : Measure Y} {κ : Y → KG α}

omit [MeasurableConstVAdd Γ Y] in
lemma graphMeasure_map_fst (hκ : Measurable κ) : (graphMeasure μ κ).map Prod.fst = μ := by
  rw [graphMeasure, Measure.map_map measurable_fst (measurable_id'.prodMk hκ)]
  exact Measure.map_id

omit [MeasurableConstVAdd Γ Y] in
lemma graphMeasure_map_snd (hκ : Measurable κ) : (graphMeasure μ κ).map Prod.snd = μ.map κ := by
  rw [graphMeasure, Measure.map_map measurable_snd (measurable_id'.prodMk hκ)]
  rfl

omit [MeasurableConstVAdd Γ Y] in
lemma ae_graphMeasure (hκ : Measurable κ) : ∀ᵐ p ∂graphMeasure μ κ, p.2 = κ p.1 := by
  have hmeas : MeasurableSet {p : Y × KG α | p.2 = κ p.1} :=
    measurableSet_eq_fun measurable_snd (hκ.comp measurable_fst)
  rw [graphMeasure, ae_map_iff (measurable_id'.prodMk hκ).aemeasurable hmeas]
  exact Eventually.of_forall fun y => rfl

/-- The second projection is a (continuous, everywhere equivariant) Kronecker map for the
graph measure of a Kronecker map. -/
theorem IsKroneckerMap.graph [IsProbabilityMeasure μ] (hκ : IsKroneckerMap μ α κ) :
    IsKroneckerMap (graphMeasure μ κ) α Prod.snd := by
  have hκm := hκ.measurable
  have hg : Measurable fun y => (y, κ y) := measurable_id'.prodMk hκm
  refine ⟨measurable_snd, by rw [graphMeasure_map_snd hκm, hκ.map_eq],
    fun γ => Eventually.of_forall fun p => by simp [Prod.vadd_def, vadd_kg, add_comm], ?_⟩
  intro h hh he
  obtain ⟨ψ, hψ⟩ := he
  -- a measurable version of `h`
  set h' := hh.1.mk h with hh'
  have hh'm : Measurable h' := hh.1.stronglyMeasurable_mk.measurable
  have hhh' : h =ᵐ[graphMeasure μ κ] h' := hh.1.ae_eq_mk
  -- pull back to `μ`
  have hpull : MemLp (fun y => h (y, κ y)) 2 μ := by
    have := (memLp_map_measure_iff hh.1 hg.aemeasurable).1 hh
    exact this
  have heig : IsEigenfunction (Γ := Γ) μ (fun y => h (y, κ y)) := by
    refine ⟨ψ, fun γ => ?_⟩
    have h1 : ∀ᵐ y ∂μ, h (γ +ᵥ (y, κ y)) = ψ γ * h (y, κ y) :=
      ae_of_ae_map hg.aemeasurable (hψ γ)
    filter_upwards [h1, hκ.ae_equivariant γ] with y hy1 hy2
    have : (γ +ᵥ y, κ (γ +ᵥ y)) = γ +ᵥ (y, κ y) := by
      simp [Prod.vadd_def, hy2, vadd_kg, add_comm]
    simp only [this, hy1]
  obtain ⟨g, hgm, hgg⟩ := hκ.eigen _ hpull heig
  refine ⟨g, hgm, ?_⟩
  have h2 : ∀ᵐ y ∂μ, h' (y, κ y) = g (κ y) := by
    have := ae_of_ae_map hg.aemeasurable hhh'
    filter_upwards [this, hgg] with y hy1 hy2
    rw [← hy1]; exact hy2
  have hmeas : MeasurableSet {p : Y × KG α | h' p = g p.2} :=
    measurableSet_eq_fun hh'm (hgm.comp measurable_snd)
  have h3 : ∀ᵐ p ∂graphMeasure μ κ, h' p = g p.2 := by
    rw [graphMeasure, ae_map_iff hg.aemeasurable hmeas]
    exact h2
  filter_upwards [hhh', h3] with p hp1 hp2
  rw [hp1, hp2]; rfl

end GraphKron

/-! ## The induction step -/

section Step

variable {Γ Y : Type u} [AddCommGroup Γ] [Countable Γ]
variable [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y]
  [ContinuousConstVAdd Γ Y] [Nonempty Y]

/-- Steps 1 and 2 of the proof of Proposition \ref{K:prop:step}: re-basing, generic pairs, and
projection to `Y × Y`. -/
theorem exists_rebased_pairs (hG : GenericPointsExist.{u}) (hW : WienerKoopman.{u})
    {lam : Measure Y} [IsProbabilityMeasure lam] [ErgodicVAdd Γ Y lam] {Ψ : ℕ → Finset Γ}
    {w : Y} (hw : IsGeneric lam Ψ w) {α : Γ →+ Torus} {κ : Y → KG α}
    (hκ : IsKroneckerMap lam α κ) :
    ∃ (d : KG α) (Ψ' : ℕ → Finset Γ) (φ : ℕ → ℕ), IsFolner Ψ' ∧ StrictMono φ ∧
      IsGeneric (graphMeasure lam κ) Ψ' (w, d) ∧
      ∀ᵐ x ∂lam, IsGeneric (relJ lam κ (κ x - d)) (Ψ' ∘ φ) (w, x) := by
  obtain ⟨d, Ψ', hΨ', hgen⟩ := rebase hG hw.support_subset hκ.measurable hκ.ae_equivariant
  have herg : ErgodicVAdd Γ (Y × KG α) (graphMeasure lam κ) :=
    graphMeasure_ergodic hκ.measurable hκ.ae_equivariant
  have : IsProbabilityMeasure (graphMeasure lam κ) :=
    isProbabilityMeasure_graphMeasure hκ.measurable
  have : VAddInvariantMeasure Γ (Y × KG α) (graphMeasure lam κ) := herg.toVAddInvariantMeasure
  have hπe : ∀ (γ : Γ) (q : Y × KG α), (γ +ᵥ q).2 = q.2 + kα α γ := fun γ q => by
    simp [Prod.vadd_def, vadd_kg, add_comm]
  obtain ⟨φ, hφ, hae⟩ := generic_pairs hW continuous_snd hπe hκ.graph hΨ' hgen
  refine ⟨d, Ψ', φ, hΨ', hφ, hgen, ?_⟩
  have hg : Measurable fun y => (y, κ y) := measurable_id'.prodMk hκ.measurable
  have hae' := ae_of_ae_map hg.aemeasurable hae
  -- the factor map `fst`
  have hP : IsFactorMap (Γ := Γ) (graphMeasure lam κ) lam Prod.fst :=
    ⟨measurable_fst, fun γ q => rfl, graphMeasure_map_fst hκ.measurable⟩
  have hc : ∀ᵐ q ∂graphMeasure lam κ, κ q.1 = id q.2 + 0 :=
    (ae_graphMeasure hκ.measurable).mono fun q hq => by simp [hq]
  have : BorelSpace ((Y × KG α) × (Y × KG α)) := Prod.borelSpace
  filter_upwards [hae'] with x hx
  have := hx.map (continuous_fst.prodMap continuous_fst) (fun γ q => rfl)
  rw [hP.map_relJ hW hκ.graph.toRotFactor hκ isFactorHom_id hc] at this
  simpa using this

/-- Step 4 of the proof of Proposition \ref{K:prop:step}, direction `i ≤ m`: for `λ`-a.e. `x`,
`(U_i w, U_i x)` lies in the support of `J^{ν_i}_{χ̄_i(κ x - d)}`. -/
theorem face_support (hK : DiscreteSpectrumThm.{u}) {lam : Measure Y} [IsProbabilityMeasure lam]
    [ErgodicVAdd Γ Y lam] {α : Γ →+ Torus} {κ : Y → KG α} (hκ : IsRotFactor lam α κ)
    {Ψ' : ℕ → Finset Γ} {w : Y} {d : KG α} (hgen : IsGeneric (graphMeasure lam κ) Ψ' (w, d))
    {U : Y → Y} (hUc : Continuous U) (hUe : ∀ (γ : Γ) y, U (γ +ᵥ y) = γ +ᵥ U y)
    (hsupp : U w ∈ (lam.map U).support) [IsProbabilityMeasure (lam.map U)] {αj : Γ →+ Torus}
    {ι : Y → KG αj}
    (hι : IsRotFactor (lam.map U) αj ι) {χ : KG α → KG αj} (hχ : IsFactorHom α αj χ) {c : KG αj}
    (hcU : ∀ᵐ x ∂lam, ι (U x) = χ (κ x) + c) :
    ∀ᵐ x ∂lam, (U w, U x) ∈ (relJ (lam.map U) ι (χ (κ x - d))).support := by
  have : ErgodicVAdd Γ Y (lam.map U) := ErgodicVAdd.map hUc.measurable hUe
  set θ := χ d + c with hθ
  set Φj : Y × KG α → Y × KG αj := fun q => (U q.1, χ q.2 + c) with hΦj
  have hΦc : Continuous Φj := (hUc.comp continuous_fst).prodMk
    ((hχ.continuous.comp continuous_snd).add continuous_const)
  have hΦe : ∀ (γ : Γ) q, Φj (γ +ᵥ q) = γ +ᵥ Φj q := fun γ q => by
    simp only [hΦj, Prod.vadd_def, vadd_kg, hUe, hχ.map_add, hχ.comp_eq, add_assoc]
  have hmapΦ : (graphMeasure lam κ).map Φj = graphMeasure (lam.map U) ι := by
    rw [graphMeasure, graphMeasure, Measure.map_map hΦc.measurable
      (measurable_id'.prodMk hκ.measurable), Measure.map_map
      (measurable_id'.prodMk hι.measurable) hUc.measurable]
    refine Measure.map_congr (hcU.mono fun x hx => ?_)
    simp [hΦj, hx]
  have hgenj : IsGeneric (graphMeasure (lam.map U) ι) Ψ' (U w, θ) := by
    have := hgen.map hΦc hΦe; rwa [hmapΦ] at this
  have hmem := mem_support_graph_of_isGeneric hι.measurable hι.ae_equivariant hgenj hsupp
  have hPS := hι.ae_mem_support_relJ hmem
  have hg : Measurable fun x => (U x, ι (U x)) := hUc.measurable.prodMk (hι.measurable.comp
    hUc.measurable)
  have hgraph : graphMeasure (lam.map U) ι = lam.map fun x => (U x, ι (U x)) := by
    rw [graphMeasure, Measure.map_map (measurable_id'.prodMk hι.measurable) hUc.measurable]
    rfl
  rw [hgraph] at hPS
  have hPS' := ae_of_ae_map hg.aemeasurable hPS
  filter_upwards [hPS', hcU] with x hx1 hx2
  have : ι (U x) - θ = χ (κ x - d) := by
    rw [hx2, hθ, hχ.map_sub]; abel
  simpa [this] using hx1

end Step

section StepMain

variable {Γ X : Type u} [AddCommGroup Γ] [Countable Γ]
variable [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [AddAction Γ X]
  [ContinuousConstVAdd Γ X]

/-- Paper, Proposition \ref{K:prop:step} (induction step): an `m`-dimensional cube datum gives an
`(m+1)`-dimensional cube datum. -/
theorem CubeDatum.succ (hG : GenericPointsExist.{u}) (hK : DiscreteSpectrumThm.{u})
    (hW : WienerKoopman.{u}) {μX : Measure X} {a : X} {m : ℕ} {w : CubeSp X m}
    {lam : Measure (CubeSp X m)} {Ψ : ℕ → Finset Γ} (hd : CubeDatum Γ μX a m w lam Ψ) :
    ∃ (w' : CubeSp X (m + 1)) (lam' : Measure (CubeSp X (m + 1))) (Ψ' : ℕ → Finset Γ),
      CubeDatum Γ μX a (m + 1) w' lam' Ψ' := by
  have := hd.prob
  have := hd.erg
  have : Nonempty (CubeSp X m) := ⟨w⟩
  obtain ⟨α, κ, hκ⟩ := hK Γ (CubeSp X m) lam
  have hκR := hκ.toRotFactor
  -- the faces and their Kronecker data
  have hνprob : ∀ i : Fin m, IsProbabilityMeasure (lam.map (cU i)) := fun i =>
    Measure.isProbabilityMeasure_map (continuous_cU i).measurable.aemeasurable
  have hνerg : ∀ i : Fin m, ErgodicVAdd Γ (CubeSp X m) (lam.map (cU i)) := fun i =>
    ErgodicVAdd.map (continuous_cU i).measurable (cU_vadd i)
  have hKi : ∀ i : Fin m, ∃ (αi : Γ →+ Torus) (ιi : CubeSp X m → KG αi),
      IsKroneckerMap (lam.map (cU i)) αi ιi := fun i => by
    have := hνprob i; have := hνerg i; exact hK Γ _ _
  choose αi ιi hιi using hKi
  have hUf : ∀ i : Fin m, IsFactorMap (Γ := Γ) lam (lam.map (cU i)) (cU i) := fun i =>
    ⟨(continuous_cU i).measurable, cU_vadd i, rfl⟩
  have hLf : ∀ i : Fin m, IsFactorMap (Γ := Γ) lam (lam.map (cU i)) (cL i) := fun i =>
    ⟨(continuous_cL i).measurable, cL_vadd i, hd.face i⟩
  have hχex : ∀ i : Fin m, ∃ χ, IsFactorHom α (αi i) χ := fun i =>
    (hUf i).exists_isFactorHom hκ (hιi i).toRotFactor
  choose χi hχi using hχex
  have hcUex : ∀ i : Fin m, ∃ c, ∀ᵐ x ∂lam, ιi i (cU i x) = χi i (κ x) + c := fun i =>
    (hUf i).exists_affine hκR (hιi i).toRotFactor (hχi i)
  choose cUi hcUi using hcUex
  have hcLex : ∀ i : Fin m, ∃ c, ∀ᵐ x ∂lam, ιi i (cL i x) = χi i (κ x) + c := fun i =>
    (hLf i).exists_affine hκR (hιi i).toRotFactor (hχi i)
  choose cLi hcLi using hcLex
  -- Steps 1 and 2: re-basing and generic pairs
  obtain ⟨d, Ψ', φ, hΨ', hφ, hgen, hpairs⟩ := exists_rebased_pairs hG hW hd.gen hκ
  -- ergodicity of `J_{κ x - d}`
  have hJerg := hκ.ae_ergodic_relJ hW
  have hmaps : lam.map (fun x => κ x - d) = haarK α := by
    rw [show (fun x => κ x - d) = (fun z => z + -d) ∘ κ by funext x; simp [sub_eq_add_neg],
      ← Measure.map_map (measurable_add_const _) hκ.measurable, hκ.map_eq, map_haarK_add]
  rw [← hmaps] at hJerg
  have hJerg' := ae_of_ae_map (hκ.measurable.sub_const d).aemeasurable hJerg
  -- supports
  have hsuppx : ∀ᵐ x ∂lam, x ∈ lam.support := Measure.support_mem_ae
  have hfaces : ∀ᵐ x ∂lam, ∀ i : Fin m,
      (cU i w, cU i x) ∈ (relJ (lam.map (cU i)) (ιi i) (χi i (κ x - d))).support := by
    rw [ae_all_iff]
    intro i
    have := hνprob i
    exact face_support hK hκR hgen (continuous_cU i) (cU_vadd i) (hd.supp i)
      (hιi i).toRotFactor (hχi i) (hcUi i)
  -- choice of `x`
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ := (hpairs.and (hJerg'.and (hsuppx.and hfaces))).exists
  set sx := κ x - d with hsx
  set J := relJ lam κ sx with hJ
  have : ErgodicVAdd Γ (CubeSp X m × CubeSp X m) J := hx2
  have hmm : Measurable (merge (X := X) (m := m)) := continuous_merge.measurable
  -- the face measures of `J.map merge`
  have hfaceL : ∀ j : Fin m, (J.map merge).map (cL (Fin.castSucc j)) =
      (relJ (lam.map (cU j)) (ιi j) (χi j sx)).map merge := by
    intro j
    have := hνprob j
    rw [Measure.map_map (continuous_cL _).measurable hmm,
      show cL (Fin.castSucc j) ∘ merge = merge ∘ Prod.map (cL j) (cL j) from
        funext fun p => cL_castSucc_merge j p,
      ← Measure.map_map hmm ((continuous_cL j).measurable.prodMap (continuous_cL j).measurable),
      (hLf j).map_relJ hW hκR (hιi j) (hχi j) (hcLi j) sx]
  have hfaceU : ∀ j : Fin m, (J.map merge).map (cU (Fin.castSucc j)) =
      (relJ (lam.map (cU j)) (ιi j) (χi j sx)).map merge := by
    intro j
    have := hνprob j
    rw [Measure.map_map (continuous_cU _).measurable hmm,
      show cU (Fin.castSucc j) ∘ merge = merge ∘ Prod.map (cU j) (cU j) from
        funext fun p => cU_castSucc_merge j p,
      ← Measure.map_map hmm ((continuous_cU j).measurable.prodMap (continuous_cU j).measurable),
      (hUf j).map_relJ hW hκR (hιi j) (hχi j) (hcUi j) sx]
  have hfaceLlast : (J.map merge).map (cL (Fin.last m)) = lam.map dup := by
    rw [Measure.map_map (continuous_cL _).measurable hmm,
      show cL (Fin.last m) ∘ merge = dup ∘ Prod.fst from funext fun p => cL_last_merge p,
      ← Measure.map_map continuous_dup.measurable measurable_fst, hκR.relJ_map_fst]
  have hfaceUlast : (J.map merge).map (cU (Fin.last m)) = lam.map dup := by
    rw [Measure.map_map (continuous_cU _).measurable hmm,
      show cU (Fin.last m) ∘ merge = dup ∘ Prod.snd from funext fun p => cU_last_merge p,
      ← Measure.map_map continuous_dup.measurable measurable_snd, hκR.relJ_map_snd]
  refine ⟨merge (w, x), J.map merge, Ψ' ∘ φ, ?_⟩
  refine ⟨Measure.isProbabilityMeasure_map hmm.aemeasurable, ErgodicVAdd.map hmm merge_vadd,
    hΨ'.comp hφ, hx1.map continuous_merge merge_vadd, by rw [botV_merge]; exact hd.bot, ?_, ?_, ?_⟩
  · rw [Measure.map_map continuous_topV.measurable hmm,
      show topV ∘ merge = topV ∘ Prod.snd from funext fun p => topV_merge p,
      ← Measure.map_map continuous_topV.measurable measurable_snd, hκR.relJ_map_snd]
    exact hd.top
  · intro i
    induction i using Fin.lastCases with
    | last => rw [hfaceLlast, hfaceUlast]
    | cast j => rw [hfaceL j, hfaceU j]
  · intro i
    induction i using Fin.lastCases with
    | last =>
      rw [hfaceUlast, cU_last_merge]
      exact image_support_subset_support_map continuous_dup ⟨x, hx3, rfl⟩
    | cast j =>
      rw [hfaceU j, cU_castSucc_merge]
      exact image_support_subset_support_map continuous_merge ⟨_, hx4 j, rfl⟩

end StepMain

end Kmrr25.ThmK
