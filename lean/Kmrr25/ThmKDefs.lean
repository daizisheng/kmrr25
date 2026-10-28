import Kmrr25.Q516

/-!
# Theorem K: definitions and the classical inputs

Paper, Section \ref{K:sec:main} (*Sums of `k` infinite sets in countable abelian groups*).

This file fixes the vocabulary used in the formalization of Theorem \ref{K:thm:main} and states,
as explicit `Prop`s, the four published theorems which the proof uses without proof.
They are collected in the structure `ClassicalInputs`, which is a *hypothesis* of the main
theorem (no axioms are added).

## Conventions

* `Γ` is a countable abelian group, written additively; it acts on spaces by `AddAction`,
  `T^γ y = γ +ᵥ y`.
* A *topological `Γ`-system* is a compact metrizable space `Y` with its Borel σ-algebra and an
  action of `Γ` by continuous maps (`ContinuousConstVAdd`); since the action is a group action,
  each `T^γ` is a homeomorphism.
* Følner sequences and upper Banach density are those of `Kmrr25.Q516`
  (`Q516.IsFolner`, `Q516.ubd`).
* Ergodicity is Mathlib's `ErgodicVAdd`: the measure is invariant, and every measurable set which
  is a.e. invariant under every `T^γ` is null or conull. Supports are Mathlib's `Measure.support`.
* `Torus = ℕ → ℝ/ℤ`. For a homomorphism `α : Γ →+ Torus`, the compact group
  `KG α = closure (α Γ)` with its normalised Haar measure `haarK α` is the rotation
  `(K, α)` of the paper. Every compact metrizable abelian group with a dense homomorphic image
  of `Γ` is of this form (its dual is countable), so this is no loss of generality; it has the
  advantage that the coordinate characters separate the points of `K`.

## The classical inputs

1. `CorrespondencePrinciple`: Furstenberg's correspondence principle in the ergodic form of
   Charamaras and Mountakis, *Finding product sets in some classes of amenable groups*,
   Theorem 2.15 (paper, Theorem \ref{K:thm:corr}).
2. `GenericPointsExist`: for an ergodic measure, almost every point is generic along a
   subsequence of any Følner sequence; Charamaras–Mountakis, Lemma 2.7, a consequence of
   Lindenstrauss' pointwise ergodic theorem (paper, fact (G4)).
3. `DiscreteSpectrumThm`: the Halmos–von Neumann theorem: the Kronecker factor of an ergodic
   system is a rotation on a compact abelian group (paper, Lemma \ref{K:lem:kron}(a);
   Charamaras–Mountakis, Proposition 2.12).
4. `WienerKoopman`: the Koopman–von Neumann theorem (via the spectral theorem and Wiener's
   lemma): a vector orthogonal to all eigenfunctions has Cesàro-vanishing self-correlations
   along every Følner sequence (paper, Lemma \ref{K:lem:wiener}(c),(d)).
-/

open Filter Topology Finset MeasureTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

universe u

/-! ## Averages and generic points -/

/-- The average `𝔼_{γ ∈ F} f(γ) = |F|⁻¹ ∑_{γ ∈ F} f γ` over a finite set. -/
def avg {ι E : Type*} [AddCommMonoid E] [Module ℝ E] (F : Finset ι) (f : ι → E) : E :=
  (#F : ℝ)⁻¹ • ∑ i ∈ F, f i

/-- `y` is *generic for `ν` along `Φ`*: `𝔼_{γ ∈ Φ_N} f(T^γ y) → ∫ f dν` for every continuous
`f : Y → ℝ`. -/
def IsGeneric {Γ Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [VAdd Γ Y]
    (ν : Measure Y) (Φ : ℕ → Finset Γ) (y : Y) : Prop :=
  ∀ f : C(Y, ℝ), Tendsto (fun N => avg (Φ N) fun γ => f (γ +ᵥ y)) atTop (𝓝 (∫ x, f x ∂ν))

/-- `h` is an *eigenfunction* of the Koopman representation of `λ`: there are numbers `ψ γ` with
`h ∘ T^γ = ψ γ · h` almost everywhere, for every `γ` (`h = 0` is allowed). -/
def IsEigenfunction {Γ Y : Type*} [MeasurableSpace Y] [VAdd Γ Y] (μ : Measure Y)
    (h : Y → ℂ) : Prop :=
  ∃ ψ : Γ → ℂ, ∀ γ : Γ, (fun y => h (γ +ᵥ y)) =ᵐ[μ] fun y => ψ γ * h y

/-! ## Rotations on closed subgroups of the infinite torus -/

/-- The infinite torus `(ℝ/ℤ)^ℕ`. -/
abbrev Torus : Type := ℕ → UnitAddCircle

/-- The closed subgroup `K = closure (α Γ)` of the torus. -/
def kgroup {Γ : Type*} [AddCommGroup Γ] (α : Γ →+ Torus) : AddSubgroup Torus :=
  α.range.topologicalClosure

/-- The compact abelian group `K = closure (α Γ)`, as a type. -/
abbrev KG {Γ : Type*} [AddCommGroup Γ] (α : Γ →+ Torus) : Type := ↥(kgroup α)

section KGInstances

variable {Γ : Type*} [AddCommGroup Γ] (α : Γ →+ Torus)

instance : SecondCountableTopology (KG α) :=
  TopologicalSpace.Subtype.secondCountableTopology (kgroup α : Set Torus)

instance : TopologicalSpace.MetrizableSpace (KG α) :=
  TopologicalSpace.MetrizableSpace.subtype (kgroup α : Set Torus)

instance : CompactSpace (KG α) :=
  isCompact_iff_compactSpace.mp (AddSubgroup.isClosed_topologicalClosure _).isCompact

/-- The normalised Haar measure `m_K` on `K = closure (α Γ)`. -/
def haarK : Measure (KG α) := Measure.addHaarMeasure ⊤

/-- The homomorphism `α : Γ → K` (corestriction of `α` to `K`). -/
def kα : Γ →+ KG α where
  toFun γ := ⟨α γ, AddSubgroup.le_topologicalClosure _ ⟨γ, rfl⟩⟩
  map_zero' := by ext1; simp
  map_add' _ _ := by ext1; simp

end KGInstances

/-- `κ : Y → K` is a *Kronecker map* for `λ` with rotation `α` (paper,
Definition \ref{K:def:kron}): it is measurable, pushes `λ` to Haar measure, is a.e. equivariant,
and every `L²` eigenfunction is a.e. a function of `κ` (that is, the Kronecker subspace is
contained in `L²(σ(κ))`; the reverse inclusion is automatic and is proved in this formalization). -/
structure IsKroneckerMap {Γ Y : Type*} [AddCommGroup Γ] [MeasurableSpace Y] [AddAction Γ Y]
    (μ : Measure Y) (α : Γ →+ Torus) (κ : Y → KG α) : Prop where
  measurable : Measurable κ
  map_eq : μ.map κ = haarK α
  ae_equivariant : ∀ γ : Γ, ∀ᵐ y ∂μ, κ (γ +ᵥ y) = κ y + kα α γ
  eigen : ∀ h : Y → ℂ, MemLp h 2 μ → IsEigenfunction (Γ := Γ) μ h →
    ∃ g : KG α → ℂ, Measurable g ∧ h =ᵐ[μ] g ∘ κ

/-! ## The classical inputs -/

/-- **Furstenberg's correspondence principle**, ergodic form of Charamaras–Mountakis
(*Finding product sets in some classes of amenable groups*, Theorem 2.15), as quoted in the paper
(Theorem \ref{K:thm:corr}): if `Φ` is a Følner sequence along which the density of `A` exists and
equals `c`, then there are an ergodic topological `Γ`-system `(X, μ, T)` on a compact metric space,
a clopen set `E ⊆ X` with `μ E ≥ c`, a Følner sequence `Ψ` and a point `a` generic for `μ` along
`Ψ` with `A = {γ | T^γ a ∈ E}`. -/
def CorrespondencePrinciple : Prop :=
  ∀ (Γ : Type u) [AddCommGroup Γ] [Countable Γ] (A : Set Γ) (Φ : ℕ → Finset Γ) (c : ℝ),
    Q516.IsFolner Φ → Tendsto (fun N => Q516.relDens (Φ N) A) atTop (𝓝 c) →
    ∃ (X : Type u) (_ : MetricSpace X) (_ : CompactSpace X) (_ : MeasurableSpace X)
      (_ : BorelSpace X) (_ : AddAction Γ X) (_ : ContinuousConstVAdd Γ X)
      (μ : Measure X) (E : Set X) (Ψ : ℕ → Finset Γ) (a : X),
      IsProbabilityMeasure μ ∧ ErgodicVAdd Γ X μ ∧ IsClopen E ∧ ENNReal.ofReal c ≤ μ E ∧
      Q516.IsFolner Ψ ∧ IsGeneric μ Ψ a ∧ A = {γ | γ +ᵥ a ∈ E}

/-- **Existence of generic points** (Charamaras–Mountakis, Lemma 2.7, resting on Lindenstrauss'
pointwise ergodic theorem; paper, fact (G4)): if `ν` is an ergodic measure on a topological
`Γ`-system, then every Følner sequence `Φ` has a subsequence `Φ ∘ φ` along which `ν`-almost every
point is generic for `ν`. -/
def GenericPointsExist : Prop :=
  ∀ (Γ : Type u) [AddCommGroup Γ] [Countable Γ] (Y : Type u) [TopologicalSpace Y]
    [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [AddAction Γ Y] [ContinuousConstVAdd Γ Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    [ErgodicVAdd Γ Y ν] (Φ : ℕ → Finset Γ), Q516.IsFolner Φ →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ y ∂ν, IsGeneric ν (Φ ∘ φ) y

/-- **Discrete spectrum theorem** (Halmos–von Neumann; for amenable groups Charamaras–Mountakis,
Proposition 2.12; paper, Lemma \ref{K:lem:kron}(a)): every ergodic measure on a topological
`Γ`-system has a Kronecker map onto a rotation `(K, α)`, `K = closure (α Γ)` a closed subgroup of
the torus `(ℝ/ℤ)^ℕ` (whose coordinates enumerate the countably many eigenvalues). -/
def DiscreteSpectrumThm : Prop :=
  ∀ (Γ : Type u) [AddCommGroup Γ] [Countable Γ] (Y : Type u) [TopologicalSpace Y]
    [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [AddAction Γ Y] [ContinuousConstVAdd Γ Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    [ErgodicVAdd Γ Y μ], ∃ (α : Γ →+ Torus) (κ : Y → KG α), IsKroneckerMap μ α κ

/-- **Koopman–von Neumann / Wiener** (spectral theorem for the Koopman representation together
with Wiener's lemma; paper, Lemma \ref{K:lem:wiener}(c),(d)): let `λ` be an invariant probability
measure on a topological `Γ`-system and let `v ∈ L²(λ)` be orthogonal to every eigenfunction.
Then the spectral measure of `v` has no atoms, and hence, for every Følner sequence `Θ`,
`𝔼_{β ∈ Θ_M} |⟨v ∘ T^β, v⟩| → 0`. -/
def WienerKoopman : Prop :=
  ∀ (Γ : Type u) [AddCommGroup Γ] [Countable Γ] (Y : Type u) [TopologicalSpace Y]
    [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [AddAction Γ Y] [ContinuousConstVAdd Γ Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    [VAddInvariantMeasure Γ Y μ] (v : Y → ℂ), MemLp v 2 μ →
    (∀ h : Y → ℂ, MemLp h 2 μ → IsEigenfunction (Γ := Γ) μ h →
      ∫ y, v y * conj (h y) ∂μ = 0) →
    ∀ Θ : ℕ → Finset Γ, Q516.IsFolner Θ →
      Tendsto (fun M => avg (Θ M) fun β => ‖∫ y, v (β +ᵥ y) * conj (v y) ∂μ‖) atTop (𝓝 0)

/-- The four published theorems used without proof in the formalization of
Theorem \ref{K:thm:main}. -/
structure ClassicalInputs : Prop where
  corr : CorrespondencePrinciple.{u}
  generic : GenericPointsExist.{u}
  kronecker : DiscreteSpectrumThm.{u}
  wiener : WienerKoopman.{u}

end Kmrr25.ThmK
