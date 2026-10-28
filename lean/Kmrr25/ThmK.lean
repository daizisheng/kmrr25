import Kmrr25.ThmKStep

/-!
# Theorem K: sums of `k` infinite sets in countable abelian groups

Paper, Theorem \ref{K:thm:main} (answering Question 5.14 of the problem list of Kra, Moreira,
Richter and Robertson): let `Γ` be a countably infinite abelian group and `k ≥ 1`. If `A ⊆ Γ`
has positive upper Banach density, then there are infinite sets `B_1, …, B_k ⊆ Γ` with
`B_1 + ⋯ + B_k ⊆ A`.

## Statement

`thmK` below. The upper Banach density is `Kmrr25.Q516.ubd A = sup_Φ limsup_N |A ∩ Φ_N| / |Φ_N|`,
the supremum over all Følner sequences `Φ` (`Kmrr25.Q516.IsFolner`); "infinite" is
`Set.Infinite`; `B_1 + ⋯ + B_k ⊆ A` is written as `∑ i, b i ∈ A` for all `b` with `b i ∈ B i`.

## Classical inputs

The theorem is proved assuming the four published theorems collected in
`Kmrr25.ThmK.ClassicalInputs` (file `Kmrr25/ThmKDefs.lean`), passed as the hypothesis `hC`:

1. the ergodic Furstenberg correspondence principle (Charamaras–Mountakis, Theorem 2.15);
2. existence of generic points along a subsequence of any Følner sequence (Charamaras–Mountakis,
   Lemma 2.7; Lindenstrauss' pointwise ergodic theorem);
3. the discrete spectrum theorem of Halmos and von Neumann (Kronecker factor as a rotation);
4. the Koopman–von Neumann/Wiener theorem (vanishing Cesàro averages of correlations of vectors
   orthogonal to all eigenfunctions; spectral theorem and Wiener's lemma).

Everything else — in particular Lemmas \ref{K:lem:cube-sumset}, \ref{K:lem:J}, \ref{K:lem:factor},
\ref{K:lem:pairs}, \ref{K:lem:rebase}, \ref{K:lem:stab}, \ref{K:lem:phase}, \ref{K:lem:PS} and
Propositions \ref{K:prop:criterion}, \ref{K:prop:step} — is proved in the files
`Kmrr25/ThmK*.lean`. Disintegrations are Mathlib's conditional kernels.

## Proof

As in the paper (Section \ref{K:ssec:proof}): the correspondence principle gives `(X, μ, E, a)`;
`(a, μ, Ψ)` is a `0`-dimensional cube datum; `k - 1` induction steps (`CubeDatum.succ`) and the
cube criterion (`CubeDatum.exists_erdosCube`) give a `k`-dimensional Erdős cube with bottom vertex
`a` and top vertex in `E`; Lemma \ref{K:lem:cube-sumset} (`cube_sumset`) gives the sets `B_i`.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

namespace Kmrr25.ThmK

open Q516

universe u

/-- A Følner sequence along which the density of `A` converges to a positive limit. -/
lemma exists_folner_tendsto_relDens {Γ : Type u} [AddCommGroup Γ] {A : Set Γ} (hA : 0 < ubd A) :
    ∃ (Φ : ℕ → Finset Γ) (c : ℝ), IsFolner Φ ∧ 0 < c ∧
      Tendsto (fun N => relDens (Φ N) A) atTop (𝓝 c) := by
  obtain ⟨Φ, hΦ, hpos⟩ := (ubd_pos_iff A).1 hA
  have hfreq : ∃ᶠ N in atTop, udensAlong Φ A / 2 < relDens (Φ N) A :=
    frequently_lt_of_lt_limsup (isCoboundedUnder_relDens Φ A) (half_lt_self hpos)
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hfreq
  have hmem : ∀ n, relDens (Φ (φ n)) A ∈ Set.Icc (udensAlong Φ A / 2) 1 :=
    fun n => ⟨(hφP n).le, relDens_le_one _ _⟩
  obtain ⟨c, hc, ψ, hψ, hlim⟩ := (isCompact_Icc).tendsto_subseq hmem
  refine ⟨Φ ∘ φ ∘ ψ, c, hΦ.comp (hφ.comp hψ), lt_of_lt_of_le (half_pos hpos) hc.1, ?_⟩
  exact hlim

section Main

variable {Γ X : Type u} [AddCommGroup Γ] [Countable Γ] [Infinite Γ]
variable [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [AddAction Γ X]
  [ContinuousConstVAdd Γ X]

/-- The embedding `X → X^{[0]}`. -/
def emb0 (x : X) : CubeSp X 0 := fun _ => x

lemma continuous_emb0 : Continuous (emb0 (X := X)) := continuous_pi fun _ => continuous_id

/-- A generic point gives a `0`-dimensional cube datum. -/
lemma cubeDatum_zero {μ : Measure X} [IsProbabilityMeasure μ] [ErgodicVAdd Γ X μ]
    {Ψ : ℕ → Finset Γ} (hΨ : IsFolner Ψ) {a : X} (ha : IsGeneric μ Ψ a) :
    CubeDatum Γ μ a 0 (emb0 a) (μ.map emb0) Ψ := by
  refine ⟨Measure.isProbabilityMeasure_map continuous_emb0.measurable.aemeasurable,
    ErgodicVAdd.map continuous_emb0.measurable (fun γ x => rfl), hΨ,
    ha.map continuous_emb0 (fun γ x => rfl), rfl, ?_, fun i => i.elim0, fun i => i.elim0⟩
  rw [Measure.map_map continuous_topV.measurable continuous_emb0.measurable]
  exact Measure.map_id

/-- Iterating the induction step. -/
lemma exists_cubeDatum (hG : GenericPointsExist.{u}) (hK : DiscreteSpectrumThm.{u})
    (hW : WienerKoopman.{u}) {μ : Measure X} [IsProbabilityMeasure μ] [ErgodicVAdd Γ X μ]
    {Ψ : ℕ → Finset Γ} (hΨ : IsFolner Ψ) {a : X} (ha : IsGeneric μ Ψ a) (n : ℕ) :
    ∃ (w : CubeSp X n) (lam : Measure (CubeSp X n)) (Ψ' : ℕ → Finset Γ),
      CubeDatum Γ μ a n w lam Ψ' := by
  induction n with
  | zero => exact ⟨_, _, _, cubeDatum_zero hΨ ha⟩
  | succ n ih =>
    obtain ⟨w, lam, Ψ', hd⟩ := ih
    exact hd.succ hG hK hW

end Main

/-- **Theorem K** (paper, Theorem \ref{K:thm:main}). Let `Γ` be a countably infinite abelian group
and `k ≥ 1`. If `A ⊆ Γ` has positive upper Banach density, then there are infinite sets
`B_1, …, B_k ⊆ Γ` with `B_1 + ⋯ + B_k ⊆ A`.

The four classical theorems used without proof are the fields of the hypothesis
`hC : ClassicalInputs`. -/
theorem thmK (hC : ClassicalInputs.{u}) {Γ : Type u} [AddCommGroup Γ] [Countable Γ] [Infinite Γ]
    (k : ℕ) (hk : 1 ≤ k) (A : Set Γ) (hA : 0 < ubd A) :
    ∃ B : Fin k → Set Γ, (∀ i, (B i).Infinite) ∧
      ∀ b : Fin k → Γ, (∀ i, b i ∈ B i) → ∑ i, b i ∈ A := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Φ, c, hΦ, hc, hlim⟩ := exists_folner_tendsto_relDens hA
  obtain ⟨X, _, _, _, _, _, _, μ, E, Ψ, a, hμ, herg, hE, hμE, hΨ, ha, hAE⟩ :=
    hC.corr Γ A Φ c hΦ hlim
  obtain ⟨w, lam, Ψ', hd⟩ := exists_cubeDatum hC.generic hC.kronecker hC.wiener hΨ ha n
  have hEpos : 0 < μ E := lt_of_lt_of_le (ENNReal.ofReal_pos.2 hc) hμE
  obtain ⟨y, hy, hbot, htop⟩ :=
    hd.exists_erdosCube hC.generic hC.kronecker hC.wiener hE.isOpen hEpos
  obtain ⟨B, hBinf, hB⟩ := cube_sumset hy hE.isOpen htop
  refine ⟨B, hBinf, fun b hb => ?_⟩
  have := hB b hb
  rw [show y (fun _ => false) = a from hbot] at this
  rw [hAE]
  exact this

end Kmrr25.ThmK
