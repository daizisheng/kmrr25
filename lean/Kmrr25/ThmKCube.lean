import Kmrr25.ThmKDefs

/-!
# Theorem K: Erdős cubes and sumsets

Paper, Definition \ref{K:def:cube} and Lemma \ref{K:lem:cube-sumset}.

A point of `X^{[k]}` is a function `y : (Fin k → Bool) → X`. For a direction `i` and a vertex
`ε` with `ε i = false`, the vertex `ε + e_i` is `Function.update ε i true`.
`y` is an *Erdős cube* if for every direction `i` there are pairwise distinct `β_n` with
`T^{β_n} y_ε → y_{ε + e_i}` for every `ε` with `ε i = false` (this is the convergence
`T^{β_n} L_i(y) → U_i(y)` of the paper, written vertex by vertex).

`cube_sumset` (Lemma \ref{K:lem:cube-sumset}): if `y` is an Erdős cube and `E` is an open set
containing the top vertex `y_{1⋯1}`, then there are infinite sets `B_1, …, B_k` with
`T^{b_1 + ⋯ + b_k} y_{0⋯0} ∈ E` for all `b_i ∈ B_i`.
-/

open Filter Topology Finset
open scoped Classical

noncomputable section

namespace Kmrr25.ThmK

variable {Γ X : Type*} [AddCommGroup Γ] [TopologicalSpace X] [AddAction Γ X]
  [ContinuousConstVAdd Γ X]

/-- Paper, Definition \ref{K:def:cube}: `y ∈ X^{[k]}` is a `k`-dimensional *Erdős cube*. -/
def IsErdosCube {k : ℕ} (y : (Fin k → Bool) → X) : Prop :=
  ∀ i : Fin k, ∃ β : ℕ → Γ, Function.Injective β ∧ ∀ ε : Fin k → Bool, ε i = false →
    Tendsto (fun n => β n +ᵥ y ε) atTop (𝓝 (y (Function.update ε i true)))

namespace CubeSumset

variable {k : ℕ}

/-- The choices `b` of elements `b_j ∈ B_j` for the digits `j` of `ε` equal to `0`
(and `b_j = 0` for the other digits). -/
def choices (B : Fin k → Finset Γ) (ε : Fin k → Bool) : Finset (Fin k → Γ) :=
  Fintype.piFinset fun j => if ε j = false then B j else {0}

/-- The acceptability condition of the proof of Lemma \ref{K:lem:cube-sumset}. -/
def Acceptable (y : (Fin k → Bool) → X) (E : Set X) (B : Fin k → Finset Γ) : Prop :=
  ∀ ε : Fin k → Bool, ∀ b ∈ choices B ε, (∑ j, b j) +ᵥ y ε ∈ E

lemma mem_choices {B : Fin k → Finset Γ} {ε : Fin k → Bool} {b : Fin k → Γ} :
    b ∈ choices B ε ↔ ∀ j, (ε j = false → b j ∈ B j) ∧ (ε j = true → b j = 0) := by
  simp only [choices, Fintype.mem_piFinset]
  refine forall_congr' fun j => ?_
  cases ε j <;> simp

omit [TopologicalSpace X] [ContinuousConstVAdd Γ X] in
lemma acceptable_empty (y : (Fin k → Bool) → X) {E : Set X} (hE : y (fun _ => true) ∈ E) :
    Acceptable y E (fun _ => (∅ : Finset Γ)) := by
  intro ε b hb
  rw [mem_choices] at hb
  have hε : ε = fun _ => true := by
    funext j
    by_contra h
    simpa using (hb j).1 (by simpa using h)
  have hb0 : b = 0 := by
    funext j
    exact (hb j).2 (by simp [hε])
  subst hε hb0
  simpa using hE

/-- One extension step: a new element `b*`, avoiding a given finite set, can be added to the
`i`-th set while keeping acceptability. -/
lemma exists_extend {y : (Fin k → Bool) → X} {E : Set X} (hEo : IsOpen E)
    (hy : IsErdosCube (Γ := Γ) y) {B : Fin k → Finset Γ} (hB : Acceptable y E B) (i : Fin k)
    (F : Finset Γ) :
    ∃ b' : Γ, b' ∉ F ∧ Acceptable y E (Function.update B i (insert b' (B i))) := by
  obtain ⟨β, hβinj, hβ⟩ := hy i
  -- the open sets `H_ε`
  let S : (Fin k → Bool) → Finset Γ := fun ε =>
    (choices B (Function.update ε i true)).image fun b => ∑ j, b j
  let H : (Fin k → Bool) → Set X := fun ε => ⋂ s ∈ S ε, (s +ᵥ ·) ⁻¹' E
  have hHo : ∀ ε, IsOpen (H ε) := fun ε =>
    isOpen_biInter_finset fun s _ => hEo.preimage (continuous_const_vadd s)
  have hyH : ∀ ε, y (Function.update ε i true) ∈ H ε := by
    intro ε
    simp only [H, S, Set.mem_iInter, Finset.mem_image]
    rintro s ⟨b, hb, rfl⟩
    exact hB _ b hb
  -- eventually `β n +ᵥ y ε ∈ H ε` for all relevant `ε`, and `β n ∉ F`
  have hev : ∀ᶠ n in atTop, (∀ ε : Fin k → Bool, ε i = false → β n +ᵥ y ε ∈ H ε) ∧ β n ∉ F := by
    refine Eventually.and ?_ ?_
    · rw [eventually_all]
      intro ε
      by_cases hεi : ε i = false
      · filter_upwards [(hβ ε hεi).eventually ((hHo ε).mem_nhds (hyH ε))] with n hn _ using hn
      · exact Eventually.of_forall fun n h => absurd h hεi
    · have h1 : Tendsto β atTop cofinite := by
        rw [← Nat.cofinite_eq_atTop]; exact hβinj.tendsto_cofinite
      exact (h1.eventually F.finite_toSet.compl_mem_cofinite).mono fun n hn => hn
  obtain ⟨n, hn, hnF⟩ := hev.exists
  refine ⟨β n, hnF, ?_⟩
  intro ε b hb
  rw [mem_choices] at hb
  by_cases hεi : ε i = false
  · have hbi := (hb i).1 hεi
    simp only [Function.update_self, Finset.mem_insert] at hbi
    rcases hbi with hbi | hbi
    · -- the new element is used
      have hsplit : (∑ j, b j) = (∑ j, Function.update b i 0 j) + β n := by
        rw [Finset.sum_update_of_mem (Finset.mem_univ i), zero_add,
          Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase Finset.univ b (Finset.mem_univ i),
          hbi, add_comm]
      have hmem : (∑ j, Function.update b i 0 j) ∈ S ε := by
        simp only [S, Finset.mem_image]
        refine ⟨Function.update b i 0, ?_, rfl⟩
        rw [mem_choices]
        intro j
        by_cases hj : j = i
        · subst hj; simp
        · simp only [Function.update_of_ne hj]
          refine ⟨fun h => ?_, fun h => (hb j).2 h⟩
          have := (hb j).1 h
          simpa [Function.update_of_ne hj] using this
      have := hn ε hεi
      simp only [H, Set.mem_iInter] at this
      have h2 := this _ hmem
      simp only [Set.mem_preimage] at h2
      rw [hsplit, add_vadd]
      exact h2
    · -- an old element is used
      apply hB ε b
      rw [mem_choices]
      intro j
      by_cases hj : j = i
      · subst hj; exact ⟨fun _ => hbi, fun h => absurd h (by simp [hεi])⟩
      · have := hb j
        simpa [Function.update_of_ne hj] using this
  · apply hB ε b
    rw [mem_choices]
    intro j
    by_cases hj : j = i
    · subst hj; exact ⟨fun h => absurd h hεi, (hb j).2⟩
    · have := hb j
      simpa [Function.update_of_ne hj] using this

end CubeSumset

open CubeSumset in
/-- Paper, Lemma \ref{K:lem:cube-sumset}: an Erdős cube whose top vertex lies in the open set `E`
gives infinite sets `B_1, …, B_k` with `T^{b_1 + ⋯ + b_k} y_{0⋯0} ∈ E` for all `b_i ∈ B_i`. -/
theorem cube_sumset {k : ℕ} {y : (Fin k → Bool) → X} (hy : IsErdosCube (Γ := Γ) y) {E : Set X}
    (hEo : IsOpen E) (hE : y (fun _ => true) ∈ E) :
    ∃ B : Fin k → Set Γ, (∀ i, (B i).Infinite) ∧
      ∀ b : Fin k → Γ, (∀ i, b i ∈ B i) → (∑ i, b i) +ᵥ y (fun _ => false) ∈ E := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨fun i => i.elim0, fun i => i.elim0, fun b _ => ?_⟩
    have : (fun _ : Fin 0 => false) = fun _ => true := funext fun i => i.elim0
    simpa [this] using hE
  -- the recursive construction
  let dir : ℕ → Fin k := fun n => ⟨n % k, Nat.mod_lt _ hk⟩
  have step : ∀ (B : {B : Fin k → Finset Γ // Acceptable y E B}) (n : ℕ),
      ∃ b' : Γ, b' ∉ Finset.univ.biUnion B.1 ∧
        Acceptable y E (Function.update B.1 (dir n) (insert b' (B.1 (dir n)))) :=
    fun B n => exists_extend hEo hy B.2 (dir n) _
  choose bstar hbstar hacc using step
  let seq : ℕ → {B : Fin k → Finset Γ // Acceptable y E B} := fun n =>
    Nat.rec ⟨fun _ => ∅, acceptable_empty y hE⟩
      (fun n B => ⟨Function.update B.1 (dir n) (insert (bstar B n) (B.1 (dir n))), hacc B n⟩) n
  have seq_succ : ∀ n, (seq (n + 1)).1 =
      Function.update (seq n).1 (dir n) (insert (bstar (seq n) n) ((seq n).1 (dir n))) :=
    fun n => rfl
  have mono1 : ∀ n j, (seq n).1 j ⊆ (seq (n + 1)).1 j := by
    intro n j
    rw [seq_succ]
    by_cases hj : j = dir n
    · subst hj; simp [Finset.subset_insert]
    · simp [Function.update_of_ne hj]
  have mono : ∀ n m, n ≤ m → ∀ j, (seq n).1 j ⊆ (seq m).1 j := by
    intro n m hnm j
    induction m, hnm using Nat.le_induction with
    | base => exact le_rfl
    | succ m _ ih => exact ih.trans (mono1 m j)
  let b' : ℕ → Γ := fun n => bstar (seq n) n
  have hb'mem : ∀ n, b' n ∈ (seq (n + 1)).1 (dir n) := by
    intro n; rw [seq_succ]; simp [b']
  have hb'new : ∀ n, ∀ j, b' n ∉ (seq n).1 j := by
    intro n j h
    exact hbstar (seq n) n (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, h⟩)
  have hb'inj : Function.Injective b' := by
    intro n m hnm
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hb'new m (dir n) (hnm ▸ mono (n + 1) m h _ (hb'mem n))
    · exact hb'new n (dir m) (hnm ▸ mono (m + 1) n h _ (hb'mem m))
  refine ⟨fun i => ⋃ n, ((seq n).1 i : Set Γ), fun i => ?_, fun b hb => ?_⟩
  · -- infinitely many new elements land in `B_i`
    have hinj : Function.Injective fun t : ℕ => b' (i.1 + k * t) := by
      intro s t hst
      have := hb'inj hst
      have hk' : 0 < k := hk
      simpa [Nat.mul_left_cancel_iff hk'] using this
    refine Set.infinite_of_injective_forall_mem hinj fun t => ?_
    refine Set.mem_iUnion.2 ⟨i.1 + k * t + 1, ?_⟩
    have hdir : dir (i.1 + k * t) = i := by
      ext; simp [dir, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2]
    have := hb'mem (i.1 + k * t)
    rw [hdir] at this
    exact this
  · -- all `b_i` lie in a common stage
    have : ∀ i, ∃ n, b i ∈ (seq n).1 i := fun i => by
      simpa using hb i
    choose n hn using this
    let N := Finset.univ.sup n
    have hN : ∀ i, b i ∈ (seq N).1 i := fun i =>
      mono (n i) N (Finset.le_sup (Finset.mem_univ i)) i (hn i)
    apply (seq N).2 (fun _ => false) b
    rw [mem_choices]
    intro j
    exact ⟨fun _ => hN j, fun h => absurd h (by simp)⟩

end Kmrr25.ThmK
