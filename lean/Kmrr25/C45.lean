import Kmrr25.Basic

/-!
# Ordered sumsets in the primes with summands in `P - 1` (Conjecture 4.5)

Paper, Section \ref{IB:sec:c45}, Theorem \ref{IB:thm:c45}.

## Conditional result

The proof in the paper is a short corollary of a theorem of Tao and Ziegler
(*Infinite partial sumsets in the primes*, arXiv:2301.10303, Theorem 1.5), which is quoted in the
paper and is **not** formalized here. All results of this file are therefore **conditional**:
the Tao–Ziegler theorem is the `Prop` `TaoZieglerThm15` below, transcribed from the paper's
quotation, and it appears as an explicit hypothesis `(hTZ : TaoZieglerThm15)` of every main
theorem. It is not declared as an axiom, and nothing in this file proves it.

Tao–Ziegler, Theorem 1.5 (as quoted in the paper): *there exists an infinite sequence
`h₁ < h₂ < ⋯` of natural numbers such that the `k`-tuple `(h₁, …, h_k)` is prime-producing for
every `k`*, where a tuple `(h₁, …, h_k)` is *prime-producing* if there are infinitely many `n`
such that `n + h₁, …, n + h_k` are simultaneously prime.

## Main results

* `c45_of_TZ` — Theorem \ref{IB:thm:c45}: assuming `TaoZieglerThm15`, for all integers `s, t`
  there are infinite sets `B, C ⊆ {1, 2, …}` with `C + t ⊆ P` and `b + c + s ∈ P` whenever
  `b ∈ B`, `c ∈ C`, `b < c`.
* `conjecture45_of_TZ` — the case `s = 0`, `t = 1`: Conjecture 4.5 of the survey
  (Question \ref{IB:q:c45}), stated as the `Prop` `Conjecture45`.
* `c45_shifted_of_TZ` — the case `s = t = 1`: infinite `B, C` with `C ⊆ P - 1` and
  `{b + c : b ∈ B, c ∈ C, b < c} ⊆ P - 1`.

## Conventions

* The paper's `ℕ` is `{1, 2, …}`; the sets `B, C` produced here consist of positive integers.
* In `TaoZieglerThm15` the sequence is indexed from `0` (`h 0 < h 1 < ⋯`) and takes values in
  Lean's `ℕ = {0, 1, …}`, and the `n` in the definition of prime-producing range over `ℕ`. This
  is implied by the quoted statement with `ℕ = {1, 2, …}` (and also by its reading with `n ∈ ℤ`,
  since `n + h₁` prime forces `n > -h₁`), so the hypothesis used here is no stronger than the
  quoted theorem.
* An integer `z` lies in `P` when `z = p` for a prime number `p` (`InP z`).
-/

namespace Kmrr25.C45

/-- An integer `z` belongs to the set `P` of primes: `z = p` for some prime number `p`. -/
def InP (z : ℤ) : Prop := ∃ p : ℕ, p.Prime ∧ (p : ℤ) = z

/-- A tuple `(h₀, …, h_{k-1})` of natural numbers is *prime-producing* if there are infinitely
many `n` such that `n + h₀, …, n + h_{k-1}` are simultaneously prime
(Tao–Ziegler, Definition 1.1). -/
def PrimeProducing {k : ℕ} (h : Fin k → ℕ) : Prop :=
  {n : ℕ | ∀ i, (n + h i).Prime}.Infinite

/-- The statement of Tao–Ziegler, Theorem 1.5, as quoted in the paper (Section
\ref{IB:sec:c45}): there exists an infinite sequence `h 0 < h 1 < h 2 < ⋯` of natural numbers
such that the `k`-tuple `(h 0, …, h (k-1))` is prime-producing for every `k`.

This is a hypothesis of the results below; it is not proved in this file. -/
def TaoZieglerThm15 : Prop :=
  ∃ h : ℕ → ℕ, StrictMono h ∧ ∀ k : ℕ, PrimeProducing (fun i : Fin k => h i)

/-- Conjecture 4.5 of the survey (Question \ref{IB:q:c45}): there exist infinite sets
`B ⊆ ℕ` and `C ⊆ P - 1` (with `ℕ = {1, 2, …}`) such that
`P ⊇ {b + c : b ∈ B, c ∈ C, b < c}`. -/
def Conjecture45 : Prop :=
  ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ (∀ c ∈ C, 0 < c) ∧
    C ⊆ {n | (n + 1).Prime} ∧ {x | ∃ b ∈ B, ∃ c ∈ C, b < c ∧ x = b + c} ⊆ {p | p.Prime}

section Proof

variable {h : ℕ → ℕ} (s t : ℤ)

/-- `β i = h i - h 0 + t - s` (the paper's `β_i = h_{i+1} - h_1 + t - s`, reindexed). -/
def β (h : ℕ → ℕ) (s t : ℤ) (i : ℕ) : ℤ := (h i : ℤ) - h 0 + t - s

lemma β_strictMono (hh : StrictMono h) : StrictMono (β h s t) := by
  intro i j hij
  have : h i < h j := hh hij
  unfold β
  omega

lemma exists_β_gt (hh : StrictMono h) (c : ℤ) : ∃ i, c < β h s t i := by
  refine ⟨(c - t + s).toNat + h 0 + 1, ?_⟩
  have h1 : (c - t + s).toNat + h 0 + 1 ≤ h ((c - t + s).toNat + h 0 + 1) := hh.id_le _
  unfold β
  omega

/-- `M_k = {m ≥ 1 : m + t ∈ P and m + s + β_i ∈ P for all i ≤ k}`. -/
def M (h : ℕ → ℕ) (s t : ℤ) (k : ℕ) : Set ℕ :=
  {m | 0 < m ∧ InP ((m : ℤ) + t) ∧ ∀ i ≤ k, InP ((m : ℤ) + s + β h s t i)}

/-- Each `M_k` is infinite (this is where Tao–Ziegler, Theorem 1.5 is used). -/
lemma M_infinite (hpp : ∀ k : ℕ, PrimeProducing (fun i : Fin k => h i)) (k : ℕ) :
    (M h s t k).Infinite := by
  have hS := hpp (k + 1)
  rw [Set.infinite_iff_exists_gt]
  intro a
  -- choose `n` with all `n + h i` prime (`i ≤ k`) and `n` large
  obtain ⟨n, hn, hna⟩ := hS.exists_gt (a + t.natAbs + h 0 + 1)
  refine ⟨(n + h 0 - t).toNat, ⟨?_, ?_, ?_⟩, ?_⟩
  · omega
  · refine ⟨n + h 0, hn ⟨0, by omega⟩, ?_⟩
    push_cast
    omega
  · intro i hi
    refine ⟨n + h i, hn ⟨i, by omega⟩, ?_⟩
    unfold β
    push_cast
    omega
  · omega

/-- Choice of an element `c ∈ M_i` with `c > β_i`. -/
noncomputable def pickC
    (hpp : ∀ k : ℕ, PrimeProducing (fun i : Fin k => h i)) (i : ℕ) : ℕ :=
  ((M_infinite s t hpp i).exists_gt (β h s t i).toNat).choose

lemma pickC_spec (hpp : ∀ k : ℕ, PrimeProducing (fun i : Fin k => h i))
    (i : ℕ) : pickC s t hpp i ∈ M h s t i ∧ β h s t i < pickC s t hpp i := by
  have := ((M_infinite s t hpp i).exists_gt (β h s t i).toNat).choose_spec
  refine ⟨this.1, ?_⟩
  have h2 := this.2
  unfold pickC
  omega

/-- Choice of an index `i` with `β_i > c`. -/
noncomputable def nextI (hh : StrictMono h) (c : ℤ) : ℕ := (exists_β_gt s t hh c).choose

lemma nextI_spec (hh : StrictMono h) (c : ℤ) : c < β h s t (nextI s t hh c) :=
  (exists_β_gt s t hh c).choose_spec

/-- The indices `i_1 < i_2 < ⋯`: `i_1` with `β_{i_1} > 0`, and `i_{j+1}` with
`β_{i_{j+1}} > c_j`. -/
noncomputable def idx (hh : StrictMono h)
    (hpp : ∀ k : ℕ, PrimeProducing (fun i : Fin k => h i)) : ℕ → ℕ
  | 0 => nextI s t hh 0
  | j + 1 => nextI s t hh (pickC s t hpp (idx hh hpp j))

/-- The elements `c_j ∈ M_{i_j}` with `c_j > β_{i_j}`. -/
noncomputable def cseq (hh : StrictMono h)
    (hpp : ∀ k : ℕ, PrimeProducing (fun i : Fin k => h i)) (j : ℕ) : ℕ :=
  pickC s t hpp (idx s t hh hpp j)

variable (hh : StrictMono h) (hpp : ∀ k : ℕ, PrimeProducing (fun i : Fin k => h i))

lemma interlace (j : ℕ) :
    β h s t (idx s t hh hpp j) < cseq s t hh hpp j ∧
      (cseq s t hh hpp j : ℤ) < β h s t (idx s t hh hpp (j + 1)) :=
  ⟨(pickC_spec s t hpp _).2, nextI_spec s t hh _⟩

lemma β_idx_pos (j : ℕ) : 0 < β h s t (idx s t hh hpp j) := by
  cases j with
  | zero => exact nextI_spec s t hh 0
  | succ j =>
    have := (interlace s t hh hpp j).2
    omega

lemma β_idx_strictMono : StrictMono (fun j => β h s t (idx s t hh hpp j)) := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  have := interlace s t hh hpp j
  show β h s t (idx s t hh hpp j) < β h s t (idx s t hh hpp (j + 1))
  omega

lemma cseq_strictMono : StrictMono (cseq s t hh hpp) := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  have h1 := interlace s t hh hpp j
  have h2 := interlace s t hh hpp (j + 1)
  omega

end Proof

/-- Paper, Theorem \ref{IB:thm:c45}, **conditional on Tao–Ziegler, Theorem 1.5**
(`TaoZieglerThm15`). For all integers `s, t` there are infinite sets `B, C ⊆ {1, 2, …}` such that
`C + t ⊆ P` and `b + c + s ∈ P` for all `b ∈ B`, `c ∈ C` with `b < c`. -/
theorem c45_of_TZ (hTZ : TaoZieglerThm15) (s t : ℤ) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ (∀ c ∈ C, 0 < c) ∧
      (∀ c ∈ C, InP ((c : ℤ) + t)) ∧
      ∀ b ∈ B, ∀ c ∈ C, b < c → InP ((b : ℤ) + c + s) := by
  obtain ⟨h, hh, hpp⟩ := hTZ
  set bseq : ℕ → ℕ := fun j => (β h s t (idx s t hh hpp j)).toNat with hbseq
  have hbcast : ∀ j, (bseq j : ℤ) = β h s t (idx s t hh hpp j) := fun j => by
    have := β_idx_pos s t hh hpp j
    simp only [hbseq]
    omega
  have hbmono : StrictMono bseq := by
    intro i j hij
    have : β h s t (idx s t hh hpp i) < β h s t (idx s t hh hpp j) :=
      β_idx_strictMono s t hh hpp hij
    have h1 := hbcast i
    have h2 := hbcast j
    omega
  refine ⟨Set.range bseq, Set.range (cseq s t hh hpp),
    Set.infinite_range_of_injective hbmono.injective,
    Set.infinite_range_of_injective (cseq_strictMono s t hh hpp).injective, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨j, rfl⟩
    have := β_idx_pos s t hh hpp j
    have := hbcast j
    omega
  · rintro _ ⟨j, rfl⟩
    have := (interlace s t hh hpp j).1
    have := β_idx_pos s t hh hpp j
    omega
  · rintro _ ⟨j, rfl⟩
    exact (pickC_spec s t hpp _).1.2.1
  · rintro _ ⟨l, rfl⟩ _ ⟨j, rfl⟩ hlt
    -- the interlacing forces `l ≤ j`
    have hlj : l ≤ j := by
      by_contra hcon
      have h1 : β h s t (idx s t hh hpp (j + 1)) ≤ β h s t (idx s t hh hpp l) :=
        (β_idx_strictMono s t hh hpp).monotone (by omega)
      have h2 := (interlace s t hh hpp j).2
      have h3 := hbcast l
      have h4 : ((bseq l : ℕ) : ℤ) < (cseq s t hh hpp j : ℤ) := by exact_mod_cast hlt
      omega
    have hidx : idx s t hh hpp l ≤ idx s t hh hpp j :=
      (β_strictMono s t hh).le_iff_le.1 ((β_idx_strictMono s t hh hpp).monotone hlj)
    have hM := (pickC_spec s t hpp (idx s t hh hpp j)).1.2.2 _ hidx
    rw [hbcast l]
    have e : (β h s t (idx s t hh hpp l)) + (cseq s t hh hpp j : ℤ) + s =
        (pickC s t hpp (idx s t hh hpp j) : ℤ) + s + β h s t (idx s t hh hpp l) := by
      simp only [cseq]; ring
    rw [e]
    exact hM

/-- Paper, Theorem \ref{IB:thm:c45}, case `s = 0`, `t = 1`, **conditional on Tao–Ziegler,
Theorem 1.5**: Conjecture 4.5 of the survey holds. -/
theorem conjecture45_of_TZ (hTZ : TaoZieglerThm15) : Conjecture45 := by
  obtain ⟨B, C, hB, hC, hB0, hC0, hCt, hBC⟩ := c45_of_TZ hTZ 0 1
  refine ⟨B, C, hB, hC, hB0, hC0, fun c hc => ?_, ?_⟩
  · obtain ⟨p, hp, e⟩ := hCt c hc
    have : p = c + 1 := by omega
    simpa [this] using hp
  · rintro _ ⟨b, hb, c, hc, hbc, rfl⟩
    obtain ⟨p, hp, e⟩ := hBC b hb c hc hbc
    have : p = b + c := by omega
    simpa [this] using hp

/-- Paper, Theorem \ref{IB:thm:c45}, case `s = t = 1`, **conditional on Tao–Ziegler,
Theorem 1.5**: there are infinite sets `B, C ⊆ {1, 2, …}` with `C ⊆ P - 1` and
`{b + c : b ∈ B, c ∈ C, b < c} ⊆ P - 1`. -/
theorem c45_shifted_of_TZ (hTZ : TaoZieglerThm15) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ (∀ c ∈ C, 0 < c) ∧
      C ⊆ {n | (n + 1).Prime} ∧
      {x | ∃ b ∈ B, ∃ c ∈ C, b < c ∧ x = b + c} ⊆ {n | (n + 1).Prime} := by
  obtain ⟨B, C, hB, hC, hB0, hC0, hCt, hBC⟩ := c45_of_TZ hTZ 1 1
  refine ⟨B, C, hB, hC, hB0, hC0, fun c hc => ?_, ?_⟩
  · obtain ⟨p, hp, e⟩ := hCt c hc
    have : p = c + 1 := by omega
    simpa [this] using hp
  · rintro _ ⟨b, hb, c, hc, hbc, rfl⟩
    obtain ⟨p, hp, e⟩ := hBC b hb c hc hbc
    have : p = b + c + 1 := by omega
    simpa [this] using hp

end Kmrr25.C45
