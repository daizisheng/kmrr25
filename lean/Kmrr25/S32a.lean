import Kmrr25.Basic

/-!
# Unrestricted sums `B + B` at the lower density threshold (paper, Section \ref{IA:sec:u32a})

The survey asks whether `|A ∩ [N]| > 3N/4 + log N` for infinitely many `N` forces a set `A ⊆ ℕ`
to contain an unrestricted sumset `B + B = {b + b' : b, b' ∈ B}` with `B` infinite. The answer is
negative under both readings of the question.

## Main results

* `thm_u32a_a` — Theorem \ref{IA:thm:u32a}\ref{IA:it:u32a-io} (literal reading): there is
  `A ⊆ ℕ` such that for every `C > 0` we have `|A ∩ [N]| > 3N/4 + C log N` for infinitely many
  `N`, and `B + B ⊄ A` for every infinite `B`. It uses the explicit set of the proof,
  `S = ⋃_{n ≥ 1} [4^n, 2·4^n - 2n)` and `A = (2ℕ - 1) ∪ (S ∩ 2ℕ)` (`setS`, `setA`), with
  - `setS_no_sumset`: `S` contains no `D + D` with `D` infinite;
  - `setA_no_sumset`: `A` contains no `B + B` with `B` infinite;
  - `count_exact`: the exact count at `N_n = 2·4^n - 2n - 1`:
    `|A ∩ [N_n]| - (3/4) N_n = 4^n/6 - n^2/2 + 1/12`;
  - `count_infinitely_often`: for every real `C`, `|A ∩ [N]| > 3N/4 + C log N` for infinitely
    many `N`.
* `thm_u32a_b` — Theorem \ref{IA:thm:u32a}\ref{IA:it:u32a-all} ("for all sufficiently large
  `N`"): there are `A ⊆ ℕ` and a non-decreasing unbounded `ψ : ℕ → [0, ∞)` with
  `|A ∩ [N]| ≥ 3N/4 + ψ(N) log N` for all large `N`, and `B + B ⊄ A` for every infinite `B`.
  Its ingredients are formalized as
  - `parity_reduce`, `ncard_Aset` — Lemma \ref{IA:lem:parity};
  - `Rset`, `Gset`, `Eset` — Definition \ref{IA:def:rot}; `prop_rot` —
    Proposition \ref{IA:prop:rot};
  - `card_R`, `excess` — Lemma \ref{IA:lem:excess};
  - `interval_bound_q`, `S_pow_succ`, `S_pow`, `Sf_sub_le` — Lemma \ref{IA:lem:TD0};
    `TD1_bound`, `TD1_interval` — Lemma \ref{IA:lem:TD1}; `rr_eq_of_close` —
    Lemma \ref{IA:lem:TD2}; `TD3` — Lemma \ref{IA:lem:TD3}; `TD4_agree`, `TD4_lower`,
    `TD_step` — Lemma \ref{IA:lem:TD4};
  - `prop_TD` — Proposition \ref{IA:prop:TD} (including the irrationality of `α`).

## Conventions

* The paper's `ℕ` is `{1, 2, …}`; `[N] = {1, …, N}` is `Set.Icc 1 N`, and `|·|` is `Set.ncard`
  (or `Finset.card`). All sets `A` constructed here are subsets of Lean's `ℕ` not containing `0`.
* `B + B` is the unrestricted sumset `Kmrr25.sumset B B`. Non-containment is proved for all
  infinite `B ⊆ {0, 1, 2, …}`, which contains the paper's statement (about infinite
  `B ⊆ {1, 2, …}`) as a special case.
* `log` is the natural logarithm. In part (a) the excess statement is proved for every real `C`.
  In part (b) "unbounded" is `¬ BddAbove (Set.range ψ)` and "for all sufficiently large `N`" is
  `∀ᶠ N in atTop`.
* `ρ(x) = 𝟙_{[0,1/2)}({x}) - 1/2` is `rho`, `ε(n) = (-1)^{⌊log₂ n⌋}` is `eps` (with
  `⌊log₂ n⌋ = Nat.log 2 n`), `r_θ(n) = ρ(nθ - 1/6)` is `rr θ n`, and
  `S_{α,β}(M) = ∑_{1 ≤ n < M} ε(n) ρ(nα - β)` is `Sab α β M`.
* An element `θ = a/q`, `q = 3·2^p`, of the paper's set `𝒬` is represented by the pair `(p, a)`
  (`thq p a = a / (3·2^p)`) with `p ≥ 1`, `a` odd and `a < q`. The lemmas only use that `a` is
  odd, not the full condition `gcd(a, q) = 1`, so they hold on this slightly larger set.
* Lemma \ref{IA:lem:TD3} is proved for any `R ≥ 1` with `2^R ≡ 1 (mod 3b)` (the order of `2` is
  one such `R`); in the construction `R = φ(3b)` is used. In Proposition \ref{IA:prop:TD} the
  limit `α` is obtained as the supremum of nested approximations `θ_k ≤ α ≤ θ_k + w_k`, which
  gives `r_α = r_{θ_k}` on `[0, N_k)` directly from Lemma \ref{IA:lem:TD2}, instead of the
  continuity argument of the paper.
* Lemma \ref{IA:lem:excess} is formalized in the form used in the proof (`excess`): the gap
  term is bounded by `∑_{i=1}^{K} 2 w_i` for any `K` beyond which the gap intervals miss
  `[1, M)`.
-/

open Real Finset Filter Topology

namespace Kmrr25.S32a

/-! ## The sets `S` and `A` -/

/-- `S = ⋃_{n ≥ 1} [4^n, 2·4^n - 2n) ∩ ℤ`. -/
def setS : Set ℕ := {k | ∃ n, 1 ≤ n ∧ 4 ^ n ≤ k ∧ k < 2 * 4 ^ n - 2 * n}

/-- `A = (2ℕ - 1) ∪ (S ∩ 2ℕ)`: all odd numbers, together with the even elements of `S`. -/
def setA : Set ℕ := {k | Odd k} ∪ {k | k ∈ setS ∧ Even k}

lemma two_mul_add_one_le_four_pow (m : ℕ) : 2 * m + 1 ≤ 4 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ]; omega

lemma mem_setS_iff_of_lt_pow {k n : ℕ} (hk : k < 4 ^ (n + 1)) :
    k ∈ setS ↔ ∃ m, 1 ≤ m ∧ m ≤ n ∧ 4 ^ m ≤ k ∧ k < 2 * 4 ^ m - 2 * m := by
  constructor
  · rintro ⟨m, hm1, hm2, hm3⟩
    refine ⟨m, hm1, ?_, hm2, hm3⟩
    by_contra h
    have : 4 ^ (n + 1) ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rintro ⟨m, hm1, -, hm2, hm3⟩
    exact ⟨m, hm1, hm2, hm3⟩

lemma four_le_of_mem_setS {k : ℕ} (hk : k ∈ setS) : 4 ≤ k := by
  obtain ⟨n, hn, h1, -⟩ := hk
  have : 4 ^ 1 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- No element of `S` lies in `[2·4^m, 4^(m+1))`. -/
lemma not_mem_setS_gap {k m : ℕ} (h1 : 2 * 4 ^ m ≤ k) (h2 : k < 4 ^ (m + 1)) : k ∉ setS := by
  rintro ⟨j, -, hj1, hj2⟩
  rcases le_or_gt j m with h | h
  · have : 4 ^ j ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) h
    omega
  · have : 4 ^ (m + 1) ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) h
    omega

/-! ## No infinite sumsets -/

/-- Paper, proof of Theorem \ref{IA:thm:u32a}\ref{IA:it:u32a-io}: `S` contains no `D + D` with
`D` infinite. -/
theorem setS_no_sumset (D : Set ℕ) (hD : D.Infinite) : ¬ sumset D D ⊆ setS := by
  intro hsub
  obtain ⟨d', hd'⟩ := hD.nonempty
  obtain ⟨d, hd, hdbig⟩ := hD.exists_gt (4 ^ d')
  -- `2d ∈ S` lies in some block `[4^m, 2·4^m - 2m)`
  obtain ⟨m, hm1, hm2, hm3⟩ := hsub ⟨d, hd, d, hd, two_mul d⟩
  have hdm : d' < m := by
    by_contra h
    have : 4 ^ m ≤ 4 ^ d' := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hp : 4 ^ (j + 1) = 4 * 4 ^ j := by rw [pow_succ]; ring
  -- `d + d'` falls into the gap `[2·4^j, 4^(j+1))`
  refine not_mem_setS_gap (k := d + d') (m := j) ?_ ?_ (hsub ⟨d, hd, d', hd', rfl⟩)
  · omega
  · omega

/-- Paper, proof of Theorem \ref{IA:thm:u32a}\ref{IA:it:u32a-io}: `A` contains no `B + B` with
`B` infinite. -/
theorem setA_no_sumset (B : Set ℕ) (hB : B.Infinite) : ¬ sumset B B ⊆ setA := by
  intro hsub
  -- an infinite subset `B'` of constant parity
  have hsplit : B = {b ∈ B | Even b} ∪ {b ∈ B | Odd b} := by
    ext b
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hb
      rcases Nat.even_or_odd b with h | h
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, h⟩
    · rintro (⟨hb, -⟩ | ⟨hb, -⟩) <;> exact hb
  have key : ∀ B' ⊆ B, B'.Infinite → (∀ b ∈ B', ∀ b' ∈ B', Even (b + b')) → False := by
    intro B' hB'B hB' hpar
    refine setS_no_sumset B' hB' ?_
    rintro _ ⟨b, hb, b', hb', rfl⟩
    rcases hsub ⟨b, hB'B hb, b', hB'B hb', rfl⟩ with h | h
    · exact absurd (hpar b hb b' hb') (Nat.not_even_iff_odd.mpr h)
    · exact h.1
  rw [hsplit, Set.infinite_union] at hB
  rcases hB with h | h
  · exact key _ (fun b hb => hb.1) h fun b hb b' hb' => hb.2.add hb'.2
  · exact key _ (fun b hb => hb.1) h fun b hb b' hb' => hb.2.add_odd hb'.2

/-! ## Counting -/

/-- Indicator of the odd numbers. -/
def indO (k : ℕ) : ℕ := if Odd k then 1 else 0

/-- Indicator of the even numbers. -/
def indE (k : ℕ) : ℕ := if Even k then 1 else 0

open Classical in
/-- Indicator of the even elements of `S`. -/
noncomputable def indES (k : ℕ) : ℕ := if k ∈ setS ∧ Even k then 1 else 0

lemma sum_indO (L : ℕ) : ∑ k ∈ range (2 * L), indO k = L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show 2 * (L + 1) = 2 * L + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    have h1 : ¬ Odd (2 * L) := by rw [Nat.not_odd_iff_even]; exact even_two_mul L
    have h2 : Odd (2 * L + 1) := odd_two_mul_add_one L
    simp [indO, h1, h2]

lemma sum_indE_Ico (a L : ℕ) (ha : Even a) : ∑ k ∈ Ico a (a + 2 * L), indE k = L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show a + 2 * (L + 1) = a + 2 * L + 1 + 1 by ring, sum_Ico_succ_top (by omega),
      sum_Ico_succ_top (by omega), ih]
    have h1 : Even (a + 2 * L) := ha.add (even_two_mul L)
    have h2 : ¬ Even (a + 2 * L + 1) := by
      rw [Nat.not_even_iff_odd]; exact h1.add_one
    simp [indE, h1, h2]

/-- The right end `e(n) = 2·4^n - 2n` of the `n`-th block, so that `N_n = e(n) - 1`. -/
def blockEnd (n : ℕ) : ℕ := 2 * 4 ^ n - 2 * n

lemma blockEnd_mono {m n : ℕ} (h : m ≤ n) : blockEnd m ≤ blockEnd n := by
  refine monotone_nat_of_le_succ (fun k => ?_) h
  have := two_mul_add_one_le_four_pow k
  have : 4 ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
  unfold blockEnd
  omega

/-- The number `E(n)` of even elements of `S` below `e(n)` satisfies
`6 E(n) + 3 n (n + 1) + 4 = 4^(n+1)`, i.e. `E(n) = ∑_{m=1}^{n} (4^m/2 - m)`. -/
lemma sum_indES (n : ℕ) : 6 * ∑ k ∈ range (blockEnd n), indES k + 3 * n * (n + 1) + 4 =
    4 ^ (n + 1) := by
  induction n with
  | zero =>
    have : ∑ k ∈ range (blockEnd 0), indES k = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      simp only [blockEnd, pow_zero, mul_one, mul_zero, Nat.sub_zero, mem_range] at hk
      have : k ∉ setS := fun h => by have := four_le_of_mem_setS h; omega
      simp [indES, this]
    rw [this]; norm_num
  | succ n ih =>
    have h4 := two_mul_add_one_le_four_pow n
    have h4' := two_mul_add_one_le_four_pow (n + 1)
    have hp : 4 ^ (n + 1) = 4 * 4 ^ n := by rw [pow_succ]; ring
    have he : blockEnd n ≤ 4 ^ (n + 1) := by unfold blockEnd; omega
    have he' : 4 ^ (n + 1) ≤ blockEnd (n + 1) := by unfold blockEnd; omega
    rw [← sum_range_add_sum_Ico _ (he.trans he'), ← sum_Ico_consecutive _ he he']
    -- the gap `[e(n), 4^(n+1))` contains no element of `S`
    have hgap : ∑ k ∈ Ico (blockEnd n) (4 ^ (n + 1)), indES k = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [mem_Ico] at hk
      have hk' : k ∉ setS := by
        rw [mem_setS_iff_of_lt_pow hk.2]
        rintro ⟨m, -, hmn, hm1, hm2⟩
        have hmono : blockEnd m ≤ blockEnd n := blockEnd_mono hmn
        have hbm : blockEnd m = 2 * 4 ^ m - 2 * m := rfl
        omega
      simp [indES, hk']
    -- the block `[4^(n+1), e(n+1))` consists of elements of `S`
    have hblock : ∑ k ∈ Ico (4 ^ (n + 1)) (blockEnd (n + 1)), indES k = 2 * 4 ^ n - (n + 1) := by
      have hE : ∑ k ∈ Ico (4 ^ (n + 1)) (blockEnd (n + 1)), indES k =
          ∑ k ∈ Ico (4 ^ (n + 1)) (4 ^ (n + 1) + 2 * (2 * 4 ^ n - (n + 1))), indE k := by
        have : blockEnd (n + 1) = 4 ^ (n + 1) + 2 * (2 * 4 ^ n - (n + 1)) := by
          unfold blockEnd; omega
        rw [this]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [mem_Ico] at hk
        have hkS : k ∈ setS := ⟨n + 1, by omega, hk.1, by unfold blockEnd at this; omega⟩
        simp [indES, indE, hkS]
      rw [hE, sum_indE_Ico _ _ (by rw [hp]; exact ⟨2 * 4 ^ n, by ring⟩)]
    rw [hgap, hblock]
    have : n + 1 ≤ 2 * 4 ^ n := by omega
    zify [this] at ih ⊢
    linear_combination ih

open Classical in
/-- `|A ∩ [N]|` as a sum of indicators over `{0, …, N}`. -/
lemma ncard_eq_sum (N : ℕ) :
    (setA ∩ Set.Icc 1 N).ncard = ∑ k ∈ range (N + 1), (indO k + indES k) := by
  have hset : setA ∩ Set.Icc 1 N = ↑((range (N + 1)).filter (· ∈ setA)) := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_Icc, coe_filter, mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hk, -, hkN⟩
      exact ⟨by omega, hk⟩
    · rintro ⟨hkN, hk⟩
      refine ⟨hk, ?_, by omega⟩
      rcases hk with h | h
      · obtain ⟨r, rfl⟩ := h; omega
      · have := four_le_of_mem_setS h.1; omega
  rw [hset, Set.ncard_coe_finset, card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.even_or_odd k with h | h
  · have h' : ¬ Odd k := Nat.not_odd_iff_even.mpr h
    by_cases hS : k ∈ setS
    · have : k ∈ setA := Or.inr ⟨hS, h⟩
      simp [indO, indES, h, h', hS, this]
    · have : k ∉ setA := by
        rintro (h1 | h1)
        · exact h' h1
        · exact hS h1.1
      simp [indO, indES, h', hS, this]
  · have h' : ¬ Even k := Nat.not_even_iff_odd.mpr h
    have : k ∈ setA := Or.inl h
    simp [indO, indES, h, h', this]

/-- Paper, proof of Theorem \ref{IA:thm:u32a}\ref{IA:it:u32a-io} (counting): for
`N_n = 2·4^n - 2n - 1` we have `|A ∩ [N_n]| - (3/4) N_n = 4^n/6 - n^2/2 + 1/12`. -/
theorem count_exact (n : ℕ) :
    ((setA ∩ Set.Icc 1 (2 * 4 ^ n - 2 * n - 1)).ncard : ℝ) -
      3 / 4 * ((2 * 4 ^ n - 2 * n - 1 : ℕ) : ℝ) = 4 ^ n / 6 - n ^ 2 / 2 + 1 / 12 := by
  have h4 := two_mul_add_one_le_four_pow n
  have hp : 4 ^ (n + 1) = 4 * 4 ^ n := by rw [pow_succ]; ring
  have hN : 2 * 4 ^ n - 2 * n - 1 + 1 = blockEnd n := by unfold blockEnd; omega
  rw [ncard_eq_sum, hN, sum_add_distrib]
  have hO : ∑ k ∈ range (blockEnd n), indO k = 4 ^ n - n := by
    rw [show blockEnd n = 2 * (4 ^ n - n) by unfold blockEnd; omega, sum_indO]
  have hE := sum_indES n
  rw [hO]
  set E := ∑ k ∈ range (blockEnd n), indES k
  rw [hp] at hE
  have hE' : (6 : ℝ) * E + 3 * n * (n + 1) + 4 = 4 * 4 ^ n := by exact_mod_cast hE
  have hn1 : n ≤ 4 ^ n := by omega
  have hn2 : 2 * n + 1 ≤ 2 * 4 ^ n := by omega
  have hc : ((2 * 4 ^ n - 2 * n - 1 : ℕ) : ℝ) = 2 * 4 ^ n - 2 * n - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hc]
  push_cast [Nat.cast_sub hn1]
  linear_combination hE' / 6

/-- Paper, proof of Theorem \ref{IA:thm:u32a}\ref{IA:it:u32a-io} (excess): for every real `C`,
`|A ∩ [N]| > 3N/4 + C log N` for infinitely many `N`. -/
theorem count_infinitely_often (C : ℝ) :
    {N : ℕ | 3 / 4 * (N : ℝ) + C * Real.log N < (setA ∩ Set.Icc 1 N).ncard}.Infinite := by
  set g : ℕ → ℝ := fun n => 1 / 6 - ((n : ℝ) ^ 2 / 4 ^ n) / 2 - 3 * |C| * ((n : ℝ) ^ 1 / 4 ^ n)
    - 3 * |C| * ((n : ℝ) ^ 0 / 4 ^ n)
  have hg : Tendsto g atTop (𝓝 (1 / 6 - 0 / 2 - 3 * |C| * 0 - 3 * |C| * 0)) := by
    have h := fun k => tendsto_pow_const_div_const_pow_of_one_lt k (r := 4) (by norm_num)
    exact ((tendsto_const_nhds.sub ((h 2).div_const 2)).sub
      ((h 1).const_mul _)).sub ((h 0).const_mul _)
  have hev : ∀ᶠ n in atTop, 0 < g n := hg.eventually_const_lt (by norm_num)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  rw [← Nat.frequently_atTop_iff_infinite, frequently_atTop]
  intro a
  set n := max n₀ (a + 1)
  have hgn := hn₀ n (le_max_left _ _)
  have h4 := two_mul_add_one_le_four_pow n
  refine ⟨2 * 4 ^ n - 2 * n - 1, by omega, ?_⟩
  show _ < _
  have hex := count_exact n
  set N := 2 * 4 ^ n - 2 * n - 1
  have hN1 : 1 ≤ N := by omega
  have hNle : N ≤ 4 ^ (n + 1) := by rw [pow_succ]; omega
  -- `log N ≤ 3 (n + 1)`
  have hlog : Real.log N ≤ 3 * (n + 1) := by
    have h1 : Real.log N ≤ Real.log ((4 : ℝ) ^ (n + 1)) :=
      Real.log_le_log (by exact_mod_cast hN1) (by exact_mod_cast hNle)
    rw [Real.log_pow] at h1
    have h2 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)]
    push_cast at h1
    nlinarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hClog : C * Real.log N ≤ |C| * (3 * (n + 1)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0).trans
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg C))
  -- `4^n g(n) > 0` is the required inequality
  have hpos : (0 : ℝ) < 4 ^ n := by positivity
  have hmain : 3 * |C| * (n + 1) < 4 ^ n / 6 - n ^ 2 / 2 := by
    have : 0 < 4 ^ n * g n := mul_pos hpos hgn
    simp only [g, pow_one, pow_zero] at this
    field_simp at this
    nlinarith [this]
  nlinarith [hex, hClog, hmain]

/-! ## Part (a) -/

/-- Paper, Theorem \ref{IA:thm:u32a}\ref{IA:it:u32a-io}: there is a set `A ⊆ ℕ` such that for
every `C > 0` we have `|A ∩ [N]| > (3/4) N + C log N` for infinitely many `N`, and such that
`B + B ⊄ A` for every infinite `B ⊆ ℕ`. -/
theorem thm_u32a_a : ∃ A : Set ℕ, 0 ∉ A ∧
    (∀ C : ℝ, 0 < C →
      {N : ℕ | 3 / 4 * (N : ℝ) + C * Real.log N < (A ∩ Set.Icc 1 N).ncard}.Infinite) ∧
    ∀ B : Set ℕ, B.Infinite → ¬ sumset B B ⊆ A := by
  refine ⟨setA, ?_, fun C _ => count_infinitely_often C, setA_no_sumset⟩
  rintro (h | h)
  · exact Nat.not_odd_zero h
  · have := four_le_of_mem_setS h.1; omega

/-! ## Part (b) -/

/-! ## The function `ρ` and twisted sums -/

/-- `ρ(x) = 𝟙_{[0,1/2)}({x}) - 1/2`. -/
noncomputable def rho (x : ℝ) : ℝ := if Int.fract x < 1 / 2 then 1 / 2 else -1 / 2

lemma rho_eq_floor (x : ℝ) : rho x = if Even ⌊2 * x⌋ then 1 / 2 else -1 / 2 := by
  have h1 : ⌊2 * x⌋ = 2 * ⌊x⌋ + ⌊2 * Int.fract x⌋ := by
    conv_lhs => rw [← Int.floor_add_fract x]
    rw [mul_add, show (2 : ℝ) * ⌊x⌋ = ((2 * ⌊x⌋ : ℤ) : ℝ) by push_cast; ring,
      Int.floor_intCast_add]
  have hf0 := Int.fract_nonneg x
  have hf1 := Int.fract_lt_one x
  unfold rho
  by_cases h : Int.fract x < 1 / 2
  · have : ⌊2 * Int.fract x⌋ = 0 := by
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [if_pos h, if_pos]
    rw [h1, this, add_zero]; exact even_two_mul _
  · have : ⌊2 * Int.fract x⌋ = 1 := by
      replace h := not_lt.mp h
      rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
    rw [if_neg h, if_neg]
    rw [h1, this, Int.not_even_iff_odd]; exact odd_two_mul_add_one _

lemma rho_add_half (x : ℝ) : rho (x + 1 / 2) = - rho x := by
  rw [rho_eq_floor, rho_eq_floor, show 2 * (x + 1 / 2) = 2 * x + 1 by ring, Int.floor_add_one]
  by_cases h : Even ⌊2 * x⌋
  · have : ¬ Even (⌊2 * x⌋ + 1) := by rw [Int.not_even_iff_odd]; exact h.add_one
    rw [if_pos h, if_neg this]; norm_num
  · have : Even (⌊2 * x⌋ + 1) := (Int.not_even_iff_odd.mp h).add_one
    rw [if_neg h, if_pos this]; norm_num

lemma rho_add_int (x : ℝ) (m : ℤ) : rho (x + m) = rho x := by
  unfold rho; rw [Int.fract_add_intCast]

lemma abs_rho_le (x : ℝ) : |rho x| ≤ 1 / 2 := by
  unfold rho; split_ifs <;> norm_num [abs_of_pos]

lemma rho_mem (x : ℝ) : rho x = 1 / 2 ∨ rho x = -1 / 2 := by
  unfold rho; split_ifs <;> simp

/-- If `x ≤ y` then `|ρ(x) - ρ(y)| ≤ ⌊2y⌋ - ⌊2x⌋`. -/
lemma abs_rho_sub_le {x y : ℝ} (hxy : x ≤ y) :
    |rho x - rho y| ≤ ((⌊2 * y⌋ - ⌊2 * x⌋ : ℤ) : ℝ) := by
  have hmono : ⌊2 * x⌋ ≤ ⌊2 * y⌋ := Int.floor_le_floor (by linarith)
  rcases eq_or_lt_of_le hmono with h | h
  · rw [rho_eq_floor, rho_eq_floor, h]; simp
  · have h1 : (1 : ℝ) ≤ ((⌊2 * y⌋ - ⌊2 * x⌋ : ℤ) : ℝ) := by
      have : 1 ≤ ⌊2 * y⌋ - ⌊2 * x⌋ := by omega
      exact_mod_cast this
    have := abs_sub (rho x) (rho y)
    have := abs_rho_le x
    have := abs_rho_le y
    linarith

/-- `ε(n) = (-1)^{⌊log₂ n⌋}`. -/
noncomputable def eps (n : ℕ) : ℝ := (-1) ^ Nat.log 2 n

/-- `r_θ(n) = ρ(nθ - 1/6)`. -/
noncomputable def rr (θ : ℝ) (n : ℕ) : ℝ := rho (n * θ - 1 / 6)

/-- The twisted sum `∑_{1 ≤ n < M} ε(n) f(n)`. -/
noncomputable def Sf (f : ℕ → ℝ) (M : ℕ) : ℝ := ∑ n ∈ Ico 1 M, eps n * f n

/-- `S_{α,β}(M) = ∑_{1 ≤ n < M} ε(n) ρ(nα - β)`. -/
noncomputable def Sab (α β : ℝ) (M : ℕ) : ℝ := Sf (fun n => rho (n * α - β)) M

lemma eps_of_mem {n j : ℕ} (h1 : 2 ^ j ≤ n) (h2 : n < 2 ^ (j + 1)) : eps n = (-1) ^ j := by
  unfold eps; rw [Nat.log_eq_of_pow_le_of_lt_pow h1 h2]

lemma Sf_dyadic (f : ℕ → ℝ) {j M : ℕ} (h1 : 2 ^ j ≤ M) (h2 : M ≤ 2 ^ (j + 1)) :
    Sf f M = Sf f (2 ^ j) + (-1) ^ j * ∑ n ∈ Ico (2 ^ j) M, f n := by
  unfold Sf
  rw [← sum_Ico_consecutive _ (Nat.one_le_two_pow) h1, mul_sum]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [mem_Ico] at hn
  rw [eps_of_mem hn.1 (by omega)]

lemma abs_sum_le_half (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1 / 2) (u v : ℕ) :
    |∑ n ∈ Ico u v, f n| ≤ (v - u : ℕ) / 2 := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun n _ => hf n).trans ?_
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
  ring_nf; rfl

/-- Block lemma: if every interval sum of `f` is bounded by `B`, then
`|S(M) - S(2^j)| ≤ (k - j) B` for `2^j ≤ M ≤ 2^k`. -/
lemma Sf_sub_le (f : ℕ → ℝ) {B : ℝ} (hB : ∀ u v, |∑ n ∈ Ico u v, f n| ≤ B) {j k M : ℕ}
    (hjk : j ≤ k) (h1 : 2 ^ j ≤ M) (h2 : M ≤ 2 ^ k) :
    |Sf f M - Sf f (2 ^ j)| ≤ (k - j : ℕ) * B := by
  have hB0 : 0 ≤ B := by simpa using hB 0 0
  induction k, hjk using Nat.le_induction generalizing M with
  | base => have : M = 2 ^ j := le_antisymm h2 h1
            subst this; simp
  | succ k hjk ih =>
    rcases le_or_gt M (2 ^ k) with h | h
    · refine (ih h1 h).trans ?_
      gcongr; omega
    · rw [Sf_dyadic f h.le h2]
      have h3 : |(-1 : ℝ) ^ k * ∑ n ∈ Ico (2 ^ k) M, f n| ≤ B := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hB _ _
      have hk' := ih (M := 2 ^ k) (Nat.pow_le_pow_right (by norm_num) hjk) le_rfl
      calc |Sf f (2 ^ k) + (-1) ^ k * ∑ n ∈ Ico (2 ^ k) M, f n - Sf f (2 ^ j)|
          ≤ |Sf f (2 ^ k) - Sf f (2 ^ j)| + |(-1 : ℝ) ^ k * ∑ n ∈ Ico (2 ^ k) M, f n| := by
            rw [show Sf f (2 ^ k) + (-1) ^ k * ∑ n ∈ Ico (2 ^ k) M, f n - Sf f (2 ^ j) =
              (Sf f (2 ^ k) - Sf f (2 ^ j)) + (-1) ^ k * ∑ n ∈ Ico (2 ^ k) M, f n by ring]
            exact abs_add_le _ _
        _ ≤ (k - j : ℕ) * B + B := add_le_add hk' h3
        _ = (k + 1 - j : ℕ) * B := by
            rw [show k + 1 - j = (k - j) + 1 by omega]; push_cast; ring

/-- Growth lemma: from a linear dyadic growth `S(2^j) = S(2^{j₁}) + (j - j₁) G` with gain
`G ≥ c log 2` and a large enough starting value, `S(M) ≥ c log M` for all `M ≥ 2^{j₁}`. -/
lemma Sf_growth (f : ℕ → ℝ) {B G c : ℝ} (hB : ∀ u v, |∑ n ∈ Ico u v, f n| ≤ B) (j₁ : ℕ)
    (hdy : ∀ j, j₁ ≤ j → Sf f (2 ^ j) = Sf f (2 ^ j₁) + (j - j₁ : ℕ) * G)
    (hc : 0 ≤ c) (hG : c * Real.log 2 ≤ G)
    (hS : c * (j₁ + 1) * Real.log 2 + B ≤ Sf f (2 ^ j₁)) :
    ∀ M : ℕ, 2 ^ j₁ ≤ M → c * Real.log M ≤ Sf f M := by
  intro M hM
  have hM0 : M ≠ 0 := by have := Nat.one_le_two_pow (n := j₁); omega
  set j := Nat.log 2 M
  have hj1 : 2 ^ j ≤ M := Nat.pow_log_le_self 2 hM0
  have hj2 : M < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
  have hjj : j₁ ≤ j := by
    by_contra h
    have : 2 ^ (j + 1) ≤ 2 ^ j₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hblock := Sf_sub_le f hB (Nat.le_succ j) hj1 hj2.le
  rw [show j + 1 - j = 1 by omega] at hblock
  have h1 : Sf f (2 ^ j) - B ≤ Sf f M := by
    have := neg_abs_le (Sf f M - Sf f (2 ^ j)); push_cast at hblock; linarith
  have h2 := hdy j hjj
  have hlog : Real.log M ≤ (j + 1) * Real.log 2 := by
    have : Real.log M ≤ Real.log ((2 : ℝ) ^ (j + 1)) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hj2.le)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hjj' : ((j - j₁ : ℕ) : ℝ) = j - j₁ := by push_cast [hjj]; ring
  rw [hjj'] at h2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : c * ((j : ℝ) - j₁) * Real.log 2 ≤ ((j : ℝ) - j₁) * G := by
    have : (0 : ℝ) ≤ (j : ℝ) - j₁ := by
      have : (j₁ : ℝ) ≤ j := by exact_mod_cast hjj
      linarith
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hlog hc]


/-! ## Periodicity -/

lemma sum_Ico_anti (f : ℕ → ℝ) (H : ℕ) (hf : ∀ n, f (n + H) = - f n) (u : ℕ) :
    ∑ n ∈ Ico u (u + 2 * H), f n = 0 := by
  rw [← sum_Ico_consecutive _ (Nat.le_add_right u H) (by omega : u + H ≤ u + 2 * H),
    show u + 2 * H = u + H + H by ring, ← sum_Ico_add' f u (u + H) H]
  simp only [hf, sum_neg_distrib, add_neg_cancel]

lemma sum_Ico_period_mul (f : ℕ → ℝ) (P : ℕ) (h0 : ∀ u, ∑ n ∈ Ico u (u + P), f n = 0)
    (u k : ℕ) : ∑ n ∈ Ico u (u + P * k), f n = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← sum_Ico_consecutive _ (Nat.le_add_right u (P * k)) (by nlinarith : u + P * k ≤ u + P * (k + 1)),
      ih, zero_add, show u + P * (k + 1) = u + P * k + P by ring, h0]

lemma sum_Ico_reduce (f : ℕ → ℝ) (P : ℕ) (h0 : ∀ u, ∑ n ∈ Ico u (u + P), f n = 0)
    {u v : ℕ} (huv : u ≤ v) :
    ∑ n ∈ Ico u v, f n = ∑ n ∈ Ico (u + P * ((v - u) / P)) v, f n := by
  have h1 : u + P * ((v - u) / P) ≤ v := by
    have := Nat.mul_div_le (v - u) P; omega
  rw [← sum_Ico_consecutive _ (Nat.le_add_right u _) h1, sum_Ico_period_mul f P h0, zero_add]

/-- If `f` has zero sums over all periods of length `P > 0` and interval sums of length `< P`
satisfy `|∑| ≤ len β + γ`, then all interval sums are bounded by `P β + γ`. -/
lemma interval_bound_of_period (f : ℕ → ℝ) (P : ℕ) (hP : 0 < P)
    (h0 : ∀ u, ∑ n ∈ Ico u (u + P), f n = 0) {β γ : ℝ} (hβ : 0 ≤ β)
    (hloc : ∀ u len, len < P → |∑ n ∈ Ico u (u + len), f n| ≤ len * β + γ) :
    ∀ u v, |∑ n ∈ Ico u v, f n| ≤ P * β + γ := by
  intro u v
  have hγ : 0 ≤ γ := by simpa using hloc u 0 hP
  rcases le_or_gt u v with huv | huv
  · rw [sum_Ico_reduce f P h0 huv]
    set u' := u + P * ((v - u) / P)
    have h1 : u' ≤ v := by
      have := Nat.mul_div_le (v - u) P; omega
    have h2 : v - u' < P := by
      have := Nat.div_add_mod (v - u) P
      have := Nat.mod_lt (v - u) hP
      omega
    have := hloc u' (v - u') h2
    rw [show u' + (v - u') = v by omega] at this
    refine this.trans ?_
    have : ((v - u' : ℕ) : ℝ) ≤ P := by exact_mod_cast h2.le
    nlinarith
  · rw [Ico_eq_empty (by omega), sum_empty, abs_zero]
    positivity

/-! ## The rationals `a / (3 · 2^p)` -/

/-- `θ = a / q` with `q = 3 · 2^p`. -/
noncomputable def thq (p a : ℕ) : ℝ := a / (3 * 2 ^ p)

/-- `Δ(θ) = ∑_{2^p ≤ n < 2^{p+1}} r_θ(n)`. -/
noncomputable def Delta (p a : ℕ) : ℝ := ∑ n ∈ Ico (2 ^ p) (2 ^ (p + 1)), rr (thq p a) n

/-- `G(θ) = (-1)^p Δ(θ)`. -/
noncomputable def Gain (p a : ℕ) : ℝ := (-1) ^ p * Delta p a

/-- Antiperiodicity: `r_θ(n + q/2) = -r_θ(n)` for `θ = a/q`, `a` odd. -/
lemma rr_anti {p a : ℕ} (hp : 1 ≤ p) (ha : Odd a) (n : ℕ) :
    rr (thq p a) (n + 3 * 2 ^ (p - 1)) = - rr (thq p a) n := by
  obtain ⟨j, rfl⟩ := ha
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  unfold rr thq
  have : ((n + 3 * 2 ^ (p' + 1 - 1) : ℕ) : ℝ) * ((2 * j + 1 : ℕ) / (3 * 2 ^ (p' + 1))) - 1 / 6
      = (n * ((2 * j + 1 : ℕ) / (3 * 2 ^ (p' + 1))) - 1 / 6 + 1 / 2) + ((j : ℤ) : ℝ) := by
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  rw [this, rho_add_int, rho_add_half]

lemma sum_Ico_q {p a : ℕ} (hp : 1 ≤ p) (ha : Odd a) (u : ℕ) :
    ∑ n ∈ Ico u (u + 3 * 2 ^ p), rr (thq p a) n = 0 := by
  have : 3 * 2 ^ p = 2 * (3 * 2 ^ (p - 1)) := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    simp [pow_succ]; ring
  rw [this]
  exact sum_Ico_anti _ _ (rr_anti hp ha) u

/-- Paper, Lemma \ref{IA:lem:TD0}(i): every interval sum of `r_θ` is at most `q/2` in absolute
value. -/
lemma interval_bound_q {p a : ℕ} (hp : 1 ≤ p) (ha : Odd a) (u v : ℕ) :
    |∑ n ∈ Ico u v, rr (thq p a) n| ≤ (3 * 2 ^ p : ℕ) / 2 := by
  have h := interval_bound_of_period (rr (thq p a)) (3 * 2 ^ p) (by positivity)
    (sum_Ico_q hp ha) (β := 1 / 2) (γ := 0) (by norm_num) (fun u len _ => by
      have := abs_sum_le_half (rr (thq p a)) (fun n => abs_rho_le _) u (u + len)
      rw [show u + len - u = len by omega] at this
      linarith) u v
  linarith

lemma sum_Ico_q_mul {p a : ℕ} (hp : 1 ≤ p) (ha : Odd a) (u k : ℕ) :
    ∑ n ∈ Ico u (u + 3 * 2 ^ p * k), rr (thq p a) n = 0 :=
  sum_Ico_period_mul _ _ (sum_Ico_q hp ha) u k

lemma four_pow_mod (s : ℕ) : ∃ k, 4 ^ s = 3 * k + 1 := by
  refine ⟨4 ^ s / 3, ?_⟩
  have h1 : 4 ^ s % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have := Nat.div_add_mod (4 ^ s) 3
  omega

lemma Ico_pow_sum_eq {p a : ℕ} (hp : 1 ≤ p) (ha : Odd a) (s : ℕ) :
    ∑ n ∈ Ico (2 ^ (p + 2 * s)) (2 ^ (p + 2 * s + 1)), rr (thq p a) n = Delta p a ∧
    ∑ n ∈ Ico (2 ^ (p + 2 * s + 1)) (2 ^ (p + 2 * s + 2)), rr (thq p a) n = - Delta p a := by
  obtain ⟨k, hk⟩ := four_pow_mod s
  have e1 : 2 ^ (p + 2 * s) = 2 ^ p + 3 * 2 ^ p * k := by
    rw [pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, hk]; ring
  have e2 : 2 ^ (p + 2 * s + 1) = 2 ^ (p + 1) + 3 * 2 ^ p * (2 * k) := by
    rw [pow_succ, e1, pow_succ]; ring
  have e3 : 2 ^ (p + 2 * s + 2) = 2 ^ p + 3 * 2 ^ p * (4 * k + 1) := by
    rw [show p + 2 * s + 2 = p + 2 * (s + 1) by ring, pow_add, pow_mul,
      show (2 : ℕ) ^ 2 = 4 by norm_num, pow_succ, hk]; ring
  -- `D(N) = ∑_{n < N} r(n)` is `q`-periodic
  have hD : ∀ N k, ∑ n ∈ range (N + 3 * 2 ^ p * k), rr (thq p a) n =
      ∑ n ∈ range N, rr (thq p a) n := by
    intro N k
    rw [← sum_range_add_sum_Ico _ (Nat.le_add_right N _), sum_Ico_q_mul hp ha, add_zero]
  have hpp : 2 ^ p ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hDelta : Delta p a = ∑ n ∈ range (2 ^ (p + 1)), rr (thq p a) n -
      ∑ n ∈ range (2 ^ p), rr (thq p a) n := by
    rw [Delta, ← sum_range_add_sum_Ico _ hpp]; ring
  have h12 : 2 ^ (p + 2 * s) ≤ 2 ^ (p + 2 * s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h23 : 2 ^ (p + 2 * s + 1) ≤ 2 ^ (p + 2 * s + 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  constructor
  · rw [sum_Ico_eq_sub _ h12, e1, e2, hD, hD, hDelta]
  · rw [sum_Ico_eq_sub _ h23, e2, e3, hD, hD, hDelta]; ring

/-- Paper, Lemma \ref{IA:lem:TD0}(ii),(iii): for `j ≥ p`, `S_θ(2^{j+1}) = S_θ(2^j) + G(θ)`. -/
lemma S_pow_succ {p a : ℕ} (hp : 1 ≤ p) (ha : Odd a) {j : ℕ} (hj : p ≤ j) :
    Sf (rr (thq p a)) (2 ^ (j + 1)) = Sf (rr (thq p a)) (2 ^ j) + Gain p a := by
  rw [Sf_dyadic _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)) le_rfl]
  congr 1
  obtain ⟨i, rfl⟩ : ∃ i, j = p + i := ⟨j - p, by omega⟩
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [(Ico_pow_sum_eq hp ha s).1, Gain, pow_add, pow_mul]; simp
  · rw [show p + (2 * s + 1) = p + 2 * s + 1 by ring, Nat.succ_eq_add_one,
      show p + 2 * s + 1 + 1 = p + 2 * s + 2 by ring,
      (Ico_pow_sum_eq hp ha s).2, Gain]
    have : ((-1 : ℝ)) ^ (p + 2 * s + 1) = - (-1) ^ p := by
      rw [pow_succ, pow_add, pow_mul]; simp
    rw [this]; ring

lemma S_pow {p a : ℕ} (hp : 1 ≤ p) (ha : Odd a) {j : ℕ} (hj : p ≤ j) :
    Sf (rr (thq p a)) (2 ^ j) = Sf (rr (thq p a)) (2 ^ p) + (j - p : ℕ) * Gain p a := by
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [S_pow_succ hp ha hj, ih, show j + 1 - p = (j - p) + 1 by omega]; push_cast; ring

/-! ## Lemma \ref{IA:lem:TD2} -/

lemma floor_div_add_small (K : ℤ) {Q : ℕ} (hQ : 0 < Q) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 1 / Q) : ⌊(K : ℝ) / Q + δ⌋ = ⌊(K : ℝ) / Q⌋ := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  set m := ⌊(K : ℝ) / Q⌋
  rw [Int.floor_eq_iff]
  refine ⟨by linarith [Int.floor_le ((K : ℝ) / Q)], ?_⟩
  have h1 : (K : ℝ) / Q < m + 1 := Int.lt_floor_add_one _
  have h2 : (K : ℝ) < (m + 1) * Q := by rwa [div_lt_iff₀ hQ'] at h1
  have h3 : K + 1 ≤ (m + 1) * (Q : ℤ) := by
    have : K < (m + 1) * (Q : ℤ) := by exact_mod_cast h2
    omega
  have h4 : (K : ℝ) + 1 ≤ (m + 1) * Q := by exact_mod_cast h3
  have h5 : (K : ℝ) / Q + 1 / Q ≤ m + 1 := by
    rw [← add_div, div_le_iff₀ hQ']; exact h4
  linarith

/-- Paper, Lemma \ref{IA:lem:TD2}: if `θ = a/q`, `θ' ≥ θ` and `n (θ' - θ) < 1/q`, then
`r_{θ'}(n) = r_θ(n)`. -/
lemma rr_eq_of_close {p a : ℕ} (hp : 1 ≤ p) {θ' : ℝ} (h0 : thq p a ≤ θ') (n : ℕ)
    (hn : n * (θ' - thq p a) < 1 / (3 * 2 ^ p : ℕ)) : rr θ' n = rr (thq p a) n := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  unfold rr
  rw [rho_eq_floor, rho_eq_floor]
  set K : ℤ := n * a - 2 ^ p'
  have hz : 2 * ((n : ℝ) * thq (p' + 1) a - 1 / 6) = (K : ℝ) / (3 * 2 ^ p' : ℕ) := by
    simp only [K, thq]; push_cast; field_simp; ring
  have hδ0 : 0 ≤ 2 * ((n : ℝ) * (θ' - thq (p' + 1) a)) := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hδ : 2 * ((n : ℝ) * (θ' - thq (p' + 1) a)) < 1 / (3 * 2 ^ p' : ℕ) := by
    have e : ((3 * 2 ^ (p' + 1) : ℕ) : ℝ) = 2 * (3 * 2 ^ p' : ℕ) := by push_cast; ring
    rw [e] at hn
    have hpos : (0 : ℝ) < (3 * 2 ^ p' : ℕ) := by positivity
    rw [lt_div_iff₀ hpos]
    rw [lt_div_iff₀ (by positivity)] at hn
    linarith
  have : 2 * ((n : ℝ) * θ' - 1 / 6) =
      (K : ℝ) / (3 * 2 ^ p' : ℕ) + 2 * ((n : ℝ) * (θ' - thq (p' + 1) a)) := by
    rw [← hz]; ring
  rw [this, floor_div_add_small K (by positivity) hδ0 hδ, ← hz]


/-! ## Lemma \ref{IA:lem:TD1} -/

lemma sum_range_mul_split (f : ℕ → ℝ) (q K : ℕ) :
    ∑ i ∈ range (q * K), f i = ∑ k ∈ range K, ∑ i ∈ range q, f (q * k + i) := by
  induction K with
  | zero => simp
  | succ K ih => rw [show q * (K + 1) = q * K + q by ring, sum_range_add, ih, sum_range_succ]

lemma sum_rho_pair_le (y₀ c : ℝ) (hc : 0 ≤ c) (K : ℕ) :
    |∑ k ∈ range K, (rho (y₀ + 2 * c * k) - rho (y₀ + 2 * c * k + c))| ≤ 4 * c * K + 1 := by
  set F : ℕ → ℝ := fun k => ((⌊2 * (y₀ + 2 * c * k)⌋ : ℤ) : ℝ)
  have hstep : ∀ k : ℕ, |rho (y₀ + 2 * c * k) - rho (y₀ + 2 * c * k + c)| ≤ F (k + 1) - F k := by
    intro k
    refine (abs_rho_sub_le (by linarith)).trans ?_
    simp only [F]
    push_cast
    have : ⌊2 * (y₀ + 2 * c * k + c)⌋ ≤ ⌊2 * (y₀ + 2 * c * ((k + 1 : ℕ) : ℝ))⌋ :=
      Int.floor_le_floor (by push_cast; nlinarith)
    have : ((⌊2 * (y₀ + 2 * c * k + c)⌋ : ℤ) : ℝ) ≤ ⌊2 * (y₀ + 2 * c * ((k + 1 : ℕ) : ℝ))⌋ := by
      exact_mod_cast this
    push_cast at this
    linarith
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun k _ => hstep k).trans ?_)
  rw [sum_range_sub F K]
  simp only [F]
  have h1 := Int.floor_le (2 * (y₀ + 2 * c * (K : ℝ)))
  have h2 := Int.lt_floor_add_one (2 * (y₀ + 2 * c * ((0 : ℕ) : ℝ)))
  push_cast at h1 h2 ⊢
  linarith

/-- Paper, Lemma \ref{IA:lem:TD1} (first bound): for `θ = a/q`, `a` odd, `b ≥ 0`, `L > 0` and
`θ' = θ + b/(qL)`, every sum of `r_{θ'}` over `len` consecutive integers is at most
`len · b / L + q` in absolute value. -/
lemma TD1_bound {p a : ℕ} (hp : 1 ≤ p) (ha : Odd a) (b : ℕ) {L : ℝ} (hL : 0 < L) (n₀ len : ℕ) :
    |∑ n ∈ Ico n₀ (n₀ + len), rr (thq p a + b / (3 * 2 ^ p * L)) n| ≤
      len * b / L + (3 * 2 ^ p : ℕ) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨j, rfl⟩ := ha
  set q : ℕ := 3 * 2 ^ (p' + 1)
  set H : ℕ := 3 * 2 ^ p'
  have hqH : q = H + H := by simp only [q, H]; ring
  set θ' := thq (p' + 1) (2 * j + 1) + b / (3 * 2 ^ (p' + 1) * L)
  set c : ℝ := b / (2 * L)
  have hc : 0 ≤ c := by positivity
  set K := len / q
  have hq0 : 0 < q := by positivity
  have hlen : q * K ≤ len := Nat.mul_div_le len q
  have hrem : len - q * K < q := by
    have h1 := Nat.div_add_mod len q; have h2 := Nat.mod_lt len hq0
    rw [show q * K = q * (len / q) from rfl]; omega
  rw [← sum_Ico_consecutive _ (Nat.le_add_right n₀ (q * K)) (by omega : n₀ + q * K ≤ n₀ + len)]
  -- remainder
  have hR : |∑ n ∈ Ico (n₀ + q * K) (n₀ + len), rr θ' n| ≤ (q : ℝ) / 2 := by
    refine (abs_sum_le_half _ (fun n => abs_rho_le _) _ _).trans ?_
    have : ((n₀ + len - (n₀ + q * K) : ℕ) : ℝ) ≤ q := by
      exact_mod_cast (by omega : n₀ + len - (n₀ + q * K) ≤ q)
    linarith
  -- full blocks
  have hkey : ∀ k s : ℕ, rr θ' (n₀ + (q * k + s)) + rr θ' (n₀ + (q * k + (H + s))) =
      rho (((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k) -
        rho (((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k + c) := by
    intro k s
    have hθq : (q : ℝ) * θ' = (2 * j + 1 : ℕ) + 2 * c := by
      simp only [θ', c, q, thq]; push_cast; field_simp
    have hθH : (H : ℝ) * θ' = j + 1 / 2 + c := by
      simp only [θ', c, H, thq]; push_cast; field_simp; ring
    have e1 : ((n₀ + (q * k + s) : ℕ) : ℝ) * θ' - 1 / 6 =
        (((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k) + (((2 * j + 1) * k : ℕ) : ℤ) := by
      push_cast
      have : (q : ℝ) * k * θ' = ((2 * j + 1 : ℕ) + 2 * c) * k := by rw [← hθq]; ring
      push_cast at this
      linear_combination this
    have e2 : ((n₀ + (q * k + (H + s)) : ℕ) : ℝ) * θ' - 1 / 6 =
        ((((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k + c) + 1 / 2) +
          (((2 * j + 1) * k + j : ℕ) : ℤ) := by
      push_cast
      have : (q : ℝ) * k * θ' = ((2 * j + 1 : ℕ) + 2 * c) * k := by rw [← hθq]; ring
      push_cast at this
      linear_combination this + hθH
    unfold rr
    rw [e1, e2, rho_add_int, rho_add_int, rho_add_half]
    ring
  have hblocks : ∑ n ∈ Ico n₀ (n₀ + q * K), rr θ' n =
      ∑ s ∈ range H, ∑ k ∈ range K, (rho (((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k) -
        rho (((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k + c)) := by
    rw [sum_Ico_eq_sum_range, show n₀ + q * K - n₀ = q * K by omega, sum_range_mul_split]
    have : ∀ k ∈ range K, ∑ i ∈ range q, rr θ' (n₀ + (q * k + i)) =
        ∑ s ∈ range H, (rho (((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k) -
          rho (((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k + c)) := by
      intro k _
      have hsplit : ∀ g : ℕ → ℝ, ∑ i ∈ range q, g i = ∑ s ∈ range H, (g s + g (H + s)) := by
        intro g; rw [hqH, sum_range_add, ← sum_add_distrib]
      rw [hsplit]
      exact sum_congr rfl fun s _ => hkey k s
    rw [sum_congr rfl this, sum_comm]
  rw [hblocks]
  have hB : |∑ s ∈ range H, ∑ k ∈ range K, (rho (((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k) -
        rho (((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k + c))| ≤ H * (4 * c * K + 1) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun s _ => sum_rho_pair_le _ c hc K).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul]
  have hcK : (H : ℝ) * (4 * c * K + 1) ≤ len * b / L + q / 2 := by
    have e : (H : ℝ) * (4 * c * K) = (q * K : ℕ) * b / L := by
      simp only [c, hqH]; push_cast; field_simp; ring
    have hlen' : ((q * K : ℕ) : ℝ) ≤ len := by exact_mod_cast hlen
    have : ((q * K : ℕ) : ℝ) * b / L ≤ len * b / L := by
      gcongr
    have hH : (H : ℝ) = q / 2 := by rw [hqH]; push_cast; ring
    nlinarith
  have := abs_add_le (∑ s ∈ range H, ∑ k ∈ range K, (rho (((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k) -
        rho (((n₀ + s : ℕ) : ℝ) * θ' - 1 / 6 + 2 * c * k + c)))
      (∑ n ∈ Ico (n₀ + q * K) (n₀ + len), rr θ' n)
  linarith


/-- The rational `θ' = (aL + b)/(qL)` equals `θ + b/(qL)`. -/
lemma thq_shift (p a b d : ℕ) :
    thq (p + d) (a * 2 ^ d + b) = thq p a + b / (3 * 2 ^ p * (2 ^ d : ℝ)) := by
  unfold thq; push_cast; rw [pow_add]; field_simp

/-- Paper, Lemma \ref{IA:lem:TD1} (second bound): if moreover `θ' = (aL + b)/(qL)` has odd
numerator, then all interval sums of `r_{θ'}` are at most `q (b + 1)`. -/
lemma TD1_interval {p a : ℕ} (hp : 1 ≤ p) (ha : Odd a) (b d : ℕ) (hodd : Odd (a * 2 ^ d + b))
    (u v : ℕ) :
    |∑ n ∈ Ico u v, rr (thq (p + d) (a * 2 ^ d + b)) n| ≤ (3 * 2 ^ p : ℕ) * (b + 1) := by
  have hL : (0 : ℝ) < 2 ^ d := by positivity
  have h := interval_bound_of_period (rr (thq (p + d) (a * 2 ^ d + b))) (3 * 2 ^ (p + d))
    (by positivity) (sum_Ico_q (by omega) hodd) (β := b / 2 ^ d) (γ := (3 * 2 ^ p : ℕ))
    (by positivity) (fun u len _ => by
      have := TD1_bound hp ha b hL u len
      rw [thq_shift]
      calc _ ≤ _ := this
        _ = _ := by ring) u v
  refine h.trans (le_of_eq ?_)
  push_cast; rw [pow_add]; field_simp

/-! ## Lemma \ref{IA:lem:TD3} -/

lemma rho_window {w : ℝ} (h1 : -1 / 2 ≤ w) (h2 : w < 1) :
    rho w = if 0 ≤ w ∧ w < 1 / 2 then 1 / 2 else -1 / 2 := by
  unfold rho
  rcases le_or_gt 0 w with h0 | h0
  · rw [Int.fract_eq_self.mpr ⟨h0, h2⟩]
    simp only [h0, true_and]
  · have : Int.fract w = w + 1 := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [this, if_neg (by linarith), if_neg (by intro h; linarith [h.1])]

/-- The block pattern: `+1/2` on `[v, 4v]`, `-1/2` elsewhere. -/
noncomputable def gfun (v x : ℕ) : ℝ := if v ≤ x ∧ x ≤ 4 * v then 1 / 2 else -1 / 2

lemma sum_gfun (v : ℕ) : ∑ x ∈ range (6 * v + 1), gfun v x = 1 / 2 := by
  rw [← sum_range_add_sum_Ico _ (by omega : v ≤ 6 * v + 1),
    ← sum_Ico_consecutive _ (by omega : v ≤ 4 * v + 1) (by omega : 4 * v + 1 ≤ 6 * v + 1)]
  have h1 : ∑ x ∈ range v, gfun v x = ∑ x ∈ range v, (-1 / 2 : ℝ) :=
    sum_congr rfl fun x hx => by rw [mem_range] at hx; simp [gfun]; omega
  have h2 : ∑ x ∈ Ico v (4 * v + 1), gfun v x = ∑ x ∈ Ico v (4 * v + 1), (1 / 2 : ℝ) :=
    sum_congr rfl fun x hx => by
      rw [mem_Ico] at hx; rw [gfun, if_pos ⟨hx.1, by omega⟩]
  have h3 : ∑ x ∈ Ico (4 * v + 1) (6 * v + 1), gfun v x =
      ∑ x ∈ Ico (4 * v + 1) (6 * v + 1), (-1 / 2 : ℝ) :=
    sum_congr rfl fun x hx => by
      rw [mem_Ico] at hx; rw [gfun, if_neg (by omega)]
  rw [h1, h2, h3]
  simp only [sum_const, card_range, Nat.card_Ico, nsmul_eq_mul]
  rw [show 4 * v + 1 - v = 3 * v + 1 by omega, show 6 * v + 1 - (4 * v + 1) = 2 * v by omega]
  push_cast; ring

lemma sum_mod_perm {U τ : ℕ} (hU : 0 < U) (hcop : Nat.Coprime τ U) (g : ℕ → ℝ) (n₁ : ℕ) :
    ∑ n ∈ Ico n₁ (n₁ + U), g (n * τ % U) = ∑ x ∈ range U, g x := by
  have hinj : Set.InjOn (fun n => n * τ % U) (Ico n₁ (n₁ + U) : Set ℕ) := by
    intro n hn n' hn' hnn
    simp only [coe_Ico, Set.mem_Ico] at hn hn'
    have hmod : n * τ ≡ n' * τ [MOD U] := hnn
    have hmod' : n ≡ n' [MOD U] :=
      Nat.ModEq.cancel_right_of_coprime (by rw [Nat.gcd_comm]; exact hcop) hmod
    rcases le_total n n' with h | h
    · have := (Nat.modEq_iff_dvd' h).mp hmod'
      have := Nat.eq_zero_of_dvd_of_lt this (by omega)
      omega
    · have := (Nat.modEq_iff_dvd' h).mp hmod'.symm
      have := Nat.eq_zero_of_dvd_of_lt this (by omega)
      omega
  have himg : (Ico n₁ (n₁ + U)).image (fun n => n * τ % U) = range U := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨n, -, rfl⟩ := mem_image.mp hx
      exact mem_range.mpr (Nat.mod_lt _ hU)
    · rw [card_image_of_injOn hinj, card_range, Nat.card_Ico]; omega
  rw [← himg, sum_image hinj]

/-- Core of Lemma \ref{IA:lem:TD3}, step (4): if `θ' = a'/(3N)` with `a' U = τ (3N) + 1` and
`U = 6v + 1`, then for `N ≤ n < 2N`, `r_{θ'}(n)` is `+1/2` exactly when `v ≤ nτ mod U ≤ 4v`. -/
lemma TD3_key {a' N U τ v : ℕ} {θ' : ℝ} (hθ' : θ' = (a' : ℝ) / (3 * N))
    (e1 : (a' : ℝ) * U = τ * (3 * N) + 1) (hU6 : U = 6 * v + 1) {n : ℕ} (hn1 : N ≤ n)
    (hn2 : n < 2 * N) : rr θ' n = gfun v (n * τ % U) := by
  have hU0 : 0 < U := by omega
  have hN0 : 0 < N := by omega
  set X := n * τ / U
  set Y := n * τ % U
  have hXY : U * X + Y = n * τ := Nat.div_add_mod _ _
  have hYU : Y < U := Nat.mod_lt _ hU0
  have e2 : (U : ℝ) * X + Y = n * τ := by exact_mod_cast hXY
  set z : ℝ := n / (3 * N)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU0
  have hz1 : 1 / 3 ≤ z := by
    simp only [z]; rw [le_div_iff₀ (by positivity)]
    have : (N : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  have hz2 : z < 2 / 3 := by
    simp only [z]; rw [div_lt_iff₀ (by positivity)]
    have : (n : ℝ) < 2 * N := by exact_mod_cast hn2
    linarith
  have hsplit : (n : ℝ) * θ' - 1 / 6 = ((Y + z) / U - 1 / 6) + ((X : ℤ) : ℝ) := by
    rw [hθ']
    simp only [z]
    push_cast
    field_simp
    linear_combination 6 * ((n : ℝ) * e1 - 3 * (N : ℝ) * e2)
  unfold rr
  rw [hsplit, rho_add_int]
  have hY' : (Y : ℝ) ≤ U - 1 := by
    have : Y + 1 ≤ U := hYU
    have : (Y : ℝ) + 1 ≤ U := by exact_mod_cast this
    linarith
  have hw1 : -1 / 2 ≤ (Y + z) / U - 1 / 6 := by
    have : 0 ≤ (Y + z) / U := by positivity
    linarith
  have hw2 : (Y + z) / U - 1 / 6 < 1 := by
    have : (Y + z) / U < 1 := by rw [div_lt_one hU']; linarith
    linarith
  rw [rho_window hw1 hw2, gfun]
  have hU6' : (U : ℝ) = 6 * v + 1 := by exact_mod_cast hU6
  congr 1
  apply propext
  rw [sub_nonneg, sub_lt_iff_lt_add, le_div_iff₀ hU', div_lt_iff₀ hU', hU6']
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hc
      have : Y + 1 ≤ v := by omega
      have : (Y : ℝ) + 1 ≤ v := by exact_mod_cast this
      nlinarith
    · by_contra hc
      have : 4 * v + 1 ≤ Y := by omega
      have : 4 * (v : ℝ) + 1 ≤ Y := by exact_mod_cast this
      nlinarith
  · rintro ⟨h1, h2⟩
    have h1' : (v : ℝ) ≤ Y := by exact_mod_cast h1
    have h2' : (Y : ℝ) ≤ 4 * v := by exact_mod_cast h2
    constructor <;> nlinarith

/-- Lemma \ref{IA:lem:TD3}, steps (4)-(5): the `⌊N/U⌋` full blocks of `[N, 2N)` contribute
`⌊N/U⌋/2`. -/
lemma TD3_full {a' N U τ v : ℕ} {θ' : ℝ} (hθ' : θ' = (a' : ℝ) / (3 * N))
    (e1 : (a' : ℝ) * U = τ * (3 * N) + 1) (hU6 : U = 6 * v + 1) (hcop : Nat.Coprime τ U) :
    ∑ n ∈ Ico N (N + U * (N / U)), rr θ' n = ((N / U : ℕ) : ℝ) / 2 := by
  have hU0 : 0 < U := by omega
  have hblock : ∀ n₁, N ≤ n₁ → n₁ + U ≤ 2 * N → ∑ n ∈ Ico n₁ (n₁ + U), rr θ' n = 1 / 2 := by
    intro n₁ h1 h2
    rw [sum_congr rfl fun n hn => TD3_key hθ' e1 hU6 (by rw [mem_Ico] at hn; omega)
      (by rw [mem_Ico] at hn; omega), sum_mod_perm hU0 hcop, hU6, sum_gfun]
  set B := N / U
  have hUB : U * B ≤ N := Nat.mul_div_le N U
  have hfull : ∀ B', B' ≤ B → ∑ n ∈ Ico N (N + U * B'), rr θ' n = B' / 2 := by
    intro B' hB'
    induction B' with
    | zero => simp
    | succ B' ih =>
      have hle : U * (B' + 1) ≤ U * B := Nat.mul_le_mul_left U hB'
      rw [← sum_Ico_consecutive _ (Nat.le_add_right N (U * B')) (by nlinarith),
        ih (by omega), show N + U * (B' + 1) = N + U * B' + U by ring,
        hblock _ (by omega) (by nlinarith)]
      push_cast; ring
  exact hfull B le_rfl

/-- Lemma \ref{IA:lem:TD3}, step (5): the lower bound for `Δ(θ')` from the block structure. -/
lemma TD3_delta {p a b d h m U τ v : ℕ} (hp : 1 ≤ p) (ha : Odd a)
    (hbU : b * U = h * 2 ^ d + 1)
    (ha'U : (a * 2 ^ d + b) * U = τ * (3 * 2 ^ (p + d)) + 1) (hU6 : U = 6 * v + 1)
    (hcop : Nat.Coprime τ U) (hU2m : U * 2 ^ m ≤ 2 * 2 ^ d) :
    ((3 * 2 ^ p : ℕ) * 2 ^ m / 12 : ℝ) - h - (3 * 2 ^ p : ℕ) - 2 ≤
      Delta (p + d) (a * 2 ^ d + b) := by
  have hU0 : 0 < U := by omega
  obtain ⟨N, hN⟩ : ∃ N, N = 2 ^ (p + d) := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', a' = a * 2 ^ d + b := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; positivity
  have hθ' : thq (p + d) a' = (a' : ℝ) / (3 * N) := by
    rw [thq, hN]; push_cast; ring
  have e1 : (a' : ℝ) * U = τ * (3 * N) + 1 := by
    rw [← ha', ← hN] at ha'U; exact_mod_cast ha'U
  have hfull := TD3_full hθ' e1 hU6 hcop
  have hDelta : Delta (p + d) a' = ∑ n ∈ Ico N (2 * N), rr (thq (p + d) a') n := by
    rw [Delta, ← hN, pow_succ, ← hN, mul_comm]
  rw [← ha', hDelta]
  obtain ⟨B, hB⟩ : ∃ B, B = N / U := ⟨_, rfl⟩
  rw [← hB] at hfull
  have hUB : U * B ≤ N := by rw [hB]; exact Nat.mul_div_le N U
  have hlt : N < U * (B + 1) := by rw [hB]; exact Nat.lt_mul_div_succ N hU0
  rw [← sum_Ico_consecutive _ (Nat.le_add_right N (U * B)) (by omega : N + U * B ≤ 2 * N), hfull]
  -- the remainder
  have hrem := TD1_bound hp ha b (L := (2 ^ d : ℝ)) (by positivity) (N + U * B) (N - U * B)
  rw [← thq_shift, ← ha', show N + U * B + (N - U * B) = 2 * N by omega] at hrem
  have hlenU : N - U * B < U := by rw [mul_add, mul_one] at hlt; omega
  have hL' : (0 : ℝ) < 2 ^ d := by positivity
  have hbU' : (b : ℝ) * U = h * 2 ^ d + 1 := by exact_mod_cast hbU
  have hremb : ((N - U * B : ℕ) : ℝ) * b / 2 ^ d ≤ h + 1 := by
    have : ((N - U * B : ℕ) : ℝ) ≤ U := by exact_mod_cast hlenU.le
    rw [div_le_iff₀ hL']
    have hd1 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    nlinarith
  have hrem' : -(h + 1 + (3 * 2 ^ p : ℕ) : ℝ) ≤
      ∑ n ∈ Ico (N + U * B) (2 * N), rr (thq (p + d) a') n := by
    have := neg_abs_le (∑ n ∈ Ico (N + U * B) (2 * N), rr (thq (p + d) a') n)
    linarith
  -- the main term
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU0
  have hBlow : (N : ℝ) / U - 1 ≤ B := by
    have : (N : ℝ) < U * (B + 1) := by exact_mod_cast hlt
    rw [div_sub_one hU'.ne', div_le_iff₀ hU']
    linarith
  have hmain : ((3 * 2 ^ p : ℕ) : ℝ) * 2 ^ m / 12 ≤ (N : ℝ) / U / 2 := by
    have hNL : (N : ℝ) = 2 ^ p * 2 ^ d := by rw [hN, pow_add]; push_cast; ring
    have hU2m' : (U : ℝ) * 2 ^ m ≤ 2 * 2 ^ d := by exact_mod_cast hU2m
    rw [div_div, le_div_iff₀ (by positivity), hNL]
    push_cast
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) p]
  linarith

/-- `h = q - a`. -/
def hOf (p a : ℕ) : ℕ := 3 * 2 ^ p - a

/-- `b = h 2^m + 1`. -/
def bOf (p a m : ℕ) : ℕ := hOf p a * 2 ^ m + 1

lemma modEq_one_extract {x n : ℕ} (hn : 1 < n) (hx : x ≡ 1 [MOD n]) : ∃ w, x = n * w + 1 := by
  have h1 : x % n = 1 := by rw [hx]; exact Nat.mod_eq_of_lt hn
  exact ⟨x / n, by have := Nat.div_add_mod x n; omega⟩

/-- Paper, Lemma \ref{IA:lem:TD3}. Let `θ = a/q`, `q = 3·2^p`, `a` odd, `h = q - a`, `m ≥ p`,
`b = h 2^m + 1`, and `R ≥ 1` with `2^R ≡ 1 (mod 3b)`. For `t ≥ 1` put `d = m + 2Rt`, `L = 2^d`
and `θ' = (aL + b)/(qL)`. Then `b < L`, `aL + b` is odd and less than `qL`, and
`Δ(θ') ≥ q 2^m / 12 - h - q - 2`. -/
theorem TD3 {p a m R t : ℕ} (hp : 1 ≤ p) (ha : Odd a) (haq : a < 3 * 2 ^ p) (hm : p ≤ m)
    (hR : 2 ^ R ≡ 1 [MOD 3 * bOf p a m]) (hR1 : 1 ≤ R) (ht : 1 ≤ t) :
    bOf p a m < 2 ^ (m + 2 * R * t) ∧ Odd (a * 2 ^ (m + 2 * R * t) + bOf p a m) ∧
    a * 2 ^ (m + 2 * R * t) + bOf p a m < 3 * 2 ^ (p + (m + 2 * R * t)) ∧
    ((3 * 2 ^ p : ℕ) * 2 ^ m / 12 : ℝ) - hOf p a - (3 * 2 ^ p : ℕ) - 2 ≤
      Delta (p + (m + 2 * R * t)) (a * 2 ^ (m + 2 * R * t) + bOf p a m) := by
  set q := 3 * 2 ^ p with hq
  set h := hOf p a with hh
  set b := bOf p a m with hb
  set d := m + 2 * R * t with hd
  set L := 2 ^ d with hL
  have hha : h + a = q := by simp only [h, hOf]; omega
  have hh1 : 1 ≤ h := by simp only [h, hOf]; omega
  have hb' : b = h * 2 ^ m + 1 := rfl
  have hm1 : 1 ≤ m := le_trans hp hm
  have h2m : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  have hb2 : 3 ≤ b := by rw [hb']; nlinarith
  -- `2^R = 3 b w₀ + 1` and `2^{2Rt} = 3 b w + 1`
  obtain ⟨w₀, hw₀⟩ := modEq_one_extract (by omega) hR
  have hR2 : 2 ≤ 2 ^ R := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ R := Nat.pow_le_pow_right (by norm_num) hR1
  have hw₀1 : 1 ≤ w₀ := by
    rcases Nat.eq_zero_or_pos w₀ with h0 | h0
    · rw [h0] at hw₀; omega
    · exact h0
  obtain ⟨w, hw⟩ : ∃ w, 2 ^ (2 * R * t) = 3 * b * w + 1 := by
    have : 2 ^ (2 * R * t) ≡ 1 [MOD 3 * b] := by
      have := hR.pow (2 * t)
      rwa [← pow_mul, one_pow, show R * (2 * t) = 2 * R * t by ring] at this
    exact modEq_one_extract (by omega) this
  have hLsplit : L = 2 ^ m * 2 ^ (2 * R * t) := by rw [hL, hd, pow_add]
  have hbL : b < L := by
    have : 2 ^ R ≤ L := by
      rw [hL]; exact Nat.pow_le_pow_right (by norm_num) (by rw [hd]; nlinarith)
    nlinarith
  have hLeven : Even L := by
    rw [hL, hd]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hbodd : Odd b := by
    rw [hb']; exact (Even.mul_left (Nat.even_pow.mpr ⟨even_two, by omega⟩) h).add_one
  have hodd : Odd (a * L + b) := (hLeven.mul_left a).add_odd hbodd
  have hlt : a * L + b < 3 * 2 ^ (p + d) := by
    have : 3 * 2 ^ (p + d) = q * L := by rw [hq, hL, pow_add]; ring
    rw [this, ← hha]
    nlinarith
  refine ⟨hbL, hodd, hlt, ?_⟩
  -- the integers `U`, `τ`, `v`
  set U := 1 + 3 * 2 ^ m * h * w with hU
  have hbU : b * U = h * L + 1 := by rw [hLsplit, hw, hU, hb']; ring
  have h2mp : 2 ^ m = 2 ^ p * 2 ^ (m - p) := by rw [← pow_add]; congr 1; omega
  set τ := 1 + 2 ^ (m - p) * a * h * w with hτdef
  have hτ : τ * q = a * U + h := by
    have h2mpZ : (2 : ℤ) ^ m = 2 ^ p * 2 ^ (m - p) := by exact_mod_cast h2mp
    have hhaZ : (h : ℤ) + a = 3 * 2 ^ p := by exact_mod_cast hha
    zify
    simp only [τ, U, q]
    push_cast
    linear_combination (-1 : ℤ) * hhaZ + (-3 * a * h * w : ℤ) * h2mpZ
  have ha'U : (a * L + b) * U = τ * (q * L) + 1 := by
    zify at hτ hbU ⊢
    linear_combination (L : ℤ) * hτ.symm + hbU
  have hcop : Nat.Coprime τ U := by
    have h1 : Nat.gcd τ U ∣ τ * (q * L) := dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
    have h2 : Nat.gcd τ U ∣ (a * L + b) * U := dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
    rw [ha'U] at h2
    exact Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h2)
  set v := 2 ^ (m - 1) * h * w
  have hU6 : U = 6 * v + 1 := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    rw [hU, this]; ring
  have hU2m : U * 2 ^ m ≤ 2 * 2 ^ d := by
    have h2mL : 2 ^ m ≤ L := by rw [hL]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have : U * 2 ^ m * b ≤ 2 * L * b := by
      calc U * 2 ^ m * b = h * L * 2 ^ m + 2 ^ m := by rw [mul_right_comm, mul_comm U b, hbU]; ring
        _ ≤ h * L * 2 ^ m + h * L * 2 ^ m + 2 * L := by omega
        _ = 2 * L * b := by rw [hb']; ring
    rw [← hL]
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have ha'U' : (a * 2 ^ d + b) * U = τ * (3 * 2 ^ (p + d)) + 1 := by
    rw [ha'U, hq, hL, pow_add]; ring
  exact TD3_delta hp ha hbU ha'U' hU6 hcop hU2m


/-! ## Lemma \ref{IA:lem:TD4} -/

lemma Sf_congr {f g : ℕ → ℝ} {M : ℕ} (h : ∀ n < M, f n = g n) : Sf f M = Sf g M :=
  sum_congr rfl fun n hn => by rw [h n (mem_Ico.mp hn).2]

lemma TD4_agree {p a : ℕ} (hp : 1 ≤ p) (b d ℓ : ℕ) (hbℓ : 2 * b ≤ 2 ^ ℓ) (hℓd : ℓ ≤ d) :
    ∀ n < 2 ^ (d - ℓ), rr (thq (p + d) (a * 2 ^ d + b)) n = rr (thq p a) n := by
  intro n hn
  rw [thq_shift]
  have hq : (0 : ℝ) < 3 * 2 ^ p := by positivity
  have hL : (0 : ℝ) < 2 ^ d := by positivity
  have h0 : (0 : ℝ) ≤ b / (3 * 2 ^ p * 2 ^ d) := by positivity
  refine rr_eq_of_close (a := a) hp (by linarith) n ?_
  rw [add_sub_cancel_left]
  have hn' : (n : ℝ) < 2 ^ (d - ℓ) := by exact_mod_cast hn
  have hsplit : (2 : ℝ) ^ d = 2 ^ (d - ℓ) * 2 ^ ℓ := by rw [← pow_add]; congr 1; omega
  have hbℓ' : 2 * (b : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast hbℓ
  have hpos : (0 : ℝ) < 2 ^ (d - ℓ) := by positivity
  have hpos' : (0 : ℝ) < 2 ^ ℓ := by positivity
  push_cast
  rw [hsplit, mul_div_assoc', div_lt_div_iff₀ (by positivity) hq]
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  · have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hbl : (b : ℝ) ≤ 2 ^ ℓ := by linarith
    calc (n : ℝ) * b * (3 * 2 ^ p) < 2 ^ (d - ℓ) * b * (3 * 2 ^ p) := by gcongr
      _ ≤ 2 ^ (d - ℓ) * 2 ^ ℓ * (3 * 2 ^ p) := by gcongr
      _ = 1 * (3 * 2 ^ p * (2 ^ (d - ℓ) * 2 ^ ℓ)) := by ring


/-- Paper, Lemma \ref{IA:lem:TD4}(ii), the analytic part: lower bounds for `S_{θ'}`. -/
lemma TD4_lower {p a b d ℓ : ℕ} (hp : 1 ≤ p) (ha : Odd a) (hodd : Odd (a * 2 ^ d + b))
    (hℓd : ℓ ≤ d) (hJp : p ≤ d - ℓ)
    (hagree : ∀ n < 2 ^ (d - ℓ), rr (thq (p + d) (a * 2 ^ d + b)) n = rr (thq p a) n)
    {c : ℝ} (hc : 0 ≤ c) {N₀ : ℕ}
    (hS : ∀ M : ℕ, N₀ ≤ M → c * Real.log M ≤ Sf (rr (thq p a)) M)
    (hG' : c * Real.log 2 ≤ Gain (p + d) (a * 2 ^ d + b))
    (hΦ : c * ((p + d : ℕ) + 1) * Real.log 2 + (3 * 2 ^ p : ℕ) * (b + 1) +
        (p + ℓ : ℕ) * ((3 * 2 ^ p : ℕ) * (b + 1)) ≤
      Sf (rr (thq p a)) (2 ^ p) + (d - ℓ - p : ℕ) * Gain p a) :
    ∀ M : ℕ, N₀ ≤ M → c * Real.log M ≤ Sf (rr (thq (p + d) (a * 2 ^ d + b))) M := by
  have hB₀ : (0 : ℝ) ≤ (3 * 2 ^ p : ℕ) * (b + 1) := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hSeq : ∀ M, M ≤ 2 ^ (d - ℓ) →
      Sf (rr (thq (p + d) (a * 2 ^ d + b))) M = Sf (rr (thq p a)) M :=
    fun M hM => Sf_congr fun n hn => hagree n (by omega)
  have hBint := TD1_interval hp ha b d hodd
  have hJP : d - ℓ ≤ p + d := by omega
  have hPJ : p + d - (d - ℓ) = p + ℓ := by omega
  -- the range `2^J ≤ M ≤ 2^{P'}`
  have hcaseB : ∀ M : ℕ, 2 ^ (d - ℓ) ≤ M → M ≤ 2 ^ (p + d) →
      c * ((p + d : ℕ) + 1) * Real.log 2 + (3 * 2 ^ p : ℕ) * (b + 1) ≤
        Sf (rr (thq (p + d) (a * 2 ^ d + b))) M := by
    intro M h1 h2
    have hblk := Sf_sub_le _ hBint hJP h1 h2
    rw [hPJ, hSeq _ le_rfl, S_pow hp ha hJp] at hblk
    have := neg_abs_le (Sf (rr (thq (p + d) (a * 2 ^ d + b))) M -
      (Sf (rr (thq p a)) (2 ^ p) + ((d - ℓ - p : ℕ) : ℝ) * Gain p a))
    linarith
  intro M hM
  rcases le_or_gt M (2 ^ (d - ℓ)) with h1 | h1
  · rw [hSeq M h1]; exact hS M hM
  rcases le_or_gt M (2 ^ (p + d)) with h2 | h2
  · have := hcaseB M h1.le h2
    have hlog : Real.log M ≤ ((p + d : ℕ) : ℝ) * Real.log 2 := by
      have hM0 : (0 : ℝ) < M := by
        have : 0 < M := lt_of_le_of_lt (Nat.zero_le _) h1
        exact_mod_cast this
      have : Real.log M ≤ Real.log ((2 : ℝ) ^ (p + d)) :=
        Real.log_le_log hM0 (by exact_mod_cast h2)
      rwa [Real.log_pow] at this
    nlinarith [mul_le_mul_of_nonneg_left hlog hc]
  · have hP'1 : 1 ≤ p + d := by omega
    refine Sf_growth _ hBint (p + d) (fun j hj => S_pow hP'1 hodd hj) hc hG' ?_ M h2.le
    exact hcaseB (2 ^ (p + d)) (Nat.pow_le_pow_right (by norm_num) hJP) le_rfl


/-- Paper, Lemmas \ref{IA:lem:TD3} and \ref{IA:lem:TD4} combined: one step of the construction.
From `θ = a/q ∈ 𝒬` with `G(θ) > c log 2` and `S_θ(M) ≥ c log M` for `M ≥ N₀`, we get
`θ' = a'/q' ∈ 𝒬` with `q' ≥ 2q`, `θ < θ' ≤ θ + δ`, `G(θ') > C'`, `r_{θ'} = r_θ` on `[0, X₀)` and
`S_{θ'}(M) ≥ c log M` for `M ≥ N₀`. -/
theorem TD_step {p a : ℕ} (hp : 1 ≤ p) (ha : Odd a) (haq : a < 3 * 2 ^ p) {c : ℝ} (hc : 0 ≤ c)
    {N₀ : ℕ} (X₀ : ℕ) (hG : c * Real.log 2 < Gain p a)
    (hS : ∀ M : ℕ, N₀ ≤ M → c * Real.log M ≤ Sf (rr (thq p a)) M) (C' δ : ℝ) (hδ : 0 < δ) :
    ∃ p' a' : ℕ, p + 1 ≤ p' ∧ Odd a' ∧ a' < 3 * 2 ^ p' ∧ thq p a < thq p' a' ∧
      thq p' a' ≤ thq p a + δ ∧ C' < Gain p' a' ∧
      (∀ n < X₀, rr (thq p' a') n = rr (thq p a) n) ∧
      (∀ M : ℕ, N₀ ≤ M → c * Real.log M ≤ Sf (rr (thq p' a')) M) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨q, hq⟩ : ∃ q, q = 3 * 2 ^ p := ⟨_, rfl⟩
  have hq6 : 6 ≤ q := by
    rw [hq]; have : 2 ^ 1 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp; omega
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max C' (c * Real.log 2) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = 2 * (⌈K⌉₊ + hOf p a + q + 3) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = p + 2 * s := ⟨_, rfl⟩
  have hpm : p ≤ m := by omega
  have hgainm : K < ((3 * 2 ^ p : ℕ) * 2 ^ m / 12 : ℝ) - hOf p a - (3 * 2 ^ p : ℕ) - 2 := by
    rw [← hq]
    have h1 : s < 2 ^ m := by
      have := Nat.lt_two_pow_self (n := s)
      have : 2 ^ s ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h1' : (s : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast h1
    have hs' : (s : ℝ) = 2 * (⌈K⌉₊ + hOf p a + q + 3) := by rw [hs]; push_cast; ring
    have hKc := Nat.le_ceil K
    have hq6' : (6 : ℝ) ≤ q := by exact_mod_cast hq6
    nlinarith
  obtain ⟨b, hb⟩ : ∃ b, b = bOf p a m := ⟨_, rfl⟩
  have hbodd : Odd b := by
    rw [hb, bOf]
    exact (Even.mul_left (Nat.even_pow.mpr ⟨even_two, by omega⟩) _).add_one
  have hb0 : 0 < b := hbodd.pos
  have hcop2 : Nat.Coprime 2 (3 * b) := Nat.coprime_two_left.mpr (by
    exact (odd_two_mul_add_one 1).mul hbodd)
  obtain ⟨R, hRdef⟩ : ∃ R, R = Nat.totient (3 * b) := ⟨_, rfl⟩
  have hR : 2 ^ R ≡ 1 [MOD 3 * bOf p a m] := by
    rw [hRdef, ← hb]; exact Nat.ModEq.pow_totient hcop2
  have hR1 : 1 ≤ R := by rw [hRdef]; exact Nat.totient_pos.mpr (by omega)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = b + 1 := ⟨_, rfl⟩
  have hbℓ : 2 * b ≤ 2 ^ ℓ := by
    rw [hℓ, pow_succ]; have := Nat.lt_two_pow_self (n := b); omega
  set B₀ : ℝ := (3 * 2 ^ p : ℕ) * (b + 1)
  set g : ℝ := Gain p a - c * Real.log 2
  have hg : 0 < g := by simp only [g]; linarith
  set K₁ : ℝ := p * Gain p a + c * (p + ℓ + 1) * Real.log 2 + B₀ * (1 + p + ℓ) -
    Sf (rr (thq p a)) (2 ^ p)
  obtain ⟨t, ht⟩ : ∃ t, t = X₀ + ⌈K₁ / g⌉₊ + p + ℓ + ⌈(b : ℝ) / (q * δ)⌉₊ + 1 := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by omega
  obtain ⟨hbL, hodd, hlt, hΔ⟩ := TD3 hp ha haq hpm hR hR1 ht1
  rw [← hb] at hbL hodd hlt hΔ
  obtain ⟨d, hd⟩ : ∃ d, d = m + 2 * R * t := ⟨_, rfl⟩
  rw [← hd] at hbL hodd hlt hΔ
  have hdt : t ≤ d := by rw [hd]; nlinarith
  have hℓd : ℓ ≤ d := by omega
  have hJp : p ≤ d - ℓ := by omega
  have hJX : X₀ ≤ d - ℓ := by omega
  -- parity: `p + d` is even, so `G(θ') = Δ(θ')`
  have hGain : Gain (p + d) (a * 2 ^ d + b) = Delta (p + d) (a * 2 ^ d + b) := by
    have : Even (p + d) := ⟨p + s + R * t, by rw [hd, hm]; ring⟩
    rw [Gain, this.neg_one_pow, one_mul]
  refine ⟨p + d, a * 2 ^ d + b, by omega, hodd, hlt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [thq_shift]
    have : (0 : ℝ) < b / (3 * 2 ^ p * 2 ^ d) := by
      have : (0 : ℝ) < b := by exact_mod_cast hb0
      positivity
    linarith
  · rw [thq_shift]
    have hd' : (b : ℝ) / (q * δ) ≤ 2 ^ d := by
      have h1 := Nat.le_ceil ((b : ℝ) / (q * δ))
      have h2 : ⌈(b : ℝ) / (q * δ)⌉₊ < 2 ^ d := by
        have := Nat.lt_two_pow_self (n := d); omega
      have : (⌈(b : ℝ) / (q * δ)⌉₊ : ℝ) < 2 ^ d := by exact_mod_cast h2
      linarith
    have hqδ : (0 : ℝ) < q * δ := by
      have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      positivity
    rw [div_le_iff₀ hqδ] at hd'
    have hq' : ((3 * 2 ^ p : ℕ) : ℝ) = q := by rw [hq]
    push_cast at hq'
    rw [hq', add_le_add_iff_left, div_le_iff₀ (by positivity)]
    nlinarith
  · rw [hGain]
    have : C' ≤ K := by rw [hK]; exact le_max_left _ _
    linarith
  · intro n hn
    exact TD4_agree hp b d ℓ hbℓ hℓd n (lt_of_lt_of_le hn
      (le_trans hJX (Nat.lt_two_pow_self).le))
  · refine TD4_lower hp ha hodd hℓd hJp (TD4_agree hp b d ℓ hbℓ hℓd) hc hS ?_ ?_
    · rw [hGain]
      have : c * Real.log 2 ≤ K := by rw [hK]; exact le_max_right _ _
      linarith
    · -- the condition `Φ ≥ 0`
      have hJ : K₁ / g ≤ ((d - ℓ : ℕ) : ℝ) - p := by
        have h1 := Nat.le_ceil (K₁ / g)
        have h2 : ⌈K₁ / g⌉₊ + p ≤ d - ℓ := by omega
        have : ((⌈K₁ / g⌉₊ + p : ℕ) : ℝ) ≤ ((d - ℓ : ℕ) : ℝ) := by exact_mod_cast h2
        push_cast at this
        linarith
      rw [div_le_iff₀ hg] at hJ
      have e1 : ((d - ℓ - p : ℕ) : ℝ) = ((d - ℓ : ℕ) : ℝ) - p := by
        rw [Nat.cast_sub hJp]
      have e2 : ((p + d : ℕ) : ℝ) = ((d - ℓ : ℕ) : ℝ) + p + ℓ := by
        rw [Nat.cast_sub hℓd]; push_cast; ring
      have e3 : ((p + ℓ : ℕ) : ℝ) = p + ℓ := by push_cast; ring
      rw [e1, e2, e3]
      simp only [K₁, g, B₀] at hJ ⊢
      nlinarith


/-! ## Proposition \ref{IA:prop:TD} -/

/-- If `G(θ) > c log 2` then `S_θ(M) ≥ c log M` for all large `M`
(paper, Lemma \ref{IA:lem:TD0}(iii)). -/
lemma eventually_growth {p a : ℕ} (hp : 1 ≤ p) (ha : Odd a) {c : ℝ} (hc : 0 ≤ c)
    (hG : c * Real.log 2 < Gain p a) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ M : ℕ, N ≤ M → c * Real.log M ≤ Sf (rr (thq p a)) M := by
  set g := Gain p a - c * Real.log 2
  have hg : 0 < g := by simp only [g]; linarith
  set K : ℝ := c * (p + 1) * Real.log 2 + (3 * 2 ^ p : ℕ) / 2 - Sf (rr (thq p a)) (2 ^ p)
  set j₁ := p + ⌈K / g⌉₊
  refine ⟨2 ^ j₁, Nat.one_le_two_pow, Sf_growth _ (interval_bound_q hp ha) j₁
    (fun j hj => by
      rw [S_pow hp ha (by omega : p ≤ j), S_pow hp ha (by omega : p ≤ j₁)]
      rw [Nat.cast_sub (by omega : p ≤ j), Nat.cast_sub (by omega : p ≤ j₁),
        Nat.cast_sub hj]; ring) hc hG.le ?_⟩
  rw [S_pow hp ha (by omega : p ≤ j₁), show j₁ - p = ⌈K / g⌉₊ by omega]
  have h1 := Nat.le_ceil (K / g)
  rw [div_le_iff₀ hg] at h1
  have e : (j₁ : ℝ) = p + ⌈K / g⌉₊ := by simp only [j₁]; push_cast; ring
  rw [e]
  simp only [K, g] at h1
  nlinarith

lemma log_two_lt_one : Real.log 2 < 1 := by
  have := Real.log_two_lt_d9; linarith

/-- The starting point `θ₁ = 1/12`: `G(θ₁) = 2`. -/
lemma Gain_two_one : Gain 2 1 = 2 := by
  have h : ∀ n ∈ Ico (2 ^ 2) (2 ^ (2 + 1)), rr (thq 2 1) n = 1 / 2 := by
    intro n hn
    rw [mem_Ico] at hn
    have h1 : (4 : ℝ) ≤ n := by exact_mod_cast (by simpa using hn.1 : 4 ≤ n)
    have h2 : (n : ℝ) ≤ 7 := by
      have : n ≤ 7 := by have := hn.2; norm_num at this; omega
      exact_mod_cast this
    unfold rr thq
    rw [rho_window (by norm_num; nlinarith) (by norm_num; nlinarith), if_pos]
    norm_num
    constructor <;> nlinarith
  rw [Gain, Delta, sum_congr rfl h]
  norm_num

/-- State of the inductive construction: `θ = a / (3 · 2^p)` and the threshold `N`. -/
structure TDState where
  p : ℕ
  a : ℕ
  N : ℕ

/-- `θ` of a state. -/
noncomputable def TDState.θ (s : TDState) : ℝ := thq s.p s.a

/-- The width `1 / (2 q N)` of the nesting intervals. -/
noncomputable def TDState.w (s : TDState) : ℝ := 1 / (2 * (3 * 2 ^ s.p : ℕ) * s.N)

/-- Invariant at stage `k` (the paper's `k + 1`): (H1) `G(θ) > (k + 2) log 2` and
`S_θ(M) ≥ (k + 1) log M` for `M ≥ N`. -/
def TDState.Inv (k : ℕ) (s : TDState) : Prop :=
  1 ≤ s.p ∧ Odd s.a ∧ s.a < 3 * 2 ^ s.p ∧ 1 ≤ s.N ∧ ((k : ℝ) + 2) * Real.log 2 < Gain s.p s.a ∧
    ∀ M : ℕ, s.N ≤ M → ((k : ℝ) + 1) * Real.log M ≤ Sf (rr s.θ) M

/-- The step relation between stages `k` and `k + 1`. -/
def TDState.Rel (k : ℕ) (s t : TDState) : Prop :=
  s.p + 1 ≤ t.p ∧ s.θ < t.θ ∧ t.θ ≤ s.θ + s.w / 2 ∧ s.N + 1 ≤ t.N ∧
    (∀ n < s.N, rr t.θ n = rr s.θ n) ∧ ∀ M : ℕ, s.N ≤ M → ((k : ℝ) + 1) * Real.log M ≤ Sf (rr t.θ) M

lemma TDState.w_pos {s : TDState} (h : 1 ≤ s.N) : 0 < s.w := by
  unfold TDState.w
  have : (0 : ℝ) < s.N := by exact_mod_cast h
  positivity

lemma TDState.exists_next (k : ℕ) (s : TDState) (h : s.Inv k) :
    ∃ t : TDState, t.Inv (k + 1) ∧ s.Rel k t := by
  obtain ⟨hp, ha, haq, hN, hG, hS⟩ := h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨p', a', hpp, ha', ha'q, h1, h2, hG', hagree, hS'⟩ :=
    TD_step hp ha haq (c := (k : ℝ) + 1) (by positivity) s.N (by nlinarith) hS
      ((((k + 1 : ℕ) : ℝ) + 2) * Real.log 2) (s.w / 2) (by linarith [TDState.w_pos hN])
  obtain ⟨N', hN'1, hN'⟩ := eventually_growth (by omega : 1 ≤ p') ha'
    (c := ((k + 1 : ℕ) : ℝ) + 1) (by positivity) (by push_cast at hG' ⊢; nlinarith)
  refine ⟨⟨p', a', max N' (s.N + 1)⟩, ⟨show 1 ≤ p' by omega, ha', ha'q, by simp, hG', fun M hM =>
    hN' M (le_trans (le_max_left _ _) hM)⟩, hpp, h1, h2, le_max_right _ _, hagree, hS'⟩

/-- The initial state `θ₁ = 1/12`. -/
lemma TDState.exists_init : ∃ s : TDState, s.Inv 0 := by
  have hl2 := log_two_lt_one
  obtain ⟨N, hN1, hN⟩ := eventually_growth (p := 2) (a := 1) (by norm_num) odd_one
    (c := 1) zero_le_one (by rw [Gain_two_one]; linarith)
  exact ⟨⟨2, 1, N⟩, by norm_num, odd_one, by norm_num, hN1,
    by rw [Gain_two_one]; push_cast; linarith, fun M hM => by
      simpa [TDState.θ] using hN M hM⟩

/-- The sequence of states. -/
noncomputable def tdSeq : (k : ℕ) → {s : TDState // s.Inv k}
  | 0 => ⟨TDState.exists_init.choose, TDState.exists_init.choose_spec⟩
  | k + 1 => ⟨((tdSeq k).1.exists_next k (tdSeq k).2).choose,
      ((tdSeq k).1.exists_next k (tdSeq k).2).choose_spec.1⟩

lemma tdSeq_rel (k : ℕ) : (tdSeq k).1.Rel k (tdSeq (k + 1)).1 :=
  ((tdSeq k).1.exists_next k (tdSeq k).2).choose_spec.2


section Limit

/-- `θ_k`, `w_k`, `N_k` along the construction. -/
noncomputable def thK (k : ℕ) : ℝ := (tdSeq k).1.θ
noncomputable def wK (k : ℕ) : ℝ := (tdSeq k).1.w
noncomputable def NK (k : ℕ) : ℕ := (tdSeq k).1.N

lemma NK_pos (k : ℕ) : 1 ≤ NK k := (tdSeq k).2.2.2.2.1

lemma wK_pos (k : ℕ) : 0 < wK k := TDState.w_pos (NK_pos k)

lemma NK_succ (k : ℕ) : NK k + 1 ≤ NK (k + 1) := (tdSeq_rel k).2.2.2.1

lemma NK_mono : Monotone NK := monotone_nat_of_le_succ fun k => by have := NK_succ k; omega

lemma NK_ge (k : ℕ) : k + 1 ≤ NK k := by
  induction k with
  | zero => exact NK_pos 0
  | succ k ih => have := NK_succ k; omega

lemma wK_succ (k : ℕ) : wK (k + 1) ≤ wK k / 2 := by
  have hp := (tdSeq_rel k).1
  have hN := NK_succ k
  unfold wK TDState.w
  have hq : (2 : ℝ) * (3 * 2 ^ (tdSeq k).1.p : ℕ) ≤ (3 * 2 ^ (tdSeq (k + 1)).1.p : ℕ) := by
    have : 2 * (3 * 2 ^ (tdSeq k).1.p) ≤ 3 * 2 ^ (tdSeq (k + 1)).1.p := by
      have : 2 ^ ((tdSeq k).1.p + 1) ≤ 2 ^ (tdSeq (k + 1)).1.p :=
        Nat.pow_le_pow_right (by norm_num) hp
      rw [pow_succ] at this; omega
    exact_mod_cast this
  have hN' : ((tdSeq k).1.N : ℝ) ≤ (tdSeq (k + 1)).1.N := by
    have : (tdSeq k).1.N ≤ (tdSeq (k + 1)).1.N := by unfold NK at hN; omega
    exact_mod_cast this
  have hN0 : (0 : ℝ) < (tdSeq k).1.N := by
    have := NK_pos k; unfold NK at this; exact_mod_cast this
  have : (0 : ℝ) < ((3 * 2 ^ (tdSeq k).1.p : ℕ) : ℝ) := by positivity
  have hN1 : (0 : ℝ) < (tdSeq (k + 1)).1.N := by linarith
  rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
  nlinarith

lemma thK_succ (k : ℕ) : thK k < thK (k + 1) ∧ thK (k + 1) ≤ thK k + wK k / 2 :=
  ⟨(tdSeq_rel k).2.1, (tdSeq_rel k).2.2.1⟩

lemma nest {k j : ℕ} (h : k ≤ j) : thK k ≤ thK j ∧ thK j + wK j ≤ thK k + wK k := by
  induction j, h using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl⟩
  | succ j hkj ih =>
    have h1 := thK_succ j
    have h2 := wK_succ j
    constructor <;> linarith [ih.1, ih.2, wK_pos j]

lemma thK_bdd : BddAbove (Set.range thK) :=
  ⟨thK 0 + wK 0, by
    rintro _ ⟨j, rfl⟩
    have := nest (Nat.zero_le j)
    linarith [wK_pos j]⟩

/-- The limit `α = sup_k θ_k`. -/
noncomputable def alphaTD : ℝ := ⨆ k, thK k

lemma thK_le_alpha (k : ℕ) : thK k ≤ alphaTD := le_ciSup thK_bdd k

lemma alpha_le (k : ℕ) : alphaTD ≤ thK k + wK k := by
  refine ciSup_le fun j => ?_
  rcases le_total k j with h | h
  · have := nest h; linarith [wK_pos j]
  · have := (nest h).1; linarith [wK_pos k]

lemma rr_alpha (k : ℕ) : ∀ n < NK k, rr alphaTD n = rr (thK k) n := by
  intro n hn
  have hinv := (tdSeq k).2
  refine rr_eq_of_close hinv.1 (thK_le_alpha k) n ?_
  have hN0 : (0 : ℝ) < NK k := by exact_mod_cast NK_pos k
  have hn' : (n : ℝ) < NK k := by exact_mod_cast hn
  have hw := wK_pos k
  have h1 : (n : ℝ) * (alphaTD - thK k) ≤ n * wK k :=
    mul_le_mul_of_nonneg_left (by linarith [alpha_le k]) (Nat.cast_nonneg n)
  have h2 : (n : ℝ) * wK k < NK k * wK k := mul_lt_mul_of_pos_right hn' hw
  have h3 : (NK k : ℝ) * wK k = 1 / (2 * (3 * 2 ^ (tdSeq k).1.p : ℕ)) := by
    have : ((tdSeq k).1.N : ℝ) ≠ 0 := by unfold NK at hN0; exact hN0.ne'
    unfold wK TDState.w NK; field_simp
  have h4 : (1 : ℝ) / (2 * (3 * 2 ^ (tdSeq k).1.p : ℕ)) < 1 / (3 * 2 ^ (tdSeq k).1.p : ℕ) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    have : (0 : ℝ) < ((3 * 2 ^ (tdSeq k).1.p : ℕ) : ℝ) := by positivity
    linarith
  calc (n : ℝ) * (alphaTD - (tdSeq k).1.θ) = n * (alphaTD - thK k) := rfl
    _ < 1 / (3 * 2 ^ (tdSeq k).1.p : ℕ) := by linarith

lemma alpha_irrational : Irrational alphaTD := by
  rintro ⟨r, hr⟩
  have hα : alphaTD = (r.num : ℝ) / r.den := by rw [← hr, Rat.cast_def]
  have hD : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hq : (0 : ℝ) < (3 * 2 ^ (tdSeq r.den).1.p : ℕ) := by positivity
  have hpos : 0 < alphaTD - thK r.den := by
    linarith [(thK_succ r.den).1, thK_le_alpha (r.den + 1)]
  have hN0 : (0 : ℝ) < (tdSeq r.den).1.N := by
    have := NK_pos r.den; unfold NK at this; exact_mod_cast this
  have hX : (((r.num * (3 * 2 ^ (tdSeq r.den).1.p : ℕ) - (tdSeq r.den).1.a * r.den : ℤ)) : ℝ) =
      (alphaTD - thK r.den) * r.den * (3 * 2 ^ (tdSeq r.den).1.p : ℕ) := by
    rw [hα, thK, TDState.θ, thq]
    push_cast
    field_simp
  have hX1 : (1 : ℝ) ≤
      (((r.num * (3 * 2 ^ (tdSeq r.den).1.p : ℕ) - (tdSeq r.den).1.a * r.den : ℤ)) : ℝ) := by
    have h0 : (0 : ℝ) <
        (((r.num * (3 * 2 ^ (tdSeq r.den).1.p : ℕ) - (tdSeq r.den).1.a * r.den : ℤ)) : ℝ) := by
      rw [hX]; positivity
    have : (0 : ℤ) < r.num * (3 * 2 ^ (tdSeq r.den).1.p : ℕ) - (tdSeq r.den).1.a * r.den := by
      exact_mod_cast h0
    exact_mod_cast this
  have hup : (alphaTD - thK r.den) * r.den * (3 * 2 ^ (tdSeq r.den).1.p : ℕ) ≤
      wK r.den * r.den * (3 * 2 ^ (tdSeq r.den).1.p : ℕ) := by
    have := alpha_le r.den
    gcongr; linarith
  have hw : wK r.den * r.den * (3 * 2 ^ (tdSeq r.den).1.p : ℕ) =
      r.den / (2 * (tdSeq r.den).1.N) := by
    unfold wK TDState.w; field_simp
  have hNk : (r.den : ℝ) + 1 ≤ (tdSeq r.den).1.N := by
    have := NK_ge r.den; unfold NK at this; exact_mod_cast this
  have : (r.den : ℝ) / (2 * (tdSeq r.den).1.N) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  linarith

/-- Paper, Proposition \ref{IA:prop:TD}: there are an irrational `α` and integers
`1 ≤ N_1 ≤ N_2 ≤ ⋯` with `S_{α,1/6}(M) ≥ i log M` for all `i ≥ 1` and all `M ≥ N_i`. -/
theorem prop_TD : ∃ α : ℝ, Irrational α ∧ ∃ N : ℕ → ℕ, Monotone N ∧ (∀ i, 1 ≤ N i) ∧
    ∀ i : ℕ, 1 ≤ i → ∀ M : ℕ, N i ≤ M → (i : ℝ) * Real.log M ≤ Sab α (1 / 6) M := by
  refine ⟨alphaTD, alpha_irrational, fun i => NK (i - 1), fun i j hij => NK_mono (by omega),
    fun i => NK_pos _, ?_⟩
  intro i hi M hM
  replace hM : NK (i - 1) ≤ M := hM
  have hex : ∃ k, M < NK k := ⟨M, by have := NK_ge M; omega⟩
  set k₁ := Nat.find hex
  have hk₁ : M < NK k₁ := Nat.find_spec hex
  have hk₁i : i ≤ k₁ := by
    by_contra hc
    have : NK k₁ ≤ NK (i - 1) := NK_mono (by omega)
    omega
  obtain ⟨k, hk⟩ : ∃ k, k₁ = k + 1 := ⟨k₁ - 1, by omega⟩
  have hkM : NK k ≤ M := by
    have := Nat.find_min hex (show k < k₁ by omega)
    omega
  rw [hk] at hk₁
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_trans (NK_pos k) hkM
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hM1
  have heq : Sab alphaTD (1 / 6) M = Sf (rr (thK (k + 1))) M :=
    Sf_congr fun n hn => rr_alpha (k + 1) n (by omega)
  rw [heq]
  have hgrow := (tdSeq_rel k).2.2.2.2.2 M hkM
  have hik : (i : ℝ) ≤ k + 1 := by exact_mod_cast (show i ≤ k + 1 by omega)
  calc (i : ℝ) * Real.log M ≤ (k + 1) * Real.log M := mul_le_mul_of_nonneg_right hik hlog
    _ ≤ _ := hgrow

end Limit


/-! ## Rotation blocks (Definition \ref{IA:def:rot}) -/

/-- `R = {n ∈ ℕ : nα mod 1 ∈ J_{λ(n) mod 2}}` with `J₀ = {x : {x - β} ∈ [0, 1/2)}` and
`J₁ = 𝕋 \ J₀`, `λ(n) = ⌊log₂ n⌋`. -/
def Rset (α β : ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ (Int.fract (n * α - β) < 1 / 2 ↔ Even (Nat.log 2 n))}

/-- `G = ⋃_{i ≥ 1} [2^i - w_i, 2^i + w_i)`. -/
def Gset (w : ℕ → ℕ) : Set ℕ := {n | ∃ i, 1 ≤ i ∧ 2 ^ i - w i ≤ n ∧ n < 2 ^ i + w i}

/-- `E = R \ G`. -/
def Eset (α β : ℝ) (w : ℕ → ℕ) : Set ℕ := Rset α β \ Gset w

lemma fract_lt_half_iff (y : ℝ) : Int.fract y < 1 / 2 ↔ Even ⌊2 * y⌋ := by
  have h := rho_eq_floor y
  unfold rho at h
  constructor
  · intro hy
    rw [if_pos hy] at h
    by_contra hc
    rw [if_neg hc] at h; norm_num at h
  · intro hy
    rw [if_pos hy] at h
    by_contra hc
    rw [if_neg hc] at h; norm_num at h

lemma floor_two_add_mod {x x' : ℝ} {k : ℤ} (hx : ⌊4 * x⌋ % 4 = k) (hx' : ⌊4 * x'⌋ % 4 = k) :
    ⌊2 * (x + x')⌋ % 2 = k % 2 := by
  have h1 := Int.emod_add_mul_ediv ⌊4 * x⌋ 4
  have h2 := Int.emod_add_mul_ediv ⌊4 * x'⌋ 4
  rw [hx] at h1
  rw [hx'] at h2
  set j := ⌊4 * x⌋ / 4
  set j' := ⌊4 * x'⌋ / 4
  have hf : ⌊2 * (x + x')⌋ = 2 * (j + j') + k := by
    rw [Int.floor_eq_iff]
    have a1 := Int.floor_le (4 * x)
    have a2 := Int.lt_floor_add_one (4 * x)
    have a3 := Int.floor_le (4 * x')
    have a4 := Int.lt_floor_add_one (4 * x')
    rw [← h1] at a1 a2
    rw [← h2] at a3 a4
    push_cast at a1 a2 a3 a4 ⊢
    constructor <;> linarith
  rw [hf]; omega

lemma log_two_mul_add {d t : ℕ} (hd : 1 ≤ d) (ht : t ≤ 1) :
    Nat.log 2 (2 * d + t) = Nat.log 2 d + 1 := by
  have h1 := Nat.pow_log_le_self 2 (by omega : d ≠ 0)
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) d
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · rw [pow_succ]; omega
  · rw [pow_succ, pow_succ] at *; omega

lemma exists_infinite_fiber {D : Set ℕ} (hD : D.Infinite) {β : Type*} (f : ℕ → β)
    (hf : (f '' D).Finite) : ∃ y, (D ∩ f ⁻¹' {y}).Infinite := by
  by_contra h
  simp only [not_exists, Set.not_infinite] at h
  apply hD
  have : D = ⋃ y ∈ f '' D, D ∩ f ⁻¹' {y} := by
    ext x; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_image]
    exact ⟨fun hx => ⟨f x, ⟨x, hx, rfl⟩, hx, rfl⟩, fun ⟨_, _, hx, _⟩ => hx⟩
  rw [this]
  exact hf.biUnion fun y _ => h y

/-- Paper, Proposition \ref{IA:prop:rot}: if `w_i → ∞` there are no infinite `D ⊆ ℕ₀` and
`t ∈ {0, 1}` with `D + D + t ⊆ E`. -/
theorem prop_rot (α β : ℝ) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop) (D : Set ℕ)
    (hD : D.Infinite) (t : ℕ) (ht : t ≤ 1) : ¬ ∀ d ∈ D, ∀ d' ∈ D, d + d' + t ∈ Eset α β w := by
  intro hDE
  -- remove `0`
  set D₁ := D \ {0}
  have hD₁ : D₁.Infinite := hD.sdiff (Set.finite_singleton 0)
  -- the points `z_d = dα + tα/2`
  set z : ℕ → ℝ := fun d => d * α + t * α / 2
  have hz : ∀ d d' : ℕ, ((d + d' + t : ℕ) : ℝ) * α - β = (z d - β / 2) + (z d' - β / 2) := by
    intro d d'; simp only [z]; push_cast; ring
  -- pigeonhole on `(λ(d) mod 2, ⌊4(z_d - β/2)⌋ mod 4)`
  set κ : ℕ → ℕ × ℤ := fun d => (Nat.log 2 d % 2, ⌊4 * (z d - β / 2)⌋ % 4)
  have hκ : (κ '' D₁).Finite := by
    refine Set.Finite.subset (Finset.finite_toSet (Finset.range 2 ×ˢ Finset.Ico (0 : ℤ) 4)) ?_
    rintro _ ⟨d, -, rfl⟩
    simp only [κ, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range,
      Finset.mem_Ico]
    omega
  obtain ⟨⟨σ, k⟩, hD₂⟩ := exists_infinite_fiber hD₁ κ hκ
  set D₂ := D₁ ∩ κ ⁻¹' {(σ, k)}
  have hmem : ∀ d ∈ D₂, d ∈ D ∧ 1 ≤ d ∧ Nat.log 2 d % 2 = σ ∧ ⌊4 * (z d - β / 2)⌋ % 4 = k := by
    rintro d ⟨⟨hd, hd0⟩, hκd⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, κ, Prod.mk.injEq] at hκd
    simp only [Set.mem_singleton_iff] at hd0
    exact ⟨hd, by omega, hκd.1, hκd.2⟩
  -- membership of `d + d' + t` in `R` pins down the parity of `λ`
  have hR : ∀ d ∈ D₂, ∀ d' ∈ D₂, (Even (Nat.log 2 (d + d' + t)) ↔ k % 2 = 0) := by
    intro d hd d' hd'
    have hE := hDE d (hmem d hd).1 d' (hmem d' hd').1
    have hRn := hE.1.2
    rw [fract_lt_half_iff, hz] at hRn
    rw [← hRn, Int.even_iff, floor_two_add_mod (hmem d hd).2.2.2 (hmem d' hd').2.2.2]
  -- step (iv): the diagonal element `2d + t` gives `k ≡ 1 - σ`
  obtain ⟨d₀, hd₀⟩ := hD₂.nonempty
  have hσk : (σ + 1) % 2 = 0 ↔ k % 2 = 0 := by
    have := hR d₀ hd₀ d₀ hd₀
    rw [show d₀ + d₀ + t = 2 * d₀ + t by ring, log_two_mul_add (hmem d₀ hd₀).2.1 ht,
      Nat.even_iff] at this
    rw [← this, ← (hmem d₀ hd₀).2.2.1]; omega
  -- step (v)-(vi)
  obtain ⟨I, hI⟩ := (tendsto_atTop_atTop.mp hw) (d₀ + t + 1)
  obtain ⟨d', hd', hd'big⟩ := hD₂.exists_gt (d₀ + 2 ^ I)
  have h2I : 1 ≤ 2 ^ I := Nat.one_le_two_pow
  obtain ⟨n, hn_def⟩ : ∃ n, n = d₀ + d' + t := ⟨_, rfl⟩
  have hn := hDE d₀ (hmem d₀ hd₀).1 d' (hmem d' hd').1
  rw [← hn_def] at hn
  have hpar : ¬ (Nat.log 2 n % 2 = Nat.log 2 d' % 2) := by
    have h1 := hR d₀ hd₀ d' hd'
    rw [← hn_def, Nat.even_iff, ← hσk, ← (hmem d' hd').2.2.1] at h1
    omega
  have hlog_le : Nat.log 2 d' ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
  have hlog_lt : Nat.log 2 d' < Nat.log 2 n := lt_of_le_of_ne hlog_le (fun h => hpar (by rw [h]))
  set i := Nat.log 2 n
  have hi1 : 2 ^ i ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hdi : d' < 2 ^ i := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) d'
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) hlog_lt)
  have hiI : I ≤ i := by
    have : 2 ^ I ≤ d' := by omega
    have : I ≤ Nat.log 2 d' := Nat.le_log_of_pow_le (by norm_num) this
    omega
  have hi0 : 1 ≤ i := by
    by_contra h
    have : i = 0 := by omega
    rw [this] at hdi; omega
  have hnG : n ∉ Gset w := hn.2
  have : n ≥ 2 ^ i + w i := by
    by_contra h
    exact hnG ⟨i, hi0, by omega, by omega⟩
  have := hI i hiI
  omega


/-! ## Counting (Lemmas \ref{IA:lem:parity} and \ref{IA:lem:excess}) -/

/-- `A = (2ℕ - 1) ∪ 2E`. -/
def Aset (E : Set ℕ) : Set ℕ := {k | Odd k} ∪ {k | ∃ e ∈ E, k = 2 * e}

/-- Paper, Lemma \ref{IA:lem:parity} (first part): if `B + B ⊆ (2ℕ - 1) ∪ 2E` for an infinite
`B`, then `D + D + t ⊆ E` for some infinite `D ⊆ ℕ₀` and `t ∈ {0, 1}`. -/
lemma parity_reduce (E : Set ℕ) (B : Set ℕ) (hB : B.Infinite) (hBA : sumset B B ⊆ Aset E) :
    ∃ D : Set ℕ, D.Infinite ∧ ∃ t ≤ 1, ∀ d ∈ D, ∀ d' ∈ D, d + d' + t ∈ E := by
  have key : ∀ t ≤ 1, ∀ B' ⊆ B, B'.Infinite → (∀ b ∈ B', b % 2 = t) →
      ∃ D : Set ℕ, D.Infinite ∧ ∃ t ≤ 1, ∀ d ∈ D, ∀ d' ∈ D, d + d' + t ∈ E := by
    intro t ht B' hB'B hB' hpar
    refine ⟨(fun b => b / 2) '' B', hB'.image fun b hb b' hb' h => ?_, t, ht, ?_⟩
    · have := hpar b hb; have := hpar b' hb'; omega
    · rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
      have hb1 := hpar b hb
      have hb2 := hpar b' hb'
      rcases hBA ⟨b, hB'B hb, b', hB'B hb', rfl⟩ with h | ⟨e, he, hee⟩
      · exfalso; have h' : Odd (b + b') := h; rw [Nat.odd_iff] at h'; omega
      · have : e = b / 2 + b' / 2 + t := by omega
        rw [← this]; exact he
  have hsplit : B = {b ∈ B | b % 2 = 0} ∪ {b ∈ B | b % 2 = 1} := by
    ext b
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hb; rcases Nat.mod_two_eq_zero_or_one b with h | h
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, h⟩
    · rintro (⟨hb, -⟩ | ⟨hb, -⟩) <;> exact hb
  rw [hsplit, Set.infinite_union] at hB
  rcases hB with h | h
  · exact key 0 (by norm_num) _ (fun b hb => hb.1) h fun b hb => hb.2
  · exact key 1 le_rfl _ (fun b hb => hb.1) h fun b hb => hb.2

lemma card_filter_odd (N : ℕ) : ((range (N + 1)).filter Odd).card = (N + 1) / 2 := by
  induction N with
  | zero => decide
  | succ N ih =>
    rw [range_add_one (n := N + 1), filter_insert]
    by_cases h : Odd (N + 1)
    · rw [if_pos h, card_insert_of_notMem (by simp), ih]
      rw [Nat.odd_iff] at h; omega
    · rw [if_neg h, ih]
      rw [Nat.not_odd_iff_even, Nat.even_iff] at h; omega

open Classical in
/-- Paper, Lemma \ref{IA:lem:parity} (counting): `|A ∩ [N]| = ⌈N/2⌉ + |E ∩ [1, ⌊N/2⌋]|`. -/
lemma ncard_Aset (E : Set ℕ) (hE : 0 ∉ E) (N : ℕ) :
    (Aset E ∩ Set.Icc 1 N).ncard = (N + 1) / 2 + ((Ico 1 (N / 2 + 1)).filter (· ∈ E)).card := by
  set Fo := (range (N + 1)).filter Odd
  set Fe := ((Ico 1 (N / 2 + 1)).filter (· ∈ E)).image (fun j => 2 * j)
  have hset : Aset E ∩ Set.Icc 1 N = ↑(Fo ∪ Fe) := by
    ext k
    simp only [Aset, Set.mem_inter_iff, Set.mem_union, Set.mem_Icc, Set.mem_ofPred_eq, coe_union,
      coe_filter, coe_image, mem_range, mem_Ico, Fo, Fe, Set.mem_image]
    constructor
    · rintro ⟨h | ⟨e, he, rfl⟩, h1, h2⟩
      · exact Or.inl ⟨by omega, h⟩
      · refine Or.inr ⟨e, ⟨⟨?_, by omega⟩, he⟩, rfl⟩
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · exact absurd (h0 ▸ he) hE
        · exact h0
    · rintro (⟨h1, h2⟩ | ⟨e, ⟨⟨h1, h2⟩, he⟩, rfl⟩)
      · refine ⟨Or.inl h2, ?_, by omega⟩
        obtain ⟨r, rfl⟩ := h2; omega
      · exact ⟨Or.inr ⟨e, he, rfl⟩, by omega, by omega⟩
  have hdisj : Disjoint Fo Fe := by
    rw [disjoint_left]
    intro k hk hk'
    simp only [Fo, Fe, mem_filter, mem_image] at hk hk'
    obtain ⟨e, -, rfl⟩ := hk'
    exact (Nat.not_odd_iff_even.mpr (even_two_mul e)) hk.2
  rw [hset, Set.ncard_coe_finset, card_union_of_disjoint hdisj, card_filter_odd,
    card_image_of_injective _ (fun a b h => by omega)]

lemma indicator_R (α β : ℝ) {n : ℕ} (hn : 1 ≤ n) [Decidable (n ∈ Rset α β)] :
    (if n ∈ Rset α β then (1 : ℝ) else 0) - 1 / 2 = eps n * rho (n * α - β) := by
  unfold eps rho
  rcases Nat.even_or_odd (Nat.log 2 n) with h | h
  · rw [h.neg_one_pow, one_mul]
    by_cases hf : Int.fract (n * α - β) < 1 / 2
    · have : n ∈ Rset α β := ⟨hn, iff_of_true hf h⟩
      rw [if_pos this, if_pos hf]; norm_num
    · have : n ∉ Rset α β := fun h' => hf (h'.2.mpr h)
      rw [if_neg this, if_neg hf]; norm_num
  · rw [h.neg_one_pow]
    have h' : ¬ Even (Nat.log 2 n) := Nat.not_even_iff_odd.mpr h
    by_cases hf : Int.fract (n * α - β) < 1 / 2
    · have : n ∉ Rset α β := fun h'' => h' (h''.2.mp hf)
      rw [if_neg this, if_pos hf]; norm_num
    · have : n ∈ Rset α β := ⟨hn, iff_of_false hf h'⟩
      rw [if_pos this, if_neg hf]; norm_num

open Classical in
lemma card_R (α β : ℝ) (M : ℕ) :
    (((Ico 1 M).filter (· ∈ Rset α β)).card : ℝ) = ((M - 1 : ℕ) : ℝ) / 2 + Sab α β M := by
  rw [card_filter]
  push_cast
  have : ∑ n ∈ Ico 1 M, (if n ∈ Rset α β then (1 : ℝ) else 0) =
      ∑ n ∈ Ico 1 M, ((1 : ℝ) / 2 + eps n * rho (n * α - β)) := by
    refine sum_congr rfl fun n hn => ?_
    rw [← indicator_R α β (mem_Ico.mp hn).1]; ring
  rw [this, sum_add_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul]
  unfold Sab Sf
  ring

open Classical in
/-- Paper, Lemma \ref{IA:lem:excess}, in the form used: `|E ∩ [1, M)| ≥ (M - 1)/2 + S(M) - g`
whenever every index `i` whose gap interval meets `[1, M)` satisfies `i ≤ K`, with
`g = ∑_{i=1}^{K} 2 w_i`. -/
lemma excess (α β : ℝ) (w : ℕ → ℕ) (M K : ℕ)
    (hK : ∀ i, 1 ≤ i → 2 ^ i - w i < M → i ≤ K) :
    ((M - 1 : ℕ) : ℝ) / 2 + Sab α β M - ∑ i ∈ Icc 1 K, (2 * w i : ℝ) ≤
      ((Ico 1 M).filter (· ∈ Eset α β w)).card := by
  have h1 : (Ico 1 M).filter (· ∈ Rset α β) ⊆
      (Ico 1 M).filter (· ∈ Eset α β w) ∪ (Ico 1 M).filter (· ∈ Gset w) := by
    intro n hn
    simp only [mem_filter, mem_union] at hn ⊢
    by_cases hG : n ∈ Gset w
    · exact Or.inr ⟨hn.1, hG⟩
    · exact Or.inl ⟨hn.1, hn.2, hG⟩
  have h2 : (Ico 1 M).filter (· ∈ Gset w) ⊆
      (Icc 1 K).biUnion (fun i => Ico (2 ^ i - w i) (2 ^ i + w i)) := by
    intro n hn
    simp only [mem_filter, mem_Ico] at hn
    obtain ⟨⟨-, hnM⟩, i, hi, h1, h2⟩ := hn
    simp only [mem_biUnion, mem_Icc, mem_Ico]
    exact ⟨i, ⟨hi, hK i hi (by omega)⟩, h1, h2⟩
  have h3 : (((Icc 1 K).biUnion (fun i => Ico (2 ^ i - w i) (2 ^ i + w i))).card : ℝ) ≤
      ∑ i ∈ Icc 1 K, (2 * w i : ℝ) := by
    refine (Nat.cast_le.mpr (card_biUnion_le)).trans ?_
    push_cast
    refine sum_le_sum fun i _ => ?_
    rw [Nat.card_Ico]
    have : 2 ^ i + w i - (2 ^ i - w i) ≤ 2 * w i := by omega
    exact_mod_cast this
  have hR := card_R α β M
  have hc1 := card_le_card h1
  have hc2 := card_le_card h2
  have hc3 := card_union_le ((Ico 1 M).filter (· ∈ Eset α β w)) ((Ico 1 M).filter (· ∈ Gset w))
  have : (((Ico 1 M).filter (· ∈ Rset α β)).card : ℝ) ≤
      ((Ico 1 M).filter (· ∈ Eset α β w)).card + ((Ico 1 M).filter (· ∈ Gset w)).card := by
    exact_mod_cast hc1.trans hc3
  have : (((Ico 1 M).filter (· ∈ Gset w)).card : ℝ) ≤
      (((Icc 1 K).biUnion (fun i => Ico (2 ^ i - w i) (2 ^ i + w i))).card : ℝ) := by
    exact_mod_cast hc2
  linarith


/-! ## Proof of Theorem \ref{IA:thm:u32a}\ref{IA:it:u32a-all} -/

section Final

variable (Nf : ℕ → ℕ)

/-- `ψ₀(M) = max {i ≤ M : N_i ≤ M}` (and `0` if there is none). -/
def psi0 (M : ℕ) : ℕ := Nat.findGreatest (fun i => Nf i ≤ M) M

lemma psi0_mono : Monotone (psi0 Nf) := fun _ _ h =>
  Nat.findGreatest_mono (fun _ hi => le_trans hi h) h

lemma psi0_ge {i M : ℕ} (h1 : Nf i ≤ M) (h2 : i ≤ M) : i ≤ psi0 Nf M := Nat.le_findGreatest h2 h1

lemma psi0_spec {M : ℕ} (h : psi0 Nf M ≠ 0) : Nf (psi0 Nf M) ≤ M :=
  Nat.findGreatest_of_ne_zero (P := fun i => Nf i ≤ M) (n := M) rfl h

/-- The gap widths `w_i = max(1, min(⌊2^i/4⌋, ⌊ψ₀(2^{i-1})/16⌋))`. -/
def wseq (i : ℕ) : ℕ := max 1 (min (2 ^ i / 4) (psi0 Nf (2 ^ (i - 1)) / 16))

lemma wseq_le_pow {i : ℕ} (hi : 1 ≤ i) : wseq Nf i ≤ 2 ^ (i - 1) := by
  have h1 : 2 ^ i = 2 * 2 ^ (i - 1) := by rw [← pow_succ']; congr 1; omega
  have h2 : 1 ≤ 2 ^ (i - 1) := Nat.one_le_two_pow
  unfold wseq
  have : min (2 ^ i / 4) (psi0 Nf (2 ^ (i - 1)) / 16) ≤ 2 ^ i / 4 := min_le_left _ _
  omega

lemma wseq_le_psi {i M : ℕ} (hM : 2 ^ (i - 1) ≤ M) (h16 : 16 ≤ psi0 Nf M) :
    wseq Nf i ≤ psi0 Nf M / 16 := by
  have h1 := psi0_mono Nf hM
  unfold wseq
  have : min (2 ^ i / 4) (psi0 Nf (2 ^ (i - 1)) / 16) ≤ psi0 Nf (2 ^ (i - 1)) / 16 :=
    min_le_right _ _
  have : psi0 Nf (2 ^ (i - 1)) / 16 ≤ psi0 Nf M / 16 := Nat.div_le_div_right h1
  have : 1 ≤ psi0 Nf M / 16 := by omega
  omega

lemma wseq_tendsto : Tendsto (wseq Nf) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro K
  refine ⟨Nf (16 * K) + 16 * K + K + 2, fun i hi => ?_⟩
  have h1 : Nf (16 * K) + 16 * K ≤ 2 ^ (i - 1) := by
    have := Nat.lt_two_pow_self (n := i - 1); omega
  have h2 : 16 * K ≤ psi0 Nf (2 ^ (i - 1)) := psi0_ge Nf (by omega) (by omega)
  have h3 : 4 * K ≤ 2 ^ i := by
    have : 2 ^ i = 4 * 2 ^ (i - 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have := Nat.lt_two_pow_self (n := i - 2); omega
  unfold wseq
  have : K ≤ min (2 ^ i / 4) (psi0 Nf (2 ^ (i - 1)) / 16) :=
    le_min (by omega) (by omega)
  exact le_trans this (le_max_right _ _)

end Final

/-- Paper, Theorem \ref{IA:thm:u32a}\ref{IA:it:u32a-all}: there are a set `A ⊆ ℕ` and a
non-decreasing unbounded function `ψ : ℕ → [0, ∞)` such that
`|A ∩ [N]| ≥ (3/4) N + ψ(N) log N` for all sufficiently large `N`, and `B + B ⊄ A` for every
infinite `B ⊆ ℕ`. -/
theorem thm_u32a_b : ∃ A : Set ℕ, 0 ∉ A ∧ ∃ ψ : ℕ → ℝ, (∀ N, 0 ≤ ψ N) ∧ Monotone ψ ∧
    ¬ BddAbove (Set.range ψ) ∧
    (∀ᶠ N : ℕ in atTop, 3 / 4 * (N : ℝ) + ψ N * Real.log N ≤ (A ∩ Set.Icc 1 N).ncard) ∧
    ∀ B : Set ℕ, B.Infinite → ¬ sumset B B ⊆ A := by
  classical
  obtain ⟨α, -, Nf, -, -, hS⟩ := prop_TD
  set w := wseq Nf
  set E := Eset α (1 / 6) w
  have hE0 : 0 ∉ E := fun h => by have := h.1.1; omega
  refine ⟨Aset E, ?_, fun N => (psi0 Nf (N / 2 + 1) : ℝ) / 4, fun N => by positivity,
    fun N N' h => by
      have := psi0_mono Nf (show N / 2 + 1 ≤ N' / 2 + 1 by omega)
      simp only; gcongr, ?_, ?_, ?_⟩
  · rintro (h | ⟨e, he, h0⟩)
    · exact Nat.not_odd_zero h
    · have : e = 0 := by omega
      exact hE0 (this ▸ he)
  · rintro ⟨C, hC⟩
    set i := ⌈4 * C⌉₊ + 1
    have h1 := hC ⟨2 * (Nf i + i), rfl⟩
    have h2 : i ≤ psi0 Nf (2 * (Nf i + i) / 2 + 1) := psi0_ge Nf (by omega) (by omega)
    have h3 : (i : ℝ) ≤ psi0 Nf (2 * (Nf i + i) / 2 + 1) := by exact_mod_cast h2
    have h4 := Nat.le_ceil (4 * C)
    have h5 : (i : ℝ) = ⌈4 * C⌉₊ + 1 := by simp only [i]; push_cast; ring
    simp only at h1
    linarith
  · -- the counting estimate
    have hl2 := Real.log_two_gt_d9
    have hl2' : Real.log 2 < 1 := log_two_lt_one
    have hEbound : ∀ M : ℕ, Nf 16 + 16 ≤ M →
        ((M - 1 : ℕ) : ℝ) / 2 + (psi0 Nf M : ℝ) * Real.log M / 2 + 1 ≤
          ((Ico 1 M).filter (· ∈ E)).card := by
      intro M hM
      set ψ := psi0 Nf M
      have hψ16 : 16 ≤ ψ := psi0_ge Nf (by omega) (by omega)
      have hSM := hS ψ (by omega) M (psi0_spec Nf (by omega))
      set K := Nat.log 2 M + 1
      have hK : ∀ i, 1 ≤ i → 2 ^ i - w i < M → i ≤ K := by
        intro i hi hlt
        have h1 := wseq_le_pow Nf hi
        have h2 : 2 ^ i = 2 * 2 ^ (i - 1) := by rw [← pow_succ']; congr 1; omega
        have : 2 ^ (i - 1) ≤ M := by simp only [w] at hlt; omega
        have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) this
        omega
      have hex := excess α (1 / 6) w M K hK
      have hsum : ∑ i ∈ Icc 1 K, (2 * w i : ℝ) ≤ K * (2 * ((ψ / 16 : ℕ) : ℝ)) := by
        have : ∀ i ∈ Icc 1 K, (2 * w i : ℝ) ≤ 2 * ((ψ / 16 : ℕ) : ℝ) := by
          intro i hi
          rw [mem_Icc] at hi
          have : 2 ^ (i - 1) ≤ M := by
            have h1 : 2 ^ (i - 1) ≤ 2 ^ Nat.log 2 M := Nat.pow_le_pow_right (by norm_num) (by omega)
            exact h1.trans (Nat.pow_log_le_self 2 (by omega))
          have := wseq_le_psi Nf this hψ16
          have : (w i : ℝ) ≤ (ψ / 16 : ℕ) := by exact_mod_cast this
          linarith
        refine (sum_le_sum this).trans ?_
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul, show K + 1 - 1 = K by omega]
      have hdiv : ((ψ / 16 : ℕ) : ℝ) ≤ (ψ : ℝ) / 16 := Nat.cast_div_le
      have hL2 : (Nat.log 2 M : ℝ) * Real.log 2 ≤ Real.log M := by
        have h := Nat.pow_log_le_self 2 (by omega : M ≠ 0)
        have : Real.log ((2 : ℝ) ^ Nat.log 2 M) ≤ Real.log M :=
          Real.log_le_log (by positivity) (by exact_mod_cast h)
        rwa [Real.log_pow] at this
      have hlogM : 1 ≤ Real.log M := by
        have : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
        rw [Real.le_log_iff_exp_le this]
        have : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
        have : (3 : ℝ) ≤ M := by exact_mod_cast (by omega : 3 ≤ M)
        linarith
      have hψ' : (16 : ℝ) ≤ ψ := by exact_mod_cast hψ16
      have hK' : (K : ℝ) = Nat.log 2 M + 1 := by simp only [K]; push_cast; ring
      have hL2' : (Nat.log 2 M : ℝ) ≤ 3 / 2 * Real.log M := by nlinarith
      have hfin : (K : ℝ) * (2 * ((ψ / 16 : ℕ) : ℝ)) ≤ K * ψ / 8 := by
        have : (0 : ℝ) ≤ K := by positivity
        nlinarith
      have : (ψ : ℝ) * (4 * Real.log M - Nat.log 2 M - 1) ≥ 24 := by nlinarith
      nlinarith
    rw [eventually_atTop]
    refine ⟨2 * (Nf 16 + 16) + 4, fun N hN => ?_⟩
    rw [ncard_Aset E hE0 N]
    have hb := hEbound (N / 2 + 1) (by omega)
    rw [show N / 2 + 1 - 1 = N / 2 by omega] at hb
    have h1 : (N : ℝ) / 2 ≤ ((N + 1) / 2 : ℕ) := by
      have : N ≤ 2 * ((N + 1) / 2) := by omega
      have : (N : ℝ) ≤ 2 * ((N + 1) / 2 : ℕ) := by exact_mod_cast this
      linarith
    have h2 : ((N : ℝ) - 1) / 2 ≤ (N / 2 : ℕ) := by
      have : N ≤ 2 * (N / 2) + 1 := by omega
      have : (N : ℝ) ≤ 2 * (N / 2 : ℕ) + 1 := by exact_mod_cast this
      linarith
    have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast (by omega : 4 ≤ N)
    have h3 : Real.log N / 2 ≤ Real.log ((N / 2 + 1 : ℕ) : ℝ) := by
      have hM : (N : ℝ) / 2 ≤ ((N / 2 + 1 : ℕ) : ℝ) := by
        have : N ≤ 2 * (N / 2 + 1) := by omega
        have : (N : ℝ) ≤ 2 * ((N / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have : Real.log ((N : ℝ) / 2) ≤ Real.log ((N / 2 + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) hM
      rw [Real.log_div (by positivity) (by norm_num)] at this
      have : Real.log 4 ≤ Real.log N := Real.log_le_log (by norm_num) hN4
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      linarith
    have hψ0 : (0 : ℝ) ≤ psi0 Nf (N / 2 + 1) := Nat.cast_nonneg _
    have : (psi0 Nf (N / 2 + 1) : ℝ) * (Real.log N / 2) ≤
        psi0 Nf (N / 2 + 1) * Real.log ((N / 2 + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left h3 hψ0
    show 3 / 4 * (N : ℝ) + (psi0 Nf (N / 2 + 1) : ℝ) / 4 * Real.log N ≤ _
    push_cast at hb this ⊢
    nlinarith
  · intro B hB hBA
    obtain ⟨D, hD, t, ht, hDE⟩ := parity_reduce E B hB hBA
    exact prop_rot α (1 / 6) w (wseq_tendsto Nf) D hD t ht hDE

end Kmrr25.S32a
