import Kmrr25.Basic

/-!
# Logarithmic equidistribution and Question 3.24

Paper, Section \ref{IA:sec:q324}: Proposition \ref{IA:prop:KR}, Theorem \ref{IA:thm:324}, and the
negative answer to Question \ref{IA:q:324}.

Question 3.24 of the survey asks whether every `A ⊆ ℕ` with `d_log(A) > 0` satisfying
`(21)`: `d_log({n ∈ A : {θ log n} ∈ (a, b)}) = d_log(A) (b - a)` for all `θ > 0` and all intervals
`(a, b) ⊆ [0, 1)`, contains `B + B + t` for some `t ≥ 0` and some infinite `B ⊆ ℕ`.

## Main results

* `prop_KR` — Proposition \ref{IA:prop:KR}: the set of Kousek and Radić
  `A_KR = (A^{(1)} ∩ 2ℕ) ∪ (A^{(2)} ∩ (2ℕ + 1))`, with `A^{(1)} = ⋃_{n ≥ 1} [4^n, (2 - 1/n) 4^n)`
  and `A^{(2)} = ⋃_{n ≥ 1} [(2 + 1/n) 4^n, 4^{n+1})`, has natural density `1/2`
  (`AKR_natDensity`), contains no `B + B + t` for any `t ∈ ℤ` and infinite `B` (`AKR_no_BBt`), has
  logarithmic density `1/2` (`AKR_logDensity`) and satisfies `(21)` (`AKR_eq21`).
* `thm324` — Theorem \ref{IA:thm:324}: for `0 < η < 1/2`, `f(x) = x/2 + √x` and
  `A = {n ∈ ℕ : {f(log₂ n)} ∈ [0, 1/2 - η)}`, `d_log(A) = 1/2 - η` (`A324_logDensity`), `A`
  satisfies `(21)` (`A324_eq21`), and `A` contains no `B + B + t` with `t ∈ ℤ`, `B` infinite
  (`A324_no_BBt`).
* `not_question324` (via `A_KR`) and `not_question324'` (via the set of Theorem
  \ref{IA:thm:324}) — the answer to Question 3.24, stated as the `Prop` `Question324`, is negative.

Everything is proved; no result of this file is conditional.

## Conventions

* The paper's `ℕ` is `{1, 2, …}`: the sets `A_KR` and `A` do not contain `0`, and in
  `Question324` the set `B` consists of positive integers. In the non-existence statements the
  set `B` ranges over all infinite subsets of `{0, 1, 2, …}` and `t` over `ℤ`, which contains the
  paper's statements; `B + B + t ⊆ A` (`SumsetIn B t A`) means that every integer `b + b' + t`
  (`b, b' ∈ B`) is an element of `A`.
* `HasLogDensity A d` means `(1 / log N) ∑_{n=1}^{N} 𝟙_A(n)/n → d` (natural logarithm), and
  `HasNatDensity A d` means `|A ∩ [1, N]| / N → d`. The interval condition `(a, b) ⊆ [0, 1)` is
  `0 ≤ a < b ≤ 1`, and `{x}` is `Int.fract x`.

## Proofs

The proofs are elementary and avoid the continuous measure-theoretic route of the paper
(Lemma \ref{IA:lem:logsum} and Lemma \ref{IA:lem:oscint}), working directly with the discrete
sums `∑ 1/n`.

* *Linear phases.* With `Ψ(z) = ⌊z⌋(⌊z⌋ - 1)/2 + ⌊z⌋ {z}` (an antiderivative of `⌊z⌋`) and
  `Φ_{a,b}(y) = Ψ(y - a) - Ψ(y - b)` (an antiderivative of `1[{y} ∈ [a, b)]`), the sum
  `∑_{n ≤ N} 1[{θ log n} ∈ [a, b)]/n` telescopes against `θ⁻¹ Φ_{a,b}(θ log n)` up to an error
  supported on the `O(log N)` integers where `⌊θ log n - a⌋` or `⌊θ log n - b⌋` jumps; this gives
  `(b - a) log N + o(log N)` (`logSmall_sum_gθ`).
* *`A_KR`.* Up to a set `W` of logarithmic density `0`, `A_KR` is
  `{n ≥ 4 : n ≡ ⌊log₂ n⌋ (mod 2)}`, whose indicator is
  `(1 + (-1)^n (-1)^{⌊log₂ n⌋})/2`; the alternating part is `o(log N)` by summation by parts,
  because `(-1)^{⌊log₂ n⌋} 1[{θ log n} ∈ [a, b)]` changes only `O(log N)` times
  (`logSmall_AKR`). The natural density is obtained in the same way (`AKR_natDensity`).
* *Theorem \ref{IA:thm:324}.* Writing `F_n = f(log₂ n)`, the same telescoping applied to the phase
  `F_n` gives `d_log(A) = c = 1/2 - η` (`logSmall_T0`). For `(21)`, summation by parts against the
  jumps of `⌊F_n⌋` and `⌊F_n - c⌋` reduces the joint sum to averages of the periodic function
  `τ({y}) = {y} - {y}²` along the sequences `θ log 2 · f⁻¹(m + r)` (`r ∈ {0, c}`), i.e. along
  `α m - √(γ m + δ) + σ` (`jump_sum`). These averages tend to `1/6` for every `α` and every
  `γ > 0` (`tendsto_τ_avg`): by the Fourier series of the Bernoulli polynomial `B₂`
  (`hasSum_one_div_nat_pow_mul_cos`) and dominated convergence it suffices that the Weyl sums
  `∑_{m<M} e(k(α m + √(γ m + δ)))` are `O(1 + √M)` (`weyl_bound`), which follows by summation by
  parts against the geometric sums of `e(kαm)` if `kα ∉ ℤ`, and against the weights
  `1/(e(kΔ_m) - 1)`, `Δ_m = √(γ(m+1) + δ) - √(γ m + δ)`, if `kα ∈ ℤ`. This plays the role of
  Lemma \ref{IA:lem:oscint}.

## Not covered

The further counterexamples mentioned in the paper are not formalized: the colour class of
logarithmic density `1/3` from the remark after Proposition 5.1 of Kousek and Radić (residues
modulo `3`), and the set `A_η` of Section \ref{IA:sec:q323} in Remark \ref{IA:rem:324}(ii).
Theorem 1.3 of Kousek and Radić (optimality of the value `1/2`), quoted in the discussion, is not
formalized either.
-/

open Real Filter Topology Finset

namespace Kmrr25.Q324

/-! ## Definitions -/

/-- `A ⊆ ℕ` has logarithmic density `d`:
`(1 / log N) ∑_{n=1}^{N} 𝟙_A(n) / n → d` as `N → ∞`. -/
def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, A.indicator (fun n : ℕ => (1 : ℝ) / n) n) /
    Real.log N) atTop (𝓝 d)

/-- `A ⊆ ℕ` has natural density `d`: `|A ∩ [1, N]| / N → d` as `N → ∞`. -/
def HasNatDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, A.indicator (fun _ : ℕ => (1 : ℝ)) n) / N)
    atTop (𝓝 d)

/-- The integer `z` is (the image of) an element of `A`. -/
def InA (A : Set ℕ) (z : ℤ) : Prop := ∃ n ∈ A, (n : ℤ) = z

/-- `B + B + t ⊆ A` (unrestricted sumset, `t ∈ ℤ`): `b + b' + t ∈ A` for all `b, b' ∈ B`. -/
def SumsetIn (B : Set ℕ) (t : ℤ) (A : Set ℕ) : Prop :=
  ∀ b ∈ B, ∀ b' ∈ B, InA A ((b : ℤ) + b' + t)

/-- `A^{(1)} = ⋃_{n ≥ 1} [4^n, (2 - 1/n) 4^n)` (intersected with `ℕ`). -/
def A1 : Set ℕ := {m | ∃ n : ℕ, 1 ≤ n ∧ 4 ^ n ≤ m ∧ (m : ℝ) < (2 - 1 / n) * 4 ^ n}

/-- `A^{(2)} = ⋃_{n ≥ 1} [(2 + 1/n) 4^n, 4^{n+1})` (intersected with `ℕ`). -/
def A2 : Set ℕ := {m | ∃ n : ℕ, 1 ≤ n ∧ (2 + 1 / n) * 4 ^ n ≤ (m : ℝ) ∧ m < 4 ^ (n + 1)}

/-- The set of Kousek and Radić, `A_KR = (A^{(1)} ∩ 2ℕ) ∪ (A^{(2)} ∩ (2ℕ + 1))`. -/
def AKR : Set ℕ := {m | (Even m ∧ m ∈ A1) ∨ (Odd m ∧ m ∈ A2)}

/-- `f(x) = x/2 + √x`. -/
noncomputable def f (x : ℝ) : ℝ := x / 2 + √x

/-- The set of Theorem \ref{IA:thm:324}: `A = {n ∈ ℕ : {f(log₂ n)} ∈ [0, 1/2 - η)}`. -/
def A324 (η : ℝ) : Set ℕ := {n | 0 < n ∧ Int.fract (f (Real.logb 2 n)) ∈ Set.Ico 0 (1 / 2 - η)}

/-! ## No `B + B + t` in `A_KR` -/

lemma exists_infinite_residue {B : Set ℕ} (hB : B.Infinite) {k : ℕ} (hk : 0 < k) :
    ∃ n < k, {b ∈ B | b % k = n}.Infinite := by
  by_contra h
  simp only [not_exists, not_and, Set.not_infinite] at h
  apply hB
  refine ((Set.finite_lt_nat k).biUnion fun n hn => h n hn).subset ?_
  intro b hb
  exact Set.mem_biUnion (Nat.mod_lt b hk) ⟨hb, rfl⟩

/-- For every `C ≥ 0` there is `n₀` with `4 n C ≤ 4^n` for all `n ≥ n₀`. -/
lemma exists_four_pow_ge (C : ℝ) (hC : 0 ≤ C) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, 4 * n * C ≤ (4 : ℝ) ^ n := by
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt (4 * C) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n₀, fun n hn => ?_⟩
  have h1 : (2 : ℝ) ^ n₀ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self.le
  have e : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  rw [e]
  have h3 : 0 ≤ (n : ℝ) := n.cast_nonneg
  nlinarith

/-- The `A^{(1)}` case: if `x ∈ A^{(1)}` is large and `y = x/2 + C`, then `y ∉ A^{(1)}`. -/
lemma A1_gap (C : ℝ) : ∃ X : ℝ, ∀ x y : ℕ, X ≤ x → (y : ℝ) = x / 2 + C → x ∈ A1 → y ∉ A1 := by
  obtain ⟨n₀, hn₀⟩ := exists_four_pow_ge |C| (abs_nonneg C)
  refine ⟨2 * 4 ^ n₀, fun x y hX hy hx hy1 => ?_⟩
  obtain ⟨n, hn1, hxl, hxu⟩ := hx
  obtain ⟨m, hm1, hyl, hyu⟩ := hy1
  have hxl' : (4 : ℝ) ^ n ≤ x := by exact_mod_cast hxl
  have hyl' : (4 : ℝ) ^ m ≤ y := by exact_mod_cast hyl
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  -- `n ≥ n₀`
  have hnn : n₀ ≤ n := by
    by_contra hcon
    have : (4 : ℝ) ^ n ≤ 4 ^ n₀ := pow_le_pow_right₀ (by norm_num) (by omega)
    have : (2 - 1 / (n : ℝ)) ≤ 2 := by
      have : 0 ≤ 1 / (n : ℝ) := by positivity
      linarith
    have : (2 - 1 / (n : ℝ)) * 4 ^ n ≤ 2 * 4 ^ n₀ := by
      have h4 : (0 : ℝ) ≤ 4 ^ n := by positivity
      nlinarith
    linarith
  have hC := hn₀ n hnn
  have hC' : |C| * (4 * n) ≤ 4 ^ n := by linarith
  have h4n : (0 : ℝ) < 4 ^ n := by positivity
  have hCle : C ≤ 4 ^ n / (4 * n) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [le_abs_self C]
  have hCge : -(4 ^ n / (4 * n)) ≤ C := by
    have : -C ≤ 4 ^ n / (4 * n) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [neg_abs_le C]
    linarith
  have hfrac : (4 : ℝ) ^ n / n = 4 * (4 ^ n / (4 * n)) := by field_simp
  rcases lt_or_ge m n with hmn | hmn
  · -- `m ≤ n - 1`: `y < (2 - 1/m) 4^m ≤ 4^n/2 - 4^{n-1}/(n-1)`, too small
    rcases lt_or_ge m (n - 1) with hmn' | hmn'
    · have h1 : (4 : ℝ) ^ (m + 2) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (2 - 1 / (m : ℝ)) * 4 ^ m ≤ 2 * 4 ^ m := by
        have : 0 ≤ 1 / (m : ℝ) := by positivity
        have : (0 : ℝ) ≤ 4 ^ m := by positivity
        nlinarith
      have h3 : (4 : ℝ) ^ (m + 2) = 16 * 4 ^ m := by ring
      have : (4 : ℝ) ^ n / (4 * n) ≤ 4 ^ n / 4 := by
        apply div_le_div_of_nonneg_left h4n.le (by norm_num); linarith
      linarith
    · have hm' : m = n - 1 := by omega
      have hn2 : 2 ≤ n := by omega
      have e4 : (4 : ℝ) ^ n = 4 * 4 ^ m := by rw [hm', ← pow_succ']; congr 1; omega
      have hmr : (m : ℝ) = n - 1 := by rw [hm']; push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
      -- `y < (2 - 1/m) 4^m = 4^n/2 - 4^m/m ≤ 4^n/2 - 4^n/(4n)`
      have h5 : (4 : ℝ) ^ n / (4 * n) ≤ 4 ^ m / m := by
        rw [e4, div_le_div_iff₀ (by positivity) (by positivity)]
        have : (0 : ℝ) ≤ 4 ^ m := by positivity
        nlinarith
      have h6 : (2 - 1 / (m : ℝ)) * 4 ^ m = 4 ^ n / 2 - 4 ^ m / m := by
        rw [e4]; field_simp; ring
      linarith
  · -- `m ≥ n`: `y ≥ 4^m ≥ 4^n > y`
    have h1 : (4 : ℝ) ^ n ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hmn
    have h2 : (2 - 1 / (n : ℝ)) * 4 ^ n = 2 * 4 ^ n - 4 ^ n / n := by ring
    linarith

/-- The `A^{(2)}` case: if `x ∈ A^{(2)}` is large and `y = x/2 + C`, then `y ∉ A^{(2)}`. -/
lemma A2_gap (C : ℝ) : ∃ X : ℝ, ∀ x y : ℕ, X ≤ x → (y : ℝ) = x / 2 + C → x ∈ A2 → y ∉ A2 := by
  obtain ⟨n₀, hn₀⟩ := exists_four_pow_ge |C| (abs_nonneg C)
  refine ⟨4 ^ (n₀ + 1), fun x y hX hy hx hy2 => ?_⟩
  obtain ⟨n, hn1, hxl, hxu⟩ := hx
  obtain ⟨m, hm1, hyl, hyu⟩ := hy2
  have hxu' : (x : ℝ) < 4 ^ (n + 1) := by exact_mod_cast hxu
  have hyu' : (y : ℝ) < 4 ^ (m + 1) := by exact_mod_cast hyu
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hnn : n₀ ≤ n := by
    by_contra hcon
    have : (4 : ℝ) ^ (n + 1) ≤ 4 ^ (n₀ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hC := hn₀ n hnn
  have h4n : (0 : ℝ) < 4 ^ n := by positivity
  have hCle : C ≤ 4 ^ n / (4 * n) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [le_abs_self C]
  have hCge : -(4 ^ n / (4 * n)) ≤ C := by
    have : -C ≤ 4 ^ n / (4 * n) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [neg_abs_le C]
    linarith
  have hq : (4 : ℝ) ^ n / (4 * n) ≤ 4 ^ n / 4 := by
    apply div_le_div_of_nonneg_left h4n.le (by norm_num); linarith
  have hq2 : (4 : ℝ) ^ n / (4 * n) ≤ 4 ^ n / (2 * n) := by
    apply div_le_div_of_nonneg_left h4n.le (by positivity); linarith
  rcases lt_or_ge m n with hmn | hmn
  · -- `m ≤ n - 1`: `y < 4^{m+1} ≤ 4^n`, but `y ≥ (1 + 1/(2n)) 4^n + C`
    have h1 : (4 : ℝ) ^ (m + 1) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : (2 + 1 / (n : ℝ)) * 4 ^ n / 2 = 4 ^ n + 4 ^ n / (2 * n) := by field_simp
    linarith
  · rcases eq_or_lt_of_le hmn with hmn' | hmn'
    · -- `m = n`: `y ≥ (2 + 1/n) 4^n > 2 · 4^n + C > y`
      subst hmn'
      have e : (2 + 1 / (n : ℝ)) * 4 ^ n = 2 * 4 ^ n + 4 * (4 ^ n / (4 * n)) := by
        field_simp
      have : (4 : ℝ) ^ (n + 1) = 4 * 4 ^ n := by ring
      have : (0 : ℝ) < 4 ^ n / (4 * n) := by positivity
      linarith
    · -- `m ≥ n + 1`: `y ≥ 2 · 4^{n+1} > y`
      have h1 : (4 : ℝ) ^ (n + 1) ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hmn'
      have h2 : (2 : ℝ) * 4 ^ m ≤ (2 + 1 / (m : ℝ)) * 4 ^ m := by
        have : 0 ≤ 1 / (m : ℝ) := by positivity
        have : (0 : ℝ) ≤ 4 ^ m := by positivity
        nlinarith
      have : (4 : ℝ) ^ (n + 1) = 4 * 4 ^ n := by ring
      linarith

/-- Paper, Proposition \ref{IA:prop:KR}, second assertion (Kousek–Radić, Proposition 4.2), for
all `t ∈ ℤ`: `A_KR` contains no `B + B + t` with `B ⊆ ℕ` infinite. -/
theorem AKR_no_BBt (t : ℤ) {B : Set ℕ} (hB : B.Infinite) : ¬ SumsetIn B t AKR := by
  intro hS
  obtain ⟨r, hr, hB'⟩ := exists_infinite_residue hB (by norm_num : 0 < 2)
  obtain ⟨b₁, hb₁B, hb₁r⟩ := hB'.nonempty
  set C : ℝ := b₁ + t / 2 with hC
  obtain ⟨X1, hX1⟩ := A1_gap C
  obtain ⟨X2, hX2⟩ := A2_gap C
  obtain ⟨b, ⟨hbB, hbr⟩, hbX⟩ := hB'.exists_gt (⌈max X1 X2⌉₊ + t.natAbs)
  obtain ⟨x, hxA, hx⟩ := hS b hbB b hbB
  obtain ⟨y, hyA, hy⟩ := hS b hbB b₁ hb₁B
  have hxy : (y : ℝ) = x / 2 + C := by
    have hx' : (x : ℝ) = b + b + t := by exact_mod_cast hx
    have hy' : (y : ℝ) = b + b₁ + t := by exact_mod_cast hy
    rw [hx', hy', hC]; ring
  have hXx : max X1 X2 ≤ x := by
    have h1 : max X1 X2 ≤ ⌈max X1 X2⌉₊ := Nat.le_ceil _
    have h2 : (⌈max X1 X2⌉₊ : ℤ) + t.natAbs < b := by exact_mod_cast hbX
    have h3 : (⌈max X1 X2⌉₊ : ℤ) ≤ x := by
      have := Int.le_natAbs (a := -t)
      rw [Int.natAbs_neg] at this
      omega
    have h4 : ((⌈max X1 X2⌉₊ : ℕ) : ℝ) ≤ x := by exact_mod_cast h3
    linarith
  -- `x` and `y` have the parity of `t`
  have hpar : (Even x ↔ Even y) := by
    have hbb : b % 2 = b₁ % 2 := by rw [hbr, hb₁r]
    have hx2 : (x : ℤ) % 2 = t % 2 := by rw [hx]; omega
    have hy2 : (y : ℤ) % 2 = t % 2 := by rw [hy]; omega
    rw [Nat.even_iff, Nat.even_iff]
    omega
  rcases hxA with ⟨hxe, hx1⟩ | ⟨hxo, hx2⟩
  · rcases hyA with ⟨-, hy1⟩ | ⟨hyo, -⟩
    · exact hX1 x y (le_trans (le_max_left _ _) hXx) hxy hx1 hy1
    · exact (Nat.not_even_iff_odd.2 hyo) (hpar.1 hxe)
  · rcases hyA with ⟨hye, -⟩ | ⟨-, hy2⟩
    · exact (Nat.not_even_iff_odd.2 hxo) (hpar.2 hye)
    · exact hX2 x y (le_trans (le_max_right _ _) hXx) hxy hx2 hy2

/-! ## No `B + B + t` in the set of Theorem \ref{IA:thm:324} -/

lemma tendsto_ratio (c d : ℝ) :
    Tendsto (fun b : ℕ => (2 * (b : ℝ) + c) / (2 * ((b : ℝ) + d))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun b : ℕ => (1 + c / 2 * (1 / (b : ℝ))) / (1 + d * (1 / (b : ℝ))))
      atTop (𝓝 ((1 + c / 2 * 0) / (1 + d * 0))) := by
    have h0 : Tendsto (fun b : ℕ => 1 / (b : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    exact ((tendsto_const_nhds.add (h0.const_mul _)).div
      (tendsto_const_nhds.add (h0.const_mul _)) (by norm_num))
  simp only [mul_zero, add_zero, div_one] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp

/-- `f(log₂ (2b + t)) - f(log₂ (b + b' + t)) → 1/2` as `b → ∞`. -/
lemma tendsto_f_diff (b' : ℕ) (t : ℤ) :
    Tendsto (fun b : ℕ => f (Real.logb 2 (2 * (b : ℝ) + t)) - f (Real.logb 2 ((b : ℝ) + b' + t)))
      atTop (𝓝 (1 / 2)) := by
  set X1 : ℕ → ℝ := fun b => Real.logb 2 ((b : ℝ) + b' + t)
  set X2 : ℕ → ℝ := fun b => Real.logb 2 (2 * (b : ℝ) + t)
  have hpos : ∀ᶠ b : ℕ in atTop, 0 < (b : ℝ) + b' + t ∧ 0 < 2 * (b : ℝ) + t := by
    filter_upwards [eventually_gt_atTop t.natAbs] with b hb
    have : (t.natAbs : ℝ) < b := by exact_mod_cast hb
    have h2 : -(t : ℝ) ≤ t.natAbs := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact neg_le_abs _
    have h3 : (0 : ℝ) ≤ b' := b'.cast_nonneg
    constructor <;> linarith
  -- `X2 - X1 → 1`
  have hd : Tendsto (fun b => X2 b - X1 b) atTop (𝓝 1) := by
    have hl : Tendsto
        (fun b : ℕ => 1 + Real.logb 2 ((2 * (b : ℝ) + t) / (2 * ((b : ℝ) + (b' + t)))))
        atTop (𝓝 (1 + Real.logb 2 1)) :=
      tendsto_const_nhds.add (((Real.continuousAt_logb (by norm_num)).tendsto).comp
        (tendsto_ratio t (b' + t)))
    rw [Real.logb_one, add_zero] at hl
    refine hl.congr' ?_
    filter_upwards [hpos] with b ⟨h1, h2⟩
    simp only [X1, X2]
    rw [Real.logb_div h2.ne' (ne_of_gt (by linarith)), Real.logb_mul (by norm_num) (by linarith),
      Real.logb_self_eq_one (by norm_num)]
    ring_nf
  -- `X1 → ∞`
  have hX1 : Tendsto X1 atTop atTop := by
    refine (Real.tendsto_logb_atTop (by norm_num)).comp ?_
    exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
      tendsto_natCast_atTop_atTop)
  -- `√X2 - √X1 → 0`
  have hs : Tendsto (fun b => √(X2 b) - √(X1 b)) atTop (𝓝 0) := by
    have hq : Tendsto (fun b => |X2 b - X1 b| / √(X1 b)) atTop (𝓝 0) := by
      refine (hd.abs).div_atTop ?_
      exact Real.tendsto_sqrt_atTop.comp hX1
    refine squeeze_zero_norm' ?_ hq
    filter_upwards [hX1.eventually_gt_atTop 0, (hd.eventually (lt_mem_nhds (by norm_num :
      (0 : ℝ) < 1)))] with b hb hb2
    have h2 : 0 < X2 b := by linarith
    have hs1 : 0 < √(X1 b) := Real.sqrt_pos.2 hb
    have hs2 : 0 < √(X2 b) := Real.sqrt_pos.2 h2
    have e : √(X2 b) - √(X1 b) = (X2 b - X1 b) / (√(X2 b) + √(X1 b)) := by
      field_simp
      linear_combination (Real.sq_sqrt h2.le) - (Real.sq_sqrt hb.le)
    rw [Real.norm_eq_abs, e, abs_div, abs_of_pos (by positivity : 0 < √(X2 b) + √(X1 b))]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hs1 (by linarith)
  have := (hd.div_const 2).add hs
  rw [add_zero] at this
  refine this.congr fun b => ?_
  simp only [f, X1, X2]; ring

/-- Paper, Theorem \ref{IA:thm:324}, last assertion: for `0 < η < 1/2`, the set
`A = {n : {f(log₂ n)} ∈ [0, 1/2 - η)}` contains no `B + B + t` with `t ∈ ℤ` and `B ⊆ ℕ`
infinite. -/
theorem A324_no_BBt {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) (t : ℤ) {B : Set ℕ}
    (hB : B.Infinite) : ¬ SumsetIn B t (A324 η) := by
  intro hS
  obtain ⟨b', hb'⟩ := hB.nonempty
  have hev := (tendsto_f_diff b' t).eventually (Metric.ball_mem_nhds (1 / 2 : ℝ)
    (by linarith : 0 < η / 2))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  obtain ⟨b, hb, hbN⟩ := hB.exists_gt N0
  have hΔ := hN0 b hbN.le
  rw [Real.dist_eq] at hΔ
  obtain ⟨m1, ⟨-, hm1⟩, e1⟩ := hS b hb b' hb'
  obtain ⟨m2, ⟨-, hm2⟩, e2⟩ := hS b hb b hb
  have e1' : (m1 : ℝ) = b + b' + t := by exact_mod_cast e1
  have e2' : (m2 : ℝ) = 2 * b + t := by
    have : ((m2 : ℤ) : ℝ) = ((b : ℤ) + b + t : ℤ) := by rw [e2]
    push_cast at this; linarith
  rw [e1'] at hm1
  rw [e2'] at hm2
  set y1 := f (Real.logb 2 ((b : ℝ) + b' + t))
  set y2 := f (Real.logb 2 (2 * (b : ℝ) + t))
  set u := Int.fract y1
  have hu := hm1
  simp only [Set.mem_Ico] at hu
  have hw : Int.fract y2 = u + 1 / 2 + (y2 - y1 - 1 / 2) := by
    rw [Int.fract_eq_iff]
    refine ⟨?_, ?_, ⌊y1⌋, ?_⟩
    · have := abs_lt.1 hΔ; linarith
    · have := abs_lt.1 hΔ; linarith
    · have := Int.floor_add_fract y1
      simp only [u] at *
      linarith
  have := hm2.1
  have h2 := hm2.2
  rw [hw] at h2
  have := abs_lt.1 hΔ
  linarith

/-! ## Error terms of size `o(log N)` -/

/-- `u(N) = o(log N)`: `u(N) / log N → 0`. -/
def LogSmall (u : ℕ → ℝ) : Prop := Tendsto (fun N => u N / Real.log N) atTop (𝓝 0)

lemma tendsto_log_nat : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma eventually_log_pos : ∀ᶠ N : ℕ in atTop, 0 < Real.log N :=
  tendsto_log_nat.eventually_gt_atTop 0

lemma LogSmall.add {u v : ℕ → ℝ} (hu : LogSmall u) (hv : LogSmall v) :
    LogSmall fun N => u N + v N := by
  unfold LogSmall at *; simpa [add_div] using hu.add hv

lemma LogSmall.neg {u : ℕ → ℝ} (hu : LogSmall u) : LogSmall fun N => -u N := by
  unfold LogSmall at *; simpa [neg_div] using hu.neg

lemma LogSmall.sub {u v : ℕ → ℝ} (hu : LogSmall u) (hv : LogSmall v) :
    LogSmall fun N => u N - v N := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

lemma LogSmall.const_mul {u : ℕ → ℝ} (hu : LogSmall u) (c : ℝ) : LogSmall fun N => c * u N := by
  unfold LogSmall at *; simpa [mul_div_assoc] using hu.const_mul c

lemma LogSmall.congr' {u v : ℕ → ℝ} (hu : LogSmall u) (h : ∀ᶠ N in atTop, u N = v N) :
    LogSmall v := by
  unfold LogSmall at *
  exact hu.congr' (h.mono fun N hN => by rw [hN])

/-- Criterion: `u = o(log N)` if for every `ε > 0`, eventually `|u N| ≤ K + ε log N`. -/
lemma logSmall_of_forall {u : ℕ → ℝ}
    (h : ∀ ε > 0, ∃ K : ℝ, ∀ᶠ N in atTop, |u N| ≤ K + ε * Real.log N) : LogSmall u := by
  rw [LogSmall, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := h (ε / 2) (by positivity)
  have hK' : Tendsto (fun N : ℕ => |K| / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_nat
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hK'.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < ε / 2)))
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hK
  obtain ⟨N3, hN3⟩ := eventually_atTop.1 eventually_log_pos
  refine ⟨max N1 (max N2 N3), fun N hN => ?_⟩
  have h1 := hN1 N (le_trans (le_max_left _ _) hN)
  have h2 := hN2 N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have h3 := hN3 N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos h3, div_lt_iff₀ h3]
  rw [div_lt_iff₀ h3] at h1
  have := le_abs_self K
  nlinarith

lemma LogSmall.of_abs_le {u v : ℕ → ℝ} (hv : LogSmall v) (h : ∀ᶠ N in atTop, |u N| ≤ v N) :
    LogSmall u := by
  unfold LogSmall at *
  refine squeeze_zero_norm' ?_ hv
  filter_upwards [h, eventually_log_pos] with N hN hlog
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog]
  exact div_le_div_of_nonneg_right hN hlog.le

lemma logSmall_of_bdd {u : ℕ → ℝ} {C : ℝ} (h : ∀ᶠ N in atTop, |u N| ≤ C) : LogSmall u :=
  logSmall_of_forall fun ε hε => ⟨C, by
    filter_upwards [h, eventually_log_pos] with N hN hl
    nlinarith⟩

/-- If `u N - d log N = o(log N)` then `u N / log N → d`. -/
lemma tendsto_of_logSmall {u : ℕ → ℝ} {d : ℝ} (h : LogSmall fun N => u N - d * Real.log N) :
    Tendsto (fun N => u N / Real.log N) atTop (𝓝 d) := by
  have := h.add (u := fun N => u N - d * Real.log N) (logSmall_of_bdd (C := 0)
    (Eventually.of_forall fun N => (abs_zero).le))
  unfold LogSmall at h
  have h2 := h.add (tendsto_const_nhds (x := d))
  rw [zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_log_pos] with N hN
  field_simp
  ring

/-! ## Changes of a sequence -/

open scoped Classical in
/-- The number of `n ∈ [m, N)` with `h (n + 1) ≠ h n`. -/
noncomputable def changes {α : Type*} (h : ℕ → α) (m N : ℕ) : ℕ :=
  ∑ n ∈ Ico m N, if h (n + 1) ≠ h n then 1 else 0

open scoped Classical in
lemma changes_succ {α : Type*} (h : ℕ → α) {m N : ℕ} (hmN : m ≤ N) :
    changes h m (N + 1) = changes h m N + (if h (N + 1) ≠ h N then 1 else 0) := by
  classical
  unfold changes
  rw [sum_Ico_succ_top hmN]

/-- A monotone integer sequence changes at most `u N - u m` times on `[m, N)`. -/
lemma changes_le_of_monotone {u : ℕ → ℤ} (hu : Monotone u) {m N : ℕ} (hmN : m ≤ N) :
    (changes u m N : ℤ) ≤ u N - u m := by
  induction N, hmN using Nat.le_induction with
  | base => simp [changes]
  | succ N hmN ih =>
    classical
    rw [changes_succ u hmN]
    have h1 := hu (Nat.le_succ N)
    split_ifs with hne
    · have : u N < u (N + 1) := lt_of_le_of_ne h1 (Ne.symm hne)
      push_cast; linarith
    · push_cast; linarith

lemma changes_comp₂ {α β γ : Type*} (F : α → β → γ) (u : ℕ → α) (v : ℕ → β) (m N : ℕ) :
    changes (fun n => F (u n) (v n)) m N ≤ changes u m N + changes v m N := by
  classical
  unfold changes
  rw [← sum_add_distrib]
  refine sum_le_sum fun n _ => ?_
  by_cases hu : u (n + 1) = u n <;> by_cases hv : v (n + 1) = v n <;> simp [hu, hv] <;>
    split_ifs <;> norm_num

lemma changes_comp {α β : Type*} (F : α → β) (u : ℕ → α) (m N : ℕ) :
    changes (fun n => F (u n)) m N ≤ changes u m N := by
  classical
  unfold changes
  refine sum_le_sum fun n _ => ?_
  by_cases hu : u (n + 1) = u n
  · simp [hu]
  · simp only [ne_eq, hu, not_false_eq_true, if_true]
    split_ifs <;> norm_num

/-! ## Alternating sums -/

/-- Partial sums of an alternating series with nonincreasing nonnegative terms:
`0 ≤ (-1)^m ∑_{n ∈ [m, m + L)} (-1)^n w n ≤ w m`. -/
lemma alt_partial {w : ℕ → ℝ} {M : ℕ} (hw : ∀ n, M ≤ n → 0 ≤ w n ∧ w (n + 1) ≤ w n) :
    ∀ L m, M ≤ m → 0 ≤ (-1) ^ m * ∑ n ∈ Ico m (m + L), (-1) ^ n * w n ∧
      (-1) ^ m * ∑ n ∈ Ico m (m + L), (-1) ^ n * w n ≤ w m := by
  intro L
  induction L with
  | zero => intro m hm; simp [(hw m hm).1]
  | succ L ih =>
    intro m hm
    have h1 := ih (m + 1) (by omega)
    rw [sum_eq_sum_Ico_succ_bot (by omega : m < m + (L + 1)),
      show m + (L + 1) = m + 1 + L by ring]
    have e : (-1 : ℝ) ^ m * ((-1) ^ m * w m + ∑ n ∈ Ico (m + 1) (m + 1 + L), (-1) ^ n * w n) =
        w m - (-1) ^ (m + 1) * ∑ n ∈ Ico (m + 1) (m + 1 + L), (-1) ^ n * w n := by
      rw [mul_add, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul,
        pow_succ]
      ring
    rw [e]
    have h2 := hw m hm
    constructor <;> linarith [h1.1, h1.2]

lemma abs_alt_partial {w : ℕ → ℝ} {M : ℕ} (hw : ∀ n, M ≤ n → 0 ≤ w n ∧ w (n + 1) ≤ w n)
    {N : ℕ} (hMN : M ≤ N) : |∑ n ∈ Ico M N, (-1) ^ n * w n| ≤ w M := by
  obtain ⟨L, rfl⟩ : ∃ L, N = M + L := ⟨N - M, by omega⟩
  have h := alt_partial hw L M le_rfl
  have habs : |(-1 : ℝ) ^ M| = 1 := by simp
  calc |∑ n ∈ Ico M (M + L), (-1) ^ n * w n|
      = |(-1) ^ M * ∑ n ∈ Ico M (M + L), (-1) ^ n * w n| := by rw [abs_mul, habs, one_mul]
    _ ≤ w M := abs_le.2 ⟨by linarith [h.1], h.2⟩

/-- An alternating sum weighted by a sequence `h` with `|h| ≤ 1` and few changes:
`|∑_{n ∈ [M, N)} (-1)^n h(n) w(n)| ≤ w(M) (1 + 2 · #changes of h)`. -/
lemma abs_alt_le {w : ℕ → ℝ} {M : ℕ} (hw : ∀ n, M ≤ n → 0 ≤ w n ∧ w (n + 1) ≤ w n)
    {h : ℕ → ℝ} (hh : ∀ n, |h n| ≤ 1) {N : ℕ} (hMN : M ≤ N) :
    |∑ n ∈ Ico M N, (-1) ^ n * h n * w n| ≤ w M * (1 + 2 * changes h M N) := by
  -- invariant: `|T N - h N S N| ≤ 2 w(M) · changes`
  have key : ∀ N, M ≤ N → |∑ n ∈ Ico M N, (-1) ^ n * h n * w n -
      h N * ∑ n ∈ Ico M N, (-1) ^ n * w n| ≤ 2 * w M * changes h M N := by
    intro N hMN
    induction N, hMN using Nat.le_induction with
    | base => simp [changes]
    | succ N hMN ih =>
      classical
      rw [sum_Ico_succ_top hMN, sum_Ico_succ_top hMN, changes_succ h hMN]
      have hS := abs_alt_partial hw (Nat.le_succ_of_le hMN)
      rw [sum_Ico_succ_top hMN] at hS
      have hwM := (hw M le_rfl).1
      split_ifs with hne
      · have e : ∑ n ∈ Ico M N, (-1) ^ n * h n * w n + (-1) ^ N * h N * w N -
            h (N + 1) * (∑ n ∈ Ico M N, (-1) ^ n * w n + (-1) ^ N * w N) =
            (∑ n ∈ Ico M N, (-1) ^ n * h n * w n - h N * ∑ n ∈ Ico M N, (-1) ^ n * w n) +
            (h N - h (N + 1)) * (∑ n ∈ Ico M N, (-1) ^ n * w n + (-1) ^ N * w N) := by ring
        rw [e]
        have h3 : |h N - h (N + 1)| ≤ 2 := by
          have := hh N; have := hh (N + 1)
          calc |h N - h (N + 1)| ≤ |h N| + |h (N + 1)| := abs_sub _ _
            _ ≤ 2 := by linarith
        calc _ ≤ |∑ n ∈ Ico M N, (-1) ^ n * h n * w n - h N * ∑ n ∈ Ico M N, (-1) ^ n * w n| +
              |(h N - h (N + 1)) * (∑ n ∈ Ico M N, (-1) ^ n * w n + (-1) ^ N * w N)| :=
              abs_add_le _ _
          _ ≤ 2 * w M * changes h M N + 2 * w M := by
              rw [abs_mul]
              gcongr
          _ = 2 * w M * ((changes h M N + 1 : ℕ) : ℝ) := by push_cast; ring
      · rw [ne_eq, not_not] at hne
        rw [hne]
        have e : ∑ n ∈ Ico M N, (-1) ^ n * h n * w n + (-1) ^ N * h N * w N -
            h N * (∑ n ∈ Ico M N, (-1) ^ n * w n + (-1) ^ N * w N) =
            ∑ n ∈ Ico M N, (-1) ^ n * h n * w n - h N * ∑ n ∈ Ico M N, (-1) ^ n * w n := by ring
        rw [e]
        simpa using ih
  have h1 := key N hMN
  have h2 := abs_alt_partial hw hMN
  have h3 : |h N * ∑ n ∈ Ico M N, (-1) ^ n * w n| ≤ w M := by
    rw [abs_mul]
    calc |h N| * |∑ n ∈ Ico M N, (-1) ^ n * w n| ≤ 1 * w M :=
          mul_le_mul (hh N) h2 (abs_nonneg _) (by norm_num)
      _ = w M := one_mul _
  calc |∑ n ∈ Ico M N, (-1) ^ n * h n * w n|
      ≤ |∑ n ∈ Ico M N, (-1) ^ n * h n * w n - h N * ∑ n ∈ Ico M N, (-1) ^ n * w n| +
        |h N * ∑ n ∈ Ico M N, (-1) ^ n * w n| := by
        have := abs_add_le (∑ n ∈ Ico M N, (-1) ^ n * h n * w n -
          h N * ∑ n ∈ Ico M N, (-1) ^ n * w n) (h N * ∑ n ∈ Ico M N, (-1) ^ n * w n)
        simpa using this
    _ ≤ 2 * w M * changes h M N + w M := add_le_add h1 h3
    _ = w M * (1 + 2 * changes h M N) := by ring

/-! ## Sparse sums -/

/-- If `0 ≤ s n ≤ K / n`, `s n = 0` off a set `P` with `|P ∩ [1, N]| ≤ C (log N + 1)`, then
`∑_{n ≤ N} s n = o(log N)`. -/
lemma logSmall_sparse {s : ℕ → ℝ} {P : ℕ → Prop} [DecidablePred P] {K C : ℝ} (hK : 0 ≤ K)
    (hs0 : ∀ n, 0 ≤ s n) (hsP : ∀ n, ¬ P n → s n = 0)
    (hsK : ∀ n, 1 ≤ n → s n ≤ K / n)
    (hcount : ∀ N : ℕ, (((Icc 1 N).filter P).card : ℝ) ≤ C * (Real.log N + 1)) :
    LogSmall fun N => ∑ n ∈ Icc 1 N, s n := by
  apply logSmall_of_forall
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (K * C / ε)
  have hM1 : (1 : ℝ) ≤ M + 1 := by linarith [M.cast_nonneg (α := ℝ)]
  set M' := M + 1 with hM'
  have hM'pos : (0 : ℝ) < M' := by push_cast [hM']; linarith
  have hKCM : K * C / M' ≤ ε := by
    rw [div_le_iff₀ hM'pos]
    rw [div_lt_iff₀ hε] at hM
    push_cast [hM']; nlinarith
  refine ⟨K * M' + K * C / M', Eventually.of_forall fun N => ?_⟩
  have hterm : ∀ n ∈ Icc 1 N, s n ≤ (if n < M' then K else 0) + (if P n then K / M' else 0) := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    by_cases hnM : n < M'
    · rw [if_pos hnM]
      have : K / n ≤ K := div_le_self hK hn1'
      have := hsK n hn1
      split_ifs <;> [linarith [div_nonneg hK hM'pos.le]; linarith]
    · rw [if_neg hnM, zero_add]
      by_cases hP : P n
      · rw [if_pos hP]
        refine (hsK n hn1).trans (div_le_div_of_nonneg_left hK hM'pos ?_)
        exact_mod_cast not_lt.1 hnM
      · rw [if_neg hP, hsP n hP]
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, sum_ite, sum_ite, sum_const_zero, sum_const_zero, add_zero, add_zero,
    sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul] at hsum
  have h1 : (((Icc 1 N).filter fun n => n < M').card : ℝ) ≤ M' := by
    have : (Icc 1 N).filter (fun n => n < M') ⊆ range M' := by
      intro n hn; exact mem_range.2 (mem_filter.1 hn).2
    exact_mod_cast (card_le_card this).trans (card_range _).le
  have h2 := hcount N
  have hs : 0 ≤ ∑ n ∈ Icc 1 N, s n := sum_nonneg fun n _ => hs0 n
  rw [abs_of_nonneg hs]
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  calc ∑ n ∈ Icc 1 N, s n ≤ _ := hsum
    _ ≤ M' * K + (C * (Real.log N + 1)) * (K / M') := by
        gcongr
    _ = K * M' + K * C / M' + (K * C / M') * Real.log N := by ring
    _ ≤ K * M' + K * C / M' + ε * Real.log N := by gcongr

lemma sum_Icc_telescope (F : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (F (n + 1) - F n) = F (N + 1) - F 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih]; ring

lemma log_nat_mono : Monotone fun n : ℕ => Real.log n := by
  intro m n hmn
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [Real.log_natCast_nonneg]
  · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hmn)

lemma log_succ_sub_le {n : ℕ} (hn : 1 ≤ n) : Real.log (n + 1) - Real.log n ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hn'.ne']
  have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (n + 1) / n)
  have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
  linarith

lemma log_succ_sub_ge {n : ℕ} (hn : 1 ≤ n) : 1 / (n + 1) ≤ Real.log (n + 1) - Real.log n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hn'.ne']
  have := Real.one_sub_inv_le_log_of_pos (by positivity : (0 : ℝ) < (n + 1) / n)
  have e : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / (n + 1) := by field_simp; ring
  linarith

lemma log_succ_le_log_add_one {N : ℕ} (hN : 1 ≤ N) : Real.log (N + 1) ≤ Real.log N + 1 := by
  have := log_succ_sub_le hN
  have h1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hN)]; exact_mod_cast hN
  linarith

/-! ## Phase indicators and their antiderivatives -/

/-- The indicator `1[{y} ∈ [a, b)]`, as a real number. -/
noncomputable def ind (a b y : ℝ) : ℝ := by
  classical
  exact if Int.fract y ∈ Set.Ico a b then 1 else 0

lemma ind_nonneg (a b y : ℝ) : 0 ≤ ind a b y := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (a b y : ℝ) : ind a b y ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-- For `0 ≤ a ≤ 1`: `⌊y - a⌋ = ⌊y⌋` if `a ≤ {y}`, and `⌊y - a⌋ = ⌊y⌋ - 1` otherwise. -/
lemma floor_sub_eq {y a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ⌊y - a⌋ = ⌊y⌋ - (if a ≤ Int.fract y then 0 else 1) := by
  have h1 := Int.fract_nonneg y
  have h2 := Int.fract_lt_one y
  have e := Int.floor_add_fract y
  rw [Int.floor_eq_iff]
  split_ifs with h <;> push_cast <;> constructor <;> linarith

/-- For `0 ≤ a ≤ b ≤ 1`: `1[{y} ∈ [a, b)] = ⌊y - a⌋ - ⌊y - b⌋`. -/
lemma ind_eq_floor {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (y : ℝ) :
    ind a b y = ((⌊y - a⌋ - ⌊y - b⌋ : ℤ) : ℝ) := by
  rw [floor_sub_eq ha (hab.trans hb), floor_sub_eq (ha.trans hab) hb]
  unfold ind
  simp only [Set.mem_Ico]
  by_cases h1 : a ≤ Int.fract y <;> by_cases h2 : b ≤ Int.fract y
  · rw [if_neg (fun h => absurd h.2 (not_lt.2 h2)), if_pos h1, if_pos h2]; simp
  · rw [if_pos ⟨h1, lt_of_not_ge h2⟩, if_pos h1, if_neg h2]; simp
  · exact absurd (hab.trans h2) h1
  · rw [if_neg (fun h => h1 h.1), if_neg h1, if_neg h2]; simp

lemma ind_zero_one (y : ℝ) : ind 0 1 y = 1 := by
  unfold ind
  rw [if_pos ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩]

/-- `Ψ(z) = k (k - 1)/2 + k {z}` with `k = ⌊z⌋`: the continuous piecewise linear function with
slope `⌊z⌋`. -/
noncomputable def Ψ (z : ℝ) : ℝ := (⌊z⌋ : ℝ) * (⌊z⌋ - 1) / 2 + ⌊z⌋ * Int.fract z

lemma Ψ_same {z₀ z₁ : ℝ} (h : ⌊z₀⌋ = ⌊z₁⌋) : Ψ z₁ - Ψ z₀ = ⌊z₀⌋ * (z₁ - z₀) := by
  unfold Ψ
  rw [Int.fract, Int.fract, ← h]
  ring

lemma Ψ_step {z₀ z₁ : ℝ} (h01 : z₀ ≤ z₁) (h1 : z₁ ≤ z₀ + 1) :
    0 ≤ Ψ z₁ - Ψ z₀ - ⌊z₀⌋ * (z₁ - z₀) ∧ Ψ z₁ - Ψ z₀ - ⌊z₀⌋ * (z₁ - z₀) ≤ z₁ - z₀ := by
  have hf0 := Int.floor_le z₀
  have hf0' := Int.lt_floor_add_one z₀
  have hf1 := Int.floor_le z₁
  have hf1' := Int.lt_floor_add_one z₁
  have hle : ⌊z₀⌋ ≤ ⌊z₁⌋ := Int.floor_mono h01
  have hle' : ⌊z₁⌋ ≤ ⌊z₀⌋ + 1 := by
    have : z₁ < ⌊z₀⌋ + 1 + 1 := by linarith
    have := Int.floor_lt.2 (show z₁ < ((⌊z₀⌋ + 2 : ℤ) : ℝ) by push_cast; linarith)
    omega
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [Ψ_same heq]; constructor <;> linarith
  · have hk : ⌊z₁⌋ = ⌊z₀⌋ + 1 := by omega
    unfold Ψ
    rw [hk, Int.fract, Int.fract, hk]
    push_cast
    have : (⌊z₀⌋ : ℝ) + 1 ≤ z₁ := by exact_mod_cast hk ▸ Int.floor_le z₁
    constructor <;> nlinarith

/-- `τ(u) = u - u²`. -/
def τ (u : ℝ) : ℝ := u - u ^ 2

lemma τ_fract_nonneg (y : ℝ) : 0 ≤ τ (Int.fract y) := by
  unfold τ; nlinarith [Int.fract_nonneg y, Int.fract_lt_one y]

lemma τ_fract_le (y : ℝ) : τ (Int.fract y) ≤ 1 / 4 := by
  unfold τ; nlinarith [sq_nonneg (Int.fract y - 1 / 2)]

lemma Ψ_eq (z : ℝ) : Ψ z = (z ^ 2 - z + τ (Int.fract z)) / 2 := by
  unfold Ψ τ
  have e := Int.floor_add_fract z
  set k := (⌊z⌋ : ℝ)
  set u := Int.fract z
  rw [← e]
  ring

/-- `Φ_{a,b}(y) = Ψ(y - a) - Ψ(y - b)`, an antiderivative of `1[{y} ∈ [a, b)]`. -/
noncomputable def Φ (a b y : ℝ) : ℝ := Ψ (y - a) - Ψ (y - b)

lemma Φ_eq (a b y : ℝ) :
    Φ a b y = (b - a) * y - (b - a) * (a + b + 1) / 2 +
      (τ (Int.fract (y - a)) - τ (Int.fract (y - b))) / 2 := by
  unfold Φ; rw [Ψ_eq, Ψ_eq]; ring

lemma abs_Φ_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (y : ℝ) :
    |Φ a b y - (b - a) * y| ≤ 2 := by
  rw [Φ_eq]
  have h1 := τ_fract_nonneg (y - a); have h2 := τ_fract_le (y - a)
  have h3 := τ_fract_nonneg (y - b); have h4 := τ_fract_le (y - b)
  have h5 : 0 ≤ (b - a) * (a + b + 1) := by nlinarith
  have h6 : (b - a) * (a + b + 1) ≤ 3 := by nlinarith
  rw [abs_le]; constructor <;> nlinarith

lemma Φ_step {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {y₀ y₁ : ℝ} (h01 : y₀ ≤ y₁)
    (h1 : y₁ ≤ y₀ + 1) : |Φ a b y₁ - Φ a b y₀ - ind a b y₀ * (y₁ - y₀)| ≤ y₁ - y₀ := by
  have hA := Ψ_step (z₀ := y₀ - a) (z₁ := y₁ - a) (by linarith) (by linarith)
  have hB := Ψ_step (z₀ := y₀ - b) (z₁ := y₁ - b) (by linarith) (by linarith)
  rw [ind_eq_floor ha hab hb]
  unfold Φ
  push_cast
  have e1 : y₁ - a - (y₀ - a) = y₁ - y₀ := by ring
  have e2 : y₁ - b - (y₀ - b) = y₁ - y₀ := by ring
  rw [e1] at hA; rw [e2] at hB
  rw [abs_le]; constructor <;> nlinarith [hA.1, hA.2, hB.1, hB.2]

lemma Φ_step_reg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {y₀ y₁ : ℝ}
    (hA : ⌊y₀ - a⌋ = ⌊y₁ - a⌋) (hB : ⌊y₀ - b⌋ = ⌊y₁ - b⌋) :
    Φ a b y₁ - Φ a b y₀ = ind a b y₀ * (y₁ - y₀) := by
  rw [ind_eq_floor ha hab hb]
  unfold Φ
  have h1 := Ψ_same hA
  have h2 := Ψ_same hB
  push_cast
  have e1 : y₁ - a - (y₀ - a) = y₁ - y₀ := by ring
  have e2 : y₁ - b - (y₀ - b) = y₁ - y₀ := by ring
  rw [e1] at h1; rw [e2] at h2
  linarith

/-! ## Linear phases `θ log n` -/

section Linear

variable (θ a b : ℝ)

/-- `g(n) = 1[{θ log n} ∈ [a, b)]`. -/
noncomputable def gθ (n : ℕ) : ℝ := ind a b (θ * Real.log n)

/-- `H(n) = θ⁻¹ Φ_{a,b}(θ log n)`. -/
noncomputable def Hθ (n : ℕ) : ℝ := θ⁻¹ * Φ a b (θ * Real.log n)

/-- The error `d(n) = g(n)/n - (H(n+1) - H(n))`. -/
noncomputable def dθ (n : ℕ) : ℝ := gθ θ a b n / n - (Hθ θ a b (n + 1) - Hθ θ a b n)

/-- `⌊θ log n - r⌋`. -/
noncomputable def uθ (r : ℝ) (n : ℕ) : ℤ := ⌊θ * Real.log n - r⌋

variable {θ a b}

lemma uθ_mono (hθ : 0 ≤ θ) (r : ℝ) : Monotone (uθ θ r) := by
  intro m n hmn
  unfold uθ
  exact Int.floor_mono (by have := log_nat_mono hmn; nlinarith)

lemma uθ_changes (hθ : 0 ≤ θ) (r : ℝ) (N : ℕ) :
    (changes (uθ θ r) 1 (N + 1) : ℝ) ≤ θ * Real.log (N + 1) + 1 := by
  have h := changes_le_of_monotone (uθ_mono hθ r) (by omega : 1 ≤ N + 1)
  have h1 : (uθ θ r (N + 1) : ℝ) ≤ θ * Real.log (N + 1) - r := by
    unfold uθ; push_cast; exact Int.floor_le _
  have h2 : -r - 1 < (uθ θ r 1 : ℝ) := by
    unfold uθ; simp only [Nat.cast_one, Real.log_one, mul_zero, zero_sub]
    have := Int.lt_floor_add_one (-r); linarith
  have h' : ((changes (uθ θ r) 1 (N + 1) : ℤ) : ℝ) ≤ ((uθ θ r (N + 1) - uθ θ r 1 : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith

/-- `n` is *irregular* if `⌊θ log n - a⌋` or `⌊θ log n - b⌋` jumps between `n` and `n + 1`. -/
def Irr (θ a b : ℝ) (n : ℕ) : Prop := uθ θ a (n + 1) ≠ uθ θ a n ∨ uθ θ b (n + 1) ≠ uθ θ b n

lemma card_Irr_le (hθ : 0 ≤ θ) (N : ℕ) [DecidablePred (Irr θ a b)] :
    (((Icc 1 N).filter (Irr θ a b)).card : ℝ) ≤ 2 * (θ * Real.log (N + 1) + 1) := by
  classical
  have h : ((Icc 1 N).filter (Irr θ a b)).card ≤ changes (uθ θ a) 1 (N + 1) +
      changes (uθ θ b) 1 (N + 1) := by
    unfold changes
    rw [← sum_add_distrib, card_filter, Finset.Ico_add_one_right_eq_Icc]
    refine sum_le_sum fun n _ => ?_
    unfold Irr
    by_cases h1 : uθ θ a (n + 1) = uθ θ a n <;> by_cases h2 : uθ θ b (n + 1) = uθ θ b n <;>
      simp [h1, h2]
  have h' : (((Icc 1 N).filter (Irr θ a b)).card : ℝ) ≤ (changes (uθ θ a) 1 (N + 1) : ℝ) +
      changes (uθ θ b) 1 (N + 1) := by exact_mod_cast h
  have := uθ_changes hθ a N
  have := uθ_changes hθ b N
  linarith

lemma card_Irr_le' (hθ : 0 ≤ θ) (N : ℕ) [DecidablePred (Irr θ a b)] :
    (((Icc 1 N).filter (Irr θ a b)).card : ℝ) ≤ (2 * θ + 2) * (Real.log N + 1) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp; positivity
  · have := card_Irr_le (a := a) (b := b) hθ N
    have := log_succ_le_log_add_one h
    have := Real.log_natCast_nonneg N
    nlinarith

open scoped Classical in
lemma Hθ_step (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (hnθ : θ ≤ n) :
    |dθ θ a b n| ≤ (1 / n - 1 / (n + 1)) + (if Irr θ a b n then 1 / (n : ℝ) else 0) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set y₀ := θ * Real.log n
  set y₁ := θ * Real.log (n + 1)
  have hl1 := log_succ_sub_le hn
  have hl2 := log_succ_sub_ge hn
  have hΔ : y₁ - y₀ = θ * (Real.log (n + 1) - Real.log n) := by simp only [y₀, y₁]; ring
  have hΔ0 : 0 ≤ y₁ - y₀ := by
    rw [hΔ]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact mul_nonneg hθ.le (by linarith)
  have hΔ1 : y₁ - y₀ ≤ 1 := by
    rw [hΔ]
    calc θ * (Real.log (n + 1) - Real.log n) ≤ θ * (1 / n) := by gcongr
      _ ≤ 1 := by rw [mul_one_div, div_le_one hn']; exact hnθ
  set g := ind a b y₀
  have hg0 : 0 ≤ g := ind_nonneg _ _ _
  have hg1 : g ≤ 1 := ind_le_one _ _ _
  have hd : dθ θ a b n = (g / n - g * (Real.log (n + 1) - Real.log n)) -
      θ⁻¹ * (Φ a b y₁ - Φ a b y₀ - g * (y₁ - y₀)) := by
    unfold dθ gθ Hθ
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hΔ]; field_simp; ring
  rw [hd]
  have e1 : |g / n - g * (Real.log (n + 1) - Real.log n)| ≤ 1 / n - 1 / (n + 1) := by
    rw [div_eq_mul_one_div, ← mul_sub, abs_mul, abs_of_nonneg hg0]
    rw [abs_of_nonneg (by linarith)]
    calc g * (1 / ↑n - (Real.log (↑n + 1) - Real.log ↑n)) ≤ 1 * (1 / n - 1 / (n + 1)) := by
          apply mul_le_mul hg1 (by linarith) (by linarith) (by norm_num)
      _ = 1 / n - 1 / (n + 1) := one_mul _
  have e2 : |θ⁻¹ * (Φ a b y₁ - Φ a b y₀ - g * (y₁ - y₀))| ≤
      if Irr θ a b n then 1 / (n : ℝ) else 0 := by
    split_ifs with hirr
    · rw [abs_mul, abs_of_pos (inv_pos.2 hθ)]
      have := Φ_step ha hab hb (y₀ := y₀) (y₁ := y₁) (by linarith) (by linarith)
      calc θ⁻¹ * |Φ a b y₁ - Φ a b y₀ - g * (y₁ - y₀)| ≤ θ⁻¹ * (y₁ - y₀) := by
            gcongr
        _ = Real.log (n + 1) - Real.log n := by rw [hΔ]; field_simp
        _ ≤ 1 / n := hl1
    · unfold Irr at hirr
      simp only [ne_eq, not_or, not_not] at hirr
      have := Φ_step_reg ha hab hb (y₀ := y₀) (y₁ := y₁)
        (by have := hirr.1; unfold uθ at this; simp only [Nat.cast_add, Nat.cast_one] at this
            exact this.symm)
        (by have := hirr.2; unfold uθ at this; simp only [Nat.cast_add, Nat.cast_one] at this
            exact this.symm)
      rw [this, sub_self, mul_zero, abs_zero]
  calc _ ≤ |g / n - g * (Real.log (n + 1) - Real.log n)| +
        |θ⁻¹ * (Φ a b y₁ - Φ a b y₀ - g * (y₁ - y₀))| := abs_sub _ _
    _ ≤ _ := add_le_add e1 e2

end Linear

/-! ## Logarithmic sums of `1[{θ log n} ∈ [a, b)]` -/

section LinearSum

variable {θ a b : ℝ}

open scoped Classical in
/-- `∑_{n ≤ N} |d(n)| = o(log N)`. -/
lemma logSmall_sum_abs_dθ (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    LogSmall fun N => ∑ n ∈ Icc 1 N, |dθ θ a b n| := by
  set n₀ : ℕ := ⌈θ⌉₊ + 1
  have hn₀ : θ ≤ n₀ := by
    have := Nat.le_ceil θ; simp only [n₀]; push_cast; linarith
  set P : ℕ → Prop := fun n => n < n₀ ∨ Irr θ a b n
  set s : ℕ → ℝ := fun n => if P n then |dθ θ a b n| else 0
  set t : ℕ → ℝ := fun n => if P n then 0 else |dθ θ a b n|
  have hst : ∀ n, |dθ θ a b n| = s n + t n := fun n => by
    simp only [s, t]; split_ifs <;> ring
  -- crude bound for all `n ≥ 1`
  have hcrude : ∀ n : ℕ, 1 ≤ n → |dθ θ a b n| ≤ 2 / n + 4 / θ := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := abs_Φ_sub_le ha hab hb (θ * Real.log (n + 1))
    have h2 := abs_Φ_sub_le ha hab hb (θ * Real.log n)
    have hl := log_succ_sub_le hn
    have hl0 : 0 ≤ Real.log (n + 1) - Real.log n := by
      have := log_succ_sub_ge hn; have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
    have hg0 := ind_nonneg a b (θ * Real.log n)
    have hg1 := ind_le_one a b (θ * Real.log n)
    have hba0 : 0 ≤ b - a := by linarith
    have hba1 : b - a ≤ 1 := by linarith
    unfold dθ gθ Hθ
    simp only [Nat.cast_add, Nat.cast_one]
    have e : θ⁻¹ * Φ a b (θ * Real.log (↑n + 1)) - θ⁻¹ * Φ a b (θ * Real.log ↑n) =
        (b - a) * (Real.log (n + 1) - Real.log n) +
        θ⁻¹ * ((Φ a b (θ * Real.log (↑n + 1)) - (b - a) * (θ * Real.log (↑n + 1))) -
          (Φ a b (θ * Real.log ↑n) - (b - a) * (θ * Real.log ↑n))) := by
      field_simp; ring
    rw [e]
    have h3 : |θ⁻¹ * ((Φ a b (θ * Real.log (↑n + 1)) - (b - a) * (θ * Real.log (↑n + 1))) -
          (Φ a b (θ * Real.log ↑n) - (b - a) * (θ * Real.log ↑n)))| ≤ θ⁻¹ * 4 := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hθ)]
      gcongr
      calc _ ≤ |Φ a b (θ * Real.log (↑n + 1)) - (b - a) * (θ * Real.log (↑n + 1))| +
            |Φ a b (θ * Real.log ↑n) - (b - a) * (θ * Real.log ↑n)| := abs_sub _ _
        _ ≤ 4 := by linarith
    have h4 : |ind a b (θ * Real.log ↑n) / ↑n| ≤ 1 / n := by
      rw [abs_div, abs_of_nonneg hg0, abs_of_pos hn']
      exact div_le_div_of_nonneg_right hg1 hn'.le
    have h5 : |(b - a) * (Real.log (n + 1) - Real.log n)| ≤ 1 / n := by
      rw [abs_mul, abs_of_nonneg hba0, abs_of_nonneg hl0]
      calc (b - a) * (Real.log (n + 1) - Real.log n) ≤ 1 * (1 / n) :=
            mul_le_mul hba1 hl hl0 (by norm_num)
        _ = 1 / n := one_mul _
    have e2 : θ⁻¹ * 4 = 4 / θ := by field_simp
    calc _ ≤ |ind a b (θ * Real.log ↑n) / ↑n| + |(b - a) * (Real.log (n + 1) - Real.log n) +
          θ⁻¹ * ((Φ a b (θ * Real.log (↑n + 1)) - (b - a) * (θ * Real.log (↑n + 1))) -
          (Φ a b (θ * Real.log ↑n) - (b - a) * (θ * Real.log ↑n)))| := abs_sub _ _
      _ ≤ 1 / n + (1 / n + θ⁻¹ * 4) := add_le_add h4 ((abs_add_le _ _).trans (add_le_add h5 h3))
      _ = 2 / n + 4 / θ := by rw [e2]; ring
  -- the sparse part
  have hs : LogSmall fun N => ∑ n ∈ Icc 1 N, s n := by
    refine logSmall_sparse (P := P) (K := 2 + 4 * n₀ / θ) (C := n₀ + 2 * θ + 2)
      (by positivity) (fun n => by simp only [s]; split_ifs <;> simp)
      (fun n hn => by simp only [s]; rw [if_neg hn]) ?_ ?_
    · intro n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [s]
      split_ifs with hP
      · rcases hP with hlt | hirr
        · have h1 := hcrude n hn
          have hle : (n : ℝ) ≤ n₀ := by exact_mod_cast hlt.le
          have : 4 / θ ≤ 4 * n₀ / θ / n := by
            rw [div_div, div_le_div_iff₀ hθ (by positivity)]
            nlinarith
          calc |dθ θ a b n| ≤ 2 / n + 4 / θ := h1
            _ ≤ 2 / n + 4 * n₀ / θ / n := by linarith
            _ = (2 + 4 * n₀ / θ) / n := by ring
        · by_cases hge : θ ≤ n
          · have h1 := Hθ_step hθ ha hab hb hn hge
            rw [if_pos hirr] at h1
            have : 1 / (n : ℝ) - 1 / (n + 1) ≤ 1 / n := by
              have : (0 : ℝ) < 1 / (n + 1) := by positivity
              linarith
            calc |dθ θ a b n| ≤ 2 / n := by
                  have e : (2 : ℝ) / n = 1 / n + 1 / n := by ring
                  linarith
              _ ≤ (2 + 4 * n₀ / θ) / n := by
                  apply div_le_div_of_nonneg_right _ hn'.le
                  have : 0 ≤ 4 * (n₀ : ℝ) / θ := by positivity
                  linarith
          · push Not at hge
            have h1 := hcrude n hn
            have hle : (n : ℝ) ≤ n₀ := by linarith
            have : 4 / θ ≤ 4 * n₀ / θ / n := by
              rw [div_div, div_le_div_iff₀ hθ (by positivity)]
              nlinarith
            calc |dθ θ a b n| ≤ 2 / n + 4 / θ := h1
              _ ≤ 2 / n + 4 * n₀ / θ / n := by linarith
              _ = (2 + 4 * n₀ / θ) / n := by ring
      · positivity
    · intro N
      have hsub : (Icc 1 N).filter P ⊆ (range n₀) ∪ (Icc 1 N).filter (Irr θ a b) := by
        intro n hn
        obtain ⟨hn1, hP⟩ := mem_filter.1 hn
        rcases hP with hlt | hirr
        · exact mem_union_left _ (mem_range.2 hlt)
        · exact mem_union_right _ (mem_filter.2 ⟨hn1, hirr⟩)
      have h1 := (card_le_card hsub).trans (card_union_le _ _)
      rw [card_range] at h1
      have h1' : (((Icc 1 N).filter P).card : ℝ) ≤ n₀ + ((Icc 1 N).filter (Irr θ a b)).card := by
        exact_mod_cast h1
      have h2 := card_Irr_le' (a := a) (b := b) hθ.le N
      have hl := Real.log_natCast_nonneg N
      nlinarith
  -- the regular part is summable
  have ht : ∀ N, |∑ n ∈ Icc 1 N, t n| ≤ 1 := by
    intro N
    have h0 : ∀ n ∈ Icc 1 N, 0 ≤ t n := fun n _ => by simp only [t]; split_ifs <;> simp
    have h1 : ∀ n ∈ Icc 1 N, t n ≤ (-1 / ((n + 1 : ℕ) : ℝ)) - (-1 / (n : ℝ)) := by
      intro n hn
      have hn1 := (mem_Icc.1 hn).1
      simp only [t]
      have e : -1 / (((n + 1 : ℕ) : ℝ)) - -1 / (n : ℝ) = 1 / n - 1 / (n + 1) := by push_cast; ring
      rw [e]
      split_ifs with hP
      · have : (1 : ℝ) / (n + 1) ≤ 1 / n := by
          apply div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hn1) (by linarith)
        linarith
      · simp only [P, not_or, not_lt] at hP
        have hge : θ ≤ n := hn₀.trans (by exact_mod_cast hP.1)
        have := Hθ_step hθ ha hab hb hn1 hge
        rw [if_neg hP.2, add_zero] at this
        exact this
    have h2 := sum_le_sum h1
    rw [sum_Icc_telescope (fun n => -1 / (n : ℝ)) N] at h2
    rw [abs_of_nonneg (sum_nonneg h0)]
    have : (0 : ℝ) ≤ 1 / ((N + 1 : ℕ) : ℝ) := by positivity
    simp only [Nat.cast_one, div_one] at h2
    have e : -1 / ((N + 1 : ℕ) : ℝ) = -(1 / ((N + 1 : ℕ) : ℝ)) := by ring
    linarith
  have := hs.add (logSmall_of_bdd (Eventually.of_forall ht))
  refine this.congr' (Eventually.of_forall fun N => ?_)
  rw [← sum_add_distrib]
  exact sum_congr rfl fun n _ => (hst n).symm

/-- `∑_{n ≤ N} 1[{θ log n} ∈ [a, b)] / n = (b - a) log N + o(log N)`. -/
lemma logSmall_sum_gθ (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    LogSmall fun N => ∑ n ∈ Icc 1 N, gθ θ a b n / n - (b - a) * Real.log N := by
  have hdecomp : ∀ N, ∑ n ∈ Icc 1 N, gθ θ a b n / n =
      (Hθ θ a b (N + 1) - Hθ θ a b 1) + ∑ n ∈ Icc 1 N, dθ θ a b n := by
    intro N
    rw [← sum_Icc_telescope (Hθ θ a b) N, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by unfold dθ; ring
  have hbdd : ∀ᶠ N : ℕ in atTop, |Hθ θ a b (N + 1) - Hθ θ a b 1 - (b - a) * Real.log N| ≤
      2 / θ + 1 + |Hθ θ a b 1| := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h1 := abs_Φ_sub_le ha hab hb (θ * Real.log ((N + 1 : ℕ) : ℝ))
    have h2 := log_succ_le_log_add_one hN
    have h3 : Real.log N ≤ Real.log (N + 1) := Real.log_le_log (by exact_mod_cast hN) (by linarith)
    have e : Hθ θ a b (N + 1) - Hθ θ a b 1 - (b - a) * Real.log N =
        θ⁻¹ * (Φ a b (θ * Real.log ((N + 1 : ℕ) : ℝ)) - (b - a) * (θ * Real.log ((N + 1 : ℕ) : ℝ)))
        + (b - a) * (Real.log (N + 1) - Real.log N) - Hθ θ a b 1 := by
      unfold Hθ; push_cast; field_simp; ring
    rw [e]
    have h4 : |θ⁻¹ * (Φ a b (θ * Real.log ((N + 1 : ℕ) : ℝ)) -
        (b - a) * (θ * Real.log ((N + 1 : ℕ) : ℝ)))| ≤ 2 / θ := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hθ), div_eq_inv_mul]
      gcongr
    have h5 : |(b - a) * (Real.log (N + 1) - Real.log N)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ b - a), abs_of_nonneg (by linarith)]
      calc (b - a) * (Real.log (N + 1) - Real.log N) ≤ 1 * 1 :=
            mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
        _ = 1 := one_mul _
    calc _ ≤ |θ⁻¹ * (Φ a b (θ * Real.log ((N + 1 : ℕ) : ℝ)) -
          (b - a) * (θ * Real.log ((N + 1 : ℕ) : ℝ))) + (b - a) * (Real.log (N + 1) -
          Real.log N)| + |Hθ θ a b 1| := abs_sub _ _
      _ ≤ 2 / θ + 1 + |Hθ θ a b 1| := by
          gcongr; exact (abs_add_le _ _).trans (add_le_add h4 h5)
  have hd := (logSmall_sum_abs_dθ hθ ha hab hb).of_abs_le (u := fun N => ∑ n ∈ Icc 1 N,
    dθ θ a b n) (Eventually.of_forall fun N => abs_sum_le_sum_abs _ _)
  have := (logSmall_of_bdd hbdd).add hd
  refine this.congr' (Eventually.of_forall fun N => ?_)
  simp only [hdecomp]; ring

end LinearSum

/-! ## Alternating logarithmic sums -/

lemma changes_mono_left {α : Type*} (h : ℕ → α) {m m' N : ℕ} (hm : m ≤ m') :
    changes h m' N ≤ changes h m N := by
  classical
  unfold changes
  exact sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico hm le_rfl) fun _ _ _ => Nat.zero_le _

lemma changes_natCast (u : ℕ → ℕ) (m N : ℕ) :
    changes (fun n => (u n : ℤ)) m N = changes u m N := by
  classical
  unfold changes
  refine sum_congr rfl fun n _ => ?_
  by_cases h : u (n + 1) = u n <;> simp [h]

lemma changes_le_of_monotone_nat {u : ℕ → ℕ} (hu : Monotone u) {m N : ℕ} (hmN : m ≤ N) :
    changes u m N ≤ u N - u m := by
  have h := changes_le_of_monotone (u := fun n => (u n : ℤ))
    (fun a b hab => by show (u a : ℤ) ≤ u b; exact_mod_cast hu hab) hmN
  rw [changes_natCast] at h
  have := hu hmN
  omega

/-- If `|h| ≤ 1` and `h` has `O(log N)` changes on `[1, N]`, then
`∑_{M₀ ≤ n ≤ N} (-1)^n h(n) / n = o(log N)`. -/
lemma logSmall_alt {h : ℕ → ℝ} (hh : ∀ n, |h n| ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hch : ∀ N : ℕ, (changes h 1 (N + 1) : ℝ) ≤ C * (Real.log N + 1)) (M₀ : ℕ) :
    LogSmall fun N => ∑ n ∈ Icc 1 N, if M₀ ≤ n then (-1) ^ n * h n * (1 / n) else 0 := by
  classical
  apply logSmall_of_forall
  intro ε hε
  obtain ⟨M₁, hM₁⟩ := exists_nat_gt (2 * C / ε)
  set M := M₁ + M₀ + 1
  have hM1 : 1 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hCM : 2 * C / M ≤ ε := by
    rw [div_le_iff₀ hMpos]
    rw [div_lt_iff₀ hε] at hM₁
    have : (M₁ : ℝ) ≤ M := by simp only [M]; push_cast; linarith
    nlinarith
  set x : ℕ → ℝ := fun n => if M₀ ≤ n then (-1) ^ n * h n * (1 / n) else 0
  have hx : ∀ n, |x n| ≤ 1 := by
    intro n
    simp only [x]
    split_ifs
    · rw [abs_mul, abs_mul]
      have h1 : |((-1 : ℝ)) ^ n| = 1 := by simp
      rw [h1, one_mul]
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp
      · have : |1 / (n : ℝ)| ≤ 1 := by
          rw [abs_of_pos (by positivity), div_le_one (by exact_mod_cast h0)]
          exact_mod_cast h0
        calc |h n| * |1 / (n : ℝ)| ≤ 1 * 1 := mul_le_mul (hh n) this (abs_nonneg _) (by norm_num)
          _ = 1 := one_mul _
    · simp
  refine ⟨M + (1 + 2 * C), ?_⟩
  filter_upwards [eventually_ge_atTop M] with N hN
  show |∑ n ∈ Icc 1 N, x n| ≤ M + (1 + 2 * C) + ε * Real.log N
  rw [← Finset.Ico_add_one_right_eq_Icc, ← sum_Ico_consecutive x hM1 (by omega : M ≤ N + 1)]
  have h1 : |∑ n ∈ Ico 1 M, x n| ≤ M := by
    calc |∑ n ∈ Ico 1 M, x n| ≤ ∑ n ∈ Ico 1 M, |x n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Ico 1 M, (1 : ℝ) := sum_le_sum fun n _ => hx n
      _ = (M - 1 : ℕ) := by simp
      _ ≤ M := by exact_mod_cast Nat.sub_le M 1
  have h2 : ∑ n ∈ Ico M (N + 1), x n = ∑ n ∈ Ico M (N + 1), (-1) ^ n * h n * (1 / n) := by
    refine sum_congr rfl fun n hn => ?_
    simp only [x]
    rw [if_pos (by have := (mem_Ico.1 hn).1; omega)]
  have hw : ∀ n, M ≤ n → 0 ≤ 1 / (n : ℝ) ∧ 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 / (n : ℝ) := by
    intro n hn
    have : (1 : ℝ) ≤ n := by exact_mod_cast hM1.trans hn
    refine ⟨by positivity, ?_⟩
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith)
    push_cast; linarith
  have h3 := abs_alt_le (w := fun n => 1 / (n : ℝ)) hw hh (by omega : M ≤ N + 1)
  have h4 : (changes h M (N + 1) : ℝ) ≤ C * (Real.log N + 1) :=
    (by exact_mod_cast changes_mono_left h hM1 : (changes h M (N + 1) : ℝ) ≤
      changes h 1 (N + 1)).trans (hch N)
  rw [h2]
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h5 : 1 / (M : ℝ) * (1 + 2 * (C * (Real.log N + 1))) ≤ (1 + 2 * C) + ε * Real.log N := by
    have : 1 / (M : ℝ) ≤ 1 := by rw [div_le_one hMpos]; exact_mod_cast hM1
    have e : 1 / (M : ℝ) * (1 + 2 * (C * (Real.log N + 1))) =
        1 / M * (1 + 2 * C) + (2 * C / M) * Real.log N := by ring
    rw [e]
    have : 1 / (M : ℝ) * (1 + 2 * C) ≤ 1 * (1 + 2 * C) := by gcongr
    have : 2 * C / M * Real.log N ≤ ε * Real.log N := by gcongr
    linarith
  calc |∑ n ∈ Ico 1 M, x n + ∑ n ∈ Ico M (N + 1), (-1) ^ n * h n * (1 / ↑n)|
      ≤ |∑ n ∈ Ico 1 M, x n| + |∑ n ∈ Ico M (N + 1), (-1) ^ n * h n * (1 / ↑n)| := abs_add_le _ _
    _ ≤ M + 1 / (M : ℝ) * (1 + 2 * (C * (Real.log N + 1))) := by
        gcongr
        refine h3.trans ?_
        gcongr
    _ ≤ M + (1 + 2 * C) + ε * Real.log N := by linarith

/-! ## The set of Kousek and Radić: logarithmic density and `(21)` -/

/-- `Q = {n ≥ 4 : n ≡ ⌊log₂ n⌋ (mod 2)}`. -/
def Qset : Set ℕ := {n | 4 ≤ n ∧ (Even n ↔ Even (Nat.log 2 n))}

/-- `W_k = [(2 - 1/k) 4^k, (2 + 1/k) 4^k)`. -/
def Wk (k : ℕ) : Set ℕ :=
  {n | (2 - 1 / (k : ℝ)) * 4 ^ k ≤ n ∧ (n : ℝ) < (2 + 1 / (k : ℝ)) * 4 ^ k}

/-- `W = ⋃_{k ≥ 1} W_k`. -/
def W : Set ℕ := {n | ∃ k, 1 ≤ k ∧ n ∈ Wk k}

lemma log2_eq {k n : ℕ} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) : Nat.log 2 n = k :=
  (Nat.log_eq_iff (Or.inr ⟨by norm_num, by have := Nat.one_le_two_pow (n := k); omega⟩)).2
    ⟨h1, h2⟩

lemma four_pow (k : ℕ) : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num

lemma AKR_subset_Q : AKR ⊆ Qset := by
  rintro m (⟨hme, n, hn, h1, h2⟩ | ⟨hmo, n, hn, h1, h2⟩)
  · have h2' : m < 2 * 4 ^ n := by
      have : (m : ℝ) < 2 * 4 ^ n := by
        have : 0 ≤ 1 / (n : ℝ) * 4 ^ n := by positivity
        nlinarith
      exact_mod_cast this
    have hl : Nat.log 2 m = 2 * n := log2_eq (by rw [← four_pow]; exact h1)
      (by rw [pow_succ, ← four_pow]; linarith)
    refine ⟨le_trans (by calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn) h1, ?_⟩
    rw [hl]
    exact ⟨fun _ => even_two_mul n, fun _ => hme⟩
  · have h1' : 2 * 4 ^ n ≤ m := by
      have : (2 : ℝ) * 4 ^ n ≤ m := by
        have : 0 ≤ 1 / (n : ℝ) * 4 ^ n := by positivity
        nlinarith
      exact_mod_cast this
    have hl : Nat.log 2 m = 2 * n + 1 := log2_eq (by rw [pow_succ, ← four_pow]; linarith)
      (by rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, ← four_pow]; exact h2)
    refine ⟨le_trans (by calc 4 ≤ 2 * 4 ^ 1 := by norm_num
      _ ≤ 2 * 4 ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hn)) h1', ?_⟩
    rw [hl]
    exact ⟨fun h => absurd h (Nat.not_even_iff_odd.2 hmo),
      fun h => absurd h (Nat.not_even_iff_odd.2 (odd_two_mul_add_one n))⟩

lemma mem_AKR_of_Q {n : ℕ} (hQ : n ∈ Qset) (hW : n ∉ W) : n ∈ AKR := by
  obtain ⟨h4, hpar⟩ := hQ
  set L := Nat.log 2 n with hL
  have hn0 : n ≠ 0 := by omega
  have hL1 : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
  have hL2 : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hL2' : 2 ≤ L := by
    have : Nat.log 2 4 ≤ L := Nat.log_mono_right h4
    have e : Nat.log 2 4 = 2 := log2_eq (by norm_num) (by norm_num)
    omega
  rcases Nat.even_or_odd' L with ⟨k, hk | hk⟩
  · -- `L = 2k`: `n` is even and `4^k ≤ n < 2 · 4^k`
    have hk1 : 1 ≤ k := by omega
    have hne : Even n := hpar.2 (by rw [hk]; exact even_two_mul k)
    rw [hk, ← four_pow] at hL1
    rw [hk, pow_succ, ← four_pow] at hL2
    left
    refine ⟨hne, k, hk1, hL1, ?_⟩
    by_contra hcon
    apply hW
    refine ⟨k, hk1, not_lt.1 hcon, ?_⟩
    have : (n : ℝ) < 4 ^ k * 2 := by exact_mod_cast hL2
    have : 0 ≤ 1 / (k : ℝ) * 4 ^ k := by positivity
    nlinarith
  · -- `L = 2k + 1`: `n` is odd and `2 · 4^k ≤ n < 4^{k+1}`
    have hk1 : 1 ≤ k := by omega
    have hno : Odd n := by
      rw [← Nat.not_even_iff_odd]
      intro he
      have := hpar.1 he
      rw [hk] at this
      exact (Nat.not_even_iff_odd.2 (odd_two_mul_add_one k)) this
    rw [hk, pow_succ, ← four_pow] at hL1
    rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, ← four_pow] at hL2
    right
    refine ⟨hno, k, hk1, ?_, hL2⟩
    by_contra hcon
    apply hW
    refine ⟨k, hk1, ?_, not_le.1 hcon⟩
    have : (4 : ℝ) ^ k * 2 ≤ n := by exact_mod_cast hL1
    have : 0 ≤ 1 / (k : ℝ) * 4 ^ k := by positivity
    nlinarith

lemma neg_one_pow_mul_eq (n L : ℕ) :
    ((-1 : ℝ) ^ n * (-1) ^ L = 1 ↔ (Even n ↔ Even L)) ∧
    ((-1 : ℝ) ^ n * (-1) ^ L = 1 ∨ (-1 : ℝ) ^ n * (-1) ^ L = -1) := by
  rcases Nat.even_or_odd n with hn | hn <;> rcases Nat.even_or_odd L with hL | hL <;>
    simp [hn.neg_one_pow, hL.neg_one_pow, hn, hL, Nat.not_even_iff_odd.2]
      <;> norm_num

lemma Q_indicator (G : ℕ → ℝ) (n : ℕ) :
    Qset.indicator G n =
      (if 4 ≤ n then G n / 2 else 0) +
      (if 4 ≤ n then (-1) ^ n * ((-1) ^ Nat.log 2 n * G n) * (1 / 2) else 0) := by
  classical
  have h := neg_one_pow_mul_eq n (Nat.log 2 n)
  by_cases h4 : 4 ≤ n
  · rw [if_pos h4, if_pos h4]
    by_cases hp : (Even n ↔ Even (Nat.log 2 n))
    · rw [Set.indicator_of_mem (show n ∈ Qset from ⟨h4, hp⟩)]
      have := h.1.2 hp
      linear_combination (-(G n) / 2) * this
    · rw [Set.indicator_of_notMem (fun h' => hp h'.2)]
      have : (-1 : ℝ) ^ n * (-1) ^ Nat.log 2 n = -1 := by
        rcases h.2 with h' | h'
        · exact absurd (h.1.1 h') hp
        · exact h'
      linear_combination (-(G n) / 2) * this
  · rw [if_neg h4, if_neg h4, Set.indicator_of_notMem (fun h' => h4 h'.1)]; ring

lemma card_Ico_real_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (s : Finset ℕ) :
    ((s.filter fun n : ℕ => x ≤ n ∧ (n : ℝ) < y).card : ℝ) ≤ y - x + 1 := by
  classical
  have hsub : s.filter (fun n : ℕ => x ≤ n ∧ (n : ℝ) < y) ⊆ Ico ⌈x⌉₊ ⌈y⌉₊ := by
    intro n hn
    obtain ⟨-, h1, h2⟩ := mem_filter.1 hn
    exact mem_Ico.2 ⟨Nat.ceil_le.2 h1, Nat.lt_ceil.2 h2⟩
  have h1 := card_le_card hsub
  rw [Nat.card_Ico] at h1
  have h2 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
  have h3 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have h4 : ⌈x⌉₊ ≤ ⌈y⌉₊ := Nat.ceil_mono hxy
  have h5 : (((s.filter fun n : ℕ => x ≤ n ∧ (n : ℝ) < y).card : ℕ) : ℝ) ≤
      ((⌈y⌉₊ - ⌈x⌉₊ : ℕ) : ℝ) := by exact_mod_cast h1
  rw [Nat.cast_sub h4] at h5
  linarith

lemma sum_Wk_le {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (Wk k).indicator (fun n : ℕ => 1 / (n : ℝ)) n ≤ 3 / k := by
  classical
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h4k : (0 : ℝ) < 4 ^ k := by positivity
  have hx : (0 : ℝ) ≤ (2 - 1 / (k : ℝ)) * 4 ^ k := by
    have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hk'
    nlinarith
  have hterm : ∀ n ∈ Icc 1 N, (Wk k).indicator (fun n : ℕ => 1 / (n : ℝ)) n ≤
      if (2 - 1 / (k : ℝ)) * 4 ^ k ≤ n ∧ (n : ℝ) < (2 + 1 / (k : ℝ)) * 4 ^ k
      then 1 / 4 ^ k else 0 := by
    intro n hn
    by_cases h : n ∈ Wk k
    · rw [Set.indicator_of_mem h, if_pos (show (2 - 1 / (k : ℝ)) * 4 ^ k ≤ n ∧
        (n : ℝ) < (2 + 1 / (k : ℝ)) * 4 ^ k from h)]
      have : (4 : ℝ) ^ k ≤ n := by
        have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hk'
        nlinarith [h.1]
      exact div_le_div_of_nonneg_left (by norm_num) h4k this
    · rw [Set.indicator_of_notMem h, if_neg (show ¬((2 - 1 / (k : ℝ)) * 4 ^ k ≤ n ∧
        (n : ℝ) < (2 + 1 / (k : ℝ)) * 4 ^ k) from h)]
  refine (sum_le_sum hterm).trans ?_
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  have hc := card_Ico_real_le hx (y := (2 + 1 / (k : ℝ)) * 4 ^ k)
    (by have : 0 ≤ 1 / (k : ℝ) := by positivity
        nlinarith) (Icc 1 N)
  have e : (2 + 1 / (k : ℝ)) * 4 ^ k - (2 - 1 / (k : ℝ)) * 4 ^ k + 1 = 2 / k * 4 ^ k + 1 := by
    ring
  rw [e] at hc
  have hk4 : (k : ℝ) ≤ 4 ^ k := by
    have : k < 4 ^ k := Nat.lt_pow_self (by norm_num)
    exact_mod_cast this.le
  calc _ ≤ (2 / (k : ℝ) * 4 ^ k + 1) * (1 / 4 ^ k) := by gcongr
    _ = 2 / (k : ℝ) + 1 / 4 ^ k := by
        rw [add_mul, mul_assoc, mul_one_div_cancel h4k.ne', mul_one, one_mul]
    _ ≤ 2 / (k : ℝ) + 1 / k := by gcongr
    _ = 3 / (k : ℝ) := by ring

/-- `∑_{n ≤ N, n ∈ W} 1/n = o(log N)`. -/
lemma logSmall_W : LogSmall fun N => ∑ n ∈ Icc 1 N, W.indicator (fun n : ℕ => 1 / (n : ℝ)) n := by
  classical
  apply logSmall_of_forall
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (3 / ε)
  have hk₀pos : (0 : ℝ) < k₀ := lt_of_le_of_lt (by positivity) hk₀
  refine ⟨3 * k₀, Eventually.of_forall fun N => ?_⟩
  set K := Nat.log 4 N
  -- `1_W(n)/n ≤ ∑_{k ≤ K} 1_{W_k}(n)/n`
  have hterm : ∀ n ∈ Icc 1 N, W.indicator (fun n : ℕ => 1 / (n : ℝ)) n ≤
      ∑ k ∈ Icc 1 K, (Wk k).indicator (fun n : ℕ => 1 / (n : ℝ)) n := by
    intro n hn
    by_cases h : n ∈ W
    · obtain ⟨k, hk, hkn⟩ := h
      rw [Set.indicator_of_mem (show n ∈ W from ⟨k, hk, hkn⟩)]
      have hkK : k ∈ Icc 1 K := by
        refine mem_Icc.2 ⟨hk, ?_⟩
        have h1 : (4 : ℝ) ^ k ≤ n := by
          have : 1 / (k : ℝ) ≤ 1 := by
            rw [div_le_one (by exact_mod_cast hk)]; exact_mod_cast hk
          nlinarith [hkn.1, (by positivity : (0 : ℝ) ≤ 4 ^ k)]
        have h2 : 4 ^ k ≤ N := by
          have : 4 ^ k ≤ n := by exact_mod_cast h1
          exact this.trans (mem_Icc.1 hn).2
        exact Nat.le_log_of_pow_le (by norm_num) h2
      have := single_le_sum (f := fun k => (Wk k).indicator (fun n : ℕ => 1 / (n : ℝ)) n)
        (fun k _ => Set.indicator_nonneg (fun n _ => by positivity) n) hkK
      simpa [Set.indicator_of_mem hkn] using this
    · rw [Set.indicator_of_notMem h]
      exact sum_nonneg fun k _ => Set.indicator_nonneg (fun n _ => by positivity) n
  have h1 := sum_le_sum hterm
  rw [sum_comm] at h1
  have h2 : ∑ k ∈ Icc 1 K, ∑ n ∈ Icc 1 N, (Wk k).indicator (fun n : ℕ => 1 / (n : ℝ)) n ≤
      ∑ k ∈ Icc 1 K, ((if k < k₀ then 3 else 0) + 3 / k₀ : ℝ) := by
    refine sum_le_sum fun k hk => (sum_Wk_le (mem_Icc.1 hk).1 N).trans ?_
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.1 hk).1
    split_ifs with hkk
    · have : 3 / (k : ℝ) ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
      have : 0 ≤ 3 / (k₀ : ℝ) := by positivity
      linarith
    · rw [zero_add]
      exact div_le_div_of_nonneg_left (by norm_num) hk₀pos (by exact_mod_cast not_lt.1 hkk)
  rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero, sum_const, sum_const, nsmul_eq_mul,
    nsmul_eq_mul] at h2
  have h3 : (((Icc 1 K).filter fun k => k < k₀).card : ℝ) ≤ k₀ := by
    have : (Icc 1 K).filter (fun k => k < k₀) ⊆ range k₀ := fun k hk =>
      mem_range.2 (mem_filter.1 hk).2
    exact_mod_cast (card_le_card this).trans (card_range _).le
  have h4 : ((Icc 1 K).card : ℝ) ≤ Real.log N := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [K]
    · have h5 : 4 ^ K ≤ N := Nat.pow_log_le_self 4 (by omega)
      have h6 : (K : ℝ) * Real.log 4 ≤ Real.log N := by
        have := Real.log_le_log (by positivity) (show ((4 : ℕ) ^ K : ℝ) ≤ N by exact_mod_cast h5)
        simpa [Real.log_pow] using this
      have h7 : (1 : ℝ) ≤ Real.log 4 := by
        have := Real.log_two_gt_d9
        have e : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        linarith
      have : (0 : ℝ) ≤ K := K.cast_nonneg
      nlinarith
  have hs0 : 0 ≤ ∑ n ∈ Icc 1 N, W.indicator (fun n : ℕ => 1 / (n : ℝ)) n :=
    sum_nonneg fun n _ => Set.indicator_nonneg (fun n _ => by positivity) n
  rw [abs_of_nonneg hs0]
  have h8 : 3 / (k₀ : ℝ) ≤ ε := by
    rw [div_le_iff₀ hk₀pos]; rw [div_lt_iff₀ hε] at hk₀; linarith
  have hl := Real.log_natCast_nonneg N
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ k₀ * 3 + Real.log N * (3 / k₀) := by gcongr
    _ ≤ 3 * k₀ + ε * Real.log N := by nlinarith

/-- `(-1)^k (p₁ - p₂)`. -/
noncomputable def sgnPair (k : ℕ) (p : ℤ × ℤ) : ℝ := (-1) ^ k * ((p.1 - p.2 : ℤ) : ℝ)

lemma changes_congr {α : Type*} {h h' : ℕ → α} (e : ∀ n, h n = h' n) (m N : ℕ) :
    changes h m N = changes h' m N := by
  rw [show h = h' from funext e]

/-- `h(n) = (-1)^{⌊log₂ n⌋} 1[{θ log n} ∈ [a, b)]` has `O(log N)` changes. -/
lemma changes_hKR {θ a b : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (N : ℕ) :
    (changes (fun n => (-1 : ℝ) ^ Nat.log 2 n * gθ θ a b n) 1 (N + 1) : ℝ) ≤
      (2 * θ + 4) * (Real.log N + 1) := by
  rw [changes_congr (h' := fun n => sgnPair (Nat.log 2 n) (uθ θ a n, uθ θ b n)) (fun n => by
    simp only [sgnPair, gθ, uθ]; rw [ind_eq_floor ha hab hb])]
  have h1 := changes_comp₂ sgnPair (fun n => Nat.log 2 n) (fun n => (uθ θ a n, uθ θ b n)) 1 (N + 1)
  have h2 := changes_comp₂ Prod.mk (uθ θ a) (uθ θ b) 1 (N + 1)
  have h3 := changes_le_of_monotone_nat (u := fun n => Nat.log 2 n)
    (fun x y hxy => Nat.log_mono_right hxy) (by omega : 1 ≤ N + 1)
  have h4 := uθ_changes hθ.le a N
  have h5 := uθ_changes hθ.le b N
  have h6 : (Nat.log 2 (N + 1) : ℝ) ≤ 2 * Real.log (N + 1) := by
    have h7 : 2 ^ Nat.log 2 (N + 1) ≤ N + 1 := Nat.pow_log_le_self 2 (by omega)
    have h8 : (Nat.log 2 (N + 1) : ℝ) * Real.log 2 ≤ Real.log (N + 1) := by
      have := Real.log_le_log (by positivity)
        (show ((2 : ℕ) ^ Nat.log 2 (N + 1) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by exact_mod_cast h7)
      simpa [Real.log_pow] using this
    have := Real.log_two_gt_d9
    have : (0 : ℝ) ≤ Nat.log 2 (N + 1) := Nat.cast_nonneg _
    nlinarith
  have hc : (changes (fun n => sgnPair (Nat.log 2 n) (uθ θ a n, uθ θ b n)) 1 (N + 1) : ℝ) ≤
      ((Nat.log 2 (N + 1) - Nat.log 2 1 : ℕ) : ℝ) + ((changes (uθ θ a) 1 (N + 1) : ℕ) : ℝ) +
        ((changes (uθ θ b) 1 (N + 1) : ℕ) : ℝ) := by
    have := h1.trans (add_le_add h3 h2)
    exact_mod_cast (show _ ≤ _ by omega)
  simp only [Nat.log_one_right, Nat.sub_zero] at hc
  have hlog : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by linarith [N.cast_nonneg (α := ℝ)])
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    simp only [CharP.cast_eq_zero, zero_add, Real.log_one, Real.log_zero, mul_zero] at *
    nlinarith
  · have := log_succ_le_log_add_one h0
    have := Real.log_natCast_nonneg N
    nlinarith

/-- The half-open version of `(21)` for `A_KR`: for `θ > 0` and `0 ≤ a ≤ b ≤ 1`,
`∑_{n ≤ N, n ∈ A_KR, {θ log n} ∈ [a, b)} 1/n = (1/2)(b - a) log N + o(log N)`. -/
lemma logSmall_AKR {θ a b : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    LogSmall fun N => ∑ n ∈ Icc 1 N, AKR.indicator (fun n : ℕ => gθ θ a b n / n) n -
      1 / 2 * (b - a) * Real.log N := by
  classical
  set G : ℕ → ℝ := fun n => gθ θ a b n / n
  have hG0 : ∀ n, 0 ≤ G n := fun n => div_nonneg (ind_nonneg _ _ _) n.cast_nonneg
  have hG1 : ∀ n, G n ≤ 1 / n := fun n => div_le_div_of_nonneg_right (ind_le_one _ _ _)
    n.cast_nonneg
  -- `1_{A_KR} G = 1_Q G - e` with `0 ≤ e ≤ 1_W / n`
  have hE : LogSmall fun N => ∑ n ∈ Icc 1 N, (Qset.indicator G n - AKR.indicator G n) := by
    refine logSmall_W.of_abs_le (Eventually.of_forall fun N => ?_)
    have h0 : ∀ n, 0 ≤ Qset.indicator G n - AKR.indicator G n := by
      intro n
      by_cases h : n ∈ AKR
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (AKR_subset_Q h), sub_self]
      · rw [Set.indicator_of_notMem h, sub_zero]
        exact Set.indicator_nonneg (fun n _ => hG0 n) n
    rw [abs_of_nonneg (sum_nonneg fun n _ => h0 n)]
    refine sum_le_sum fun n _ => ?_
    by_cases h : n ∈ AKR
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (AKR_subset_Q h), sub_self]
      exact Set.indicator_nonneg (fun n _ => by positivity) n
    · rw [Set.indicator_of_notMem h, sub_zero]
      by_cases hQ : n ∈ Qset
      · have hW : n ∈ W := by
          by_contra hW; exact h (mem_AKR_of_Q hQ hW)
        rw [Set.indicator_of_mem hQ, Set.indicator_of_mem hW]
        exact hG1 n
      · rw [Set.indicator_of_notMem hQ]
        exact Set.indicator_nonneg (fun n _ => by positivity) n
  -- the main term
  have hmain : LogSmall fun N => ∑ n ∈ Icc 1 N, (if 4 ≤ n then G n / 2 else 0) -
      1 / 2 * (b - a) * Real.log N := by
    have h1 := (logSmall_sum_gθ hθ ha hab hb).const_mul (1 / 2)
    have h2 : LogSmall fun N => ∑ n ∈ Icc 1 N, (if 4 ≤ n then 0 else G n / 2) := by
      refine logSmall_of_bdd (C := 4) (Eventually.of_forall fun N => ?_)
      have h3 : ∀ n ∈ Icc 1 N, |if 4 ≤ n then 0 else G n / 2| ≤ if n < 4 then 1 else 0 := by
        intro n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 hn).1
        by_cases h4 : 4 ≤ n
        · rw [if_pos h4, if_neg (by omega)]; simp
        · rw [if_neg h4, if_pos (by omega)]
          rw [abs_of_nonneg (by have := hG0 n; linarith)]
          have := hG1 n
          have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hn1
          linarith
      calc _ ≤ ∑ n ∈ Icc 1 N, |if 4 ≤ n then 0 else G n / 2| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Icc 1 N, (if n < 4 then (1 : ℝ) else 0) := sum_le_sum h3
        _ = (((Icc 1 N).filter fun n => n < 4).card : ℝ) := by rw [sum_ite]; simp
        _ ≤ 4 := by
            have : (Icc 1 N).filter (fun n => n < 4) ⊆ range 4 := fun n hn =>
              mem_range.2 (mem_filter.1 hn).2
            exact_mod_cast (card_le_card this).trans (card_range _).le
    have := h1.sub h2
    refine this.congr' (Eventually.of_forall fun N => ?_)
    simp only [G]
    have e : ∀ n : ℕ, (if 4 ≤ n then gθ θ a b n / n / 2 else 0) =
        1 / 2 * (gθ θ a b n / n) - (if 4 ≤ n then 0 else gθ θ a b n / n / 2) := by
      intro n; split_ifs <;> ring
    rw [sum_congr rfl fun n _ => e n, sum_sub_distrib, ← mul_sum]
    ring
  -- the alternating term
  have halt := (logSmall_alt (h := fun n => (-1 : ℝ) ^ Nat.log 2 n * gθ θ a b n)
    (fun n => by
      rw [abs_mul]; simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul]
      simp only [gθ]
      rw [abs_of_nonneg (ind_nonneg _ _ _)]; exact ind_le_one _ _ _)
    (by positivity) (changes_hKR hθ ha hab hb) 4).const_mul (1 / 2)
  have := (hmain.add halt).sub hE
  refine this.congr' (Eventually.of_forall fun N => ?_)
  have e : ∀ n : ℕ, AKR.indicator G n = (if 4 ≤ n then G n / 2 else 0) +
      1 / 2 * (if 4 ≤ n then (-1) ^ n * ((-1) ^ Nat.log 2 n * gθ θ a b n) * (1 / n) else 0) -
      (Qset.indicator G n - AKR.indicator G n) := by
    intro n
    rw [Q_indicator G n]
    simp only [G]
    split_ifs <;> ring
  simp only [G] at e ⊢
  rw [sum_congr rfl fun n _ => e n]
  simp only [sum_sub_distrib, sum_add_distrib, mul_sum]
  ring

/-! ## From half-open to open intervals -/

lemma sum_indicator_mono {S T : Set ℕ} (h : S ⊆ T) (N : ℕ) :
    ∑ n ∈ Icc 1 N, S.indicator (fun n : ℕ => (1 : ℝ) / n) n ≤
      ∑ n ∈ Icc 1 N, T.indicator (fun n : ℕ => (1 : ℝ) / n) n :=
  sum_le_sum fun n _ => Set.indicator_le_indicator_of_subset h (fun n => by positivity) n

/-- A squeeze criterion for logarithmic densities. -/
lemma hasLogDensity_of_squeeze {S : Set ℕ} {d : ℝ}
    (hlow : ∀ δ > 0, ∃ S' ⊆ S, ∃ d', d - δ ≤ d' ∧ HasLogDensity S' d')
    (hup : ∃ S'', S ⊆ S'' ∧ HasLogDensity S'' d) : HasLogDensity S d := by
  rw [HasLogDensity, tendsto_order]
  constructor
  · intro y hy
    obtain ⟨S', hS', d', hd', hS'd⟩ := hlow ((d - y) / 2) (by linarith)
    filter_upwards [hS'd.eventually (lt_mem_nhds (by linarith : y < d')), eventually_log_pos]
      with N hN hlog
    exact lt_of_lt_of_le hN (div_le_div_of_nonneg_right (sum_indicator_mono hS' N) hlog.le)
  · intro y hy
    obtain ⟨S'', hS'', hS''d⟩ := hup
    filter_upwards [hS''d.eventually (gt_mem_nhds hy), eventually_log_pos] with N hN hlog
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (sum_indicator_mono hS'' N) hlog.le) hN

lemma indicator_phase (A : Set ℕ) (θ a b : ℝ) (n : ℕ) :
    {n ∈ A | Int.fract (θ * Real.log n) ∈ Set.Ico a b}.indicator (fun n : ℕ => (1 : ℝ) / n) n =
      A.indicator (fun n : ℕ => gθ θ a b n / n) n := by
  classical
  by_cases hA : n ∈ A
  · rw [Set.indicator_of_mem hA]
    simp only [gθ, ind]
    by_cases hI : Int.fract (θ * Real.log n) ∈ Set.Ico a b
    · rw [Set.indicator_of_mem (show n ∈ {n ∈ A | Int.fract (θ * Real.log n) ∈ Set.Ico a b}
        from ⟨hA, hI⟩), if_pos hI]
    · rw [Set.indicator_of_notMem (fun h => hI h.2), if_neg hI]; simp
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem (fun h => hA h.1)]

/-- If `(21)` holds for all half-open intervals `[a, b)`, it holds for all open intervals. -/
lemma eq21_open_of_half {A : Set ℕ} {d θ : ℝ} (hd : 0 ≤ d)
    (h : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      HasLogDensity {n ∈ A | Int.fract (θ * Real.log n) ∈ Set.Ico a b} (d * (b - a)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    HasLogDensity {n ∈ A | Int.fract (θ * Real.log n) ∈ Set.Ioo a b} (d * (b - a)) := by
  apply hasLogDensity_of_squeeze
  · intro δ hδ
    set m := min (δ / (d + 1)) ((b - a) / 2)
    set a' := a + m
    have h1 : 0 < m := lt_min (by positivity) (by linarith)
    have h2 : m ≤ (b - a) / 2 := min_le_right _ _
    have h3 : m ≤ δ / (d + 1) := min_le_left _ _
    have h4 : d * m ≤ δ := by
      calc d * m ≤ d * (δ / (d + 1)) := by gcongr
        _ ≤ (d + 1) * (δ / (d + 1)) := by gcongr; linarith
        _ = δ := by field_simp
    refine ⟨{n ∈ A | Int.fract (θ * Real.log n) ∈ Set.Ico a' b}, ?_, d * (b - a'), ?_,
      h a' b (by simp only [a']; linarith) (by simp only [a']; linarith) hb⟩
    · rintro n ⟨hn, h1', h2'⟩
      exact ⟨hn, by simp only [a'] at h1'; linarith, h2'⟩
    · simp only [a']
      nlinarith
  · refine ⟨{n ∈ A | Int.fract (θ * Real.log n) ∈ Set.Ico a b}, ?_, h a b ha hab.le hb⟩
    rintro n ⟨hn, h1, h2⟩
    exact ⟨hn, h1.le, h2⟩

/-! ## Proposition \ref{IA:prop:KR} and the negative answer to Question 3.24 -/

lemma AKR_half {θ a b : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    HasLogDensity {n ∈ AKR | Int.fract (θ * Real.log n) ∈ Set.Ico a b} (1 / 2 * (b - a)) := by
  have := tendsto_of_logSmall (logSmall_AKR hθ ha hab hb)
  unfold HasLogDensity
  simp only [indicator_phase]
  convert this using 2

/-- Paper, Proposition \ref{IA:prop:KR}: `A_KR` has logarithmic density `1/2`. -/
theorem AKR_logDensity : HasLogDensity AKR (1 / 2) := by
  have h := AKR_half (θ := 1) (a := 0) (b := 1) one_pos le_rfl zero_le_one le_rfl
  have e : {n ∈ AKR | Int.fract (1 * Real.log n) ∈ Set.Ico (0 : ℝ) 1} = AKR := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_Ico, Int.fract_nonneg, Int.fract_lt_one, and_self,
      and_true]
  rw [e] at h
  simpa using h

/-- Paper, Proposition \ref{IA:prop:KR}: `A_KR` satisfies `(21)`, i.e. for every `θ > 0` and every
interval `(a, b) ⊆ [0, 1)`, `d_log({n ∈ A_KR : {θ log n} ∈ (a, b)}) = d_log(A_KR) (b - a)`. -/
theorem AKR_eq21 {θ a b : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    HasLogDensity {n ∈ AKR | Int.fract (θ * Real.log n) ∈ Set.Ioo a b} (1 / 2 * (b - a)) :=
  eq21_open_of_half (by norm_num) (fun a b ha hab hb => AKR_half hθ ha hab hb) ha hab hb

/-- Question 3.24 of the survey (Question \ref{IA:q:324}): if `A ⊆ ℕ = {1, 2, …}` has
`d_log(A) > 0` and for every interval `(a, b) ⊆ [0, 1)` and every `θ > 0`
`d_log({n ∈ A : {θ log n} ∈ (a, b)}) = d_log(A) (b - a)` (condition `(21)`), does `A` contain a
sumset `B + B + t` for some `t ≥ 0` and some infinite set `B ⊆ ℕ`? -/
def Question324 : Prop :=
  ∀ A : Set ℕ, 0 ∉ A → ∀ d : ℝ, 0 < d → HasLogDensity A d →
    (∀ θ : ℝ, 0 < θ → ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      HasLogDensity {n ∈ A | Int.fract (θ * Real.log n) ∈ Set.Ioo a b} (d * (b - a))) →
    ∃ t : ℕ, ∃ B : Set ℕ, B.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ ∀ b ∈ B, ∀ b' ∈ B, b + b' + t ∈ A

lemma zero_not_mem_AKR : 0 ∉ AKR := by
  rintro (⟨-, n, hn, h1, -⟩ | ⟨-, n, hn, h1, -⟩)
  · have : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega
  · have : (0 : ℝ) < (2 + 1 / (n : ℝ)) * 4 ^ n := by positivity
    push_cast at h1
    linarith

/-- The answer to Question 3.24 is negative (paper, Section \ref{IA:sec:q324}), witnessed by the
set `A_KR` of Kousek and Radić (Proposition \ref{IA:prop:KR}). -/
theorem not_question324 : ¬ Question324 := by
  intro hQ
  obtain ⟨t, B, hB, -, hBA⟩ := hQ AKR zero_not_mem_AKR (1 / 2) (by norm_num) AKR_logDensity
    (fun θ hθ a b ha hab hb => AKR_eq21 hθ ha hab hb)
  exact AKR_no_BBt t hB fun b hb b' hb' => ⟨b + b' + t, hBA b hb b' hb', by push_cast; ring⟩

/-! ## Weyl sums for `α j + √(γ j + δ)` -/

section Weyl

open Complex in
/-- `e(x) = exp(2π i x)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (Complex.I * ((2 * π * x : ℝ) : ℂ))

lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := Complex.norm_exp_I_mul_ofReal _

lemma ee_int (n : ℤ) : ee n = 1 := by
  unfold ee
  have := Complex.exp_int_mul_two_pi_mul_I n
  rw [← this]
  congr 1
  push_cast; ring

lemma ee_re (x : ℝ) : (ee x).re = Real.cos (2 * π * x) := by
  unfold ee
  rw [Complex.exp_re]
  simp

lemma norm_ee_sub_one (t : ℝ) : ‖ee t - 1‖ = |2 * Real.sin (π * t)| := by
  unfold ee
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  congr 2; ring_nf

lemma norm_ee_sub_one_le (t : ℝ) : ‖ee t - 1‖ ≤ 2 * π * |t| := by
  unfold ee
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos]

lemma norm_ee_sub_ee_le (x y : ℝ) : ‖ee x - ee y‖ ≤ 2 * π * |x - y| := by
  have e : ee x - ee y = ee y * (ee (x - y) - 1) := by
    rw [mul_sub, ← ee_add, mul_one]; ring_nf
  rw [e, norm_mul, norm_ee, one_mul]
  exact norm_ee_sub_one_le _

lemma four_mul_le_norm_ee_sub_one {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    4 * t ≤ ‖ee t - 1‖ := by
  rw [norm_ee_sub_one]
  have h1 : 2 / π * (π * t) ≤ Real.sin (π * t) :=
    Real.mul_le_sin (by positivity) (by nlinarith [Real.pi_pos])
  have h2 : 2 / π * (π * t) = 2 * t := by field_simp
  rw [abs_of_nonneg (by nlinarith [Real.pi_pos])]
  linarith

lemma ee_ne_one {β : ℝ} (hβ : ∀ n : ℤ, β ≠ n) : ee β ≠ 1 := by
  intro h
  have : ‖ee β - 1‖ = 0 := by rw [h, sub_self, norm_zero]
  rw [norm_ee_sub_one, abs_eq_zero, mul_eq_zero] at this
  rcases this with h2 | h2
  · norm_num at h2
  · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h2
    exact hβ n (by have := Real.pi_pos; field_simp at hn; linarith)

/-- Abel summation bound: if all partial sums of `g` have norm `≤ B`, then
`‖∑_{i<n} f i g i‖ ≤ B (‖f (n-1)‖ + ∑_{i < n-1} ‖f (i+1) - f i‖)`. -/
lemma norm_sum_mul_le (f g : ℕ → ℂ) {B : ℝ} (hB : ∀ i, ‖∑ l ∈ range i, g l‖ ≤ B) (n : ℕ) :
    ‖∑ i ∈ range n, f i * g i‖ ≤
      B * (‖f (n - 1)‖ + ∑ i ∈ range (n - 1), ‖f (i + 1) - f i‖) := by
  have h := Finset.sum_range_by_parts f g n
  simp only [smul_eq_mul] at h
  rw [h]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  calc _ ≤ ‖f (n - 1) * ∑ i ∈ range n, g i‖ +
        ‖∑ i ∈ range (n - 1), (f (i + 1) - f i) * ∑ i ∈ range (i + 1), g i‖ := norm_sub_le _ _
    _ ≤ ‖f (n - 1)‖ * B + ∑ i ∈ range (n - 1), ‖f (i + 1) - f i‖ * B := by
        gcongr
        · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB n) (norm_nonneg _)
        · refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

variable {α γ δ σ : ℝ}

/-- `u_j = √(γ j + δ) + σ`. -/
noncomputable def uS (γ δ σ : ℝ) (j : ℕ) : ℝ := √(γ * j + δ) + σ

/-- `Δ_j = u_{j+1} - u_j = γ / (√(γ(j+1) + δ) + √(γ j + δ))`. -/
lemma uS_diff (hγ : 0 < γ) (hδ : 0 ≤ δ) (j : ℕ) :
    uS γ δ σ (j + 1) - uS γ δ σ j = γ / (√(γ * (j + 1 : ℕ) + δ) + √(γ * j + δ)) := by
  unfold uS
  have h1 : 0 < √(γ * (j + 1 : ℕ) + δ) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 ≤ √(γ * j + δ) := Real.sqrt_nonneg _
  rw [eq_div_iff (by positivity)]
  have e1 := Real.sq_sqrt (show 0 ≤ γ * (j + 1 : ℕ) + δ by positivity)
  have e2 := Real.sq_sqrt (show 0 ≤ γ * j + δ by positivity)
  push_cast at e1 ⊢
  nlinarith [e1, e2]

lemma uS_diff_pos (hγ : 0 < γ) (hδ : 0 ≤ δ) (j : ℕ) : 0 < uS γ δ σ (j + 1) - uS γ δ σ j := by
  rw [uS_diff hγ hδ]
  have h1 : 0 < √(γ * (j + 1 : ℕ) + δ) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 ≤ √(γ * j + δ) := Real.sqrt_nonneg _
  positivity

lemma uS_diff_anti (hγ : 0 < γ) (hδ : 0 ≤ δ) (j : ℕ) :
    uS γ δ σ (j + 2) - uS γ δ σ (j + 1) ≤ uS γ δ σ (j + 1) - uS γ δ σ j := by
  rw [uS_diff hγ hδ, uS_diff hγ hδ]
  have h1 : √(γ * j + δ) ≤ √(γ * (j + 1 : ℕ) + δ) :=
    Real.sqrt_le_sqrt (by push_cast; nlinarith)
  have h2 : √(γ * (j + 1 : ℕ) + δ) ≤ √(γ * (j + 1 + 1 : ℕ) + δ) :=
    Real.sqrt_le_sqrt (by push_cast; nlinarith)
  have h3 : 0 < √(γ * (j + 1 : ℕ) + δ) := Real.sqrt_pos.2 (by positivity)
  apply div_le_div_of_nonneg_left hγ.le (by positivity)
  push_cast at h1 h2 ⊢
  linarith

lemma inv_uS_diff_le (hγ : 0 < γ) (hδ : 0 ≤ δ) (j : ℕ) :
    1 / (uS γ δ σ (j + 1) - uS γ δ σ j) ≤ 2 * √(γ * (j + 1 : ℕ) + δ) / γ := by
  rw [uS_diff hγ hδ, one_div_div]
  have h1 : √(γ * j + δ) ≤ √(γ * (j + 1 : ℕ) + δ) := Real.sqrt_le_sqrt (by push_cast; nlinarith)
  apply div_le_div_of_nonneg_right _ hγ.le
  linarith

lemma uS_diff_le (hγ : 0 < γ) (hδ : 0 ≤ δ) (j : ℕ) (hj : 1 ≤ j) :
    uS γ δ σ (j + 1) - uS γ δ σ j ≤ √γ / (2 * √j) := by
  rw [uS_diff hγ hδ]
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : √γ * √j ≤ √(γ * j + δ) := by
    rw [← Real.sqrt_mul hγ.le]; exact Real.sqrt_le_sqrt (by linarith)
  have h2 : √(γ * j + δ) ≤ √(γ * (j + 1 : ℕ) + δ) := Real.sqrt_le_sqrt (by push_cast; nlinarith)
  have hsγ : 0 < √γ := Real.sqrt_pos.2 hγ
  have hsj : 0 < √(j : ℝ) := Real.sqrt_pos.2 (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : √γ * √γ = γ := Real.mul_self_sqrt hγ.le
  nlinarith

/-- The Weyl sum `∑_{j<M} e(k(α j + √(γ j + δ) + σ))` is `O(1 + √M)`. -/
lemma weyl_bound (hγ : 0 < γ) (hδ : 0 ≤ δ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, ∀ M : ℕ, ‖∑ j ∈ range M, ee (k * (α * j + uS γ δ σ j))‖ ≤
      C * (1 + √(γ * M + δ)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  by_cases hint : ∃ n : ℤ, (k : ℝ) * α = n
  · -- resonant case: `e(k α j) = 1`, sum `e(k u_j)` by Abel summation with weights `1/ρ_j`
    obtain ⟨n, hn⟩ := hint
    set X : ℕ → ℂ := fun j => ee (k * uS γ δ σ j)
    have hX : ∀ j : ℕ, ee (k * (α * j + uS γ δ σ j)) = X j := by
      intro j
      have : (k : ℝ) * (α * j + uS γ δ σ j) = ((n * j : ℤ) : ℝ) + k * uS γ δ σ j := by
        push_cast; rw [← hn]; ring
      rw [this, ee_add, ee_int, one_mul]
    set Δ : ℕ → ℝ := fun j => uS γ δ σ (j + 1) - uS γ δ σ j
    have hΔpos : ∀ j, 0 < Δ j := fun j => uS_diff_pos hγ hδ j
    have hΔanti : ∀ j, Δ (j + 1) ≤ Δ j := fun j => by
      simp only [Δ]; exact uS_diff_anti hγ hδ j
    -- threshold `j₀` with `k Δ_j ≤ 1/2` for `j ≥ j₀`
    obtain ⟨j₀, hj₀⟩ := exists_nat_gt (k ^ 2 * γ)
    have hj₀1 : 1 ≤ j₀ := by
      have : (0 : ℝ) < k ^ 2 * γ := by positivity
      have : (0 : ℝ) < j₀ := by linarith
      exact_mod_cast this
    have hsmall : ∀ j, j₀ ≤ j → k * Δ j ≤ 1 / 2 := by
      intro j hj
      have h1 := uS_diff_le (σ := σ) hγ hδ j (hj₀1.trans hj)
      have hj' : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
      have hj1 : (1 : ℝ) ≤ j₀ := by exact_mod_cast hj₀1
      have hsj : 0 < √(j : ℝ) := Real.sqrt_pos.2 (by linarith)
      have h2 : k * √γ ≤ √(j : ℝ) := by
        rw [show (k : ℝ) * √γ = √(k ^ 2 * γ) by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
        exact Real.sqrt_le_sqrt (by linarith)
      calc k * Δ j ≤ k * (√γ / (2 * √j)) := by gcongr
        _ = (k * √γ) / (2 * √j) := by ring
        _ ≤ √j / (2 * √j) := by gcongr
        _ = 1 / 2 := by field_simp
    set ρ : ℕ → ℂ := fun j => ee (k * Δ j) - 1
    have hρ : ∀ j, j₀ ≤ j → 4 * (k * Δ j) ≤ ‖ρ j‖ := fun j hj =>
      four_mul_le_norm_ee_sub_one (by have := hΔpos j; positivity) (hsmall j hj)
    have hρne : ∀ j, j₀ ≤ j → ρ j ≠ 0 := fun j hj h => by
      have := hρ j hj; rw [h, norm_zero] at this; have := hΔpos j; nlinarith
    have hXρ : ∀ j, j₀ ≤ j → X j = (1 / ρ j) * (X (j + 1) - X j) := by
      intro j hj
      have : X (j + 1) = X j * ee (k * Δ j) := by
        simp only [X, Δ]; rw [← ee_add]; congr 1; ring
      rw [this]
      field_simp [hρne j hj]
      simp only [ρ]
    -- the Abel bound on `[j₀, M)`
    have hpart : ∀ i, ‖∑ l ∈ range i, (X (j₀ + l + 1) - X (j₀ + l))‖ ≤ 2 := by
      intro i
      rw [show (∑ l ∈ range i, (X (j₀ + l + 1) - X (j₀ + l))) = X (j₀ + i) - X (j₀ + 0) from
        Finset.sum_range_sub (fun l => X (j₀ + l)) i]
      calc ‖X (j₀ + i) - X (j₀ + 0)‖ ≤ ‖X (j₀ + i)‖ + ‖X (j₀ + 0)‖ := norm_sub_le _ _
        _ = 2 := by simp only [X, norm_ee]; norm_num
    refine ⟨j₀ + 2 * ((π / (8 * k) + 1 / (4 * k)) * (2 / γ)) + 2 * (π / (8 * k) + 1 / (4 * k)) *
      (2 / γ), fun M => ?_⟩
    rw [sum_congr rfl fun j _ => hX j]
    rcases le_or_gt M j₀ with hM | hM
    · calc ‖∑ j ∈ range M, X j‖ ≤ ∑ j ∈ range M, ‖X j‖ := norm_sum_le _ _
        _ = M := by simp [X, norm_ee]
        _ ≤ j₀ := by exact_mod_cast hM
        _ ≤ _ := by
            have : 0 ≤ 2 * ((π / (8 * k) + 1 / (4 * k)) * (2 / γ)) +
              2 * (π / (8 * k) + 1 / (4 * k)) * (2 / γ) := by positivity
            have : (0 : ℝ) ≤ √(γ * M + δ) := Real.sqrt_nonneg _
            nlinarith
    · obtain ⟨L, rfl⟩ : ∃ L, M = j₀ + L := ⟨M - j₀, by omega⟩
      rw [sum_range_add]
      have hL : 1 ≤ L := by omega
      have h1 : ‖∑ j ∈ range j₀, X j‖ ≤ j₀ := by
        calc ‖∑ j ∈ range j₀, X j‖ ≤ ∑ j ∈ range j₀, ‖X j‖ := norm_sum_le _ _
          _ = j₀ := by simp [X, norm_ee]
      have h2 : ∑ l ∈ range L, X (j₀ + l) =
          ∑ l ∈ range L, (1 / ρ (j₀ + l)) * (X (j₀ + l + 1) - X (j₀ + l)) :=
        sum_congr rfl fun l _ => hXρ _ (by omega)
      have h3 := norm_sum_mul_le (fun l => 1 / ρ (j₀ + l)) (fun l => X (j₀ + l + 1) - X (j₀ + l))
        hpart L
      -- bounds on the weights
      have hw : ∀ l, ‖1 / ρ (j₀ + l)‖ ≤ 1 / (4 * k) * (1 / Δ (j₀ + l)) := by
        intro l
        rw [norm_div, norm_one]
        have := hρ (j₀ + l) (by omega)
        have := hΔpos (j₀ + l)
        rw [div_le_iff₀ (norm_pos_iff.2 (hρne _ (by omega)))]
        calc (1 : ℝ) = 1 / (4 * k) * (1 / Δ (j₀ + l)) * (4 * (k * Δ (j₀ + l))) := by
              field_simp
          _ ≤ _ := by gcongr
      have hwd : ∀ l, ‖1 / ρ (j₀ + (l + 1)) - 1 / ρ (j₀ + l)‖ ≤
          π / (8 * k) * (1 / Δ (j₀ + l + 1) - 1 / Δ (j₀ + l)) := by
        intro l
        have hr1 := hρ (j₀ + l) (by omega)
        have hr2 := hρ (j₀ + l + 1) (by omega)
        have hd1 := hΔpos (j₀ + l)
        have hd2 := hΔpos (j₀ + l + 1)
        have hdd := hΔanti (j₀ + l)
        have hne1 := hρne (j₀ + l) (by omega)
        have hne2 := hρne (j₀ + l + 1) (by omega)
        rw [show j₀ + (l + 1) = j₀ + l + 1 by ring]
        rw [div_sub_div _ _ hne2 hne1, norm_div, norm_mul]
        have hnum : ‖1 * ρ (j₀ + l) - ρ (j₀ + l + 1) * 1‖ ≤
            2 * π * (k * (Δ (j₀ + l) - Δ (j₀ + l + 1))) := by
          simp only [ρ, one_mul, mul_one]
          rw [show ee (k * Δ (j₀ + l)) - 1 - (ee (k * Δ (j₀ + l + 1)) - 1) =
            ee (k * Δ (j₀ + l)) - ee (k * Δ (j₀ + l + 1)) by ring]
          refine (norm_ee_sub_ee_le _ _).trans (le_of_eq ?_)
          rw [abs_of_nonneg (by nlinarith)]; ring
        rw [div_le_iff₀ (by positivity)]
        calc ‖1 * ρ (j₀ + l) - ρ (j₀ + l + 1) * 1‖ ≤
              2 * π * (k * (Δ (j₀ + l) - Δ (j₀ + l + 1))) := hnum
          _ = π / (8 * k) * (1 / Δ (j₀ + l + 1) - 1 / Δ (j₀ + l)) *
              ((4 * (k * Δ (j₀ + l + 1))) * (4 * (k * Δ (j₀ + l)))) := by
              field_simp; ring
          _ ≤ _ := by
              have : 0 ≤ π / (8 * k) * (1 / Δ (j₀ + l + 1) - 1 / Δ (j₀ + l)) := by
                apply mul_nonneg (by positivity)
                rw [sub_nonneg]
                exact one_div_le_one_div_of_le hd2 hdd
              gcongr
      have hsum : ∑ i ∈ range (L - 1), ‖1 / ρ (j₀ + (i + 1)) - 1 / ρ (j₀ + i)‖ ≤
          π / (8 * k) * (1 / Δ (j₀ + (L - 1))) := by
        refine (sum_le_sum fun i _ => hwd i).trans ?_
        rw [← mul_sum, show (∑ i ∈ range (L - 1), (1 / Δ (j₀ + i + 1) - 1 / Δ (j₀ + i))) =
          1 / Δ (j₀ + (L - 1)) - 1 / Δ (j₀ + 0) from
          Finset.sum_range_sub (fun i => 1 / Δ (j₀ + i)) (L - 1)]
        have : 0 < 1 / Δ (j₀ + 0) := by have := hΔpos (j₀ + 0); positivity
        gcongr
        simp only [add_zero] at this ⊢
        linarith
      have hlast : 1 / Δ (j₀ + (L - 1)) ≤ 2 * √(γ * (j₀ + L : ℕ) + δ) / γ := by
        have := inv_uS_diff_le (σ := σ) hγ hδ (j₀ + (L - 1))
        simp only [Δ]
        rw [show j₀ + (L - 1) + 1 = j₀ + L by omega] at this ⊢
        exact this
      have h4 : ‖∑ l ∈ range L, X (j₀ + l)‖ ≤
          2 * ((1 / (4 * k) + π / (8 * k)) * (2 * √(γ * (j₀ + L : ℕ) + δ) / γ)) := by
        rw [h2]
        refine h3.trans ?_
        have hw' := hw (L - 1)
        gcongr
        calc ‖1 / ρ (j₀ + (L - 1))‖ + ∑ i ∈ range (L - 1), ‖1 / ρ (j₀ + (i + 1)) - 1 / ρ (j₀ + i)‖
            ≤ 1 / (4 * k) * (1 / Δ (j₀ + (L - 1))) + π / (8 * k) * (1 / Δ (j₀ + (L - 1))) :=
              add_le_add hw' hsum
          _ = (1 / (4 * k) + π / (8 * k)) * (1 / Δ (j₀ + (L - 1))) := by ring
          _ ≤ _ := by gcongr
      have hs : (0 : ℝ) ≤ √(γ * (j₀ + L : ℕ) + δ) := Real.sqrt_nonneg _
      calc ‖∑ j ∈ range j₀, X j + ∑ l ∈ range L, X (j₀ + l)‖
          ≤ ‖∑ j ∈ range j₀, X j‖ + ‖∑ l ∈ range L, X (j₀ + l)‖ := norm_add_le _ _
        _ ≤ j₀ + 2 * ((1 / (4 * k) + π / (8 * k)) * (2 * √(γ * (j₀ + L : ℕ) + δ) / γ)) :=
            add_le_add h1 h4
        _ ≤ _ := by
            have hj0 : (0 : ℝ) ≤ j₀ := j₀.cast_nonneg
            have hc : 0 ≤ 2 * ((π / (8 * k) + 1 / (4 * k)) * (2 / γ)) := by positivity
            have e : 2 * ((1 / (4 * k) + π / (8 * k)) * (2 * √(γ * (j₀ + L : ℕ) + δ) / γ)) =
                2 * ((π / (8 * k) + 1 / (4 * k)) * (2 / γ)) * √(γ * (j₀ + L : ℕ) + δ) := by ring
            rw [e]
            nlinarith
  · -- non-resonant case: Abel summation against the geometric sums of `e(k α j)`
    push Not at hint
    set z := ee (k * α)
    have hz : z ≠ 1 := ee_ne_one hint
    have hz0 : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
    set B := 2 / ‖z - 1‖
    have hgeo : ∀ i, ‖∑ l ∈ range i, z ^ l‖ ≤ B := by
      intro i
      rw [geom_sum_eq hz, norm_div]
      apply div_le_div_of_nonneg_right _ hz0.le
      calc ‖z ^ i - 1‖ ≤ ‖z ^ i‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, norm_ee, one_pow, norm_one]; norm_num
    set w : ℕ → ℂ := fun j => ee (k * uS γ δ σ j)
    have hfac : ∀ j : ℕ, ee (k * (α * j + uS γ δ σ j)) = w j * z ^ j := by
      intro j
      have : (k : ℝ) * (α * j + uS γ δ σ j) = k * uS γ δ σ j + j * (k * α) := by ring
      rw [this, ee_add]
      congr 1
      simp only [z, ee]
      rw [← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    refine ⟨B * (1 + 2 * π * k), fun M => ?_⟩
    rw [sum_congr rfl fun j _ => hfac j]
    refine (norm_sum_mul_le w (fun j => z ^ j) hgeo M).trans ?_
    have hw1 : ‖w (M - 1)‖ = 1 := norm_ee _
    have hwd : ∑ i ∈ range (M - 1), ‖w (i + 1) - w i‖ ≤ 2 * π * k * √(γ * M + δ) := by
      calc ∑ i ∈ range (M - 1), ‖w (i + 1) - w i‖ ≤
            ∑ i ∈ range (M - 1), 2 * π * k * (uS γ δ σ (i + 1) - uS γ δ σ i) := by
            refine sum_le_sum fun i _ => (norm_ee_sub_ee_le _ _).trans (le_of_eq ?_)
            rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity),
              abs_of_nonneg (by linarith [uS_diff_pos (σ := σ) hγ hδ i])]
            ring
        _ = 2 * π * k * (uS γ δ σ (M - 1) - uS γ δ σ 0) := by
            rw [← mul_sum, Finset.sum_range_sub (uS γ δ σ)]
        _ ≤ 2 * π * k * √(γ * M + δ) := by
            gcongr
            unfold uS
            have : √(γ * ((M - 1 : ℕ) : ℝ) + δ) ≤ √(γ * M + δ) :=
              Real.sqrt_le_sqrt (by
                have : ((M - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M 1
                nlinarith)
            simp only [CharP.cast_eq_zero, mul_zero, zero_add]
            have := Real.sqrt_nonneg δ
            linarith
    rw [hw1]
    have hB : 0 ≤ B := by positivity
    have hs : 0 ≤ √(γ * M + δ) := Real.sqrt_nonneg _
    calc B * (1 + ∑ i ∈ range (M - 1), ‖w (i + 1) - w i‖) ≤ B * (1 + 2 * π * k * √(γ * M + δ)) := by
          gcongr
      _ ≤ B * (1 + 2 * π * k) * (1 + √(γ * M + δ)) := by
          have : 0 ≤ 2 * π * k := by positivity
          nlinarith

/-- Weyl averages tend to `0`: `(1/M) ∑_{j<M} cos(2π k (α j + √(γ j + δ) + σ)) → 0` for `k ≥ 1`. -/
lemma tendsto_cos_avg (hγ : 0 < γ) (hδ : 0 ≤ δ) {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun M : ℕ => (∑ j ∈ range M, Real.cos (2 * π * k * (α * j + uS γ δ σ j))) / M)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := weyl_bound (α := α) (σ := σ) hγ hδ hk
  have hbound : ∀ M : ℕ, |∑ j ∈ range M, Real.cos (2 * π * k * (α * j + uS γ δ σ j))| ≤
      C * (1 + √(γ * M + δ)) := by
    intro M
    have e : ∑ j ∈ range M, Real.cos (2 * π * k * (α * j + uS γ δ σ j)) =
        (∑ j ∈ range M, ee (k * (α * j + uS γ δ σ j))).re := by
      rw [Complex.re_sum]
      exact sum_congr rfl fun j _ => by rw [ee_re]; ring_nf
    rw [e]
    exact (Complex.abs_re_le_norm _).trans (hC M)
  -- `(1 + √(γ M + δ)) / M → 0`
  have hlim : Tendsto (fun M : ℕ => C * (1 + √(γ * M + δ)) / M) atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℕ => C / M) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat C
    have h2 : Tendsto (fun M : ℕ => √(γ * M + δ) / M) atTop (𝓝 0) := by
      have h3 : Tendsto (fun M : ℕ => √((γ + δ) / M)) atTop (𝓝 0) := by
        have := (tendsto_const_div_atTop_nhds_zero_nat (γ + δ)).sqrt
        simpa using this
      refine squeeze_zero' (Eventually.of_forall fun M => by positivity) ?_ h3
      filter_upwards [eventually_ge_atTop 1] with M hM
      have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
      rw [div_le_iff₀ (by linarith)]
      calc √(γ * M + δ) ≤ √((γ + δ) * M) := Real.sqrt_le_sqrt (by nlinarith)
        _ = √((γ + δ) / M) * M := by
            rw [show (γ + δ) * (M : ℝ) = (γ + δ) / M * (M * M) by field_simp,
              Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by linarith)]
    have := h1.add (h2.const_mul C)
    simp only [add_zero, mul_zero] at this
    refine this.congr fun M => ?_
    ring
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with M hM
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by exact_mod_cast hM : (0 : ℝ) < M)]
  exact div_le_div_of_nonneg_right (hbound M) (by positivity)

/-- `τ({y}) = 1/6 - π⁻² ∑_{k ≥ 1} cos(2π k y) / k²` (Fourier series of the Bernoulli
polynomial `B₂`). -/
lemma hasSum_τ (y : ℝ) :
    HasSum (fun k : ℕ => 1 / (k : ℝ) ^ 2 * Real.cos (2 * π * k * y))
      (π ^ 2 * (1 / 6 - τ (Int.fract y))) := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero
    (x := Int.fract y) ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩
  have e1 : ∀ k : ℕ, 1 / (k : ℝ) ^ (2 * 1) * Real.cos (2 * π * k * Int.fract y) =
      1 / (k : ℝ) ^ 2 * Real.cos (2 * π * k * y) := by
    intro k
    congr 1
    rw [Int.fract, show 2 * π * (k : ℝ) * (y - ⌊y⌋) = 2 * π * k * y - ((k * ⌊y⌋ : ℤ) : ℝ) * (2 * π)
      by push_cast; ring, Real.cos_sub_int_mul_two_pi]
  simp only [e1] at h
  convert h using 1
  have hb : Polynomial.eval (Int.fract y) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2))
      = Int.fract y ^ 2 - Int.fract y + 6⁻¹ := by
    have := bernoulliFun_two (Int.fract y)
    rw [bernoulliFun] at this
    exact this
  rw [hb]
  unfold τ
  norm_num
  ring

/-- `(1/M) ∑_{j < M} τ({α j + √(γ j + δ) + σ}) → 1/6`. -/
lemma tendsto_τ_avg (hγ : 0 < γ) (hδ : 0 ≤ δ) :
    Tendsto (fun M : ℕ => (∑ j ∈ range M, τ (Int.fract (α * j + uS γ δ σ j))) / M) atTop
      (𝓝 (1 / 6)) := by
  set v : ℕ → ℝ := fun j => α * j + uS γ δ σ j
  have hτ : ∀ y, τ (Int.fract y) =
      1 / 6 - π⁻¹ ^ 2 * ∑' k : ℕ, 1 / (k : ℝ) ^ 2 * Real.cos (2 * π * k * y) := by
    intro y
    rw [(hasSum_τ y).tsum_eq]
    have := Real.pi_pos
    field_simp
    ring
  have hsum : Summable fun k : ℕ => 1 / (k : ℝ) ^ 2 := Real.summable_one_div_nat_pow.2 one_lt_two
  have hsk : ∀ y, Summable fun k : ℕ => 1 / (k : ℝ) ^ 2 * Real.cos (2 * π * k * y) :=
    fun y => (hasSum_τ y).summable
  -- the averaged series
  set F : ℕ → ℕ → ℝ := fun M k =>
    1 / (k : ℝ) ^ 2 * ((∑ j ∈ range M, Real.cos (2 * π * k * v j)) / M)
  have hrep : ∀ M : ℕ, 1 ≤ M → (∑ j ∈ range M, τ (Int.fract (v j))) / M =
      1 / 6 - π⁻¹ ^ 2 * ∑' k, F M k := by
    intro M hM
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    simp only [hτ, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
    rw [← (Summable.tsum_finsetSum fun j _ => hsk (v j))]
    have e : ∑' k : ℕ, F M k = (∑' k : ℕ, ∑ j ∈ range M, 1 / (k : ℝ) ^ 2 *
        Real.cos (2 * π * k * v j)) / M := by
      rw [← tsum_div_const]
      congr 1; funext k
      simp only [F, ← mul_sum]; ring
    rw [e]
    field_simp
    ring_nf
  have hF : Tendsto (fun M => ∑' k, F M k) atTop (𝓝 (∑' _k : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun k => ?_) ?_
    · rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simp [F]
      · have := (tendsto_cos_avg (α := α) (σ := σ) hγ hδ h0).const_mul (1 / (k : ℝ) ^ 2)
        rw [mul_zero] at this
        refine this.congr fun M => ?_
        simp only [F, v]
    · refine Eventually.of_forall fun M k => ?_
      simp only [F, Real.norm_eq_abs]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ) ^ 2)]
      have : |(∑ j ∈ range M, Real.cos (2 * π * k * v j)) / M| ≤ 1 := by
        rcases Nat.eq_zero_or_pos M with h0 | h0
        · subst h0; simp
        · rw [abs_div, abs_of_pos (by exact_mod_cast h0 : (0 : ℝ) < M), div_le_one
            (by exact_mod_cast h0)]
          calc |∑ j ∈ range M, Real.cos (2 * π * k * v j)| ≤ ∑ j ∈ range M, |Real.cos
                (2 * π * k * v j)| := abs_sum_le_sum_abs _ _
            _ ≤ ∑ j ∈ range M, (1 : ℝ) := sum_le_sum fun j _ => Real.abs_cos_le_one _
            _ = M := by simp
      calc 1 / (k : ℝ) ^ 2 * |(∑ j ∈ range M, Real.cos (2 * π * k * v j)) / M| ≤
            1 / (k : ℝ) ^ 2 * 1 := by gcongr
        _ = 1 / (k : ℝ) ^ 2 := mul_one _
  rw [tsum_zero] at hF
  have := (tendsto_const_nhds (x := (1 / 6 : ℝ))).sub (hF.const_mul (π⁻¹ ^ 2))
  rw [mul_zero, sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact (hrep M hM).symm

end Weyl

/-! ## The phase `f(log₂ n)` -/

section Fphase

/-- `x_n = log₂ n`. -/
noncomputable def xL (n : ℕ) : ℝ := Real.logb 2 n

/-- `F_n = f(log₂ n)`. -/
noncomputable def Fn (n : ℕ) : ℝ := f (xL n)

lemma xL_nonneg (n : ℕ) : 0 ≤ xL n := by
  unfold xL
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

lemma xL_mono : Monotone xL := by
  intro m n hmn
  unfold xL Real.logb
  exact div_le_div_of_nonneg_right (log_nat_mono hmn) (Real.log_nonneg (by norm_num))

lemma log_eq_xL (n : ℕ) : Real.log n = Real.log 2 * xL n := by
  unfold xL Real.logb; field_simp

lemma f_mono {x y : ℝ} (hxy : x ≤ y) : f x ≤ f y := by
  unfold f; have := Real.sqrt_le_sqrt hxy; linarith

lemma Fn_mono : Monotone Fn := fun _ _ h => f_mono (xL_mono h)

lemma Fn_nonneg (n : ℕ) : 0 ≤ Fn n := by
  unfold Fn f; have := xL_nonneg n; have := Real.sqrt_nonneg (xL n); linarith

lemma xL_succ_sub {n : ℕ} (hn : 1 ≤ n) : xL (n + 1) - xL n ≤ 2 / n := by
  have h1 := log_succ_sub_le hn
  have h2 := log_eq_xL n
  have h3 := log_eq_xL (n + 1)
  push_cast at h3
  have hl := Real.log_two_gt_d9
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : Real.log 2 * (xL (n + 1) - xL n) ≤ 1 / n := by linarith
  have h4 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith
  have h5 : 0 ≤ xL (n + 1) - xL n := by have := xL_mono (Nat.le_succ n); linarith
  rw [div_eq_mul_one_div 2]
  nlinarith

lemma Fn_succ_sub_le {n : ℕ} (hn : 1 ≤ n) : Fn (n + 1) - Fn n ≤ 3 / 2 * (xL (n + 1) - xL n) := by
  unfold Fn f
  have h0 := xL_mono (Nat.le_succ n)
  have h1 : 1 ≤ xL (n + 1) := by
    unfold xL
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    norm_num; exact_mod_cast (by omega : 2 ≤ n + 1)
  have hs1 : 1 ≤ √(xL (n + 1)) := by rw [Real.one_le_sqrt]; exact h1
  have hs0 : 0 ≤ √(xL n) := Real.sqrt_nonneg _
  have e : √(xL (n + 1)) - √(xL n) = (xL (n + 1) - xL n) / (√(xL (n + 1)) + √(xL n)) := by
    field_simp
    linear_combination (Real.sq_sqrt (by linarith : 0 ≤ xL (n + 1))) -
      (Real.sq_sqrt (xL_nonneg n))
  have h2 : (xL (n + 1) - xL n) / (√(xL (n + 1)) + √(xL n)) ≤ xL (n + 1) - xL n := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

lemma Fn_succ_sub_le' {n : ℕ} (hn : 1 ≤ n) : Fn (n + 1) - Fn n ≤ 3 / n := by
  have := Fn_succ_sub_le hn
  have := xL_succ_sub hn
  have e : (3 : ℝ) / n = 3 / 2 * (2 / n) := by ring
  rw [e]; nlinarith

/-- `f⁻¹(y) = (√(1 + 2y) - 1)²`. -/
noncomputable def finv (y : ℝ) : ℝ := (√(1 + 2 * y) - 1) ^ 2

lemma finv_f {x : ℝ} (hx : 0 ≤ x) : finv (f x) = x := by
  unfold finv f
  have : 1 + 2 * (x / 2 + √x) = (1 + √x) ^ 2 := by
    rw [add_sq, Real.sq_sqrt hx]; ring
  rw [this, Real.sqrt_sq (by positivity)]
  simp [Real.sq_sqrt hx]

lemma finv_mono {y y' : ℝ} (hy : 0 ≤ y) (hyy : y ≤ y') : finv y ≤ finv y' := by
  unfold finv
  have h1 : 1 ≤ √(1 + 2 * y) := by rw [Real.one_le_sqrt]; linarith
  have h2 : √(1 + 2 * y) ≤ √(1 + 2 * y') := Real.sqrt_le_sqrt (by linarith)
  nlinarith

lemma finv_eq (y : ℝ) (hy : 0 ≤ y) : finv y = 2 * y + 2 - 2 * √(1 + 2 * y) := by
  unfold finv
  rw [sub_sq, Real.sq_sqrt (by linarith)]; ring

/-- At a jump of `⌊F_n - r⌋`, the point `f⁻¹(m + r)` lies in `(x_n, x_{n+1}]`. -/
lemma finv_jump {n : ℕ} {y : ℝ} (h1 : Fn n < y) (h2 : y ≤ Fn (n + 1)) :
    |xL (n + 1) - finv y| ≤ xL (n + 1) - xL n := by
  have hy0 : 0 ≤ y := le_trans (Fn_nonneg n) h1.le
  have e1 : finv (Fn n) = xL n := finv_f (xL_nonneg n)
  have e2 : finv (Fn (n + 1)) = xL (n + 1) := finv_f (xL_nonneg (n + 1))
  have h3 := finv_mono (Fn_nonneg n) h1.le
  have h4 := finv_mono hy0 h2
  rw [e1] at h3; rw [e2] at h4
  rw [abs_of_nonneg (by linarith)]; linarith

/-- `√(log₂ (N + 1)) = o(log N)`. -/
lemma logSmall_sqrt_xL : LogSmall fun N => √(xL (N + 1)) := by
  apply logSmall_of_forall
  intro ε hε
  refine ⟨1 / ε + 2 * ε * 2, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have hx := xL_nonneg (N + 1)
  have h1 : xL (N + 1) ≤ 2 * (Real.log N + 1) := by
    have := log_eq_xL (N + 1)
    have := log_succ_le_log_add_one hN
    have hl := Real.log_two_gt_d9
    push_cast at *
    nlinarith
  -- `√x ≤ ε x / 2 + 1 / (2 ε)`
  have h2 : √(xL (N + 1)) ≤ ε / 2 * xL (N + 1) + 1 / (2 * ε) := by
    have hs := Real.sq_sqrt hx
    have : 0 ≤ (ε * √(xL (N + 1)) - 1) ^ 2 := sq_nonneg _
    rw [show ε / 2 * xL (N + 1) + 1 / (2 * ε) =
      (ε ^ 2 * xL (N + 1) + 1) / (2 * ε) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hl := Real.log_natCast_nonneg N
  have : 1 / (2 * ε) ≤ 1 / ε := by
    apply div_le_div_of_nonneg_left (by norm_num) hε (by linarith)
  nlinarith

/-- If `(1/M) ∑_{j<M} w_j → L` and `M(N) ≤ C (log N + 1)`, then
`∑_{j < M(N)} w_j - L M(N) = o(log N)`. -/
lemma logSmall_of_avg {w : ℕ → ℝ} {L : ℝ}
    (hw : Tendsto (fun M : ℕ => (∑ j ∈ range M, w j) / M) atTop (𝓝 L)) {Mf : ℕ → ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hM : ∀ N, (Mf N : ℝ) ≤ C * (Real.log N + 1)) :
    LogSmall fun N => ∑ j ∈ range (Mf N), w j - L * Mf N := by
  apply logSmall_of_forall
  intro ε hε
  have hε' : 0 < ε / (C + 1) := by positivity
  obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.1 hw _ hε'
  -- bound for all `M`
  set K := ∑ j ∈ range M₀, |w j| + |L| * M₀
  have hall : ∀ M : ℕ, |∑ j ∈ range M, w j - L * M| ≤ K + ε / (C + 1) * M := by
    intro M
    rcases lt_or_ge M M₀ with h | h
    · have h1 : |∑ j ∈ range M, w j| ≤ ∑ j ∈ range M₀, |w j| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum_of_subset_of_nonneg
          (range_subset_range.2 h.le) fun _ _ _ => abs_nonneg _)
      have h2 : |L * M| ≤ |L| * M₀ := by
        rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (M : ℝ) from M.cast_nonneg)]
        gcongr
      have : 0 ≤ ε / (C + 1) * M := by positivity
      calc _ ≤ |∑ j ∈ range M, w j| + |L * M| := abs_sub _ _
        _ ≤ K + ε / (C + 1) * M := by simp only [K]; linarith
    · have h1 := hM₀ M h
      rw [Real.dist_eq] at h1
      have hK0 : 0 ≤ K := by positivity
      rcases Nat.eq_zero_or_pos M with h0 | h0
      · subst h0; simp; exact hK0
      have hMpos : (0 : ℝ) < M := by exact_mod_cast h0
      have e : ∑ j ∈ range M, w j - L * M = ((∑ j ∈ range M, w j) / M - L) * M := by
        field_simp
      rw [e, abs_mul, abs_of_pos hMpos]
      have : 0 ≤ K := by positivity
      nlinarith
  refine ⟨K + ε / (C + 1) * C, Eventually.of_forall fun N => ?_⟩
  refine (hall (Mf N)).trans ?_
  have := hM N
  have hl := Real.log_natCast_nonneg N
  have h1 : ε / (C + 1) * (Mf N : ℝ) ≤ ε / (C + 1) * (C * (Real.log N + 1)) := by gcongr
  have h2 : ε / (C + 1) * C ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  nlinarith

end Fphase

/-! ## The logarithmic sums of `1[{f(log₂ n)} ∈ [0, c)]` -/

section Phase5

variable {c : ℝ}

lemma logSmall_const (C : ℝ) : LogSmall fun _ => C :=
  logSmall_of_bdd (C := |C|) (Eventually.of_forall fun _ => le_rfl)

/-- `1[{F_n} ∈ [0, c)]`. -/
noncomputable def indF (c : ℝ) (n : ℕ) : ℝ := ind 0 c (Fn n)

/-- `K_n = Φ_{0,c}(F_n)`. -/
noncomputable def KF (c : ℝ) (n : ℕ) : ℝ := Φ 0 c (Fn n)

/-- `⌊F_n - r⌋`. -/
noncomputable def uF (r : ℝ) (n : ℕ) : ℤ := ⌊Fn n - r⌋

/-- `n` is irregular for the phase `F` if `⌊F_n⌋` or `⌊F_n - c⌋` jumps between `n` and `n + 1`. -/
def IrrF (c : ℝ) (n : ℕ) : Prop := uF 0 (n + 1) ≠ uF 0 n ∨ uF c (n + 1) ≠ uF c n

lemma uF_mono (r : ℝ) : Monotone (uF r) := fun _ _ h => Int.floor_mono (by
  have := Fn_mono h; linarith)

lemma xL_succ_le {N : ℕ} (hN : 1 ≤ N) : xL (N + 1) ≤ 2 * (Real.log N + 1) := by
  have := log_eq_xL (N + 1)
  have := log_succ_le_log_add_one hN
  have hl := Real.log_two_gt_d9
  have hx := xL_nonneg (N + 1)
  push_cast at *
  nlinarith

lemma Fn_succ_le {N : ℕ} (hN : 1 ≤ N) : Fn (N + 1) ≤ 2 * (Real.log N + 1) + 1 := by
  have h1 := xL_succ_le hN
  have hx := xL_nonneg (N + 1)
  unfold Fn f
  have : √(xL (N + 1)) ≤ (xL (N + 1) + 1) / 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg (xL (N + 1)),
      sq_nonneg (√(xL (N + 1)) - 1)]
  linarith

lemma uF_changes (r : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (changes (uF r) 1 (N + 1) : ℝ) ≤ 2 * (Real.log N + 1) + 2 := by
  have h := changes_le_of_monotone (uF_mono r) (by omega : 1 ≤ N + 1)
  have h1 : (uF r (N + 1) : ℝ) ≤ Fn (N + 1) - r := Int.floor_le _
  have h2 : Fn 1 - r - 1 < (uF r 1 : ℝ) := by
    show Fn 1 - r - 1 < ((⌊Fn 1 - r⌋ : ℤ) : ℝ)
    have := Int.lt_floor_add_one (Fn 1 - r); linarith
  have h3 : Fn 1 = 0 := by simp [Fn, xL, f]
  have h' : ((changes (uF r) 1 (N + 1) : ℤ) : ℝ) ≤ ((uF r (N + 1) - uF r 1 : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  have := Fn_succ_le hN
  linarith

lemma card_IrrF_le (N : ℕ) [DecidablePred (IrrF c)] :
    (((Icc 1 N).filter (IrrF c)).card : ℝ) ≤ 8 * (Real.log N + 1) := by
  classical
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp
  have h : ((Icc 1 N).filter (IrrF c)).card ≤ changes (uF 0) 1 (N + 1) +
      changes (uF c) 1 (N + 1) := by
    unfold changes
    rw [← sum_add_distrib, card_filter, Finset.Ico_add_one_right_eq_Icc]
    refine sum_le_sum fun n _ => ?_
    unfold IrrF
    by_cases h1 : uF 0 (n + 1) = uF 0 n <;> by_cases h2 : uF c (n + 1) = uF c n <;>
      simp [h1, h2]
  have h' : (((Icc 1 N).filter (IrrF c)).card : ℝ) ≤ (changes (uF 0) 1 (N + 1) : ℝ) +
      changes (uF c) 1 (N + 1) := by exact_mod_cast h
  have := uF_changes 0 h0
  have := uF_changes c h0
  have := Real.log_natCast_nonneg N
  linarith

lemma KF_step (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {n : ℕ} (hn : 3 ≤ n) [Decidable (IrrF c n)] :
    |KF c (n + 1) - KF c n - indF c n * (Fn (n + 1) - Fn n)| ≤
      if IrrF c n then 3 / (n : ℝ) else 0 := by
  have hΔ0 : 0 ≤ Fn (n + 1) - Fn n := by have := Fn_mono (Nat.le_succ n); linarith
  have hΔ1 := Fn_succ_sub_le' (by omega : 1 ≤ n)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hΔ1' : Fn (n + 1) - Fn n ≤ 1 := by
    have : (3 : ℝ) / n ≤ 1 := by rw [div_le_one (by linarith)]; exact hn'
    linarith
  unfold KF indF
  split_ifs with hirr
  · exact (Φ_step le_rfl hc0 hc1 (by linarith) (by linarith)).trans hΔ1
  · unfold IrrF uF at hirr
    simp only [ne_eq, not_or, not_not] at hirr
    rw [Φ_step_reg le_rfl hc0 hc1 hirr.1.symm hirr.2.symm, sub_self, abs_zero]

lemma KF_crude (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    |KF c (n + 1) - KF c n - indF c n * (Fn (n + 1) - Fn n)| ≤ 10 := by
  have hΔ0 : 0 ≤ Fn (n + 1) - Fn n := by have := Fn_mono (Nat.le_succ n); linarith
  have hΔ1 := Fn_succ_sub_le' hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : (3 : ℝ) / n ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h1 := abs_Φ_sub_le le_rfl hc0 hc1 (Fn (n + 1))
  have h2 := abs_Φ_sub_le le_rfl hc0 hc1 (Fn n)
  have hi0 := ind_nonneg 0 c (Fn n)
  have hi1 := ind_le_one 0 c (Fn n)
  unfold KF indF
  rw [abs_le] at h1 h2 ⊢
  simp only [sub_zero] at h1 h2
  constructor <;> nlinarith

open scoped Classical in
lemma logSmall_sum_EF (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    LogSmall fun N => ∑ n ∈ Icc 1 N, (KF c (n + 1) - KF c n - indF c n * (Fn (n + 1) - Fn n)) := by
  set E : ℕ → ℝ := fun n => KF c (n + 1) - KF c n - indF c n * (Fn (n + 1) - Fn n)
  have hs := logSmall_sparse (s := fun n => |E n|) (P := fun n => n < 3 ∨ IrrF c n) (K := 20)
    (C := 11) (by norm_num) (fun n => abs_nonneg _) ?_ ?_ ?_
  · exact hs.of_abs_le (Eventually.of_forall fun N => abs_sum_le_sum_abs _ _)
  · intro n hn
    simp only [not_or, not_lt] at hn
    have := KF_step hc0 hc1 hn.1 (n := n)
    rw [if_neg hn.2] at this
    exact le_antisymm this (abs_nonneg _)
  · intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    by_cases h3 : 3 ≤ n
    · have := KF_step hc0 hc1 h3 (n := n)
      have h20 : (3 : ℝ) / n ≤ 20 / n := div_le_div_of_nonneg_right (by norm_num) (by linarith)
      have h0 : 0 ≤ 20 / (n : ℝ) := by positivity
      simp only [E]
      split_ifs at this <;> linarith
    · have := KF_crude hc0 hc1 hn
      have : (n : ℝ) ≤ 2 := by exact_mod_cast (by omega : n ≤ 2)
      have : (10 : ℝ) ≤ 20 / n := by rw [le_div_iff₀ (by linarith)]; linarith
      simp only [E]; linarith
  · intro N
    have hsub : (Icc 1 N).filter (fun n => n < 3 ∨ IrrF c n) ⊆
        range 3 ∪ (Icc 1 N).filter (IrrF c) := by
      intro n hn
      obtain ⟨hn1, hP⟩ := mem_filter.1 hn
      rcases hP with hlt | hirr
      · exact mem_union_left _ (mem_range.2 hlt)
      · exact mem_union_right _ (mem_filter.2 ⟨hn1, hirr⟩)
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_range] at h1
    have h1' : (((Icc 1 N).filter (fun n => n < 3 ∨ IrrF c n)).card : ℝ) ≤
        3 + ((Icc 1 N).filter (IrrF c)).card := by exact_mod_cast h1
    have := card_IrrF_le (c := c) N
    have := Real.log_natCast_nonneg N
    linarith

/-- Phase `F` alone: `∑_{n ≤ N} 1[{F_n} ∈ [0, c)] (log(n+1) - log n) = c log N + o(log N)`. -/
lemma logSmall_T0 (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    LogSmall fun N => ∑ n ∈ Icc 1 N, indF c n * (Real.log (n + 1) - Real.log n) -
      c * Real.log N := by
  have hlam : ∀ n : ℕ, Real.log (n + 1) - Real.log n =
      2 * Real.log 2 * (Fn (n + 1) - Fn n) - 2 * Real.log 2 * (√(xL (n + 1)) - √(xL n)) := by
    intro n
    have h1 := log_eq_xL n
    have h2 := log_eq_xL (n + 1)
    push_cast at h2
    rw [h1, h2]; unfold Fn f; ring
  have hsplit : ∀ N, ∑ n ∈ Icc 1 N, indF c n * (Real.log (n + 1) - Real.log n) =
      2 * Real.log 2 * ((KF c (N + 1) - KF c 1) -
        ∑ n ∈ Icc 1 N, (KF c (n + 1) - KF c n - indF c n * (Fn (n + 1) - Fn n))) -
      2 * Real.log 2 * ∑ n ∈ Icc 1 N, indF c n * (√(xL (n + 1)) - √(xL n)) := by
    intro N
    rw [← sum_Icc_telescope (KF c) N, ← sum_sub_distrib, mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by rw [hlam n]; ring
  -- the `√x` part
  have hsq : LogSmall fun N => ∑ n ∈ Icc 1 N, indF c n * (√(xL (n + 1)) - √(xL n)) := by
    refine logSmall_sqrt_xL.of_abs_le (Eventually.of_forall fun N => ?_)
    have h0 : ∀ n, 0 ≤ √(xL (n + 1)) - √(xL n) := fun n => by
      have := Real.sqrt_le_sqrt (xL_mono (Nat.le_succ n)); linarith
    have h1 : ∀ n ∈ Icc 1 N, 0 ≤ indF c n * (√(xL (n + 1)) - √(xL n)) :=
      fun n _ => mul_nonneg (ind_nonneg _ _ _) (h0 n)
    rw [abs_of_nonneg (sum_nonneg h1)]
    calc _ ≤ ∑ n ∈ Icc 1 N, (√(xL (n + 1)) - √(xL n)) :=
          sum_le_sum fun n _ => by
            have := ind_le_one 0 c (Fn n); have := h0 n
            unfold indF; nlinarith
      _ = √(xL (N + 1)) - √(xL 1) := sum_Icc_telescope (fun n => √(xL n)) N
      _ = √(xL (N + 1)) := by simp [xL]
  -- the main term
  have hK : LogSmall fun N => 2 * Real.log 2 * KF c (N + 1) - c * Real.log N := by
    have hb : ∀ᶠ N : ℕ in atTop, |2 * Real.log 2 * (KF c (N + 1) - c * Fn (N + 1)) +
        c * (Real.log (N + 1) - Real.log N)| ≤ 2 * Real.log 2 * 2 + 1 := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have h1 := abs_Φ_sub_le le_rfl hc0 hc1 (Fn (N + 1))
      simp only [sub_zero] at h1
      have h2 := log_succ_le_log_add_one hN
      have h3 : Real.log N ≤ Real.log (N + 1) :=
        Real.log_le_log (by exact_mod_cast hN) (by linarith)
      have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
      unfold KF
      rw [abs_le] at h1 ⊢
      constructor <;> nlinarith
    have h4 := (logSmall_of_bdd hb).add (logSmall_sqrt_xL.const_mul (2 * Real.log 2 * c))
    refine h4.congr' (Eventually.of_forall fun N => ?_)
    have h5 := log_eq_xL (N + 1)
    push_cast at h5
    unfold Fn f
    rw [h5]
    ring
  have := ((hK.sub (logSmall_const (2 * Real.log 2 * KF c 1))).sub
    ((logSmall_sum_EF hc0 hc1).const_mul (2 * Real.log 2))).sub (hsq.const_mul (2 * Real.log 2))
  refine this.congr' (Eventually.of_forall fun N => ?_)
  rw [hsplit N]
  ring

end Phase5

/-! ## The joint distribution of `f(log₂ n)` and `θ log n` -/

section Phase6

variable {θ a b c : ℝ}

/-- `Q(x) = θ⁻¹ (Φ_{a,b}(θ' x) - (b - a) θ' x)` with `θ' = θ log 2`: the bounded part of
`H(n) = Q(log₂ n) + (b - a) log n`. -/
noncomputable def PQ (θ a b x : ℝ) : ℝ :=
  θ⁻¹ * (Φ a b (θ * Real.log 2 * x) - (b - a) * (θ * Real.log 2 * x))

lemma Hθ_eq (θ a b : ℝ) (hθ : 0 < θ) (n : ℕ) :
    Hθ θ a b n = (b - a) * Real.log n + PQ θ a b (xL n) := by
  unfold Hθ PQ
  rw [log_eq_xL n]
  field_simp
  ring

lemma abs_PQ_le (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (x : ℝ) :
    |PQ θ a b x| ≤ 2 / θ := by
  unfold PQ
  rw [abs_mul, abs_of_pos (inv_pos.2 hθ), div_eq_inv_mul]
  gcongr
  exact abs_Φ_sub_le ha hab hb _

lemma PQ_lip (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {x x' : ℝ}
    (h1 : θ * Real.log 2 * |x' - x| ≤ 1) :
    |PQ θ a b x' - PQ θ a b x| ≤ 3 * Real.log 2 * |x' - x| := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- reduce to `x ≤ x'`
  have key : ∀ u v : ℝ, u ≤ v → θ * Real.log 2 * (v - u) ≤ 1 →
      |PQ θ a b v - PQ θ a b u| ≤ 3 * Real.log 2 * (v - u) := by
    intro u v huv h2
    have hy : θ * Real.log 2 * u ≤ θ * Real.log 2 * v :=
      mul_le_mul_of_nonneg_left huv (by positivity)
    have hs := Φ_step ha hab hb hy (by nlinarith)
    have hi0 := ind_nonneg a b (θ * Real.log 2 * u)
    have hi1 := ind_le_one a b (θ * Real.log 2 * u)
    unfold PQ
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hθ)]
    have e : Φ a b (θ * Real.log 2 * v) - (b - a) * (θ * Real.log 2 * v) -
        (Φ a b (θ * Real.log 2 * u) - (b - a) * (θ * Real.log 2 * u)) =
        (Φ a b (θ * Real.log 2 * v) - Φ a b (θ * Real.log 2 * u) -
          ind a b (θ * Real.log 2 * u) * (θ * Real.log 2 * v - θ * Real.log 2 * u)) +
        (ind a b (θ * Real.log 2 * u) - (b - a)) * (θ * Real.log 2 * (v - u)) := by ring
    rw [e]
    have hd : 0 ≤ θ * Real.log 2 * (v - u) := by nlinarith
    have h3 : |(ind a b (θ * Real.log 2 * u) - (b - a)) * (θ * Real.log 2 * (v - u))| ≤
        2 * (θ * Real.log 2 * (v - u)) := by
      rw [abs_mul, abs_of_nonneg hd]
      have : |ind a b (θ * Real.log 2 * u) - (b - a)| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith
      nlinarith
    have h4 : θ * Real.log 2 * v - θ * Real.log 2 * u = θ * Real.log 2 * (v - u) := by ring
    calc θ⁻¹ * |_ + _| ≤ θ⁻¹ * (θ * Real.log 2 * (v - u) + 2 * (θ * Real.log 2 * (v - u))) := by
          gcongr
          exact (abs_add_le _ _).trans (add_le_add (h4 ▸ hs) h3)
      _ = 3 * Real.log 2 * (v - u) := by field_simp; ring
  rcases le_total x x' with hxx | hxx
  · rw [abs_of_nonneg (show 0 ≤ x' - x by linarith)] at h1 ⊢
    exact key x x' hxx h1
  · rw [abs_of_nonpos (show x' - x ≤ 0 by linarith)] at h1 ⊢
    rw [abs_sub_comm]
    have := key x' x hxx (by linarith)
    linarith

/-- Abel summation: `∑_{n=1}^{N} V(n) (P(n+1) - P(n)) = V(N+1) P(N+1) - V(1) P(1) -
∑_{n=1}^{N} (V(n+1) - V(n)) P(n+1)`. -/
lemma abel_Icc (V P : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, V n * (P (n + 1) - P n) =
      V (N + 1) * P (N + 1) - V 1 * P 1 - ∑ n ∈ Icc 1 N, (V (n + 1) - V n) * P (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ih]
    ring

/-- Reindexing the jumps of an integer sequence that increases by `0` or `1`. -/
lemma sum_jumps {V : ℕ → ℤ} {n₀ : ℕ} (hmono : Monotone V)
    (hV : ∀ n, n₀ ≤ n → V (n + 1) ≤ V n + 1) (Z : ℤ → ℝ) {N : ℕ} (hN : n₀ ≤ N) :
    ∑ n ∈ Ico n₀ N, ((V (n + 1) - V n : ℤ) : ℝ) * Z (V (n + 1)) =
      ∑ j ∈ range (V N - V n₀).toNat, Z (V n₀ + 1 + j) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [sum_Ico_succ_top hN, ih]
    have h1 : V N ≤ V (N + 1) := hmono (Nat.le_succ N)
    have h2 := hV N hN
    have h3 := hmono hN
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h]; simp
    · have h4 : V (N + 1) = V N + 1 := by omega
      rw [h4, show (V N + 1 - V n₀).toNat = (V N - V n₀).toNat + 1 by omega, sum_range_succ]
      have h5 : ((V N - V n₀).toNat : ℤ) = V N - V n₀ := Int.toNat_of_nonneg (by omega)
      push_cast
      rw [h5]
      simp only [add_sub_cancel_left, one_mul]
      congr 2
      ring

lemma τ_fract_neg (z : ℝ) : τ (Int.fract (-z)) = τ (Int.fract z) := by
  by_cases h : Int.fract z = 0
  · rw [h, Int.fract_neg_eq_zero.2 h]
  · rw [Int.fract_neg h]; unfold τ; ring

/-- Equidistribution along `f⁻¹`: `(1/M) ∑_{j<M} τ({θ' f⁻¹(y₀ + j) - s}) → 1/6`. -/
lemma tendsto_τ_finv {θ' : ℝ} (hθ' : 0 < θ') {y₀ : ℝ} (hy₀ : 0 ≤ y₀) (s : ℝ) :
    Tendsto (fun M : ℕ => (∑ j ∈ range M, τ (Int.fract (θ' * finv (y₀ + j) - s))) / M) atTop
      (𝓝 (1 / 6)) := by
  have h := tendsto_τ_avg (α := -2 * θ') (γ := 8 * θ' ^ 2) (δ := 4 * θ' ^ 2 * (1 + 2 * y₀))
    (σ := s - 2 * θ' * (y₀ + 1)) (by positivity) (by positivity)
  refine h.congr fun M => ?_
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [← τ_fract_neg]
  congr 2
  unfold uS
  rw [finv_eq _ (by positivity)]
  have e : √(8 * θ' ^ 2 * j + 4 * θ' ^ 2 * (1 + 2 * y₀)) = 2 * θ' * √(1 + 2 * (y₀ + j)) := by
    rw [show 8 * θ' ^ 2 * j + 4 * θ' ^ 2 * (1 + 2 * y₀) = (2 * θ') ^ 2 * (1 + 2 * (y₀ + j)) by
      ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [e]
  ring

/-- `uF r` increases by at most `1` from `n ≥ 3` on. -/
lemma uF_step (r : ℝ) {n : ℕ} (hn : 3 ≤ n) : uF r (n + 1) ≤ uF r n + 1 := by
  have h1 := Fn_succ_sub_le' (by omega : 1 ≤ n)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have : (3 : ℝ) / n ≤ 1 := by rw [div_le_one (by linarith)]; exact hn'
  unfold uF
  rw [← Int.floor_add_one]
  exact Int.floor_mono (by linarith)

lemma uF_step_le (r : ℝ) {n : ℕ} (hn : 1 ≤ n) : ((uF r (n + 1) - uF r n : ℤ) : ℝ) ≤ 4 := by
  have h1 := Fn_succ_sub_le' hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (3 : ℝ) / n ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : (uF r (n + 1) : ℝ) ≤ Fn (n + 1) - r := Int.floor_le _
  have h3 : Fn n - r - 1 < (uF r n : ℝ) := by
    show Fn n - r - 1 < ((⌊Fn n - r⌋ : ℤ) : ℝ)
    have := Int.lt_floor_add_one (Fn n - r); linarith
  push_cast
  linarith

/-- The jump sums `J_r(N) = ∑_{n ≤ N} (V_r(n+1) - V_r(n)) P(n+1)`, `V_r(n) = ⌊F_n - r⌋`, are
`κ M_r(N) + o(log N)`, where `M_r(N)` is the number of jumps after `n = 3`. -/
lemma jump_sum (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (r : ℝ) :
    LogSmall fun N => ∑ n ∈ Icc 1 N, ((uF r (n + 1) - uF r n : ℤ) : ℝ) * PQ θ a b (xL (n + 1)) -
      (-(θ⁻¹ * ((b - a) * (a + b + 1) / 2))) * (uF r (N + 1) - uF r 3 : ℤ).toNat := by
  classical
  set θ' := θ * Real.log 2 with hθ'
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hθ'0 : 0 < θ' := by positivity
  set V := uF r with hVdef
  set Z : ℤ → ℝ := fun m => PQ θ a b (finv ((m : ℝ) + r)) with hZ
  set κ := -(θ⁻¹ * ((b - a) * (a + b + 1) / 2)) with hκ
  have hΔ0 : ∀ n, (0 : ℝ) ≤ ((V (n + 1) - V n : ℤ) : ℝ) := fun n => by
    have := uF_mono r (Nat.le_succ n)
    exact_mod_cast sub_nonneg.2 this
  -- `n₁` beyond which the Lipschitz estimate applies
  obtain ⟨n₁', hn₁'⟩ := exists_nat_gt (2 * θ')
  set n₁ := n₁' + 3
  have hn₁ : (2 * θ' : ℝ) ≤ n₁ := by simp only [n₁]; push_cast; linarith
  -- error terms
  set e : ℕ → ℝ := fun n => ((V (n + 1) - V n : ℤ) : ℝ) * (PQ θ a b (xL (n + 1)) - Z (V (n + 1)))
  have he : LogSmall fun N => ∑ n ∈ Icc 1 N, e n := by
    have hs := logSmall_sparse (s := fun n => |e n|) (P := fun n => n < n₁ ∨ V (n + 1) ≠ V n)
      (K := 16 * n₁ / θ + 6) (C := n₁ + 4) (by positivity)
      (fun n => abs_nonneg _) ?_ ?_ ?_
    · exact hs.of_abs_le (Eventually.of_forall fun N => abs_sum_le_sum_abs _ _)
    · intro n hn
      simp only [not_or, not_lt, ne_eq, not_not] at hn
      simp only [e, hn.2, sub_self, Int.cast_zero, zero_mul, abs_zero]
    · intro n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      by_cases hsmall : n < n₁
      · -- crude bound
        have h1 := uF_step_le r hn
        have h2 := abs_PQ_le hθ ha hab hb (xL (n + 1))
        have h3 := abs_PQ_le hθ ha hab hb (finv ((V (n + 1) : ℝ) + r))
        have h4 : |e n| ≤ 16 / θ := by
          simp only [e, Z]
          rw [abs_mul, abs_of_nonneg (hΔ0 n)]
          have : |PQ θ a b (xL (n + 1)) - PQ θ a b (finv ((V (n + 1) : ℝ) + r))| ≤ 4 / θ := by
            calc _ ≤ |PQ θ a b (xL (n + 1))| + |PQ θ a b (finv ((V (n + 1) : ℝ) + r))| :=
                  abs_sub _ _
              _ ≤ 2 / θ + 2 / θ := add_le_add h2 h3
              _ = 4 / θ := by ring
          calc _ ≤ 4 * (4 / θ) := mul_le_mul h1 this (abs_nonneg _) (by norm_num)
            _ = 16 / θ := by ring
        have hle : (n : ℝ) ≤ n₁ := by exact_mod_cast hsmall.le
        have : 16 / θ ≤ (16 * n₁ / θ + 6) / n := by
          rw [le_div_iff₀ (by linarith)]
          have : 16 / θ * n ≤ 16 * n₁ / θ := by
            rw [div_mul_eq_mul_div]; gcongr
          linarith
        linarith
      · push Not at hsmall
        have hn3 : 3 ≤ n := by simp only [n₁] at hsmall; omega
        have hstep := uF_step r hn3
        have hmono : uF r n ≤ uF r (n + 1) := uF_mono r (Nat.le_succ n)
        rcases eq_or_lt_of_le hmono with heq | hlt
        · have : e n = 0 := by simp only [e, V]; rw [← heq, sub_self, Int.cast_zero, zero_mul]
          rw [this, abs_zero]
          positivity
        · have hjump : V (n + 1) = V n + 1 := by simp only [V]; omega
          -- `f⁻¹(V(n+1) + r)` lies in `(x_n, x_{n+1}]`
          have hlo : Fn n < (V (n + 1) : ℝ) + r := by
            rw [hjump]; push_cast
            have := Int.lt_floor_add_one (Fn n - r)
            simp only [V, uF]; linarith
          have hhi : (V (n + 1) : ℝ) + r ≤ Fn (n + 1) := by
            have := Int.floor_le (Fn (n + 1) - r)
            simp only [V, uF]; linarith
          have hj := finv_jump hlo hhi
          have hx := xL_succ_sub hn
          have hd : |xL (n + 1) - finv ((V (n + 1) : ℝ) + r)| ≤ 2 / n := hj.trans hx
          have hlip := PQ_lip hθ ha hab hb (x := finv ((V (n + 1) : ℝ) + r)) (x' := xL (n + 1))
            (by
              rw [← hθ']
              calc θ' * |xL (n + 1) - finv ((V (n + 1) : ℝ) + r)| ≤ θ' * (2 / n) := by gcongr
                _ ≤ 1 := by
                  rw [mul_div_assoc', div_le_one (by linarith)]
                  have : (n₁ : ℝ) ≤ n := by exact_mod_cast hsmall
                  linarith)
          have e1 : e n = PQ θ a b (xL (n + 1)) - PQ θ a b (finv ((V (n + 1) : ℝ) + r)) := by
            simp only [e, Z]
            rw [hjump, show V n + 1 - V n = 1 by ring, Int.cast_one, one_mul]
          rw [e1]
          have hl2 : Real.log 2 < 1 := by
            have := Real.log_two_lt_d9; linarith
          calc _ ≤ 3 * Real.log 2 * |xL (n + 1) - finv ((V (n + 1) : ℝ) + r)| := hlip
            _ ≤ 3 * 1 * (2 / n) := by gcongr
            _ ≤ (16 * n₁ / θ + 6) / n := by
                rw [show 3 * 1 * (2 / (n : ℝ)) = 6 / n by ring]
                apply div_le_div_of_nonneg_right _ (by linarith)
                have : 0 ≤ 16 * (n₁ : ℝ) / θ := by positivity
                linarith
    · intro N
      have hsub : (Icc 1 N).filter (fun n => n < n₁ ∨ V (n + 1) ≠ V n) ⊆
          range n₁ ∪ ((Icc 1 N).filter fun n => V (n + 1) ≠ V n) := by
        intro n hn
        obtain ⟨hn1, hP⟩ := mem_filter.1 hn
        rcases hP with hlt | hV
        · exact mem_union_left _ (mem_range.2 hlt)
        · exact mem_union_right _ (mem_filter.2 ⟨hn1, hV⟩)
      have h1 := (card_le_card hsub).trans (card_union_le _ _)
      rw [card_range] at h1
      have h2 : ((Icc 1 N).filter fun n => V (n + 1) ≠ V n).card = changes V 1 (N + 1) := by
        unfold changes
        rw [card_filter, Finset.Ico_add_one_right_eq_Icc]
        exact sum_congr rfl fun n _ => by split_ifs <;> simp_all
      have hl0 := Real.log_natCast_nonneg N
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; simp; positivity
      have h3 := uF_changes r h0
      have h1' : (((Icc 1 N).filter (fun n => n < n₁ ∨ V (n + 1) ≠ V n)).card : ℝ) ≤
          n₁ + changes V 1 (N + 1) := by rw [← h2]; exact_mod_cast h1
      nlinarith
  -- the main term, reindexed by the jumps
  set y₀ : ℝ := ((V 3 + 1 : ℤ) : ℝ) + r
  have hy₀ : 0 ≤ y₀ := by
    simp only [y₀]; push_cast
    have := Int.lt_floor_add_one (Fn 3 - r)
    have := Fn_nonneg 3
    simp only [V, uF]; linarith
  set Mf : ℕ → ℕ := fun N => (V (N + 1) - V 3).toNat
  have hMf : ∀ N, (Mf N : ℝ) ≤ 3 * (Real.log N + 1) + 4 := by
    intro N
    rcases Nat.lt_or_ge N 2 with hN | hN
    · have : V (N + 1) ≤ V 3 := uF_mono r (by omega)
      have : Mf N = 0 := by simp only [Mf]; omega
      rw [this]; have := Real.log_natCast_nonneg N; push_cast; linarith
    · have h1 : (V (N + 1) : ℝ) ≤ Fn (N + 1) - r := Int.floor_le _
      have h2 : Fn 3 - r - 1 < (V 3 : ℝ) := by
        show Fn 3 - r - 1 < ((⌊Fn 3 - r⌋ : ℤ) : ℝ)
        have := Int.lt_floor_add_one (Fn 3 - r); linarith
      have h3 := Fn_succ_le (by omega : 1 ≤ N)
      have h4 := Fn_nonneg 3
      have h5 : V 3 ≤ V (N + 1) := uF_mono r (by omega)
      have h6 : ((Mf N : ℕ) : ℤ) = V (N + 1) - V 3 := Int.toNat_of_nonneg (by omega)
      have h7 : ((Mf N : ℕ) : ℝ) = (V (N + 1) : ℝ) - V 3 := by exact_mod_cast h6
      rw [h7]; linarith
  have hZsum : ∀ M : ℕ, ∑ j ∈ range M, Z (V 3 + 1 + j) = κ * M + (2 * θ)⁻¹ *
      (∑ j ∈ range M, τ (Int.fract (θ' * finv (y₀ + j) - a)) -
        ∑ j ∈ range M, τ (Int.fract (θ' * finv (y₀ + j) - b))) := by
    intro M
    rw [← sum_sub_distrib, mul_sum]
    rw [show κ * M = ∑ _j ∈ range M, κ by simp; ring, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [Z, PQ, κ, y₀]
    rw [Φ_eq]
    push_cast
    rw [← hθ']
    field_simp
    ring_nf
  have hA := logSmall_of_avg (tendsto_τ_finv hθ'0 hy₀ a) (Mf := Mf) (C := 7)
    (by norm_num) (fun N => by have := hMf N; have := Real.log_natCast_nonneg N; linarith)
  have hB := logSmall_of_avg (tendsto_τ_finv hθ'0 hy₀ b) (Mf := Mf) (C := 7)
    (by norm_num) (fun N => by have := hMf N; have := Real.log_natCast_nonneg N; linarith)
  have hmain : LogSmall fun N => ∑ j ∈ range (Mf N), Z (V 3 + 1 + j) - κ * Mf N := by
    have := (hA.sub hB).const_mul (2 * θ)⁻¹
    refine this.congr' (Eventually.of_forall fun N => ?_)
    rw [hZsum]; ring
  -- assemble
  have hsplit : ∀ N, 2 ≤ N → ∑ n ∈ Icc 1 N, ((V (n + 1) - V n : ℤ) : ℝ) * PQ θ a b (xL (n + 1)) =
      (∑ n ∈ Icc 1 2, ((V (n + 1) - V n : ℤ) : ℝ) * Z (V (n + 1))) +
      ∑ j ∈ range (Mf N), Z (V 3 + 1 + j) + ∑ n ∈ Icc 1 N, e n := by
    intro N hN
    have h1 : ∑ n ∈ Icc 1 N, ((V (n + 1) - V n : ℤ) : ℝ) * PQ θ a b (xL (n + 1)) =
        ∑ n ∈ Icc 1 N, ((V (n + 1) - V n : ℤ) : ℝ) * Z (V (n + 1)) + ∑ n ∈ Icc 1 N, e n := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun n _ => by simp only [e]; ring
    rw [h1]
    congr 1
    rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc,
      ← sum_Ico_consecutive _ (by norm_num : 1 ≤ 2 + 1) (by omega : 2 + 1 ≤ N + 1)]
    congr 1
    exact sum_jumps (uF_mono r) (fun n hn => uF_step r hn) Z (by omega)
  have := (hmain.add he).add (logSmall_const (∑ n ∈ Icc 1 2, ((V (n + 1) - V n : ℤ) : ℝ) *
    Z (V (n + 1))))
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [hsplit N hN]
  ring

end Phase6

/-! ## Theorem \ref{IA:thm:324} -/

section Thm324

variable {θ a b c : ℝ}

/-- `∑_{n ≤ N} 1[{F_n} ∈ [0, c)] 1[{θ log n} ∈ [a, b)] / n = c (b - a) log N + o(log N)`. -/
lemma logSmall_joint (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) :
    LogSmall fun N => ∑ n ∈ Icc 1 N, indF c n * gθ θ a b n / n - c * (b - a) * Real.log N := by
  set P : ℕ → ℝ := fun n => PQ θ a b (xL n)
  have hP : ∀ n, |P n| ≤ 2 / θ := fun n => abs_PQ_le hθ ha hab hb _
  have hgd : ∀ n : ℕ, gθ θ a b n / n = (b - a) * (Real.log (n + 1) - Real.log n) +
      (P (n + 1) - P n) + dθ θ a b n := by
    intro n
    have h1 := Hθ_eq θ a b hθ n
    have h2 := Hθ_eq θ a b hθ (n + 1)
    push_cast at h2
    unfold dθ
    simp only [P]
    rw [h1, h2]; ring
  have hind : ∀ n, indF c n = ((uF 0 n : ℝ) - uF c n) := by
    intro n
    unfold indF uF
    rw [ind_eq_floor le_rfl hc0 hc1]
    push_cast; ring
  -- (i) the linear part
  have h1 := (logSmall_T0 hc0 hc1).const_mul (b - a)
  -- (ii) the error `d`
  have h2 : LogSmall fun N => ∑ n ∈ Icc 1 N, indF c n * dθ θ a b n := by
    refine (logSmall_sum_abs_dθ hθ ha hab hb).of_abs_le (Eventually.of_forall fun N => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    have := ind_nonneg 0 c (Fn n); have := ind_le_one 0 c (Fn n)
    rw [abs_of_nonneg (by unfold indF; assumption)]
    calc indF c n * |dθ θ a b n| ≤ 1 * |dθ θ a b n| := by
          gcongr; unfold indF; assumption
      _ = |dθ θ a b n| := one_mul _
  -- (iii) the bounded part, by Abel summation
  have hJ0 := jump_sum hθ ha hab hb 0
  have hJc := jump_sum hθ ha hab hb c
  set κ := -(θ⁻¹ * ((b - a) * (a + b + 1) / 2))
  have hM : ∀ᶠ N : ℕ in atTop, |κ * ((uF 0 (N + 1) - uF 0 3 : ℤ).toNat : ℝ) -
      κ * ((uF c (N + 1) - uF c 3 : ℤ).toNat : ℝ)| ≤ |κ| * 2 := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have e0 : (((uF 0 (N + 1) - uF 0 3 : ℤ).toNat : ℕ) : ℤ) = uF 0 (N + 1) - uF 0 3 :=
      Int.toNat_of_nonneg (by have := uF_mono 0 (by omega : 3 ≤ N + 1); omega)
    have ec : (((uF c (N + 1) - uF c 3 : ℤ).toNat : ℕ) : ℤ) = uF c (N + 1) - uF c 3 :=
      Int.toNat_of_nonneg (by have := uF_mono c (by omega : 3 ≤ N + 1); omega)
    have e0' : (((uF 0 (N + 1) - uF 0 3 : ℤ).toNat : ℕ) : ℝ) = (uF 0 (N + 1) : ℝ) - uF 0 3 := by
      exact_mod_cast e0
    have ec' : (((uF c (N + 1) - uF c 3 : ℤ).toNat : ℕ) : ℝ) = (uF c (N + 1) : ℝ) - uF c 3 := by
      exact_mod_cast ec
    rw [← mul_sub, abs_mul, e0', ec']
    gcongr
    have i1 := hind (N + 1); have i2 := hind 3
    have j1 := ind_nonneg 0 c (Fn (N + 1)); have j2 := ind_le_one 0 c (Fn (N + 1))
    have j3 := ind_nonneg 0 c (Fn 3); have j4 := ind_le_one 0 c (Fn 3)
    unfold indF at i1 i2
    rw [abs_le]; constructor <;> linarith
  have hbd : ∀ N : ℕ, |indF c (N + 1) * P (N + 1) - indF c 1 * P 1| ≤ 4 / θ := by
    intro N
    have hb1 : ∀ n, |indF c n * P n| ≤ 2 / θ := by
      intro n
      rw [abs_mul]
      have j1 := ind_nonneg 0 c (Fn n); have j2 := ind_le_one 0 c (Fn n)
      have : |indF c n| ≤ 1 := by unfold indF; rw [abs_of_nonneg j1]; exact j2
      calc |indF c n| * |P n| ≤ 1 * (2 / θ) := mul_le_mul this (hP n) (abs_nonneg _) (by norm_num)
        _ = 2 / θ := one_mul _
    calc _ ≤ |indF c (N + 1) * P (N + 1)| + |indF c 1 * P 1| := abs_sub _ _
      _ ≤ 2 / θ + 2 / θ := add_le_add (hb1 _) (hb1 _)
      _ = 4 / θ := by ring
  have h3 : LogSmall fun N => ∑ n ∈ Icc 1 N, indF c n * (P (n + 1) - P n) := by
    have := ((logSmall_of_bdd (Eventually.of_forall hbd)).sub (hJ0.sub hJc)).sub
      (logSmall_of_bdd hM)
    refine this.congr' (Eventually.of_forall fun N => ?_)
    have a0 := abel_Icc (fun n => (uF 0 n : ℝ)) P N
    have ac := abel_Icc (fun n => (uF c n : ℝ)) P N
    have e : ∑ n ∈ Icc 1 N, indF c n * (P (n + 1) - P n) =
        ∑ n ∈ Icc 1 N, (uF 0 n : ℝ) * (P (n + 1) - P n) -
        ∑ n ∈ Icc 1 N, (uF c n : ℝ) * (P (n + 1) - P n) := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun n _ => by rw [hind]; ring
    rw [e, a0, ac, hind (N + 1), hind 1]
    simp only [P]
    push_cast
    ring
  have := (h1.add h3).add h2
  refine this.congr' (Eventually.of_forall fun N => ?_)
  have e : ∑ n ∈ Icc 1 N, indF c n * gθ θ a b n / n =
      (b - a) * ∑ n ∈ Icc 1 N, indF c n * (Real.log (n + 1) - Real.log n) +
      ∑ n ∈ Icc 1 N, indF c n * (P (n + 1) - P n) + ∑ n ∈ Icc 1 N, indF c n * dθ θ a b n := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by rw [mul_div_assoc, hgd n]; ring
  rw [e]
  ring

lemma A324_indicator (η θ a b : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (A324 η).indicator (fun n : ℕ => gθ θ a b n / n) n = indF (1 / 2 - η) n * gθ θ a b n / n := by
  classical
  unfold indF ind Fn xL
  by_cases h : Int.fract (f (Real.logb 2 n)) ∈ Set.Ico 0 (1 / 2 - η)
  · rw [Set.indicator_of_mem (show n ∈ A324 η from ⟨hn, h⟩), if_pos h]; ring
  · rw [Set.indicator_of_notMem (fun h' => h h'.2), if_neg h]; ring

lemma A324_half {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) :
    HasLogDensity {n ∈ A324 η | Int.fract (θ * Real.log n) ∈ Set.Ico a b}
      ((1 / 2 - η) * (b - a)) := by
  have h := tendsto_of_logSmall (logSmall_joint (c := 1 / 2 - η) hθ ha hab hb (by linarith)
    (by linarith))
  unfold HasLogDensity
  simp only [indicator_phase]
  refine h.congr fun N => ?_
  congr 1
  exact sum_congr rfl fun n hn => (A324_indicator η θ a b (mem_Icc.1 hn).1).symm

/-- Paper, Theorem \ref{IA:thm:324}, first assertion: `d_log(A) = 1/2 - η`. -/
theorem A324_logDensity {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) :
    HasLogDensity (A324 η) (1 / 2 - η) := by
  have h := A324_half (θ := 1) (a := 0) (b := 1) hη hη' one_pos le_rfl zero_le_one le_rfl
  have e : {n ∈ A324 η | Int.fract (1 * Real.log n) ∈ Set.Ico (0 : ℝ) 1} = A324 η := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_Ico, Int.fract_nonneg, Int.fract_lt_one, and_self,
      and_true]
  rw [e] at h
  simpa using h

/-- Paper, Theorem \ref{IA:thm:324}, second assertion: `A` satisfies `(21)`. -/
theorem A324_eq21 {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) (hθ : 0 < θ) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) :
    HasLogDensity {n ∈ A324 η | Int.fract (θ * Real.log n) ∈ Set.Ioo a b}
      ((1 / 2 - η) * (b - a)) :=
  eq21_open_of_half (by linarith) (fun a b ha hab hb => A324_half hη hη' hθ ha hab hb) ha hab hb

/-- Paper, Theorem \ref{IA:thm:324}: for `0 < η < 1/2`, `f(x) = x/2 + √x` and
`A = {n ∈ ℕ : {f(log₂ n)} ∈ [0, 1/2 - η)}`, the set `A` has logarithmic density `1/2 - η`,
satisfies `(21)`, and contains no `B + B + t` with `t ∈ ℤ` and `B ⊆ ℕ` infinite. -/
theorem thm324 {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) :
    HasLogDensity (A324 η) (1 / 2 - η) ∧
    (∀ θ : ℝ, 0 < θ → ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      HasLogDensity {n ∈ A324 η | Int.fract (θ * Real.log n) ∈ Set.Ioo a b}
        ((1 / 2 - η) * (b - a))) ∧
    ∀ t : ℤ, ∀ B : Set ℕ, B.Infinite → ¬ SumsetIn B t (A324 η) :=
  ⟨A324_logDensity hη hη', fun _ hθ _ _ ha hab hb => A324_eq21 hη hη' hθ ha hab hb,
    fun t _ hB => A324_no_BBt hη hη' t hB⟩

/-- The negative answer to Question 3.24, witnessed by the set of Theorem \ref{IA:thm:324}
(with `η = 1/4`). -/
theorem not_question324' : ¬ Question324 := by
  intro hQ
  have hη : (0 : ℝ) < 1 / 4 := by norm_num
  have hη' : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  have h0 : 0 ∉ A324 (1 / 4) := fun h => (lt_irrefl 0) h.1
  obtain ⟨t, B, hB, -, hBA⟩ := hQ (A324 (1 / 4)) h0 (1 / 2 - 1 / 4) (by norm_num)
    (A324_logDensity hη hη') (fun θ hθ a b ha hab hb => A324_eq21 hη hη' hθ ha hab hb)
  exact A324_no_BBt hη hη' t hB fun b hb b' hb' => ⟨b + b' + t, hBA b hb b' hb', by push_cast; ring⟩

end Thm324

/-! ## The natural density of `A_KR` -/

section NatDensity

/-- Criterion: `u N / N → 0` if for every `ε > 0`, eventually `|u N| ≤ K + ε N`. -/
lemma natSmall_of_forall {u : ℕ → ℝ}
    (h : ∀ ε > 0, ∃ K : ℝ, ∀ᶠ N in atTop, |u N| ≤ K + ε * N) :
    Tendsto (fun N => u N / N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := h (ε / 2) (by positivity)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hK
  obtain ⟨N2, hN2⟩ := exists_nat_gt (2 * |K| / ε)
  refine ⟨max (max N1 N2) 1, fun N hN => ?_⟩
  have h1 := hN1 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have hN2' : (N2 : ℝ) ≤ N := by
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast this
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hNpos, div_lt_iff₀ hNpos]
  have : 2 * |K| < ε * N := by
    rw [div_lt_iff₀ hε] at hN2; nlinarith
  have := le_abs_self K
  nlinarith

lemma card_W_le (N : ℕ) {k₀ : ℕ} (hk₀ : 1 ≤ k₀) :
    (∑ n ∈ Icc 1 N, W.indicator (fun _ : ℕ => (1 : ℝ)) n) ≤
      4 ^ k₀ + 8 / (3 * k₀) * N + (Real.log N + 1) := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · subst hN0; simp; positivity
  set K := Nat.log 4 N
  -- `1_W(n) ≤ ∑_{k ≤ K} 1_{W_k}(n)`
  have hterm : ∀ n ∈ Icc 1 N, W.indicator (fun _ : ℕ => (1 : ℝ)) n ≤
      ∑ k ∈ Icc 1 K, (Wk k).indicator (fun _ : ℕ => (1 : ℝ)) n := by
    intro n hn
    by_cases h : n ∈ W
    · obtain ⟨k, hk, hkn⟩ := h
      rw [Set.indicator_of_mem (show n ∈ W from ⟨k, hk, hkn⟩)]
      have hkK : k ∈ Icc 1 K := by
        refine mem_Icc.2 ⟨hk, ?_⟩
        have h1 : (4 : ℝ) ^ k ≤ n := by
          have : 1 / (k : ℝ) ≤ 1 := by
            rw [div_le_one (by exact_mod_cast hk)]; exact_mod_cast hk
          nlinarith [hkn.1, (by positivity : (0 : ℝ) ≤ 4 ^ k)]
        have h2 : 4 ^ k ≤ N := by
          have : 4 ^ k ≤ n := by exact_mod_cast h1
          exact this.trans (mem_Icc.1 hn).2
        exact Nat.le_log_of_pow_le (by norm_num) h2
      have := single_le_sum (f := fun k => (Wk k).indicator (fun _ : ℕ => (1 : ℝ)) n)
        (fun k _ => Set.indicator_nonneg (fun _ _ => zero_le_one) n) hkK
      simpa [Set.indicator_of_mem hkn] using this
    · rw [Set.indicator_of_notMem h]
      exact sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => zero_le_one) n
  have h1 := sum_le_sum hterm
  rw [sum_comm] at h1
  -- each `W_k` has at most `(2/k) 4^k + 1` elements
  have hWk : ∀ k ∈ Icc 1 K, ∑ n ∈ Icc 1 N, (Wk k).indicator (fun _ : ℕ => (1 : ℝ)) n ≤
      2 / k * 4 ^ k + 1 := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.1 hk).1
    have hx : (0 : ℝ) ≤ (2 - 1 / (k : ℝ)) * 4 ^ k := by
      have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hk1
      nlinarith [(by positivity : (0 : ℝ) ≤ 4 ^ k)]
    have hc := card_Ico_real_le hx (y := (2 + 1 / (k : ℝ)) * 4 ^ k)
      (by have : 0 ≤ 1 / (k : ℝ) := by positivity
          nlinarith [(by positivity : (0 : ℝ) ≤ 4 ^ k)]) (Icc 1 N)
    have e : ∑ n ∈ Icc 1 N, (Wk k).indicator (fun _ : ℕ => (1 : ℝ)) n =
        (((Icc 1 N).filter fun n : ℕ => (2 - 1 / (k : ℝ)) * 4 ^ k ≤ n ∧
          (n : ℝ) < (2 + 1 / (k : ℝ)) * 4 ^ k).card : ℝ) := by
      rw [card_filter]; push_cast
      exact sum_congr rfl fun n _ => by
        unfold Set.indicator Wk; simp only [Set.mem_ofPred_eq]
    rw [e]
    have : (2 + 1 / (k : ℝ)) * 4 ^ k - (2 - 1 / (k : ℝ)) * 4 ^ k + 1 = 2 / k * 4 ^ k + 1 := by
      ring
    linarith
  have h2 := sum_le_sum hWk
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel] at h2
  -- `∑_{k ≤ K} (2/k) 4^k ≤ 4^{k₀} + (8/(3k₀)) 4^K`
  have h3 : ∑ k ∈ Icc 1 K, 2 / (k : ℝ) * 4 ^ k ≤ 4 ^ k₀ + 8 / (3 * k₀) * 4 ^ K := by
    have hterm2 : ∀ k ∈ Icc 1 K, 2 / (k : ℝ) * 4 ^ k ≤
        (if k < k₀ then 2 * 4 ^ k else 0) + 2 / k₀ * 4 ^ k := by
      intro k hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.1 hk).1
      split_ifs with hkk
      · have : 2 / (k : ℝ) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
        have : 0 ≤ 2 / (k₀ : ℝ) * 4 ^ k := by positivity
        nlinarith [(by positivity : (0 : ℝ) ≤ 4 ^ k)]
      · rw [zero_add]
        gcongr
        exact_mod_cast not_lt.1 hkk
    refine (sum_le_sum hterm2).trans ?_
    rw [sum_add_distrib, ← mul_sum]
    have hg : ∀ m : ℕ, ∑ k ∈ range m, (4 : ℝ) ^ k ≤ 4 ^ m / 3 := by
      intro m
      rw [geom_sum_eq (by norm_num)]
      have : (0 : ℝ) < 4 ^ m := by positivity
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      linarith
    have ha : ∑ k ∈ Icc 1 K, (if k < k₀ then 2 * (4 : ℝ) ^ k else 0) ≤ 4 ^ k₀ := by
      calc _ ≤ ∑ k ∈ range k₀, 2 * (4 : ℝ) ^ k := by
            rw [sum_ite, sum_const_zero, add_zero]
            refine sum_le_sum_of_subset_of_nonneg (fun k hk => mem_range.2 (mem_filter.1 hk).2)
              fun _ _ _ => by positivity
        _ ≤ 2 * (4 ^ k₀ / 3) := by rw [← mul_sum]; gcongr; exact hg k₀
        _ ≤ 4 ^ k₀ := by have : (0 : ℝ) ≤ 4 ^ k₀ := by positivity
                         linarith
    have hb : ∑ k ∈ Icc 1 K, (4 : ℝ) ^ k ≤ 4 ^ (K + 1) / 3 := by
      refine le_trans (sum_le_sum_of_subset_of_nonneg (fun k hk => mem_range.2
        (by have := (mem_Icc.1 hk).2; omega)) fun _ _ _ => by positivity) (hg (K + 1))
    have hk0 : (0 : ℝ) < k₀ := by exact_mod_cast hk₀
    calc _ ≤ (4 : ℝ) ^ k₀ + 2 / k₀ * (4 ^ (K + 1) / 3) := by gcongr
      _ = 4 ^ k₀ + 8 / (3 * k₀) * 4 ^ K := by rw [pow_succ]; field_simp; ring
  have h4 : (4 : ℝ) ^ K ≤ N := by exact_mod_cast Nat.pow_log_le_self 4 (by omega)
  have h5 : (K : ℝ) ≤ Real.log N := by
    have h6 : (K : ℝ) * Real.log 4 ≤ Real.log N := by
      have := Real.log_le_log (by positivity) h4
      simpa [Real.log_pow] using this
    have h7 : (1 : ℝ) ≤ Real.log 4 := by
      have := Real.log_two_gt_d9
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      linarith
    have : (0 : ℝ) ≤ K := K.cast_nonneg
    nlinarith
  have h8 : 8 / (3 * (k₀ : ℝ)) * 4 ^ K ≤ 8 / (3 * k₀) * N := by gcongr
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ 4 ^ k₀ + 8 / (3 * k₀) * N + (Real.log N + 1) := by linarith

/-- Paper, Proposition \ref{IA:prop:KR}, first assertion (Kousek–Radić, Proposition 4.2):
`A_KR` has natural density `1/2`. -/
theorem AKR_natDensity : HasNatDensity AKR (1 / 2) := by
  classical
  set h : ℕ → ℝ := fun n => (-1 : ℝ) ^ Nat.log 2 n
  -- `1_{A_KR} = 1_Q - e` with `0 ≤ e ≤ 1_W`
  have hE : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (Qset.indicator (fun _ => (1 : ℝ)) n -
      AKR.indicator (fun _ => (1 : ℝ)) n)) / N) atTop (𝓝 0) := by
    apply natSmall_of_forall
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (16 / (3 * ε))
    have hk₀1 : 1 ≤ k₀ := by
      have : (0 : ℝ) < k₀ := lt_of_le_of_lt (by positivity) hk₀
      exact_mod_cast this
    refine ⟨4 ^ k₀ + 1 + 1, ?_⟩
    have hlogN : ∀ᶠ N : ℕ in atTop, Real.log N + 1 ≤ ε / 2 * N + 1 := by
      have := (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop)
      have h2 := this.def (c := ε / 2) (by positivity)
      filter_upwards [h2, eventually_ge_atTop 1] with N hN hN1
      simp only [Function.comp, id, Real.norm_eq_abs] at hN
      have := Real.log_natCast_nonneg N
      rw [abs_of_nonneg this, abs_of_nonneg (N.cast_nonneg)] at hN
      linarith
    filter_upwards [hlogN] with N hN
    have h0 : ∀ n,
        0 ≤ Qset.indicator (fun _ => (1 : ℝ)) n - AKR.indicator (fun _ => (1 : ℝ)) n := by
      intro n
      by_cases hn : n ∈ AKR
      · rw [Set.indicator_of_mem hn, Set.indicator_of_mem (AKR_subset_Q hn), sub_self]
      · rw [Set.indicator_of_notMem hn, sub_zero]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) n
    have hle : ∀ n, Qset.indicator (fun _ => (1 : ℝ)) n - AKR.indicator (fun _ => (1 : ℝ)) n ≤
        W.indicator (fun _ => (1 : ℝ)) n := by
      intro n
      by_cases hn : n ∈ AKR
      · rw [Set.indicator_of_mem hn, Set.indicator_of_mem (AKR_subset_Q hn), sub_self]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) n
      · rw [Set.indicator_of_notMem hn, sub_zero]
        by_cases hQ : n ∈ Qset
        · have hW : n ∈ W := by by_contra hW; exact hn (mem_AKR_of_Q hQ hW)
          rw [Set.indicator_of_mem hQ, Set.indicator_of_mem hW]
        · rw [Set.indicator_of_notMem hQ]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) n
    rw [abs_of_nonneg (sum_nonneg fun n _ => h0 n)]
    have h1 := (sum_le_sum fun n (_ : n ∈ Icc 1 N) => hle n).trans (card_W_le N hk₀1)
    have h2 : 8 / (3 * (k₀ : ℝ)) ≤ ε / 2 := by
      have hk : (0 : ℝ) < k₀ := by exact_mod_cast hk₀1
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hk₀
      nlinarith
    have h3 : 8 / (3 * (k₀ : ℝ)) * N ≤ ε / 2 * N := by gcongr
    linarith
  -- the alternating part
  have hA : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N,
      (if 4 ≤ n then (-1) ^ n * (h n * 1) * (1 / 2) else 0 : ℝ)) / N) atTop (𝓝 0) := by
    apply natSmall_of_forall
    intro ε hε
    refine ⟨5, ?_⟩
    have hlogN : ∀ᶠ N : ℕ in atTop, 2 * Real.log (N + 1) ≤ ε * N + 2 := by
      have := (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop)
      have h2 := this.def (c := ε / 4) (by positivity)
      filter_upwards [h2, eventually_ge_atTop 1] with N hN hN1
      simp only [Function.comp, id, Real.norm_eq_abs] at hN
      have := Real.log_natCast_nonneg N
      rw [abs_of_nonneg this, abs_of_nonneg (N.cast_nonneg)] at hN
      have := log_succ_le_log_add_one hN1
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      nlinarith
    filter_upwards [hlogN, eventually_ge_atTop 4] with N hN hN4
    rw [← Finset.Ico_add_one_right_eq_Icc, ← sum_Ico_consecutive _ (by norm_num : 1 ≤ 4)
      (by omega : 4 ≤ N + 1)]
    have e1 : ∑ n ∈ Ico 1 4, (if 4 ≤ n then (-1) ^ n * (h n * 1) * (1 / 2) else 0 : ℝ) = 0 :=
      sum_eq_zero fun n hn => by rw [if_neg (by have := (mem_Ico.1 hn).2; omega)]
    have e2 : ∑ n ∈ Ico 4 (N + 1), (if 4 ≤ n then (-1) ^ n * (h n * 1) * (1 / 2) else 0 : ℝ) =
        1 / 2 * ∑ n ∈ Ico 4 (N + 1), (-1) ^ n * h n * 1 := by
      rw [mul_sum]
      exact sum_congr rfl fun n hn => by rw [if_pos (mem_Ico.1 hn).1]; ring
    rw [e1, zero_add, e2]
    have hw : ∀ n : ℕ, 4 ≤ n → (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 := fun _ _ => ⟨zero_le_one, le_rfl⟩
    have hh : ∀ n, |h n| ≤ 1 := fun n => by simp [h]
    have h3 := abs_alt_le (w := fun _ => (1 : ℝ)) hw hh (by omega : 4 ≤ N + 1)
    have h4 : (changes h 4 (N + 1) : ℝ) ≤ 2 * Real.log (N + 1) := by
      have h5 := changes_comp (fun k : ℕ => (-1 : ℝ) ^ k) (fun n => Nat.log 2 n) 4 (N + 1)
      have h6 := changes_le_of_monotone_nat (u := fun n => Nat.log 2 n)
        (fun x y hxy => Nat.log_mono_right hxy) (by omega : 4 ≤ N + 1)
      have h7 : (Nat.log 2 (N + 1) : ℝ) ≤ 2 * Real.log (N + 1) := by
        have h7 : 2 ^ Nat.log 2 (N + 1) ≤ N + 1 := Nat.pow_log_le_self 2 (by omega)
        have h8 : (Nat.log 2 (N + 1) : ℝ) * Real.log 2 ≤ Real.log (N + 1) := by
          have := Real.log_le_log (by positivity)
            (show ((2 : ℕ) ^ Nat.log 2 (N + 1) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by exact_mod_cast h7)
          simpa [Real.log_pow] using this
        have := Real.log_two_gt_d9
        have : (0 : ℝ) ≤ Nat.log 2 (N + 1) := Nat.cast_nonneg _
        nlinarith
      have h9 : (changes h 4 (N + 1) : ℝ) ≤ (Nat.log 2 (N + 1) : ℝ) := by
        have : changes h 4 (N + 1) ≤ Nat.log 2 (N + 1) := h5.trans (h6.trans (Nat.sub_le _ _))
        exact_mod_cast this
      linarith
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h5 : (0 : ℝ) ≤ Real.log (N + 1) := Real.log_nonneg (by linarith [N.cast_nonneg (α := ℝ)])
    nlinarith
  -- the main term `(N - 3)/2`
  have hM : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (if 4 ≤ n then (1 : ℝ) / 2 else 0)) / N) atTop
      (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun N : ℕ => 1 / 2 - 3 / 2 * (1 / (N : ℝ))) atTop (𝓝 (1 / 2 - 3 / 2 * 0)) :=
      tendsto_const_nhds.sub ((tendsto_const_div_atTop_nhds_zero_nat 1).const_mul _)
    rw [mul_zero, sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 4] with N hN
    rw [← Finset.Ico_add_one_right_eq_Icc, ← sum_Ico_consecutive _ (by norm_num : 1 ≤ 4)
      (by omega : 4 ≤ N + 1)]
    have e1 : ∑ n ∈ Ico 1 4, (if 4 ≤ n then (1 : ℝ) / 2 else 0) = 0 :=
      sum_eq_zero fun n hn => by rw [if_neg (by have := (mem_Ico.1 hn).2; omega)]
    have e2 : ∑ n ∈ Ico 4 (N + 1), (if 4 ≤ n then (1 : ℝ) / 2 else 0) = (N - 3) / 2 := by
      rw [sum_congr rfl fun n hn => if_pos (mem_Ico.1 hn).1, sum_const, Nat.card_Ico,
        nsmul_eq_mul]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1, e2, zero_add]
    have : (N : ℝ) ≠ 0 := by have : (4 : ℝ) ≤ N := by exact_mod_cast hN
                             linarith
    field_simp
  have := (hM.add hA).sub hE
  rw [add_zero, sub_zero] at this
  unfold HasNatDensity
  refine this.congr fun N => ?_
  rw [← add_div, ← sub_div]
  congr 1
  rw [← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [Q_indicator (fun _ => (1 : ℝ)) n]
  simp only [h]
  ring

end NatDensity

/-- Paper, Proposition \ref{IA:prop:KR} (set of Kousek–Radić): `A_KR` has natural density `1/2`,
contains no `B + B + t` (for every `t ∈ ℤ` and every infinite `B ⊆ ℕ`), has logarithmic density
`1/2`, and satisfies `(21)`. -/
theorem prop_KR :
    HasNatDensity AKR (1 / 2) ∧ (∀ t : ℤ, ∀ B : Set ℕ, B.Infinite → ¬ SumsetIn B t AKR) ∧
    HasLogDensity AKR (1 / 2) ∧
    ∀ θ : ℝ, 0 < θ → ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      HasLogDensity {n ∈ AKR | Int.fract (θ * Real.log n) ∈ Set.Ioo a b} (1 / 2 * (b - a)) :=
  ⟨AKR_natDensity, fun t _ hB => AKR_no_BBt t hB, AKR_logDensity,
    fun _ hθ _ _ ha hab hb => AKR_eq21 hθ ha hab hb⟩

end Kmrr25.Q324
