import Kmrr25.Q413

/-!
# Theorem \ref{IB:thm:413}\ref{IB:413a}: thickness of `A_x` for non-integer `γ` (partial)

Paper, Section \ref{IB:sec:q413}, proof of Theorem \ref{IB:thm:413}\ref{IB:413a}. Here
`A_x = {n ∈ ℕ : {n^γ x} ≤ 1 / log n}` is `Kmrr25.Q413.Ax γ x`, and thickness is
`Kmrr25.Q413.Thick`.

## What is formalized

* `taylor_rpow` — the Taylor expansion \eqref{IB:eq:taylor} of `(n + h)^γ` with Lagrange
  remainder, with `c_j(n) = binom(γ, j) n^{γ - j}` (`cj`, `gbinom`).
* `lem_En` — Lemma \ref{IB:lem:En}, in full: for `N ≥ N₀`, `N ≤ n < 2N`, `x ∈ E_n` and
  `|x| ≤ X₀`, the block `{n, …, n + L - 1}` lies in `A_x`. The sets `E_n` (`En`) and the
  parameters `η = 1/log(4N)`, `ρ = η / (16 (k + 1) L^k)` (`eta`, `rho`) are those of the paper.
* `thm413a_of_secondMoment`, `thm413a_sumset_of_secondMoment` — Theorem
  \ref{IB:thm:413}\ref{IB:413a} (`A_x` thick for almost every `x`, hence `A_x ⊇ B + C` with
  `B, C` infinite) **conditional on** `SecondMomentBound γ`, i.e. the final paragraph of the
  proof: the passage from the second-moment estimate to the almost-everywhere statement
  (the `limsup` of the events, Lemma \ref{IB:lem:En}, intersection over `L` and `X₀`, and
  Lemma \ref{IB:lem:thick}).

## What is not formalized

The second-moment estimate itself, stated here as the `Prop` `SecondMomentBound γ`: for every
`L ≥ 1` and `X₀ > 0`, the measure of the set of `x ∈ [-X₀, X₀]` lying in no `E_n`,
`2^r ≤ n < 2^{r+1}`, tends to `0`. In the paper this is the computation with the smooth windows
`φ_{α,w}`, the functions `F_n`, `Z_N`, the Fourier bounds \eqref{IB:eq:window} and
\eqref{IB:eq:tail}, Lemma \ref{IB:lem:freq}, Lemma \ref{IB:lem:bad}, the first and second
moments and Chebyshev's inequality; none of this is formalized. `SecondMomentBound` is an
intermediate claim of the paper's own proof (not a cited theorem); it is not an axiom, and the
results of this file that depend on it take it as an explicit hypothesis. Consequently the final
"if and only if" of Theorem \ref{IB:thm:413} is also not formalized.

## Conventions

* `γ ∉ ℤ` is `∀ m : ℤ, γ ≠ m`; `k = ⌊γ⌋₊`. "Almost every `x ∈ ℝ`" refers to Lebesgue measure
  (`volume`). `‖t‖` (distance to `ℤ`) is `|t - round t|`.
* `N` ranges over `ℕ` in `lem_En` (the paper only needs powers of `2`).
-/

open Real Finset Filter Topology MeasureTheory

noncomputable section

namespace Kmrr25.Q413a

open Kmrr25.Q413

/-- The generalized binomial coefficient `binom(γ, j) = γ (γ - 1) ⋯ (γ - j + 1) / j!`. -/
def gbinom (γ : ℝ) (j : ℕ) : ℝ := (descPochhammer ℝ j).eval γ / (j.factorial : ℝ)

/-- `c_j(n) = binom(γ, j) n^{γ - j}`. -/
def cj (γ : ℝ) (j : ℕ) (n : ℝ) : ℝ := gbinom γ j * n ^ (γ - j)

/-- Taylor's formula with Lagrange remainder for `t ↦ t^γ` (paper, \eqref{IB:eq:taylor}):
for `n > 0`, `h ≥ 0` there is `ξ ∈ [n, n + h]` with
`(n + h)^γ = ∑_{j ≤ k} c_j(n) h^j + binom(γ, k + 1) ξ^{γ - k - 1} h^{k + 1}`. -/
lemma taylor_rpow (γ : ℝ) (k : ℕ) {n h : ℝ} (hn : 0 < n) (hh : 0 ≤ h) :
    ∃ ξ ∈ Set.Icc n (n + h), (n + h) ^ γ =
      ∑ j ∈ range (k + 1), cj γ j n * h ^ j + gbinom γ (k + 1) * ξ ^ (γ - (k + 1 : ℕ)) *
        h ^ (k + 1) := by
  rcases hh.eq_or_lt with rfl | hh
  · refine ⟨n, ⟨le_rfl, by simp⟩, ?_⟩
    rw [sum_range_succ', sum_eq_zero fun j _ => by simp]
    simp [cj, gbinom]
  set f : ℝ → ℝ := fun x => x ^ γ with hf
  have hne : n ≠ n + h := by linarith
  have hsub : Set.uIcc n (n + h) ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le (by linarith)]
    exact fun x hx => lt_of_lt_of_le hn hx.1
  have hcd : ContDiffOn ℝ (k + 1 : ℕ) f (Set.uIcc n (n + h)) := fun x hx =>
    (contDiffAt_rpow_const_of_ne (ne_of_gt (hsub hx))).contDiffWithinAt
  obtain ⟨ξ, hξ, hT⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne (by exact_mod_cast hcd)
  rw [Set.uIoo_of_le (by linarith)] at hξ
  refine ⟨ξ, ⟨hξ.1.le, hξ.2.le⟩, ?_⟩
  have hu : UniqueDiffOn ℝ (Set.uIcc n (n + h)) := uniqueDiffOn_uIcc hne
  have hmem : n ∈ Set.uIcc n (n + h) := Set.left_mem_uIcc
  rw [taylor_within_apply] at hT
  have hterm : ∀ j ∈ range (k + 1), ((j.factorial : ℝ)⁻¹ * (n + h - n) ^ j) •
      iteratedDerivWithin j f (Set.uIcc n (n + h)) n = cj γ j n * h ^ j := by
    intro j _
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      (contDiffAt_rpow_const_of_ne (ne_of_gt hn)) hmem, iteratedDeriv_eq_iterate,
      iter_deriv_rpow_const, smul_eq_mul, cj, gbinom]
    ring_nf
  rw [sum_congr rfl hterm, iteratedDeriv_eq_iterate, iter_deriv_rpow_const] at hT
  rw [gbinom]
  have : (n + h - n) = h := by ring
  rw [this] at hT
  push_cast at hT ⊢
  field_simp at hT ⊢
  linarith

/-! ## The sets `E_n` and Lemma \ref{IB:lem:En} -/

/-- `η_N = 1 / log(4N)`. -/
def eta (N : ℕ) : ℝ := 1 / Real.log (4 * N)

/-- `ρ_N = η_N / (16 (k + 1) L^k)` with `k = ⌊γ⌋`. -/
def rho (γ : ℝ) (L N : ℕ) : ℝ := eta N / (16 * ((⌊γ⌋₊ : ℝ) + 1) * (L : ℝ) ^ ⌊γ⌋₊)

/-- The set `E_n` (for `N ≤ n < 2N`): the `x ∈ ℝ` with `{c_0(n) x} ∈ [η/4, η/2]` and
`‖c_j(n) x‖ ≤ ρ` for `1 ≤ j ≤ k = ⌊γ⌋`, where `‖t‖ = |t - round t|` is the distance to `ℤ`. -/
def En (γ : ℝ) (L N n : ℕ) : Set ℝ :=
  {x | Int.fract (cj γ 0 n * x) ∈ Set.Icc (eta N / 4) (eta N / 2) ∧
    ∀ j, 1 ≤ j → j ≤ ⌊γ⌋₊ → |cj γ j n * x - round (cj γ j n * x)| ≤ rho γ L N}

lemma tendsto_rpow_mul_log {s : ℝ} (hs : s < 0) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ s * Real.log (4 * N)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℝ => N ^ s) atTop (𝓝 0) := by
    simpa using tendsto_rpow_neg_atTop (y := -s) (by linarith)
  have h2 : Tendsto (fun N : ℝ => Real.log N / N ^ (-s)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by linarith : 0 < -s)).tendsto_div_nhds_zero
  have h3 : Tendsto (fun N : ℝ => N ^ s * Real.log 4 + Real.log N / N ^ (-s)) atTop (𝓝 0) := by
    simpa using (h1.mul_const (Real.log 4)).add h2
  have h4 : Tendsto (fun N : ℝ => N ^ s * Real.log (4 * N)) atTop (𝓝 0) := by
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.log_mul (by norm_num) hN.ne', Real.rpow_neg hN.le, div_eq_mul_inv, inv_inv]
    ring
  exact h4.comp tendsto_natCast_atTop_atTop

lemma eta_pos {N : ℕ} (hN : 1 ≤ N) : 0 < eta N := by
  unfold eta
  have : (1 : ℝ) < 4 * N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  exact one_div_pos.2 (Real.log_pos this)

lemma eta_lt_one {N : ℕ} (hN : 1 ≤ N) : eta N < 1 := by
  unfold eta
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h4 : (4 : ℝ) ≤ 4 * N := by linarith
  have hl : 1 < Real.log (4 * N) := by
    have : Real.log 4 ≤ Real.log (4 * N) := Real.log_le_log (by norm_num) h4
    have h4e : 1 < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    linarith
  rw [div_lt_one (by linarith)]
  exact hl

/-- Paper, Lemma \ref{IB:lem:En}. Let `γ > 0`, `γ ∉ ℤ`, `L ≥ 1` and `X₀ ∈ ℝ`. There is `N₀`
such that for `N ≥ N₀`, `N ≤ n < 2N` and `x ∈ E_n` with `|x| ≤ X₀` we have
`{n, n + 1, …, n + L - 1} ⊆ A_x`. -/
theorem lem_En (γ : ℝ) (hγ : 0 < γ) (hγZ : ∀ m : ℤ, γ ≠ m) (L : ℕ) (hL : 1 ≤ L) (X₀ : ℝ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n : ℕ, N ≤ n → n < 2 * N → ∀ x ∈ En γ L N n, |x| ≤ X₀ →
      ∀ h < L, n + h ∈ Ax γ x := by
  set k := ⌊γ⌋₊ with hk
  have hkγ : (k : ℝ) ≤ γ := Nat.floor_le hγ.le
  have hγk : γ < k + 1 := Nat.lt_floor_add_one γ
  have hkne : (k : ℝ) ≠ γ := fun h => hγZ k (by rw [← h]; norm_cast)
  set ς := γ - k with hς
  have hς1 : ς - 1 < 0 := by rw [hς]; linarith
  set gb := gbinom γ (k + 1)
  set K₁ : ℝ := (|X₀| + 1) * |gb| * (L : ℝ) ^ (k + 1) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hev := (tendsto_rpow_mul_log hς1).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (16 * (K₁ + 1)) by positivity))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  refine ⟨max N₁ (max L 2), fun N hN n hNn hn2N x hx hxX h hh => ?_⟩
  have hN1 : N₁ ≤ N := le_of_max_le_left hN
  have hNL : L ≤ N := (le_max_left _ _).trans (le_of_max_le_right hN)
  have hN2 : 2 ≤ N := (le_max_right _ _).trans (le_of_max_le_right hN)
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hnr : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hnpos : (0 : ℝ) < n := by linarith
  set η := eta N with hη
  have hη0 : 0 < η := eta_pos (by omega)
  have hη1 : η < 1 := eta_lt_one (by omega)
  have hlog : 0 < Real.log (4 * N) := Real.log_pos (by linarith)
  have hηlog : η * Real.log (4 * N) = 1 := by
    rw [hη, eta]; field_simp
  -- Taylor expansion
  obtain ⟨ξ, hξ, hT⟩ := taylor_rpow γ k hnpos (Nat.cast_nonneg h : (0 : ℝ) ≤ h)
  set R := gb * ξ ^ (γ - (k + 1 : ℕ)) * (h : ℝ) ^ (k + 1) with hR
  have hhL : (h : ℝ) ≤ L := by exact_mod_cast hh.le
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  -- bound on the remainder
  have hRb : |R * x| ≤ η / 16 := by
    have hexp : γ - ((k + 1 : ℕ) : ℝ) = ς - 1 := by rw [hς]; push_cast; ring
    have hξpos : 0 < ξ := lt_of_lt_of_le hnpos hξ.1
    have h1 : ξ ^ (ς - 1) ≤ (N : ℝ) ^ (ς - 1) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (hnr.trans hξ.1) hς1.le
    have h2 : (h : ℝ) ^ (k + 1) ≤ (L : ℝ) ^ (k + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hhL _
    have h3 := hN₁ N hN1
    have hNs : 0 ≤ (N : ℝ) ^ (ς - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h4 : K₁ * (N : ℝ) ^ (ς - 1) ≤ η / 16 := by
      have : (N : ℝ) ^ (ς - 1) * Real.log (4 * N) * (16 * (K₁ + 1)) < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at h3
      have h5 : K₁ * (N : ℝ) ^ (ς - 1) * (16 * Real.log (4 * N)) ≤ 1 := by
        nlinarith [mul_nonneg hNs hlog.le]
      have : η / 16 = 1 / (16 * Real.log (4 * N)) := by rw [hη, eta]; field_simp
      rw [this, le_div_iff₀ (by positivity)]
      exact h5
    rw [hR, hexp, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hξpos.le (ς - 1)),
      abs_of_nonneg (pow_nonneg (Nat.cast_nonneg h : (0 : ℝ) ≤ h) (k + 1))]
    calc |gb| * ξ ^ (ς - 1) * (h : ℝ) ^ (k + 1) * |x|
        ≤ |gb| * (N : ℝ) ^ (ς - 1) * (L : ℝ) ^ (k + 1) * (|X₀| + 1) := by
          gcongr
          · exact hxX.trans ((le_abs_self X₀).trans (by linarith))
      _ = K₁ * (N : ℝ) ^ (ς - 1) := by rw [hK₁]; ring
      _ ≤ η / 16 := h4
  -- the small terms `θ_j h^j`, `1 ≤ j ≤ k`
  set a : ℕ → ℝ := fun j => cj γ (j + 1) n * x with ha
  have hθb : |∑ j ∈ range k, (a j - round (a j)) * (h : ℝ) ^ (j + 1)| ≤ η / 16 := by
    have hρ : rho γ L N * (k : ℝ) * (L : ℝ) ^ k ≤ η / 16 := by
      rw [rho, ← hk, ← hη]
      have hLk : 0 < (L : ℝ) ^ k := by positivity
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (k : ℝ) ≤ k + 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hη0.le hLk.le)]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ range k, |(a j - round (a j)) * (h : ℝ) ^ (j + 1)|
        ≤ ∑ j ∈ range k, rho γ L N * (L : ℝ) ^ k := by
          refine sum_le_sum fun j hj => ?_
          rw [mem_range] at hj
          rw [abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg h : (0 : ℝ) ≤ h) (j + 1))]
          refine mul_le_mul (hx.2 (j + 1) (by omega) (by omega)) ?_ (by positivity)
            ((abs_nonneg _).trans (hx.2 (j + 1) (by omega) (by omega)))
          exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hhL _).trans
            (pow_le_pow_right₀ hL1 (by omega))
      _ = rho γ L N * (k : ℝ) * (L : ℝ) ^ k := by rw [sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ η / 16 := hρ
  -- the decomposition `(n + h)^γ x = M + θ₀ + δ`
  set θ₀ := Int.fract (cj γ 0 n * x)
  set δ := ∑ j ∈ range k, (a j - round (a j)) * (h : ℝ) ^ (j + 1) + R * x with hδ
  set M : ℤ := ⌊cj γ 0 n * x⌋ + ∑ j ∈ range k, round (a j) * (h : ℤ) ^ (j + 1) with hM
  have hdec : ((n : ℝ) + h) ^ γ * x = M + (θ₀ + δ) := by
    rw [hT, sum_range_succ']
    have e1 : ∑ j ∈ range k, a j * (h : ℝ) ^ (j + 1) =
        ∑ j ∈ range k, (round (a j) : ℝ) * (h : ℝ) ^ (j + 1) +
          ∑ j ∈ range k, (a j - round (a j)) * (h : ℝ) ^ (j + 1) := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
    have e2 : (∑ j ∈ range k, cj γ (j + 1) n * (h : ℝ) ^ (j + 1) + cj γ 0 n * (h : ℝ) ^ 0 + R) * x
        = cj γ 0 n * x + ∑ j ∈ range k, a j * (h : ℝ) ^ (j + 1) + R * x := by
      simp only [ha, pow_zero, mul_one]
      rw [add_mul, add_mul, sum_mul]
      have : ∀ j ∈ range k, cj γ (j + 1) n * (h : ℝ) ^ (j + 1) * x =
          cj γ (j + 1) n * x * (h : ℝ) ^ (j + 1) := fun j _ => by ring
      rw [sum_congr rfl this]
      ring
    rw [e2, e1, hδ, hM]
    have := Int.floor_add_fract (cj γ 0 n * x)
    push_cast
    linarith
  have hθ₀ := hx.1
  have hδb : |δ| ≤ η / 8 := by
    rw [hδ]
    refine (abs_add_le _ _).trans ?_
    linarith
  have hlo : η / 8 ≤ θ₀ + δ := by
    have := neg_abs_le δ; linarith [hθ₀.1]
  have hhi : θ₀ + δ ≤ 5 * η / 8 := by
    have := le_abs_self δ; linarith [hθ₀.2]
  have hfr : Int.fract (((n : ℝ) + h) ^ γ * x) = θ₀ + δ := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, M, ?_⟩
    rw [hdec]; ring
  -- conclusion
  refine ⟨by omega, fun h2 => ?_⟩
  push_cast
  rw [hfr]
  have hnh2 : (2 : ℝ) ≤ (n : ℝ) + h := by
    have : (2 : ℝ) ≤ n := hNr.trans hnr
    linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
  have hnh4 : (n : ℝ) + h ≤ 4 * N := by
    have h1 : (n : ℝ) + 1 ≤ 2 * N := by exact_mod_cast hn2N
    have h2 : (L : ℝ) ≤ N := by exact_mod_cast hNL
    linarith
  have hlognh : 0 < Real.log ((n : ℝ) + h) := Real.log_pos (by linarith)
  have hle : η ≤ 1 / Real.log ((n : ℝ) + h) := by
    rw [hη, eta]
    exact one_div_le_one_div_of_le hlognh (Real.log_le_log (by linarith) hnh4)
  linarith

/-! ## From the second-moment estimate to Theorem \ref{IB:thm:413}\ref{IB:413a} -/

/-- The set of `x ∈ [-X₀, X₀]` lying in no `E_n` with `2^r ≤ n < 2^{r+1}` (with `N = 2^r`),
i.e. (up to the comparison `0 ≤ F_n ≤ 1_{E_n}`) the event `Z_N = 0` of the paper. -/
def badSet (γ : ℝ) (L : ℕ) (X₀ : ℝ) (r : ℕ) : Set ℝ :=
  {x | x ∈ Set.Icc (-X₀) X₀ ∧ ∀ n : ℕ, 2 ^ r ≤ n → n < 2 ^ (r + 1) → x ∉ En γ L (2 ^ r) n}

/-- The **second-moment estimate** of the paper's proof of Theorem \ref{IB:thm:413}\ref{IB:413a},
in the form in which it is used: for every `L ≥ 1` and `X₀ > 0`, the Lebesgue measure of the set
of `x ∈ [-X₀, X₀]` lying in no `E_n`, `2^r ≤ n < 2^{r+1}`, tends to `0` as `r → ∞`.

In the paper this is the outcome of the first- and second-moment computation for
`Z_N = ∑_{N ≤ n < 2N} F_n` (Fourier expansion of the smooth windows, \eqref{IB:eq:window},
\eqref{IB:eq:tail}, Lemmas \ref{IB:lem:freq} and \ref{IB:lem:bad}, and Chebyshev's inequality,
giving `P_ψ(Z_N = 0) → 0`; since `F_n > 0` forces `x ∈ E_n`, applying this with `X₀ + 1` and
`ψ = 1` on `[-X₀, X₀]` gives the statement here). That computation is **not** formalized; this
`Prop` is a hypothesis of `thm413a_of_secondMoment` below. -/
def SecondMomentBound (γ : ℝ) : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ X₀ : ℝ, 0 < X₀ → Tendsto (fun r => volume (badSet γ L X₀ r)) atTop (𝓝 0)

/-- For fixed `L` and `X₀`: almost every `x ∈ [-X₀, X₀]` has `{n, …, n + L - 1} ⊆ A_x` for some
`n` (paper, last paragraph of the proof of Theorem \ref{IB:thm:413}\ref{IB:413a}). -/
lemma ae_block (γ : ℝ) (hγ : 0 < γ) (hγZ : ∀ m : ℤ, γ ≠ m) (hSM : SecondMomentBound γ)
    (L : ℕ) (hL : 1 ≤ L) (X₀ : ℝ) (hX₀ : 0 < X₀) :
    ∀ᵐ x : ℝ, x ∈ Set.Icc (-X₀) X₀ → ∃ n, ∀ h < L, n + h ∈ Ax γ x := by
  -- `limsup` of the good events: the set of `x` eventually bad has measure zero
  set S : Set ℝ := ⋃ R : ℕ, ⋂ r ∈ Set.Ici R, badSet γ L X₀ r with hS
  have hS0 : volume S = 0 := by
    refine measure_iUnion_null fun R => ?_
    refine le_antisymm (ge_of_tendsto (hSM L hL X₀ hX₀) ?_) zero_le
    filter_upwards [eventually_ge_atTop R] with r hr
    exact measure_mono (Set.biInter_subset_of_mem (Set.mem_Ici.2 hr))
  obtain ⟨N₀, hN₀⟩ := lem_En γ hγ hγZ L hL X₀
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS0] with x hxS hxI
  -- `x` is not eventually bad, so it is good for some `r` with `2^r ≥ N₀`
  have hfreq : ∃ᶠ r in atTop, x ∉ badSet γ L X₀ r := by
    rw [Filter.frequently_atTop]
    intro R
    by_contra hcon
    push Not at hcon
    exact hxS (Set.mem_iUnion.2 ⟨R, Set.mem_iInter₂.2 fun r hr => hcon r hr⟩)
  obtain ⟨r, hr, hrN⟩ := (hfreq.and_eventually (eventually_ge_atTop N₀)).exists
  have hN : N₀ ≤ 2 ^ r := hrN.trans (Nat.lt_two_pow_self).le
  have : ∃ n : ℕ, 2 ^ r ≤ n ∧ n < 2 ^ (r + 1) ∧ x ∈ En γ L (2 ^ r) n := by
    by_contra hcon
    push Not at hcon
    exact hr ⟨hxI, fun n h1 h2 hx => (hcon n h1 h2) hx⟩
  obtain ⟨n, hn1, hn2, hxE⟩ := this
  refine ⟨n, hN₀ (2 ^ r) hN n hn1 (by rw [pow_succ] at hn2; omega) x hxE ?_⟩
  exact abs_le.2 hxI

/-- Paper, Theorem \ref{IB:thm:413}\ref{IB:413a}, **conditional on the second-moment estimate**
`SecondMomentBound γ`: if `γ > 0` is not an integer, then for almost every `x ∈ ℝ` the set
`A_x` is thick. -/
theorem thm413a_of_secondMoment (γ : ℝ) (hγ : 0 < γ) (hγZ : ∀ m : ℤ, γ ≠ m)
    (hSM : SecondMomentBound γ) : ∀ᵐ x : ℝ, Thick (Ax γ x) := by
  have h : ∀ᵐ x : ℝ, ∀ L : ℕ, ∀ X : ℕ, x ∈ Set.Icc (-((X : ℝ) + 1)) ((X : ℝ) + 1) →
      ∃ n, ∀ h < L + 1, n + h ∈ Ax γ x := by
    rw [ae_all_iff]; intro L
    rw [ae_all_iff]; intro X
    exact ae_block γ hγ hγZ hSM (L + 1) (by omega) _ (by positivity)
  filter_upwards [h] with x hx
  intro L
  have hxI : x ∈ Set.Icc (-((⌈|x|⌉₊ : ℝ) + 1)) ((⌈|x|⌉₊ : ℝ) + 1) := by
    have := Nat.le_ceil |x|
    exact abs_le.1 (by linarith)
  obtain ⟨n, hn⟩ := hx L _ hxI
  exact ⟨n, fun h hh => hn h (by omega)⟩

/-- Paper, Theorem \ref{IB:thm:413}\ref{IB:413a}, second clause, **conditional on the
second-moment estimate**: for non-integer `γ > 0` and almost every `x`, `A_x` contains `B + C`
for some infinite `B, C ⊆ ℕ` (via Lemma \ref{IB:lem:thick}, `Kmrr25.Q413.lem_thick`). -/
theorem thm413a_sumset_of_secondMoment (γ : ℝ) (hγ : 0 < γ) (hγZ : ∀ m : ℤ, γ ≠ m)
    (hSM : SecondMomentBound γ) :
    ∀ᵐ x : ℝ, ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ Ax γ x := by
  filter_upwards [thm413a_of_secondMoment γ hγ hγZ hSM] with x hx
  exact lem_thick hx

end Kmrr25.Q413a
