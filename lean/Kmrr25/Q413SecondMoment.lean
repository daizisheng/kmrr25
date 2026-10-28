import Kmrr25.Q413a

/-!
# The second-moment estimate for Theorem \ref{IB:thm:413}\ref{IB:413a}

Paper, Section \ref{IB:sec:q413}, proof of Theorem \ref{IB:thm:413}\ref{IB:413a}. We prove the
`Prop` `Kmrr25.Q413a.SecondMomentBound γ` (exactly as stated in `Kmrr25.Q413a`) for every
non-integer `γ > 0`. Combined with `Kmrr25.Q413a.thm413a_of_secondMoment` and with part (b)
(`Kmrr25.Q413.thm413b_sumset`) this gives Theorem \ref{IB:thm:413} in full.

## Main results

* `secondMomentBound` — for `γ > 0`, `γ ∉ ℤ`: `SecondMomentBound γ`, i.e. for every `L ≥ 1`
  and `X₀ > 0` the measure of the set of `x ∈ [-X₀, X₀]` lying in no `E_n`,
  `2^r ≤ n < 2^{r+1}`, tends to `0` as `r → ∞`.
* `thm413a`, `thm413a_sumset` — Theorem \ref{IB:thm:413}\ref{IB:413a}, unconditionally: for
  `γ > 0`, `γ ∉ ℤ`, the set `A_x` is thick for almost every `x`, hence contains `B + C` with
  `B, C ⊆ ℕ` infinite.
* `thm413_iff` — the final statement of Theorem \ref{IB:thm:413}: for `γ > 0`, `A_x` contains
  `B + C` with `B, C` infinite for almost every `x` if and only if `γ ∉ ℕ`.

## Method (differences from the paper)

The paper uses smooth windows `φ_{α,w}` with rapidly decaying Fourier coefficients, the
minorant `F_n ≤ 1_{E_n}`, a smooth cut-off `ψ` and Chebyshev's inequality. We use instead the
same second-moment method with finite trigonometric polynomials, so that no Fourier series or
Fourier transforms are needed:

1. The Fejér kernel `K_Q(t) = |∑_{m < Q} e(m t)|² / Q` (`fejer`): `0 ≤ K_Q ≤ Q`, `K_1 = 1`, and
   `K_Q(t) ≤ 1 / (4 Q w²)` if `t` has distance `≥ w` from `ℤ` (`fejer_out`).
2. `trig_integral`: if `|∑_i d_i λ_i| ≥ T` for every non-zero integer vector `d` with
   `|d_i| < Q_i`, then `∫_{-X}^{X} ∏_i K_{Q_i}(λ_i x - α_i) dx = 2X + O(∏ Q_i / (π T))`
   (the cut-off is the indicator of `[-X₀, X₀]`; its Fourier transform decays like `1/|ξ|`,
   which suffices).
3. `freq` (Lemma \ref{IB:lem:freq}), `dfreq` and `count_close` (the mean value theorem argument
   of Lemma \ref{IB:lem:bad}), and `bad_count` (Lemma \ref{IB:lem:bad}).
4. `F_n(x) = ∏_{j ≤ k} K_Q(c_j(n) x - α_j)` (`Fn`), with `α_0 = 3η/8`, `α_j = 0`. Here
   `F_n` is not a minorant of `1_{E_n}`; instead, outside `E_n` it is bounded by
   `U_n = ∑_{j₀} (4 Q ρ²)⁻¹ ∏_{j ≠ j₀} K_Q(c_j(n) x - α_j)` (`Fn_le_Un`), whose integral is
   small. With `G = ∑_{N ≤ n < 2N} F_n` one gets `∫ (G - N)² = o(N²)` (first and second moments,
   good and bad pairs) and `∫ ∑_n U_n = o(N)`; on the bad set `G ≤ ∑_n U_n`, so Markov's
   inequality applied to `(G - N)²/N² + ∑_n U_n / N` bounds its measure (`bad_measure_le`).
5. Parameters: `u = N^θ` with `θ = ς / (32 (k + 1))`, `Q = ⌊u⁴⌋`, `T = u^{16(k+1)}`,
   `T₁ = (b/2) u^{32(k+1)} = (b/2) N^ς`; the measure of the bad set is `O(u⁻²)`.

## Conventions

As in `Kmrr25.Q413a`: `γ ∉ ℤ` is `∀ m : ℤ, γ ≠ m`, `k = ⌊γ⌋₊`, `ς = γ - k`, "almost every"
refers to Lebesgue measure, `e(t) = exp(2 π i t)` (`ee`).
-/

open Real Finset Filter Topology MeasureTheory ComplexConjugate

noncomputable section

namespace Kmrr25.Q413SM

open Kmrr25.Q413 Kmrr25.Q413a

/-! ## The Fejér kernel -/

/-- `e(t) = exp(2 π i t)`. -/
def ee (t : ℝ) : ℂ := Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I)

lemma norm_ee (t : ℝ) : ‖ee t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma ee_add (a b : ℝ) : ee (a + b) = ee a * ee b := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_int (m : ℤ) : ee m = 1 := by
  unfold ee
  have : (((2 * π * m : ℝ) : ℂ) * Complex.I) = m * (2 * π * Complex.I) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma ee_nat_mul (m : ℕ) (t : ℝ) : ee (m * t) = ee t ^ m := by
  unfold ee; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma conj_ee (t : ℝ) : conj (ee t) = ee (-t) := by
  unfold ee; rw [← Complex.exp_conj]; congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

lemma ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  unfold ee; rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.mul_sum, Finset.sum_mul]

lemma continuous_ee : Continuous ee := by unfold ee; fun_prop

/-- The Dirichlet-type sum `D_Q(t) = ∑_{m < Q} e(m t)`. -/
def dirichlet (Q : ℕ) (t : ℝ) : ℂ := ∑ m ∈ range Q, ee (m * t)

/-- The Fejér kernel `K_Q(t) = |D_Q(t)|² / Q`. -/
def fejer (Q : ℕ) (t : ℝ) : ℝ := ‖dirichlet Q t‖ ^ 2 / Q

lemma fejer_nonneg (Q : ℕ) (t : ℝ) : 0 ≤ fejer Q t := by unfold fejer; positivity

lemma continuous_fejer (Q : ℕ) : Continuous (fejer Q) := by
  unfold fejer dirichlet
  have := continuous_ee
  fun_prop

lemma norm_dirichlet_le (Q : ℕ) (t : ℝ) : ‖dirichlet Q t‖ ≤ Q := by
  unfold dirichlet
  refine (norm_sum_le _ _).trans ?_
  simp [norm_ee]

lemma fejer_le {Q : ℕ} (hQ : 1 ≤ Q) (t : ℝ) : fejer Q t ≤ Q := by
  unfold fejer
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [div_le_iff₀ hQ']
  have := norm_dirichlet_le Q t
  nlinarith [norm_nonneg (dirichlet Q t)]

lemma fejer_one (t : ℝ) : fejer 1 t = 1 := by
  simp [fejer, dirichlet, ee_zero]

lemma fejer_expand (Q : ℕ) (t : ℝ) : (fejer Q t : ℂ) =
    ∑ p ∈ range Q ×ˢ range Q, (1 / (Q : ℂ)) * ee ((((p.1 : ℤ) - p.2 : ℤ) : ℝ) * t) := by
  unfold fejer
  rw [← Finset.mul_sum, Finset.sum_product]
  push_cast
  rw [← Complex.mul_conj', dirichlet, map_sum, Finset.sum_mul_sum, div_eq_inv_mul, one_div]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [conj_ee, ← ee_add]; congr 1; ring

/-- Lower bound `|e(t) - 1| ≥ 4 w` when `t` has distance `≥ w` from `ℤ`. -/
lemma norm_ee_sub_one_ge {t w : ℝ} (h : ∀ m : ℤ, w ≤ |t - m|) :
    4 * w ≤ ‖ee t - 1‖ := by
  set v := t - round t with hv
  have hvt : ee t = ee v := by
    have : t = v + (round t : ℤ) := by simp [hv]
    rw [this, ee_add, ee_int, mul_one]
  have hv2 : |v| ≤ 1 / 2 := abs_sub_round t
  have hvw : w ≤ |v| := h (round t)
  rw [hvt, ee, show (((2 * π * v : ℝ) : ℂ) * Complex.I) = Complex.I * ((2 * π * v : ℝ) : ℂ) from
    mul_comm _ _, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hsin : 2 * |v| ≤ |Real.sin (2 * π * v / 2)| := by
    have e : 2 * π * v / 2 = π * v := by ring
    rw [e]
    rcases le_or_gt 0 v with h0 | h0
    · rw [abs_of_nonneg h0]
      have := Real.mul_le_sin (x := π * v) (by positivity) (by
        have := abs_of_nonneg h0 ▸ hv2; nlinarith [Real.pi_pos])
      have e2 : 2 / π * (π * v) = 2 * v := by field_simp
      rw [e2] at this
      exact this.trans (le_abs_self _)
    · rw [abs_of_neg h0]
      have := Real.mul_le_sin (x := π * (-v)) (by nlinarith [Real.pi_pos]) (by
        have := abs_of_neg h0 ▸ hv2; nlinarith [Real.pi_pos])
      have e2 : 2 / π * (π * -v) = 2 * -v := by field_simp
      rw [e2, mul_neg (π), Real.sin_neg] at this
      linarith [neg_le_abs (Real.sin (π * v))]
  rw [abs_two]
  linarith

lemma fejer_out {Q : ℕ} (hQ : 1 ≤ Q) {t w : ℝ} (hw0 : 0 < w)
    (h : ∀ m : ℤ, w ≤ |t - m|) : fejer Q t ≤ 1 / (4 * Q * w ^ 2) := by
  have h1 : dirichlet Q t * (ee t - 1) = ee t ^ Q - 1 := by
    rw [dirichlet, ← geom_sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun m _ => ee_nat_mul m t
  have h2 : ‖ee t ^ Q - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_ee]; norm_num
  have h3 := norm_ee_sub_one_ge h
  have h4 : ‖dirichlet Q t‖ * (4 * w) ≤ 2 := by
    calc ‖dirichlet Q t‖ * (4 * w) ≤ ‖dirichlet Q t‖ * ‖ee t - 1‖ :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = ‖ee t ^ Q - 1‖ := by rw [← norm_mul, h1]
      _ ≤ 2 := h2
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h5 : ‖dirichlet Q t‖ ≤ 1 / (2 * w) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  unfold fejer
  rw [div_le_div_iff₀ hQ' (by positivity)]
  have h6 : ‖dirichlet Q t‖ ^ 2 ≤ (1 / (2 * w)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h5 2
  have h7 : (1 / (2 * w)) ^ 2 * (4 * w ^ 2) = 1 := by field_simp; ring
  calc ‖dirichlet Q t‖ ^ 2 * (4 * Q * w ^ 2) = (‖dirichlet Q t‖ ^ 2 * (4 * w ^ 2)) * Q := by ring
    _ ≤ ((1 / (2 * w)) ^ 2 * (4 * w ^ 2)) * Q := by gcongr
    _ = 1 * Q := by rw [h7]


/-! ## Integrals of products of Fejér kernels -/

lemma integral_ee_bound {θ : ℝ} (hθ : θ ≠ 0) (X : ℝ) :
    ‖∫ x in (-X)..X, ee (θ * x)‖ ≤ 1 / (π * |θ|) := by
  set c : ℂ := ((2 * π * θ : ℝ) : ℂ) * Complex.I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast (by positivity : (2 * π * θ) ≠ 0)
  have hcn : ‖c‖ = 2 * π * |θ| := by
    rw [hc, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have he : ∀ x : ℝ, ee (θ * x) = Complex.exp (c * x) := fun x => by
    rw [ee, hc]; congr 1; push_cast; ring
  simp_rw [he]
  rw [integral_exp_mul_complex hc0, norm_div, hcn]
  have h1 : ∀ y : ℝ, ‖Complex.exp (c * y)‖ = 1 := fun y => by rw [← he]; exact norm_ee _
  have h2 : ‖Complex.exp (c * ↑X) - Complex.exp (c * ↑(-X))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_; rw [h1, h1]; norm_num
  have hθ' : 0 < |θ| := abs_pos.2 hθ
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ π * |θ|)]

/-- The integer difference `q.1 - q.2`. -/
def dd (q : ℕ × ℕ) : ℤ := (q.1 : ℤ) - q.2

/-- **Trigonometric integral lemma.** If `|∑ d_i λ_i| ≥ T` for every non-zero integer vector `d`
with `|d_i| < Q_i`, then `∫_{-X}^{X} ∏_i K_{Q_i}(λ_i x - α_i) dx` is `2X` up to an error at most
`∏ Q_i / (π T)`. -/
theorem trig_integral {ι : Type*} [Fintype ι] [DecidableEq ι] (lam α : ι → ℝ) (Q : ι → ℕ)
    (hQ : ∀ i, 1 ≤ Q i) (X : ℝ) {T : ℝ} (hT : 0 < T)
    (hsep : ∀ d : ι → ℤ, (∀ i, |d i| < Q i) → d ≠ 0 → T ≤ |∑ i, (d i : ℝ) * lam i|) :
    |(∫ x in (-X)..X, ∏ i, fejer (Q i) (lam i * x - α i)) - 2 * X| ≤
      (∏ i, (Q i : ℝ)) / (π * T) := by
  set S : (i : ι) → Finset (ℕ × ℕ) := fun i => range (Q i) ×ˢ range (Q i) with hS
  set c : ℂ := ∏ i, (1 / (Q i : ℂ)) with hc
  set θ : (ι → ℕ × ℕ) → ℝ := fun P => ∑ i, (dd (P i) : ℝ) * lam i with hθ
  set φ : (ι → ℕ × ℕ) → ℝ := fun P => ∑ i, (dd (P i) : ℝ) * α i with hφ
  set term : (ι → ℕ × ℕ) → ℝ → ℂ := fun P x => c * ee (-φ P) * ee (θ P * x) with hterm
  have hQpos : ∀ i, (0 : ℝ) < Q i := fun i => by exact_mod_cast hQ i
  -- expansion
  have hexp : ∀ x : ℝ, ((∏ i, fejer (Q i) (lam i * x - α i) : ℝ) : ℂ) =
      ∑ P ∈ Fintype.piFinset S, term P x := by
    intro x
    push_cast
    simp_rw [fejer_expand]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finset.prod_mul_distrib, ← ee_sum]
    show _ = c * ee (-φ P) * ee (θ P * x)
    rw [mul_assoc, ← ee_add]
    congr 2
    rw [hφ, hθ, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [dd]; ring
  have hcont : ∀ P, Continuous (term P) := fun P => by
    have := continuous_ee
    rw [hterm]; fun_prop
  have hint : (∫ x in (-X)..X, ((∏ i, fejer (Q i) (lam i * x - α i) : ℝ) : ℂ)) =
      ∑ P ∈ Fintype.piFinset S, ∫ x in (-X)..X, term P x := by
    simp_rw [hexp]
    exact intervalIntegral.integral_finsetSum fun P _ => (hcont P).intervalIntegrable _ _
  -- the diagonal weights
  set δ : (ι → ℕ × ℕ) → ℂ := fun P => ∏ i, (if (P i).1 = (P i).2 then 1 / (Q i : ℂ) else 0)
    with hδ
  have hδsum : ∑ P ∈ Fintype.piFinset S, δ P = 1 := by
    simp only [hδ]
    rw [← Finset.prod_univ_sum (t := S)
      (f := fun i q => if q.1 = q.2 then 1 / (Q i : ℂ) else 0)]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [hS, Finset.sum_product]
    simp only [Finset.sum_ite_eq, Finset.mem_range]
    rw [Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.1 hx)), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (Q i : ℂ) ≠ 0 := by exact_mod_cast (show Q i ≠ 0 by have := hQ i; omega)
    field_simp
  have hcn : ‖c‖ = ∏ i, (1 / (Q i : ℝ)) := by
    rw [hc, norm_prod]; refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_div, norm_one, Complex.norm_natCast]
  -- termwise bound
  have hterm_bd : ∀ P ∈ Fintype.piFinset S,
      ‖(∫ x in (-X)..X, term P x) - (2 * X : ℝ) * δ P‖ ≤ (∏ i, (1 / (Q i : ℝ))) / (π * T) := by
    intro P hP
    rw [Fintype.mem_piFinset] at hP
    by_cases hdiag : ∀ i, (P i).1 = (P i).2
    · have hd0 : ∀ i, (dd (P i) : ℝ) = 0 := fun i => by simp [dd, hdiag i]
      have hθ0 : θ P = 0 := by simp [hθ, hd0]
      have hφ0 : φ P = 0 := by simp [hφ, hd0]
      have hδc : δ P = c := by
        rw [hδ, hc]; exact Finset.prod_congr rfl fun i _ => if_pos (hdiag i)
      have : (fun x => term P x) = fun _ => c := by
        funext x; simp [hterm, hθ0, hφ0, ee_zero]
      rw [this, intervalIntegral.integral_const, hδc]
      simp only [sub_neg_eq_add, Complex.real_smul]
      rw [show (X + X : ℝ) = 2 * X by ring, sub_self, norm_zero]
      positivity
    · push Not at hdiag
      obtain ⟨i₀, hi₀⟩ := hdiag
      have hδ0 : δ P = 0 := Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)
      have hdne : (fun i => dd (P i)) ≠ 0 := fun h => hi₀ (by
        have := congrFun h i₀; simp [dd] at this; omega)
      have hdQ : ∀ i, |dd (P i)| < Q i := fun i => by
        have h1 := (Finset.mem_product.1 (hP i)).1
        have h2 := (Finset.mem_product.1 (hP i)).2
        rw [Finset.mem_range] at h1 h2
        simp only [dd]; rw [abs_lt]; constructor <;> omega
      have hθT : T ≤ |θ P| := hsep _ hdQ hdne
      have hθ0 : θ P ≠ 0 := fun h => by rw [h, abs_zero] at hθT; linarith
      rw [hδ0, mul_zero, sub_zero, hterm]
      simp only
      rw [intervalIntegral.integral_const_mul, norm_mul, norm_mul, hcn, norm_ee, mul_one]
      have hb := integral_ee_bound hθ0 X
      have hp : 0 ≤ ∏ i, (1 / (Q i : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
      calc (∏ i, (1 / (Q i : ℝ))) * ‖∫ x in (-X)..X, ee (θ P * x)‖
          ≤ (∏ i, (1 / (Q i : ℝ))) * (1 / (π * |θ P|)) := mul_le_mul_of_nonneg_left hb hp
        _ ≤ (∏ i, (1 / (Q i : ℝ))) * (1 / (π * T)) := by
          gcongr
        _ = _ := by ring
  -- conclusion
  have hmain : ‖((∫ x in (-X)..X, ∏ i, fejer (Q i) (lam i * x - α i) : ℝ) : ℂ) - (2 * X : ℝ)‖
      ≤ (∏ i, (Q i : ℝ)) / (π * T) := by
    rw [← intervalIntegral.integral_ofReal, hint]
    have : ((2 * X : ℝ) : ℂ) = ∑ P ∈ Fintype.piFinset S, (2 * X : ℝ) * δ P := by
      rw [← Finset.mul_sum, hδsum, mul_one]
    rw [this, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm_bd).trans ?_)
    rw [Finset.sum_const, Fintype.card_piFinset, nsmul_eq_mul]
    have : ((∏ i, (S i).card : ℕ) : ℝ) * ∏ i, (1 / (Q i : ℝ)) = ∏ i, (Q i : ℝ) := by
      push_cast
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hS, Finset.card_product, Finset.card_range]
      have := hQpos i
      push_cast; field_simp
    rw [← mul_div_assoc, this]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hmain
  exact hmain

/-! ## Frequency lower bounds -/

/-- A hierarchical lower bound: if `ℓ ≠ 0` has entries `|ℓ_j| ≤ Q`, the coefficients satisfy
`b ≤ |β_j| ≤ B`, and `s ≥ 1` is large compared with `Q`, then
`|∑_j ℓ_j β_j s^{e - j}| ≥ (b / 2) s^{e - K}` (the first non-zero term dominates). -/
lemma hier {K : ℕ} (β : Fin (K + 1) → ℝ) {b B e s Q : ℝ} (hb0 : 0 < b)
    (hb : ∀ j, b ≤ |β j|) (hB : ∀ j, |β j| ≤ B) (hs : 1 ≤ s)
    (ℓ : Fin (K + 1) → ℤ) (hℓ : ℓ ≠ 0) (hℓQ : ∀ j, |(ℓ j : ℝ)| ≤ Q)
    (hsQ : 2 * (K + 1) * Q * B ≤ b * s) :
    b / 2 * s ^ (e - K) ≤ |∑ j, (ℓ j : ℝ) * β j * s ^ (e - (j : ℕ))| := by
  classical
  have hne : (univ.filter fun j => ℓ j ≠ 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact hℓ (funext fun j => by simpa using h (mem_univ j))
  set j0 := (univ.filter fun j => ℓ j ≠ 0).min' hne with hj0def
  have hj0 : ℓ j0 ≠ 0 := (mem_filter.1 (min'_mem _ hne)).2
  have hlt : ∀ j, j < j0 → ℓ j = 0 := fun j hj => by
    by_contra h
    exact absurd (min'_le _ j (mem_filter.2 ⟨mem_univ _, h⟩)) (not_le.2 hj)
  have hs0 : 0 < s := by linarith
  have hQ0 : 0 ≤ Q := (abs_nonneg _).trans (hℓQ j0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB j0)
  set M := s ^ (e - (j0 : ℕ)) with hM
  have hMpos : 0 < M := rpow_pos_of_pos hs0 _
  have hmain : b * M ≤ |(ℓ j0 : ℝ) * β j0 * s ^ (e - (j0 : ℕ))| := by
    rw [abs_mul, abs_mul, abs_of_pos (rpow_pos_of_pos hs0 _)]
    have h1 : (1 : ℝ) ≤ |(ℓ j0 : ℝ)| := by exact_mod_cast Int.one_le_abs hj0
    have := hb j0
    have h2 : b ≤ |(ℓ j0 : ℝ)| * |β j0| := by nlinarith [abs_nonneg (β j0)]
    exact mul_le_mul_of_nonneg_right h2 hMpos.le
  have hother : ∀ j ∈ univ.erase j0,
      |(ℓ j : ℝ) * β j * s ^ (e - (j : ℕ))| ≤ Q * B * s ^ (e - (j0 : ℕ) - 1) := by
    intro j hj
    rcases lt_or_gt_of_ne (ne_of_mem_erase hj) with h | h
    · rw [hlt j h]; simp only [Int.cast_zero, zero_mul, abs_zero]; positivity
    · rw [abs_mul, abs_mul, abs_of_pos (rpow_pos_of_pos hs0 _)]
      have hexp : s ^ (e - (j : ℕ)) ≤ s ^ (e - (j0 : ℕ) - 1) := by
        refine rpow_le_rpow_of_exponent_le hs ?_
        have : (j0 : ℕ) + 1 ≤ (j : ℕ) := h
        have : ((j0 : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast this
        linarith
      have h3 := hℓQ j
      have h4 := hB j
      exact mul_le_mul (mul_le_mul h3 h4 (abs_nonneg _) hQ0) hexp (rpow_pos_of_pos hs0 _).le
        (mul_nonneg hQ0 hB0)
  have hrest : |∑ j ∈ univ.erase j0, (ℓ j : ℝ) * β j * s ^ (e - (j : ℕ))| ≤ b / 2 * M := by
    refine (abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hother).trans ?_)
    rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hsM : s ^ (e - (j0 : ℕ) - 1) * s = M := by
      rw [hM, ← rpow_add_one hs0.ne']; ring_nf
    have hR : 0 ≤ s ^ (e - (j0 : ℕ) - 1) := (rpow_pos_of_pos hs0 _).le
    push_cast
    have : (K : ℝ) * (Q * B) ≤ (K + 1) * (Q * B) := by nlinarith [mul_nonneg hQ0 hB0]
    calc (K : ℝ) * (Q * B * s ^ (e - (j0 : ℕ) - 1))
        ≤ ((K + 1) * Q * B) * s ^ (e - (j0 : ℕ) - 1) := by nlinarith
      _ ≤ (b * s / 2) * s ^ (e - (j0 : ℕ) - 1) := by gcongr; linarith
      _ = b / 2 * M := by rw [← hsM]; ring
  have hsplit := Finset.add_sum_erase univ (fun j => (ℓ j : ℝ) * β j * s ^ (e - (j : ℕ)))
    (mem_univ j0)
  rw [← hsplit]
  have hMK : s ^ (e - K) ≤ M := by
    refine rpow_le_rpow_of_exponent_le hs ?_
    have : ((j0 : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 j0.2
    linarith
  have := abs_sub_abs_le_abs_sub ((ℓ j0 : ℝ) * β j0 * s ^ (e - (j0 : ℕ)))
    (-∑ j ∈ univ.erase j0, (ℓ j : ℝ) * β j * s ^ (e - (j : ℕ)))
  rw [abs_neg, sub_neg_eq_add] at this
  nlinarith

lemma gbinom_ne_zero {γ : ℝ} (hγZ : ∀ m : ℤ, γ ≠ m) (j : ℕ) : gbinom γ j ≠ 0 := by
  unfold gbinom
  rw [descPochhammer_eval_eq_prod_range]
  refine div_ne_zero (prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 fun h => hγZ i ?_)
    (by positivity)
  rw [h]; norm_cast

lemma exists_bounds {K : ℕ} (β : Fin (K + 1) → ℝ) (h : ∀ j, β j ≠ 0) :
    ∃ b B : ℝ, 0 < b ∧ 0 ≤ B ∧ (∀ j, b ≤ |β j|) ∧ ∀ j, |β j| ≤ B := by
  obtain ⟨j1, -, hj1⟩ := Finset.exists_min_image univ (fun j => |β j|) univ_nonempty
  obtain ⟨j2, -, hj2⟩ := Finset.exists_max_image univ (fun j => |β j|) univ_nonempty
  exact ⟨|β j1|, |β j2|, abs_pos.2 (h j1), abs_nonneg _, fun j => hj1 j (mem_univ _),
    fun j => hj2 j (mem_univ _)⟩

/-- A finite set of naturals whose pairwise gaps are `≤ D` has at most `D + 1` elements. -/
lemma card_le_of_gap (S : Finset ℕ) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ a ∈ S, ∀ b ∈ S, a < b → ((b : ℝ) - a) ≤ D) : (S.card : ℝ) ≤ D + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp; linarith
  set m := S.min' hne
  have hsub : S ⊆ Finset.Icc m (m + ⌊D⌋₊) := by
    intro b hb
    have hmb : m ≤ b := S.min'_le b hb
    rw [Finset.mem_Icc]
    refine ⟨hmb, ?_⟩
    rcases hmb.eq_or_lt with h' | h'
    · omega
    · have := h m (S.min'_mem hne) b hb h'
      have : b - m ≤ ⌊D⌋₊ := Nat.le_floor (by push_cast [hmb]; linarith)
      omega
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  have hf := Nat.floor_le hD
  have : (S.card : ℝ) ≤ ((m + ⌊D⌋₊ + 1 - m : ℕ) : ℝ) := by exact_mod_cast this
  rw [show m + ⌊D⌋₊ + 1 - m = ⌊D⌋₊ + 1 by omega] at this
  push_cast at this
  linarith


/-- `Ξ_s(ℓ) = ∑_{j ≤ k} ℓ_j c_j(s)` with `c_j(s) = binom(γ, j) s^{γ - j}`. -/
def Xi (γ s : ℝ) (ℓ : Fin (⌊γ⌋₊ + 1) → ℤ) : ℝ := ∑ j, (ℓ j : ℝ) * cj γ j s

/-- The derivative of `s ↦ Ξ_s(ℓ)`. -/
def dXi (γ s : ℝ) (ℓ : Fin (⌊γ⌋₊ + 1) → ℤ) : ℝ :=
  ∑ j, (ℓ j : ℝ) * (gbinom γ j * (γ - (j : ℕ))) * s ^ (γ - 1 - (j : ℕ))

lemma hasDerivAt_Xi (γ : ℝ) (ℓ : Fin (⌊γ⌋₊ + 1) → ℤ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => Xi γ s ℓ) (dXi γ s ℓ) s := by
  unfold Xi dXi cj
  have : ∀ j : Fin (⌊γ⌋₊ + 1), HasDerivAt (fun s : ℝ => (ℓ j : ℝ) * (gbinom γ j * s ^ (γ - (j : ℕ))))
      ((ℓ j : ℝ) * (gbinom γ j * (γ - (j : ℕ))) * s ^ (γ - 1 - (j : ℕ))) s := fun j => by
    have h := ((Real.hasDerivAt_rpow_const (p := γ - (j : ℕ)) (Or.inl hs.ne')).const_mul
      (gbinom γ j)).const_mul (ℓ j : ℝ)
    refine h.congr_deriv ?_
    rw [show γ - 1 - (j : ℕ) = γ - (j : ℕ) - 1 by ring]; ring
  exact HasDerivAt.fun_sum (u := univ) fun j _ => this j

/-- Paper, Lemma \ref{IB:lem:freq} (in a uniform form): `|Ξ_s(ℓ)| ≥ (b / 2) s^ς` for
`0 ≠ ℓ`, `|ℓ_j| ≤ Q`, once `s` is large compared with `Q`. -/
lemma freq {γ : ℝ} (hγZ : ∀ m : ℤ, γ ≠ m) : ∃ b B : ℝ, 0 < b ∧ 0 ≤ B ∧
    ∀ (Q s : ℝ) (ℓ : Fin (⌊γ⌋₊ + 1) → ℤ), ℓ ≠ 0 → (∀ j, |(ℓ j : ℝ)| ≤ Q) → 1 ≤ s →
      2 * ((⌊γ⌋₊ : ℝ) + 1) * Q * B ≤ b * s → b / 2 * s ^ (γ - ⌊γ⌋₊) ≤ |Xi γ s ℓ| := by
  obtain ⟨b, B, hb, hB0, hb1, hB1⟩ :=
    exists_bounds (fun j : Fin (⌊γ⌋₊ + 1) => gbinom γ j) fun j => gbinom_ne_zero hγZ j
  refine ⟨b, B, hb, hB0, fun Q s ℓ hℓ hℓQ hs hsQ => ?_⟩
  have := hier (fun j : Fin (⌊γ⌋₊ + 1) => gbinom γ j) (e := γ) hb hb1 hB1 hs ℓ hℓ hℓQ hsQ
  unfold Xi cj
  simpa only [mul_assoc] using this

lemma dfreq {γ : ℝ} (hγZ : ∀ m : ℤ, γ ≠ m) : ∃ b B : ℝ, 0 < b ∧ 0 ≤ B ∧
    ∀ (Q s : ℝ) (ℓ : Fin (⌊γ⌋₊ + 1) → ℤ), ℓ ≠ 0 → (∀ j, |(ℓ j : ℝ)| ≤ Q) → 1 ≤ s →
      2 * ((⌊γ⌋₊ : ℝ) + 1) * Q * B ≤ b * s →
        b / 2 * s ^ (γ - ⌊γ⌋₊ - 1) ≤ |dXi γ s ℓ| := by
  obtain ⟨b, B, hb, hB0, hb1, hB1⟩ :=
    exists_bounds (fun j : Fin (⌊γ⌋₊ + 1) => gbinom γ j * (γ - (j : ℕ))) fun j =>
      mul_ne_zero (gbinom_ne_zero hγZ j) (sub_ne_zero.2 fun h => hγZ (j : ℕ) (by simp [h]))
  refine ⟨b, B, hb, hB0, fun Q s ℓ hℓ hℓQ hs hsQ => ?_⟩
  have := hier (fun j : Fin (⌊γ⌋₊ + 1) => gbinom γ j * (γ - (j : ℕ))) (e := γ - 1) hb hb1 hB1
    hs ℓ hℓ hℓQ hsQ
  unfold dXi
  rw [show γ - ⌊γ⌋₊ - 1 = γ - 1 - ⌊γ⌋₊ by ring]
  exact this

/-- Paper, proof of Lemma \ref{IB:lem:bad}: if `|∂_s Ξ_s(ℓ)| ≥ δ` on `[N, 2N]`, then at most
`2T/δ + 1` integers `n' ∈ [N, 2N)` satisfy `|A + Ξ_{n'}(ℓ)| < T`. -/
lemma count_close (γ : ℝ) (N : ℕ) (hN : 1 ≤ N) (ℓ : Fin (⌊γ⌋₊ + 1) → ℤ) (A T δ : ℝ)
    (hT : 0 ≤ T) (hδ : 0 < δ) (hd : ∀ s : ℝ, (N : ℝ) ≤ s → s ≤ 2 * N → δ ≤ |dXi γ s ℓ|) :
    (((Ico N (2 * N)).filter (fun n' : ℕ => |A + Xi γ n' ℓ| < T)).card : ℝ) ≤ 2 * T / δ + 1 := by
  refine card_le_of_gap _ (by positivity) fun a ha b hb hab => ?_
  rw [mem_filter, mem_Ico] at ha hb
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha1 : (N : ℝ) ≤ a := by exact_mod_cast ha.1.1
  have hb2 : (b : ℝ) ≤ 2 * N := by exact_mod_cast hb.1.2.le
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hderiv : ∀ s ∈ Set.Icc (a : ℝ) b, HasDerivAt (fun s => Xi γ s ℓ) (dXi γ s ℓ) s :=
    fun s hs => hasDerivAt_Xi γ ℓ (by linarith [hs.1])
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun s => Xi γ s ℓ) (dXi γ · ℓ) hab'
    (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs => hderiv s ⟨hs.1.le, hs.2.le⟩)
  have hcd := hd c (by linarith [hc.1]) (by linarith [hc.2])
  rw [hceq, abs_div, abs_of_pos (by linarith : (0 : ℝ) < b - a), le_div_iff₀ (by linarith)] at hcd
  have h2 : |Xi γ b ℓ - Xi γ a ℓ| < 2 * T := by
    have := abs_sub_le (A + Xi γ b ℓ) 0 (A + Xi γ a ℓ)
    rw [show A + Xi γ b ℓ - (A + Xi γ a ℓ) = Xi γ b ℓ - Xi γ a ℓ by ring] at this
    simp only [sub_zero, zero_sub, abs_neg] at this
    linarith [hb.2, ha.2]
  rw [le_div_iff₀ hδ]
  nlinarith


/-! ## The functions `F_n` and their moments -/

/-- The shifts: `α_0 = 3η/8` (the centre of `[η/4, η/2]`) and `α_j = 0` for `j ≥ 1`. -/
def alv (γ : ℝ) (N : ℕ) (j : Fin (⌊γ⌋₊ + 1)) : ℝ := if (j : ℕ) = 0 then 3 * eta N / 8 else 0

/-- `F_n(x) = ∏_{j ≤ k} K_Q(c_j(n) x - α_j)`, a non-negative trigonometric polynomial in `x`
concentrated near `E_n`. -/
def Fn (γ : ℝ) (Q N n : ℕ) (x : ℝ) : ℝ :=
  ∏ j : Fin (⌊γ⌋₊ + 1), fejer Q (cj γ j n * x - alv γ N j)

/-- The degree vector `(Q, …, Q)` with the `j₀`-th entry replaced by `1`. -/
def degv (γ : ℝ) (Q : ℕ) (j₀ : Fin (⌊γ⌋₊ + 1)) : Fin (⌊γ⌋₊ + 1) → ℕ :=
  Function.update (fun _ => Q) j₀ 1

/-- A majorant of `F_n` outside `E_n`: `U_n = ∑_{j₀} (4 Q ρ²)⁻¹ ∏_{j ≠ j₀} K_Q(c_j(n) x - α_j)`. -/
def Un (γ : ℝ) (L Q N n : ℕ) (x : ℝ) : ℝ :=
  ∑ j₀ : Fin (⌊γ⌋₊ + 1), 1 / (4 * Q * rho γ L N ^ 2) *
    ∏ j, fejer (degv γ Q j₀ j) (cj γ j n * x - alv γ N j)

lemma continuous_Fn (γ : ℝ) (Q N n : ℕ) : Continuous (Fn γ Q N n) := by
  unfold Fn
  exact continuous_finsetProd _ fun j _ =>
    (continuous_fejer Q).comp ((continuous_const.mul continuous_id).sub continuous_const)

lemma continuous_Un (γ : ℝ) (L Q N n : ℕ) : Continuous (Un γ L Q N n) := by
  unfold Un
  refine continuous_finsetSum _ fun j₀ _ => continuous_const.mul ?_
  exact continuous_finsetProd _ fun j _ =>
    (continuous_fejer _).comp ((continuous_const.mul continuous_id).sub continuous_const)

lemma Fn_nonneg (γ : ℝ) (Q N n : ℕ) (x : ℝ) : 0 ≤ Fn γ Q N n x :=
  Finset.prod_nonneg fun _ _ => fejer_nonneg _ _

lemma Fn_le {γ : ℝ} {Q : ℕ} (hQ : 1 ≤ Q) (N n : ℕ) (x : ℝ) :
    Fn γ Q N n x ≤ (Q : ℝ) ^ (⌊γ⌋₊ + 1) := by
  unfold Fn
  calc ∏ j : Fin (⌊γ⌋₊ + 1), fejer Q (cj γ j n * x - alv γ N j) ≤ ∏ _j : Fin (⌊γ⌋₊ + 1), (Q : ℝ) :=
        Finset.prod_le_prod (fun _ _ => fejer_nonneg _ _) fun _ _ => fejer_le hQ _
    _ = (Q : ℝ) ^ (⌊γ⌋₊ + 1) := by simp

lemma rho_pos {γ : ℝ} {L N : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ N) : 0 < rho γ L N := by
  unfold rho
  have := eta_pos hN
  have : (0 : ℝ) < L := by exact_mod_cast hL
  positivity

lemma rho_le {γ : ℝ} {L N : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ N) : rho γ L N ≤ eta N / 8 := by
  unfold rho
  have hη := eta_pos hN
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ ⌊γ⌋₊ := one_le_pow₀ (by exact_mod_cast hL)
  have hk : (0 : ℝ) ≤ ⌊γ⌋₊ := Nat.cast_nonneg _
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (8 : ℝ) ≤ 16 * ((⌊γ⌋₊ : ℝ) + 1) * (L : ℝ) ^ ⌊γ⌋₊ := by nlinarith
  nlinarith

lemma Un_nonneg {γ : ℝ} {L N : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ N) (Q n : ℕ) (x : ℝ) :
    0 ≤ Un γ L Q N n x := by
  have := rho_pos (γ := γ) hL hN
  exact Finset.sum_nonneg fun _ _ =>
    mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ => fejer_nonneg _ _)

/-- If `x ∉ E_n`, some coordinate `c_j(n) x - α_j` has distance `≥ ρ` from `ℤ`. -/
lemma out_coord {γ : ℝ} {L N : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ N) (n : ℕ) {x : ℝ}
    (hx : x ∉ En γ L N n) :
    ∃ j₀ : Fin (⌊γ⌋₊ + 1), ∀ m : ℤ, rho γ L N ≤ |cj γ j₀ n * x - alv γ N j₀ - m| := by
  have hη := eta_pos hN
  have hη1 := eta_lt_one hN
  have hρ := rho_le (γ := γ) hL hN
  simp only [En, Set.mem_ofPred_eq, not_and_or] at hx
  push Not at hx
  rcases hx with h0 | ⟨j, hj1, hjk, hj⟩
  · refine ⟨⟨0, by omega⟩, fun m => ?_⟩
    simp only [alv, if_true]
    set t := cj γ 0 n * x
    have hf := Int.floor_add_fract t
    have hf0 := Int.fract_nonneg t
    have hf1 := Int.fract_lt_one t
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h0
    refine hρ.trans ?_
    obtain hz | hz | hz : ⌊t⌋ - m ≤ -1 ∨ ⌊t⌋ - m = 0 ∨ 1 ≤ ⌊t⌋ - m := by omega
    · have : ((⌊t⌋ - m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hz
      push_cast at this
      exact le_abs.2 (Or.inr (by linarith))
    · have : ((⌊t⌋ - m : ℤ) : ℝ) = 0 := by exact_mod_cast hz
      push_cast at this
      rcases h0 with h0 | h0
      · exact le_abs.2 (Or.inr (by linarith))
      · exact le_abs.2 (Or.inl (by linarith))
    · have : (1 : ℝ) ≤ ((⌊t⌋ - m : ℤ) : ℝ) := by exact_mod_cast hz
      push_cast at this
      exact le_abs.2 (Or.inl (by linarith))
  · refine ⟨⟨j, by omega⟩, fun m => ?_⟩
    have hj0 : j ≠ 0 := by omega
    simp only [alv, hj0, if_false, sub_zero]
    exact hj.le.trans (round_le _ m)

lemma Fn_le_Un {γ : ℝ} {L Q N : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ N) (hQ : 1 ≤ Q) (n : ℕ) {x : ℝ}
    (hx : x ∉ En γ L N n) : Fn γ Q N n x ≤ Un γ L Q N n x := by
  obtain ⟨j₀, hj₀⟩ := out_coord hL hN n hx
  have hρ := rho_pos (γ := γ) hL hN
  have h1 : fejer Q (cj γ j₀ n * x - alv γ N j₀) ≤ 1 / (4 * Q * rho γ L N ^ 2) :=
    fejer_out hQ hρ hj₀
  unfold Fn Un
  rw [← Finset.mul_prod_erase univ _ (mem_univ j₀)]
  refine le_trans ?_ (Finset.single_le_sum (f := fun j₀ => 1 / (4 * Q * rho γ L N ^ 2) *
    ∏ j, fejer (degv γ Q j₀ j) (cj γ j n * x - alv γ N j)) (fun j _ => mul_nonneg
      (by positivity) (Finset.prod_nonneg fun _ _ => fejer_nonneg _ _)) (mem_univ j₀))
  rw [← Finset.mul_prod_erase univ _ (mem_univ j₀), degv, Function.update_self, fejer_one,
    one_mul]
  have : ∏ j ∈ univ.erase j₀, fejer (Function.update (fun _ => Q) j₀ 1 j)
      (cj γ j n * x - alv γ N j) = ∏ j ∈ univ.erase j₀, fejer Q (cj γ j n * x - alv γ N j) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [this]
  exact mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun _ _ => fejer_nonneg _ _)

/-- First moment: integrals of `∏_j K_{Q'_j}(c_j(n) x - α_j)` with `1 ≤ Q'_j ≤ Q`. -/
lemma moment_one {γ : ℝ} (Q N n : ℕ) (Q' : Fin (⌊γ⌋₊ + 1) → ℕ)
    (hQ' : ∀ j, 1 ≤ Q' j ∧ Q' j ≤ Q) (X₀ : ℝ) {T₁ : ℝ} (hT₁ : 0 < T₁)
    (hfreq : ∀ ℓ : Fin (⌊γ⌋₊ + 1) → ℤ, ℓ ≠ 0 → (∀ j, |ℓ j| < Q) → T₁ ≤ |Xi γ n ℓ|) :
    |(∫ x in (-X₀)..X₀, ∏ j, fejer (Q' j) (cj γ j n * x - alv γ N j)) - 2 * X₀| ≤
      (Q : ℝ) ^ (⌊γ⌋₊ + 1) / (π * T₁) := by
  have h := trig_integral (fun j : Fin (⌊γ⌋₊ + 1) => cj γ j n) (alv γ N) Q' (fun j => (hQ' j).1)
    X₀ hT₁ (fun d hd hd0 => hfreq d hd0 fun j => (hd j).trans_le (by exact_mod_cast (hQ' j).2))
  refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  calc ∏ j, (Q' j : ℝ) ≤ ∏ _j : Fin (⌊γ⌋₊ + 1), (Q : ℝ) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun j _ => by
          exact_mod_cast (hQ' j).2
    _ = (Q : ℝ) ^ (⌊γ⌋₊ + 1) := by simp

/-- The frequencies of the pair `(n, n')`. -/
def lam2 (γ : ℝ) (n n' : ℕ) : Fin (⌊γ⌋₊ + 1) ⊕ Fin (⌊γ⌋₊ + 1) → ℝ :=
  Sum.elim (fun j => cj γ j n) (fun j => cj γ j n')

/-- A pair `(n, n')` is *good* if `|Ξ_n(ℓ) + Ξ_{n'}(ℓ')| ≥ T` for all non-zero `(ℓ, ℓ')` in the
box `|ℓ_j|, |ℓ'_j| < Q`. -/
def Good (γ : ℝ) (Q : ℕ) (T : ℝ) (n n' : ℕ) : Prop :=
  ∀ d : Fin (⌊γ⌋₊ + 1) ⊕ Fin (⌊γ⌋₊ + 1) → ℤ, (∀ i, |d i| < Q) → d ≠ 0 →
    T ≤ |∑ i, (d i : ℝ) * lam2 γ n n' i|

/-- Second moment for good pairs. -/
lemma moment_two_good {γ : ℝ} {Q : ℕ} (hQ : 1 ≤ Q) (N n n' : ℕ) (X₀ : ℝ) {T : ℝ} (hT : 0 < T)
    (hg : Good γ Q T n n') :
    |(∫ x in (-X₀)..X₀, Fn γ Q N n x * Fn γ Q N n' x) - 2 * X₀| ≤
      (Q : ℝ) ^ (2 * (⌊γ⌋₊ + 1)) / (π * T) := by
  have h := trig_integral (lam2 γ n n') (Sum.elim (alv γ N) (alv γ N)) (fun _ => Q)
    (fun _ => hQ) X₀ hT hg
  have e : ∀ x, Fn γ Q N n x * Fn γ Q N n' x = ∏ i, fejer ((fun _ => Q) i)
      (lam2 γ n n' i * x - Sum.elim (alv γ N) (alv γ N) i) := fun x => by
    rw [Fintype.prod_sum_type]; rfl
  simp_rw [e]
  refine h.trans (le_of_eq ?_)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
  ring_nf


open Classical in
/-- Paper, Lemma \ref{IB:lem:bad}: if `|Ξ_n(ℓ)| ≥ T₁ ≥ T` for `0 ≠ ℓ` in the box and, for each
`ℓ' ≠ 0` in the box and each `A`, at most `D` integers `n' ∈ [N, 2N)` satisfy
`|A + Ξ_{n'}(ℓ')| < T`, then there are at most `N (2Q)^{2(k+1)} D` bad pairs. -/
lemma bad_count {γ : ℝ} (N Q : ℕ) {T T₁ D : ℝ} (hD : 0 ≤ D) (hTT₁ : T ≤ T₁)
    (hfreq : ∀ n ∈ Ico N (2 * N), ∀ ℓ : Fin (⌊γ⌋₊ + 1) → ℤ, ℓ ≠ 0 → (∀ j, |ℓ j| < Q) →
      T₁ ≤ |Xi γ n ℓ|)
    (hcount : ∀ ℓ' : Fin (⌊γ⌋₊ + 1) → ℤ, ℓ' ≠ 0 → (∀ j, |ℓ' j| < Q) → ∀ A : ℝ,
      (((Ico N (2 * N)).filter (fun n' : ℕ => |A + Xi γ n' ℓ'| < T)).card : ℝ) ≤ D) :
    ((((Ico N (2 * N)) ×ˢ (Ico N (2 * N))).filter (fun p : ℕ × ℕ => ¬ Good γ Q T p.1 p.2)).card : ℝ) ≤
      N * (2 * Q) ^ (2 * (⌊γ⌋₊ + 1)) * D := by
  set I := Ico N (2 * N) with hI
  set box := Fintype.piFinset (fun _ : Fin (⌊γ⌋₊ + 1) ⊕ Fin (⌊γ⌋₊ + 1) => Ioo (-(Q : ℤ)) Q)
    with hbox_def
  set S : ℕ → ((Fin (⌊γ⌋₊ + 1) ⊕ Fin (⌊γ⌋₊ + 1)) → ℤ) → Finset ℕ := fun n d =>
    I.filter (fun n' => (fun j => d (Sum.inr j)) ≠ 0 ∧
      |Xi γ n (fun j => d (Sum.inl j)) + Xi γ n' (fun j => d (Sum.inr j))| < T) with hS_def
  have hsub : (I ×ˢ I).filter (fun p : ℕ × ℕ => ¬ Good γ Q T p.1 p.2) ⊆
      I.biUnion (fun n => box.biUnion (fun d => (S n d).image (fun n' => (n, n')))) := by
    intro p hp
    rw [mem_filter, mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hbad⟩ := hp
    simp only [Good, not_forall, not_le] at hbad
    obtain ⟨d, hdQ, hd0, hdT⟩ := hbad
    have hsplit : ∑ i, (d i : ℝ) * lam2 γ p.1 p.2 i =
        Xi γ p.1 (fun j => d (Sum.inl j)) + Xi γ p.2 (fun j => d (Sum.inr j)) := by
      rw [Fintype.sum_sum_type]; rfl
    rw [hsplit] at hdT
    have hr : (fun j => d (Sum.inr j)) ≠ 0 := by
      intro hr
      have hl : (fun j => d (Sum.inl j)) ≠ 0 := by
        intro hl; apply hd0; funext i
        cases i with
        | inl j => exact congrFun hl j
        | inr j => exact congrFun hr j
      have hXr : Xi γ p.2 (fun j => d (Sum.inr j)) = 0 := by rw [hr]; simp [Xi]
      rw [hXr, add_zero] at hdT
      have := hfreq p.1 h1 _ hl (fun j => hdQ (Sum.inl j))
      linarith
    rw [mem_biUnion]
    refine ⟨p.1, h1, ?_⟩
    rw [mem_biUnion]
    refine ⟨d, ?_, ?_⟩
    · rw [hbox_def, Fintype.mem_piFinset]; intro i; rw [mem_Ioo]; exact abs_lt.1 (hdQ i)
    · rw [mem_image]; exact ⟨p.2, mem_filter.2 ⟨h2, hr, hdT⟩, rfl⟩
  have hS : ∀ n, ∀ d ∈ box, ((S n d).card : ℝ) ≤ D := by
    intro n d hd
    by_cases hr : (fun j => d (Sum.inr j)) = 0
    · have : S n d = ∅ := by
        rw [hS_def, Finset.filter_eq_empty_iff]; intro x _ h; exact h.1 hr
      rw [this, card_empty, Nat.cast_zero]; exact hD
    · have hdQ : ∀ j, |d (Sum.inr j)| < Q := by
        intro j; rw [hbox_def, Fintype.mem_piFinset] at hd; exact abs_lt.2 (mem_Ioo.1 (hd _))
      refine le_trans ?_ (hcount _ hr hdQ (Xi γ n (fun j => d (Sum.inl j))))
      exact_mod_cast card_le_card (fun x hx => by
        rw [hS_def, mem_filter] at hx; rw [mem_filter]; exact ⟨hx.1, hx.2.2⟩)
  have hbox : (box.card : ℝ) ≤ (2 * Q) ^ (2 * (⌊γ⌋₊ + 1)) := by
    have : box.card ≤ (2 * Q) ^ (2 * (⌊γ⌋₊ + 1)) := by
      rw [hbox_def, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_sum,
        Fintype.card_fin, Int.card_Ioo, show ⌊γ⌋₊ + 1 + (⌊γ⌋₊ + 1) = 2 * (⌊γ⌋₊ + 1) by ring]
      exact Nat.pow_le_pow_left (by omega) _
    exact_mod_cast this
  have hcard : ((((Ico N (2 * N)) ×ˢ (Ico N (2 * N))).filter
      (fun p : ℕ × ℕ => ¬ Good γ Q T p.1 p.2)).card : ℝ) ≤ ∑ n ∈ I, ∑ d ∈ box, ((S n d).card : ℝ) := by
    have : (((Ico N (2 * N)) ×ˢ (Ico N (2 * N))).filter (fun p : ℕ × ℕ => ¬ Good γ Q T p.1 p.2)).card ≤
        ∑ n ∈ I, ∑ d ∈ box, (S n d).card := by
      refine (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun n _ => ?_))
      exact card_biUnion_le.trans (sum_le_sum fun d _ => card_image_le)
    exact_mod_cast this
  refine hcard.trans ?_
  calc ∑ n ∈ I, ∑ d ∈ box, ((S n d).card : ℝ) ≤ ∑ _n ∈ I, ∑ _d ∈ box, D :=
        sum_le_sum fun n _ => sum_le_sum fun d hd => hS n d hd
    _ = N * (box.card * D) := by
        rw [sum_const, sum_const, hI, Nat.card_Ico, nsmul_eq_mul, nsmul_eq_mul,
          show 2 * N - N = N by omega]
    _ ≤ N * ((2 * Q) ^ (2 * (⌊γ⌋₊ + 1)) * D) := by gcongr
    _ = _ := by ring


/-! ## The second-moment bound for a fixed dyadic block -/

open Classical in
/-- The measure of the bad set for one dyadic block `[N, 2N)`, `N = 2^r`, in terms of the
parameters `Q`, `T`, `T₁`, `D` (paper: first and second moments and Chebyshev's inequality).
Here `V = 2X₀`, `ε₁ = Q^{k+1}/(π T₁)` and `ε₂ = Q^{2(k+1)}/(π T)`. -/
theorem bad_measure_le {γ : ℝ} {L : ℕ} (hL : 1 ≤ L) {X₀ : ℝ} (hX₀ : 0 < X₀) (r N Q : ℕ)
    (hN : N = 2 ^ r) (hQ : 1 ≤ Q) {T T₁ D : ℝ} (hT : 0 < T) (hTT₁ : T ≤ T₁) (hD : 0 ≤ D)
    (hfreq : ∀ n ∈ Ico N (2 * N), ∀ ℓ : Fin (⌊γ⌋₊ + 1) → ℤ, ℓ ≠ 0 → (∀ j, |ℓ j| < Q) →
      T₁ ≤ |Xi γ n ℓ|)
    (hcount : ∀ ℓ' : Fin (⌊γ⌋₊ + 1) → ℤ, ℓ' ≠ 0 → (∀ j, |ℓ' j| < Q) → ∀ A : ℝ,
      (((Ico N (2 * N)).filter (fun n' : ℕ => |A + Xi γ n' ℓ'| < T)).card : ℝ) ≤ D) :
    volume (badSet γ L X₀ r) ≤ ENNReal.ofReal (4 / 3 *
      ((Q : ℝ) ^ (2 * (⌊γ⌋₊ + 1)) / (π * T) + 2 * ((Q : ℝ) ^ (⌊γ⌋₊ + 1) / (π * T₁)) +
        (N * (2 * Q) ^ (2 * (⌊γ⌋₊ + 1)) * D) *
          ((Q : ℝ) ^ (⌊γ⌋₊ + 1) * (2 * X₀ + (Q : ℝ) ^ (⌊γ⌋₊ + 1) / (π * T₁))) / (N : ℝ) ^ 2 +
        ((⌊γ⌋₊ : ℝ) + 1) * (2 * X₀ + (Q : ℝ) ^ (⌊γ⌋₊ + 1) / (π * T₁)) /
          (4 * Q * rho γ L N ^ 2))) := by
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_two_pow
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hT₁ : 0 < T₁ := hT.trans_le hTT₁
  have hρ := rho_pos (γ := γ) hL hN1
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set K := ⌊γ⌋₊ with hK
  set I := Ico N (2 * N) with hI
  have hIcard : (I.card : ℝ) = N := by
    rw [hI, Nat.card_Ico, show 2 * N - N = N by omega]
  set V := 2 * X₀ with hV
  set ε₁ := (Q : ℝ) ^ (K + 1) / (π * T₁) with hε₁
  set ε₂ := (Q : ℝ) ^ (2 * (K + 1)) / (π * T) with hε₂
  have hε₁0 : 0 ≤ ε₁ := by positivity
  have hε₂0 : 0 ≤ ε₂ := by positivity
  set ρ := rho γ L N with hρdef
  set G : ℝ → ℝ := fun x => ∑ n ∈ I, Fn γ Q N n x with hG
  set U : ℝ → ℝ := fun x => ∑ n ∈ I, Un γ L Q N n x with hU
  have hGc : Continuous G := continuous_finsetSum _ fun n _ => continuous_Fn γ Q N n
  have hUc : Continuous U := continuous_finsetSum _ fun n _ => continuous_Un γ L Q N n
  have hii : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume (-X₀) X₀ :=
    fun f hf => hf.intervalIntegrable _ _
  have hconst : ∀ c : ℝ, ∫ _x in (-X₀)..X₀, c = V * c := fun c => by
    rw [intervalIntegral.integral_const, smul_eq_mul, hV]; ring
  -- first moment
  have hF1 : ∀ n ∈ I, |(∫ x in (-X₀)..X₀, Fn γ Q N n x) - V| ≤ ε₁ := fun n hn =>
    moment_one Q N n (fun _ => Q) (fun _ => ⟨hQ, le_rfl⟩) X₀ hT₁ (hfreq n hn)
  have hG1 : (N : ℝ) * (V - ε₁) ≤ ∫ x in (-X₀)..X₀, G x := by
    rw [hG, intervalIntegral.integral_finsetSum fun n _ => hii _ (continuous_Fn γ Q N n)]
    calc (N : ℝ) * (V - ε₁) = ∑ _n ∈ I, (V - ε₁) := by rw [sum_const, nsmul_eq_mul, hIcard]
      _ ≤ _ := sum_le_sum fun n hn => by linarith [(abs_le.1 (hF1 n hn)).1]
  -- second moment
  have hpair : ∀ p ∈ I ×ˢ I, (∫ x in (-X₀)..X₀, Fn γ Q N p.1 x * Fn γ Q N p.2 x) ≤
      (V + ε₂) + (if ¬ Good γ Q T p.1 p.2 then (Q : ℝ) ^ (K + 1) * (V + ε₁) else 0) := by
    intro p hp
    rw [mem_product] at hp
    by_cases hg : Good γ Q T p.1 p.2
    · rw [if_neg (not_not.2 hg), add_zero]
      linarith [(abs_le.1 (moment_two_good hQ N p.1 p.2 X₀ hT hg)).2]
    · rw [if_pos hg]
      have h1 : (∫ x in (-X₀)..X₀, Fn γ Q N p.1 x * Fn γ Q N p.2 x) ≤
          ∫ x in (-X₀)..X₀, Fn γ Q N p.1 x * (Q : ℝ) ^ (K + 1) :=
        intervalIntegral.integral_mono_on (by linarith)
          (hii _ ((continuous_Fn γ Q N p.1).mul (continuous_Fn γ Q N p.2)))
          (hii _ ((continuous_Fn γ Q N p.1).mul continuous_const)) fun x _ =>
            mul_le_mul_of_nonneg_left (Fn_le hQ N p.2 x) (Fn_nonneg γ Q N p.1 x)
      rw [intervalIntegral.integral_mul_const] at h1
      have h2 := (abs_le.1 (hF1 p.1 hp.1)).2
      have hV0 : 0 ≤ V + ε₂ := by positivity
      have hQK : (0 : ℝ) ≤ (Q : ℝ) ^ (K + 1) := by positivity
      nlinarith
  have hbad := bad_count (γ := γ) N Q hD hTT₁ hfreq hcount
  set nb := ((((Ico N (2 * N)) ×ˢ (Ico N (2 * N))).filter
    (fun p : ℕ × ℕ => ¬ Good γ Q T p.1 p.2)).card : ℝ) with hnb
  have hG2 : (∫ x in (-X₀)..X₀, G x ^ 2) ≤
      (N : ℝ) ^ 2 * (V + ε₂) + nb * ((Q : ℝ) ^ (K + 1) * (V + ε₁)) := by
    have e : ∀ x, G x ^ 2 = ∑ p ∈ I ×ˢ I, Fn γ Q N p.1 x * Fn γ Q N p.2 x := fun x => by
      rw [hG, sq, sum_mul_sum, sum_product]
    simp_rw [e]
    rw [intervalIntegral.integral_finsetSum fun p _ =>
      hii _ ((continuous_Fn γ Q N p.1).mul (continuous_Fn γ Q N p.2))]
    refine (sum_le_sum hpair).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_const, card_product, nsmul_eq_mul, ← sum_filter, sum_const,
      nsmul_eq_mul, hnb]
    push_cast
    rw [hIcard]; ring
  have hvar : (∫ x in (-X₀)..X₀, (G x - N) ^ 2) ≤
      (N : ℝ) ^ 2 * (ε₂ + 2 * ε₁) + nb * ((Q : ℝ) ^ (K + 1) * (V + ε₁)) := by
    have e : ∀ x, (G x - N) ^ 2 = G x ^ 2 - 2 * N * G x + (N : ℝ) ^ 2 := fun x => by ring
    simp_rw [e]
    have i1 : IntervalIntegrable (fun x => G x ^ 2 - 2 * N * G x) volume (-X₀) X₀ :=
      hii _ (by fun_prop)
    have i2 : IntervalIntegrable (fun x => G x ^ 2) volume (-X₀) X₀ := hii _ (by fun_prop)
    have i3 : IntervalIntegrable (fun x => 2 * (N : ℝ) * G x) volume (-X₀) X₀ :=
      hii _ (by fun_prop)
    have i4 : IntervalIntegrable (fun _ => (N : ℝ) ^ 2) volume (-X₀) X₀ := hii _ (by fun_prop)
    rw [intervalIntegral.integral_add i1 i4, intervalIntegral.integral_sub i2 i3,
      intervalIntegral.integral_const_mul, hconst]
    nlinarith
  -- the majorant `U`
  have hU1 : (∫ x in (-X₀)..X₀, U x) ≤ N * (((K : ℝ) + 1) * (V + ε₁) / (4 * Q * ρ ^ 2)) := by
    rw [hU, intervalIntegral.integral_finsetSum fun n _ => hii _ (continuous_Un γ L Q N n)]
    calc ∑ n ∈ I, (∫ x in (-X₀)..X₀, Un γ L Q N n x)
        ≤ ∑ _n ∈ I, ((K : ℝ) + 1) * (V + ε₁) / (4 * Q * ρ ^ 2) := by
          refine sum_le_sum fun n hn => ?_
          unfold Un
          have hc : ∀ j₀ : Fin (K + 1), Continuous (fun x => 1 / (4 * Q * ρ ^ 2) *
              ∏ j, fejer (degv γ Q j₀ j) (cj γ j n * x - alv γ N j)) := fun j₀ =>
            continuous_const.mul (continuous_finsetProd _ fun j _ => (continuous_fejer _).comp
              ((continuous_const.mul continuous_id).sub continuous_const))
          rw [intervalIntegral.integral_finsetSum fun j₀ _ => hii _ (hc j₀)]
          calc ∑ j₀ : Fin (K + 1), (∫ x in (-X₀)..X₀, 1 / (4 * Q * ρ ^ 2) *
                ∏ j, fejer (degv γ Q j₀ j) (cj γ j n * x - alv γ N j))
              ≤ ∑ _j₀ : Fin (K + 1), 1 / (4 * Q * ρ ^ 2) * (V + ε₁) := by
                refine sum_le_sum fun j₀ _ => ?_
                rw [intervalIntegral.integral_const_mul]
                have hdeg : ∀ j, 1 ≤ degv γ Q j₀ j ∧ degv γ Q j₀ j ≤ Q := fun j => by
                  unfold degv
                  by_cases hj : j = j₀
                  · rw [hj, Function.update_self]; exact ⟨le_rfl, hQ⟩
                  · rw [Function.update_of_ne hj]; exact ⟨hQ, le_rfl⟩
                have := (abs_le.1 (moment_one Q N n (degv γ Q j₀) hdeg X₀ hT₁ (hfreq n hn))).2
                exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = ((K : ℝ) + 1) * (V + ε₁) / (4 * Q * ρ ^ 2) := by
                rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
      _ = _ := by rw [sum_const, nsmul_eq_mul, hIcard]
  -- pointwise bound on the bad set
  set W : ℝ → ℝ := fun x => (G x - N) ^ 2 / (N : ℝ) ^ 2 + U x / N with hW
  have hWc : Continuous W := ((hGc.sub continuous_const).pow 2).div_const _ |>.add
    (hUc.div_const _)
  have hW0 : ∀ x, 0 ≤ W x := fun x => by
    have : 0 ≤ U x := sum_nonneg fun n _ => Un_nonneg hL hN1 Q n x
    rw [hW]; positivity
  have hbadW : badSet γ L X₀ r ⊆ {x | 3 / 4 ≤ W x} ∩ Set.Icc (-X₀) X₀ := by
    intro x hx
    refine ⟨?_, hx.1⟩
    have hGU : G x ≤ U x := sum_le_sum fun n hn => by
      rw [hI, mem_Ico] at hn
      have := hx.2 n (by rw [← hN]; exact hn.1) (by rw [pow_succ, ← hN]; omega)
      rw [← hN] at this
      exact Fn_le_Un hL hN1 hQ n this
    have hN0 : (0 : ℝ) < N := by linarith
    show 3 / 4 ≤ (G x - N) ^ 2 / (N : ℝ) ^ 2 + U x / N
    have e1 : (G x - N) ^ 2 / (N : ℝ) ^ 2 = ((G x - N) / N) ^ 2 := by rw [div_pow]
    have e2 : 1 + (G x - N) / N ≤ U x / N := by
      rw [show (1 : ℝ) + (G x - N) / N = G x / N by field_simp; ring]
      exact div_le_div_of_nonneg_right hGU hN0.le
    rw [e1]
    nlinarith [sq_nonneg ((G x - N) / N + 1 / 2)]
  -- Markov's inequality
  set μ := volume.restrict (Set.Icc (-X₀) X₀) with hμ
  have hWint : Integrable W μ := hWc.integrableOn_Icc
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall hW0) hWint (3 / 4)
  have hint_eq : ∫ x, W x ∂μ = ∫ x in (-X₀)..X₀, W x := by
    rw [hμ, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  have hWbound : (∫ x in (-X₀)..X₀, W x) ≤ (ε₂ + 2 * ε₁) +
      nb * ((Q : ℝ) ^ (K + 1) * (V + ε₁)) / (N : ℝ) ^ 2 +
        ((K : ℝ) + 1) * (V + ε₁) / (4 * Q * ρ ^ 2) := by
    have hN0 : (0 : ℝ) < N := by linarith
    have i1 : IntervalIntegrable (fun x => (G x - N) ^ 2 / (N : ℝ) ^ 2) volume (-X₀) X₀ :=
      hii _ (by fun_prop)
    have i2 : IntervalIntegrable (fun x => U x / N) volume (-X₀) X₀ := hii _ (by fun_prop)
    rw [hW, intervalIntegral.integral_add i1 i2, intervalIntegral.integral_div,
      intervalIntegral.integral_div]
    have h1 : (∫ x in (-X₀)..X₀, (G x - N) ^ 2) / (N : ℝ) ^ 2 ≤
        (ε₂ + 2 * ε₁) + nb * ((Q : ℝ) ^ (K + 1) * (V + ε₁)) / (N : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
      linarith
    have h2 : (∫ x in (-X₀)..X₀, U x) / N ≤ ((K : ℝ) + 1) * (V + ε₁) / (4 * Q * ρ ^ 2) := by
      rw [div_le_iff₀ hN0]; linarith
    linarith
  have hfin : μ {x | 3 / 4 ≤ W x} ≠ ⊤ := by
    refine ((measure_mono (Set.subset_univ _)).trans_lt ?_).ne
    rw [hμ, Measure.restrict_apply_univ]; exact measure_Icc_lt_top
  calc volume (badSet γ L X₀ r) ≤ volume ({x | 3 / 4 ≤ W x} ∩ Set.Icc (-X₀) X₀) :=
        measure_mono hbadW
    _ ≤ μ {x | 3 / 4 ≤ W x} := Measure.le_restrict_apply _ _
    _ = ENNReal.ofReal (μ.real {x | 3 / 4 ≤ W x}) := (ENNReal.ofReal_toReal hfin).symm
    _ ≤ _ := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hint_eq] at hmarkov
      have hnbb : nb * ((Q : ℝ) ^ (K + 1) * (V + ε₁)) ≤
          (N * (2 * Q) ^ (2 * (K + 1)) * D) * ((Q : ℝ) ^ (K + 1) * (V + ε₁)) :=
        mul_le_mul_of_nonneg_right hbad (by positivity)
      have : nb * ((Q : ℝ) ^ (K + 1) * (V + ε₁)) / (N : ℝ) ^ 2 ≤
          (N * (2 * Q) ^ (2 * (K + 1)) * D) * ((Q : ℝ) ^ (K + 1) * (V + ε₁)) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnbb (by positivity)
      linarith


/-! ## The second-moment estimate -/

set_option maxHeartbeats 400000 in
/-- Paper, proof of Theorem \ref{IB:thm:413}\ref{IB:413a}: the second-moment estimate
`Kmrr25.Q413a.SecondMomentBound γ` holds for every non-integer `γ > 0`. -/
theorem secondMomentBound {γ : ℝ} (hγ : 0 < γ) (hγZ : ∀ m : ℤ, γ ≠ m) :
    SecondMomentBound γ := by
  intro L hL X₀ hX₀
  obtain ⟨b, B, hb, hB, hfr⟩ := freq hγZ
  obtain ⟨b', B', hb', hB', hdfr⟩ := dfreq hγZ
  set k := ⌊γ⌋₊ with hk
  set ς := γ - k with hς
  have hkγ : (k : ℝ) ≤ γ := Nat.floor_le hγ.le
  have hkne : (k : ℝ) ≠ γ := fun h => hγZ k (by rw [← h]; norm_cast)
  have hς0 : 0 < ς := by rw [hς]; exact sub_pos.2 (lt_of_le_of_ne hkγ hkne)
  have hς1 : ς < 1 := by rw [hς]; linarith [Nat.lt_floor_add_one γ]
  set θ := ς / (32 * ((k : ℝ) + 1)) with hθ
  have hθ0 : 0 < θ := by positivity
  set c₁ := 2 / (π * b) with hc₁
  set c₂ := 4 / (b' * 2 ^ (ς - 1)) with hc₂
  set c₃ := (4 : ℝ) ^ θ / θ with hc₃
  set A3 := 4 ^ (k + 1) * (2 * X₀ + c₁) * (c₂ + 1) with hA3
  set A4 := ((k : ℝ) + 1) * (2 * X₀ + c₁) * (16 * ((k : ℝ) + 1) * (L : ℝ) ^ k) ^ 2 * c₃ ^ 2 / 2
    with hA4
  set C := 4 / 3 * (1 / π + 2 * c₁ + A3 + A4) with hC
  set M := max 2 (max (2 / b) (max (2 * ((k : ℝ) + 1) * B / b) (2 * ((k : ℝ) + 1) * B' / b')))
    with hM
  have key : ∀ r : ℕ, M ≤ (((2 ^ r : ℕ) : ℝ) ^ θ) →
      volume (badSet γ L X₀ r) ≤ ENNReal.ofReal (C / (((2 ^ r : ℕ) : ℝ) ^ θ) ^ 2) := by
    intro r hMu
    set N : ℕ := 2 ^ r with hNdef
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (N : ℝ) ^ θ := ⟨_, rfl⟩
    rw [← hu] at hMu ⊢
    have hN1 : 1 ≤ N := Nat.one_le_two_pow
    have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hx0 : (0 : ℝ) < N := by linarith
    have hu2 : 2 ≤ u := le_trans (le_max_left _ _) hMu
    have hu1 : 1 ≤ u := by linarith
    have hu0 : 0 < u := by linarith
    have hub : 2 / b ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMu
    have huB : 2 * ((k : ℝ) + 1) * B / b ≤ u := le_trans (le_trans (le_trans (le_max_left _ _)
      (le_max_right _ _)) (le_max_right _ _)) hMu
    have huB' : 2 * ((k : ℝ) + 1) * B' / b' ≤ u := le_trans (le_trans (le_trans
      (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hMu
    have hupow : ∀ i j : ℕ, i ≤ j → u ^ i ≤ u ^ j := fun i j h => pow_le_pow_right₀ hu1 h
    have hxς : (N : ℝ) ^ ς = u ^ (32 * (k + 1)) := by
      rw [hu, ← Real.rpow_mul_natCast hx0.le]; congr 1; rw [hθ]; push_cast; field_simp
    have hxu : u ^ (32 * (k + 1)) ≤ N := by
      rw [← hxς]
      calc (N : ℝ) ^ ς ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hς1.le
        _ = N := Real.rpow_one _
    -- the parameter `Q`
    set Q : ℕ := ⌊u ^ 4⌋₊ with hQdef
    have hu16 : (16 : ℝ) ≤ u ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) hu2 4; norm_num at this; linarith
    have hQu : (Q : ℝ) ≤ u ^ 4 := Nat.floor_le (by positivity)
    have hQl : u ^ 4 / 2 ≤ Q := by
      have := Nat.lt_floor_add_one (u ^ 4)
      linarith
    have hQ1 : 1 ≤ Q := by
      have : (1 : ℝ) ≤ Q := by linarith
      exact_mod_cast this
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
    clear_value Q
    have hcond : ∀ B₀ b₀ : ℝ, 0 < b₀ → 2 * ((k : ℝ) + 1) * B₀ / b₀ ≤ u → ∀ s : ℝ,
        (N : ℝ) ≤ s → 2 * ((k : ℝ) + 1) * Q * B₀ ≤ b₀ * s := by
      intro B₀ b₀ hb₀ hu' s hs
      have h1 : 2 * ((k : ℝ) + 1) * B₀ ≤ u * b₀ := (div_le_iff₀ hb₀).1 hu'
      have h2 : u ^ 5 ≤ N := (hupow 5 _ (by omega)).trans hxu
      have hB₀ : 0 ≤ 2 * ((k : ℝ) + 1) * B₀ ∨ 2 * ((k : ℝ) + 1) * B₀ < 0 := le_or_gt _ _
      rcases hB₀ with hB₀ | hB₀
      · calc 2 * ((k : ℝ) + 1) * Q * B₀ = (2 * ((k : ℝ) + 1) * B₀) * Q := by ring
          _ ≤ (u * b₀) * u ^ 4 := mul_le_mul h1 hQu hQ0.le (by positivity)
          _ = b₀ * u ^ 5 := by ring
          _ ≤ b₀ * s := by gcongr; linarith
      · have : 0 ≤ b₀ * s := by have : (0 : ℝ) ≤ s := by linarith
                                positivity
        nlinarith
    -- the parameters `T`, `T₁`, `δ`, `D`
    set T : ℝ := u ^ (16 * (k + 1)) with hT
    set T₁ : ℝ := b / 2 * u ^ (32 * (k + 1)) with hT₁
    set δ : ℝ := b' / 2 * (2 * (N : ℝ)) ^ (ς - 1) with hδ
    set D : ℝ := 2 * T / δ + 1 with hD
    have hT0 : 0 < T := by positivity
    have hδ0 : 0 < δ := by positivity
    have hD0 : 0 ≤ D := by positivity
    have hTT₁ : T ≤ T₁ := by
      have h1 : 1 ≤ b / 2 * u ^ (16 * (k + 1)) := by
        have : 2 / b ≤ u ^ (16 * (k + 1)) := hub.trans (by simpa using hupow 1 _ (by omega))
        rw [div_le_iff₀ hb] at this; linarith
      calc T = 1 * u ^ (16 * (k + 1)) := by rw [hT]; ring
        _ ≤ (b / 2 * u ^ (16 * (k + 1))) * u ^ (16 * (k + 1)) := by gcongr
        _ = T₁ := by
          rw [hT₁, show 32 * (k + 1) = 16 * (k + 1) + 16 * (k + 1) by ring, pow_add]; ring
    clear_value T T₁ δ D
    have hfreq : ∀ n ∈ Ico N (2 * N), ∀ ℓ : Fin (k + 1) → ℤ, ℓ ≠ 0 → (∀ j, |ℓ j| < Q) →
        T₁ ≤ |Xi γ n ℓ| := by
      intro n hn ℓ hℓ hℓQ
      rw [mem_Ico] at hn
      have hn1 : (N : ℝ) ≤ n := by exact_mod_cast hn.1
      have hℓQ' : ∀ j, |(ℓ j : ℝ)| ≤ Q := fun j => by
        have := hℓQ j; rw [← Int.cast_abs]; exact_mod_cast this.le
      have := hfr Q n ℓ hℓ hℓQ' (hx1.trans hn1) (hcond B b hb huB n hn1)
      have h2 : (N : ℝ) ^ ς ≤ (n : ℝ) ^ ς := Real.rpow_le_rpow hx0.le hn1 hς0.le
      rw [hxς] at h2
      calc T₁ = b / 2 * u ^ (32 * (k + 1)) := hT₁
        _ ≤ b / 2 * (n : ℝ) ^ ς := by gcongr
        _ ≤ _ := this
    have hcount : ∀ ℓ' : Fin (k + 1) → ℤ, ℓ' ≠ 0 → (∀ j, |ℓ' j| < Q) → ∀ A : ℝ,
        (((Ico N (2 * N)).filter (fun n' : ℕ => |A + Xi γ n' ℓ'| < T)).card : ℝ) ≤ D := by
      intro ℓ' hℓ' hℓQ A
      have hℓQ' : ∀ j, |(ℓ' j : ℝ)| ≤ Q := fun j => by
        have := hℓQ j; rw [← Int.cast_abs]; exact_mod_cast this.le
      rw [hD]
      refine count_close γ N hN1 ℓ' A T δ hT0.le hδ0 fun s hs1 hs2 => ?_
      have := hdfr Q s ℓ' hℓ' hℓQ' (hx1.trans hs1) (hcond B' b' hb' huB' s hs1)
      have h2 : (2 * (N : ℝ)) ^ (ς - 1) ≤ s ^ (ς - 1) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hs2 (by linarith)
      calc δ = b' / 2 * (2 * (N : ℝ)) ^ (ς - 1) := hδ
        _ ≤ b' / 2 * s ^ (ς - 1) := by gcongr
        _ ≤ _ := this
    have hmain := bad_measure_le (γ := γ) hL hX₀ r N Q rfl hQ1 hT0 hTT₁ hD0 hfreq hcount
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hk]
    have hm1 : 1 ≤ k + 1 := by omega
    clear hfreq hcount hmain hfr hdfr
    have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
    have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
    have hc₃0 : 0 ≤ c₃ := by rw [hc₃]; positivity
    have hA30 : 0 ≤ A3 := by rw [hA3]; positivity
    clear_value A3 A4 C c₁ c₂ c₃ N
    generalize hm : k + 1 = m at hxς hxu hT hT₁ hA3 hm1 ⊢
    have hb2 : 0 < b / 2 := by positivity
    have hT₁0 : 0 < T₁ := hT0.trans_le hTT₁
    have hupa : ∀ i j l : ℕ, i = j + l → u ^ i = u ^ j * u ^ l := fun i j l h => by
      rw [h, pow_add]
    -- `ε₁`
    have hQk : (Q : ℝ) ^ m ≤ u ^ (4 * m) := by
      rw [pow_mul u 4 m]; exact pow_le_pow_left₀ hQ0.le hQu _
    have hQk2 : (Q : ℝ) ^ (2 * m) ≤ u ^ (8 * m) := by
      rw [show 8 * m = 4 * (2 * m) by ring, pow_mul u 4 (2 * m)]
      exact pow_le_pow_left₀ hQ0.le hQu _
    have hε₁ : (Q : ℝ) ^ m / (π * T₁) ≤ c₁ / u ^ 2 := by
      calc (Q : ℝ) ^ m / (π * T₁) ≤ u ^ (4 * m) / (π * T₁) := by gcongr
        _ = c₁ / u ^ (28 * m) := by
          rw [hT₁, hc₁, hupa (32 * m) (4 * m) (28 * m) (by ring)]
          field_simp
        _ ≤ c₁ / u ^ 2 := div_le_div_of_nonneg_left hc₁0 (by positivity) (hupow 2 _ (by omega))
    have hε₁' : (Q : ℝ) ^ m / (π * T₁) ≤ c₁ := by
      exact hε₁.trans (div_le_self hc₁0 (one_le_pow₀ hu1))
    have hε₂ : (Q : ℝ) ^ (2 * m) / (π * T) ≤ (1 / π) / u ^ 2 := by
      calc (Q : ℝ) ^ (2 * m) / (π * T) ≤ u ^ (8 * m) / (π * T) := by gcongr
        _ = (1 / π) / u ^ (8 * m) := by
          rw [hT, hupa (16 * m) (8 * m) (8 * m) (by ring)]
          field_simp
        _ ≤ (1 / π) / u ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (hupow 2 _ (by omega))
    -- the bad-pair term
    have hδN : δ * N = b' / 2 * 2 ^ (ς - 1) * u ^ (32 * m) := by
      rw [hδ, Real.mul_rpow (by norm_num) hx0.le, ← hxς, Real.rpow_sub_one hx0.ne']
      field_simp
    have hDN : D / N ≤ (c₂ + 1) / u ^ (16 * m) := by
      have e : D / N = c₂ / u ^ (16 * m) + 1 / N := by
        rw [hD, add_div, div_div, hδN, hc₂, hT,
          hupa (32 * m) (16 * m) (16 * m) (by ring)]
        field_simp
        ring
      have h1 : 1 / (N : ℝ) ≤ 1 / u ^ (16 * m) :=
        one_div_le_one_div_of_le (by positivity) ((hupow _ _ (by omega)).trans hxu)
      rw [e, add_div]
      linarith only [h1]
    have hP : (2 * (Q : ℝ)) ^ (2 * m) * (Q : ℝ) ^ m ≤
        4 ^ m * u ^ (12 * m) := by
      have h4 : (2 * (Q : ℝ)) ^ (2 * m) = 4 ^ m * (Q : ℝ) ^ (2 * m) := by
        rw [mul_pow, pow_mul]; norm_num
      rw [h4, hupa (12 * m) (8 * m) (4 * m) (by ring), mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hQk2 hQk (by positivity) (by positivity))
        (by positivity)
    have hE : 2 * X₀ + (Q : ℝ) ^ m / (π * T₁) ≤ 2 * X₀ + c₁ := by linarith only [hε₁']
    have hE0 : 0 ≤ 2 * X₀ + (Q : ℝ) ^ m / (π * T₁) := by positivity
    have h3 : (N * (2 * Q) ^ (2 * m) * D) *
        ((Q : ℝ) ^ m * (2 * X₀ + (Q : ℝ) ^ m / (π * T₁))) / (N : ℝ) ^ 2 ≤
          A3 / u ^ 2 := by
      have e : (N * (2 * Q) ^ (2 * m) * D) *
          ((Q : ℝ) ^ m * (2 * X₀ + (Q : ℝ) ^ m / (π * T₁))) / (N : ℝ) ^ 2 =
          ((2 * (Q : ℝ)) ^ (2 * m) * (Q : ℝ) ^ m) *
            (2 * X₀ + (Q : ℝ) ^ m / (π * T₁)) * (D / N) := by
        field_simp
      rw [e]
      calc ((2 * (Q : ℝ)) ^ (2 * m) * (Q : ℝ) ^ m) *
            (2 * X₀ + (Q : ℝ) ^ m / (π * T₁)) * (D / N)
          ≤ (4 ^ m * u ^ (12 * m)) * (2 * X₀ + c₁) *
              ((c₂ + 1) / u ^ (16 * m)) := by
            gcongr
        _ = A3 / u ^ (4 * m) := by
          rw [hA3, hupa (16 * m) (12 * m) (4 * m) (by ring)]
          field_simp
        _ ≤ A3 / u ^ 2 := by
          have h42 : u ^ 2 ≤ u ^ (4 * m) := hupow 2 (4 * m) (by omega)
          exact div_le_div_of_nonneg_left hA30 (by positivity) h42
    -- the `U` term
    have hlog0 : 0 < Real.log (4 * N) := Real.log_pos (by linarith only [hx1])
    have hlog : Real.log (4 * N) ≤ c₃ * u := by
      have := Real.log_le_rpow_div (x := 4 * N) (by positivity) hθ0
      rw [Real.mul_rpow (by norm_num) hx0.le, ← hu] at this
      rw [hc₃]; calc _ ≤ _ := this
        _ = _ := by ring
    have hρ : 1 / rho γ L N ^ 2 = (16 * ((k : ℝ) + 1) * (L : ℝ) ^ k) ^ 2 * Real.log (4 * N) ^ 2 := by
      rw [rho, eta, ← hk]
      field_simp
    have h4 : ((k : ℝ) + 1) * (2 * X₀ + (Q : ℝ) ^ m / (π * T₁)) /
        (4 * Q * rho γ L N ^ 2) ≤ A4 / u ^ 2 := by
      have hρ0 := rho_pos (γ := γ) hL hN1
      have e : ((k : ℝ) + 1) * (2 * X₀ + (Q : ℝ) ^ m / (π * T₁)) /
          (4 * Q * rho γ L N ^ 2) = ((k : ℝ) + 1) * (2 * X₀ + (Q : ℝ) ^ m / (π * T₁)) /
            (4 * Q) * (1 / rho γ L N ^ 2) := by
        field_simp
      rw [e, hρ]
      have hl2 : Real.log (4 * N) ^ 2 ≤ (c₃ * u) ^ 2 := pow_le_pow_left₀ hlog0.le hlog 2
      calc ((k : ℝ) + 1) * (2 * X₀ + (Q : ℝ) ^ m / (π * T₁)) / (4 * Q) *
            ((16 * ((k : ℝ) + 1) * (L : ℝ) ^ k) ^ 2 * Real.log (4 * N) ^ 2)
          ≤ ((k : ℝ) + 1) * (2 * X₀ + c₁) / (4 * (u ^ 4 / 2)) *
            ((16 * ((k : ℝ) + 1) * (L : ℝ) ^ k) ^ 2 * (c₃ * u) ^ 2) := by
            gcongr
        _ = A4 / u ^ 2 := by
          rw [hA4]; field_simp; ring
    -- conclusion
    have eC : C / u ^ 2 = 4 / 3 * ((1 / π) / u ^ 2 + 2 * (c₁ / u ^ 2) + A3 / u ^ 2 +
        A4 / u ^ 2) := by
      rw [hC]; field_simp
    rw [eC]
    gcongr ?_ * ?_
    linarith only [hε₁, hε₂, h3, h4]
  have hu : Tendsto (fun r : ℕ => (((2 ^ r : ℕ) : ℝ) ^ θ)) atTop atTop :=
    (tendsto_rpow_atTop hθ0).comp (tendsto_natCast_atTop_atTop.comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
  have hlim : Tendsto (fun r : ℕ => ENNReal.ofReal (C / (((2 ^ r : ℕ) : ℝ) ^ θ) ^ 2)) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp hu))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hu.eventually_ge_atTop M] with r hr using key r hr


/-! ## Theorem \ref{IB:thm:413}: unconditional statements -/

/-- Paper, Theorem \ref{IB:thm:413}\ref{IB:413a}: if `γ > 0` is not an integer, then for almost
every `x ∈ ℝ` the set `A_x = {n : {n^γ x} ≤ 1 / log n}` is thick. -/
theorem thm413a (γ : ℝ) (hγ : 0 < γ) (hγZ : ∀ m : ℤ, γ ≠ m) : ∀ᵐ x : ℝ, Thick (Ax γ x) :=
  thm413a_of_secondMoment γ hγ hγZ (secondMomentBound hγ hγZ)

/-- Paper, Theorem \ref{IB:thm:413}\ref{IB:413a}, second clause: if `γ > 0` is not an integer,
then for almost every `x` the set `A_x` contains `B + C` for some infinite `B, C ⊆ ℕ`. -/
theorem thm413a_sumset (γ : ℝ) (hγ : 0 < γ) (hγZ : ∀ m : ℤ, γ ≠ m) :
    ∀ᵐ x : ℝ, ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ Ax γ x :=
  thm413a_sumset_of_secondMoment γ hγ hγZ (secondMomentBound hγ hγZ)

lemma ae_irrational : ∀ᵐ x : ℝ, Irrational x := by
  have : {x : ℝ | ¬ Irrational x} ⊆ Set.range ((↑) : ℚ → ℝ) := fun x hx => by
    simpa [Irrational] using hx
  exact measure_mono_null this ((Set.countable_range _).measure_zero volume)

/-- Paper, Theorem \ref{IB:thm:413}, final statement: for `γ > 0`, the set `A_x` contains an
infinite sumset `B + C` (`B, C ⊆ ℕ` infinite) for almost every `x ∈ ℝ` if and only if
`γ ∉ ℕ`. -/
theorem thm413_iff (γ : ℝ) (hγ : 0 < γ) :
    (∀ᵐ x : ℝ, ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ Ax γ x) ↔
      ∀ d : ℕ, γ ≠ d := by
  constructor
  · intro h d hd
    obtain ⟨x, ⟨B, C, hB, hC, hsub⟩, hx⟩ := (h.and ae_irrational).exists
    rw [hd] at hsub
    exact thm413b_sumset d x hx B C hB hC hsub
  · intro h
    refine thm413a_sumset γ hγ fun m hm => ?_
    rcases Int.eq_nat_or_neg m with ⟨d, rfl | rfl⟩
    · exact h d (by rw [hm]; norm_cast)
    · have : (0 : ℝ) < ((-(d : ℤ) : ℤ) : ℝ) := hm ▸ hγ
      push_cast at this
      linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

end Kmrr25.Q413SM
