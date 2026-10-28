import Kmrr25.ThmKErgJ

/-!
# Theorem K: generic pairs

Paper, Lemma \ref{K:lem:pairs}. Let `π : Y → K` be a *continuous*, everywhere equivariant
Kronecker map for `λ`, and let `y₀` be generic for `λ` along `Φ`. Then along a subsequence of `Φ`,
for `λ`-a.e. `y` the pair `(y₀, y)` is generic for `J_{π y - π y₀}`.

The proof follows the paper, with one change: the spectral theorem for `g` is replaced by the
decomposition `g = g̃ ∘ π + g^⊥`; the weakly mixing part `g^⊥` is handled by
`WeakMixing.tendsto_l2_avg`, and the Kronecker part by harmonic analysis on `K`
(trigonometric approximation, Parseval) together with the van der Corput estimate
(`vdc_estimate`) for the weights `γ ↦ f''(T^γ y₀)`.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

open Q516

universe u

/-! ## The van der Corput estimate -/

section VdC

variable {Γ : Type*} [AddCommGroup Γ]

lemma avg_mul_conj_avg {ι : Type*} (H : Finset ι) (a : ι → ℂ) :
    (avg H a) * conj (avg H a) = avg H fun h => avg H fun h' => a h * conj (a h') := by
  simp only [avg, Complex.real_smul, map_mul, Complex.conj_ofReal, map_sum, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
  ring

/-- The van der Corput estimate, uniform in the character `ψ`:
`|𝔼_{Φ_N} u ψ|² ≤ 𝔼_{h,h' ∈ H} |𝔼_{γ ∈ Φ_N} u(γ+h) ū(γ+h')| + e`, where the error
`e = 2Bε + ε²`, `ε = 2B ∑_{h∈H} |Φ_N ∖ (h + Φ_N)| / |Φ_N|`, does not depend on `ψ`. -/
lemma vdc_estimate (F H : Finset Γ) (hF : F.Nonempty) (hH : H.Nonempty) (u ψ : Γ → ℂ) {B : ℝ}
    (hB : ∀ γ, ‖u γ‖ ≤ B) (hψ : ∀ a b, ψ (a + b) = ψ a * ψ b) (hψ1 : ∀ a, ‖ψ a‖ = 1) :
    ‖avg F fun γ => u γ * ψ γ‖ ^ 2 ≤
      (avg H fun h => avg H fun h' => ‖avg F fun γ => u (γ + h) * conj (u (γ + h'))‖) +
        (2 * B * (2 * B * ∑ h ∈ H, (#(F \ F.image (h + ·)) : ℝ) / #F) +
          (2 * B * ∑ h ∈ H, (#(F \ F.image (h + ·)) : ℝ) / #F) ^ 2) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set v : Γ → ℂ := fun γ => u γ * ψ γ with hv
  have hvB : ∀ γ, ‖v γ‖ ≤ B := fun γ => by rw [hv, norm_mul, hψ1, mul_one]; exact hB γ
  set e : ℝ := 2 * B * ∑ h ∈ H, (#(F \ F.image (h + ·)) : ℝ) / #F with he
  -- shifting by `h ∈ H`
  set A : ℂ := avg F fun γ => avg H fun h => v (γ + h) with hA
  have hshift : ‖avg F v - A‖ ≤ e := by
    have e1 : A = avg H fun h => avg F fun γ => v (h + γ) := by
      simp only [hA, avg, Finset.smul_sum]
      rw [Finset.sum_comm]
      simp only [smul_smul, mul_comm (#F : ℝ)⁻¹, add_comm]
    have e2 : avg F v = avg H fun _ => avg F v := (avg_const hH _).symm
    rw [e1, e2, ← avg_sub']
    refine (norm_avg_le_avg_norm _ _).trans ?_
    have hHc : (0 : ℝ) < #H := by exact_mod_cast hH.card_pos
    calc (avg H fun h => ‖avg F v - avg F fun γ => v (h + γ)‖)
        ≤ avg H fun h => 2 * B * ((#(F \ F.image (h + ·)) : ℝ) / #F) :=
          avg_real_mono fun h _ => by
            rw [norm_sub_rev]; exact norm_avg_shift_sub_le F hF v hvB h
      _ ≤ e := by
          simp only [avg, smul_eq_mul, he, ← Finset.mul_sum]
          rw [← mul_assoc, mul_comm _ (2 * B), mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hs : 0 ≤ ∑ h ∈ H, (#(F \ F.image (h + ·)) : ℝ) / #F :=
            Finset.sum_nonneg fun _ _ => by positivity
          calc (#H : ℝ)⁻¹ * ∑ h ∈ H, (#(F \ F.image (h + ·)) : ℝ) / #F
              ≤ 1 * ∑ h ∈ H, (#(F \ F.image (h + ·)) : ℝ) / #F :=
                mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ (by exact_mod_cast hH.card_pos))
                  hs
            _ = _ := one_mul _
  -- Jensen and the expansion of the square
  have hAsq : ‖A‖ ^ 2 ≤ avg H fun h => avg H fun h' =>
      ‖avg F fun γ => u (γ + h) * conj (u (γ + h'))‖ := by
    refine (norm_avg_sq_le F _).trans ?_
    have hexp : ∀ γ, ‖avg H fun h => v (γ + h)‖ ^ 2 =
        (avg H fun h => avg H fun h' => v (γ + h) * conj (v (γ + h'))).re := by
      intro γ
      rw [← Complex.ofReal_re (‖avg H fun h => v (γ + h)‖ ^ 2), Complex.ofReal_pow,
        ← Complex.mul_conj', avg_mul_conj_avg]
    simp only [hexp]
    have hre : ∀ (G : Γ → ℂ), (avg F fun γ => (G γ).re) = (avg F G).re := fun G => by
      simp [avg, Complex.re_sum]
    rw [hre]
    have hswap : (avg F fun γ => avg H fun h => avg H fun h' => v (γ + h) * conj (v (γ + h'))) =
        avg H fun h => avg H fun h' => ψ h * conj (ψ h') *
          avg F fun γ => u (γ + h) * conj (u (γ + h')) := by
      simp only [avg, Finset.smul_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h' _ => Finset.sum_congr rfl fun γ _ => ?_
      simp only [hv, hψ, map_mul]
      have : ψ γ * conj (ψ γ) = 1 := by rw [Complex.mul_conj', hψ1]; simp
      simp only [Complex.real_smul]
      linear_combination (↑(#F : ℝ)⁻¹ * ↑(#H : ℝ)⁻¹ * ↑(#H : ℝ)⁻¹ * u (γ + h) *
        conj (u (γ + h')) * ψ h * conj (ψ h')) * this
    rw [hswap]
    refine (Complex.re_le_norm _).trans ?_
    refine (norm_avg_le_avg_norm _ _).trans (avg_real_mono fun h _ => ?_)
    refine (norm_avg_le_avg_norm _ _).trans (avg_real_mono fun h' _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj, hψ1, hψ1, one_mul, one_mul]
  -- combine
  have hAB : ‖A‖ ≤ B := by
    refine norm_avg_le _ (fun γ _ => ?_) hB0
    exact norm_avg_le _ (fun h _ => hvB _) hB0
  have h1 : ‖avg F v‖ ≤ ‖A‖ + e := by
    have := norm_sub_norm_le (avg F v) A
    linarith
  have he0 : 0 ≤ e := by
    simp only [he]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  calc ‖avg F v‖ ^ 2 ≤ (‖A‖ + e) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ‖A‖ ^ 2 + 2 * ‖A‖ * e + e ^ 2 := by ring
    _ ≤ _ := by nlinarith [norm_nonneg A]

end VdC

/-! ## Weighted averages on `K` -/

section Weighted

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}

lemma integral_avg_comp_add {φ : KG α → ℝ} (hφ : Integrable φ (haarK α)) {F : Finset Γ}
    (hF : F.Nonempty) : ∫ z, avg F (fun γ => φ (z + kα α γ)) ∂haarK α = ∫ z, φ z ∂haarK α := by
  simp only [avg, smul_eq_mul]
  rw [integral_const_mul, integral_finsetSum _ fun γ _ => hφ.comp_add_right _]
  simp only [integral_haarK_add_real φ]
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hF.card_pos.ne'), one_mul]

/-- `∫ |𝔼_F w(γ) H(z + α γ)|² dm(z) ≤ B² ∫ |H|²` for weights `|w| ≤ B`. -/
lemma integral_norm_weighted_avg_sq_le {H : KG α → ℂ} (hH : Bdd H) (F : Finset Γ) (w : Γ → ℂ)
    {B : ℝ} (hB : ∀ γ, ‖w γ‖ ≤ B) :
    ∫ z, ‖avg F (fun γ => w γ * H (z + kα α γ))‖ ^ 2 ∂haarK α ≤
      B ^ 2 * ∫ z, ‖H z‖ ^ 2 ∂haarK α := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hH2 : Integrable (fun z => ‖H z‖ ^ 2) (haarK α) :=
    (memLp_two_iff_integrable_sq_norm hH.meas.aestronglyMeasurable).1 (hH.memLp 2)
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp only [avg, Finset.sum_empty, smul_zero, norm_zero]
    norm_num
    exact mul_nonneg (by positivity) (integral_nonneg fun z => by positivity)
  have hint : Integrable (fun z => avg F fun γ => B ^ 2 * ‖H (z + kα α γ)‖ ^ 2) (haarK α) := by
    simp only [avg, smul_eq_mul]
    exact (integrable_finsetSum _ fun γ _ => (hH2.comp_add_right _).const_mul _).const_mul _
  calc ∫ z, ‖avg F (fun γ => w γ * H (z + kα α γ))‖ ^ 2 ∂haarK α
      ≤ ∫ z, (avg F fun γ => B ^ 2 * ‖H (z + kα α γ)‖ ^ 2) ∂haarK α := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) hint
          (Eventually.of_forall fun z => ?_)
        refine (norm_avg_sq_le F _).trans (avg_real_mono fun γ _ => ?_)
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB γ) 2)
          (by positivity)
    _ = B ^ 2 * ∫ z, ‖H z‖ ^ 2 ∂haarK α := by
        rw [integral_avg_comp_add (hH2.const_mul (B ^ 2)) hF, integral_const_mul]

/-- Parseval bound: if all character averages `|𝔼_F w(γ) χ(α γ)|²` are `≤ M`, then
`∫ |𝔼_F w(γ) G(z + α γ)|² dm(z) ≤ 4 M ∫ |G|²`. -/
theorem integral_weighted_avg_le {G : KG α → ℂ} (hG : Bdd G) (F : Finset Γ) (w : Γ → ℂ) {B : ℝ}
    (hB : ∀ γ, ‖w γ‖ ≤ B) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ χ ∈ Chars α, ‖avg F (fun γ => w γ * χ (kα α γ))‖ ^ 2 ≤ M) :
    ∫ z, ‖avg F (fun γ => w γ * G (z + kα α γ))‖ ^ 2 ∂haarK α ≤
      4 * M * ∫ z, ‖G z‖ ^ 2 ∂haarK α := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := ε / (2 * B ^ 2 + 4 * M + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨Q, ⟨t, b, ht, rfl⟩, hGQ⟩ := exists_trig_l2_approx hG hδ0
  have hQb : Bdd fun z => ∑ χ ∈ t, b χ * χ z := IsTrig.bdd α ⟨t, b, ht, rfl⟩
  have hGQb : Bdd fun z => G z - ∑ χ ∈ t, b χ * χ z := hG.sub hQb
  have hχb : ∀ χ ∈ t, Bdd fun z : KG α => χ z := fun χ hχ =>
    ⟨χ.continuous.measurable, 1, fun z => (Chars.norm_eq (ht hχ) z).le⟩
  -- split `G = (G - Q) + Q`
  have hsplit : ∀ z, avg F (fun γ => w γ * G (z + kα α γ)) =
      avg F (fun γ => w γ * (G (z + kα α γ) - ∑ χ ∈ t, b χ * χ (z + kα α γ))) +
        ∑ χ ∈ t, (b χ * avg F (fun γ => w γ * χ (kα α γ))) * χ z := by
    intro z
    have : (fun γ => w γ * G (z + kα α γ)) = fun γ =>
        w γ * (G (z + kα α γ) - ∑ χ ∈ t, b χ * χ (z + kα α γ)) +
          w γ * ∑ χ ∈ t, b χ * χ (z + kα α γ) := by funext γ; ring
    rw [this, avg_add']
    congr 1
    simp only [avg, Finset.mul_sum, Finset.smul_sum, Finset.sum_mul, Complex.real_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ hχ => Finset.sum_congr rfl fun γ _ => ?_
    rw [Chars.map_add (ht hχ)]
    ring
  have hm1 : Bdd fun z => avg F (fun γ => w γ * (G (z + kα α γ) - ∑ χ ∈ t, b χ * χ (z + kα α γ))) :=
    Bdd.avg F fun γ _ => (Bdd.const (w γ)).mul (hGQb.comp (measurable_add_const _))
  have hm2 : Bdd fun z => ∑ χ ∈ t, (b χ * avg F (fun γ => w γ * χ (kα α γ))) * χ z :=
    Bdd.sum t fun χ hχ => (Bdd.const _).mul (hχb χ hχ)
  have h1 := integral_norm_add_sq_le (μ := haarK α) (hm1.memLp 2) (hm2.memLp 2)
  simp only [← hsplit] at h1
  have h2 := integral_norm_weighted_avg_sq_le hGQb F w hB
  have h3 : ∫ z, ‖∑ χ ∈ t, (b χ * avg F (fun γ => w γ * χ (kα α γ))) * χ z‖ ^ 2 ∂haarK α ≤
      M * ∫ z, ‖∑ χ ∈ t, b χ * χ z‖ ^ 2 ∂haarK α := by
    rw [integral_norm_sum_chars_sq ht, integral_norm_sum_chars_sq ht, Finset.mul_sum]
    refine Finset.sum_le_sum fun χ hχ => ?_
    rw [norm_mul, mul_pow, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM χ (ht hχ)) (by positivity)
  have h4 : ∫ z, ‖∑ χ ∈ t, b χ * χ z‖ ^ 2 ∂haarK α ≤
      2 * ∫ z, ‖G z‖ ^ 2 ∂haarK α + 2 * δ := by
    have := integral_norm_add_sq_le (μ := haarK α) (hG.memLp 2) ((hGQb.memLp 2).neg)
    have e2 : (∫ y, ‖G y + -(G y - ∑ χ ∈ t, b χ * χ y)‖ ^ 2 ∂haarK α) =
        ∫ z, ‖∑ χ ∈ t, b χ * χ z‖ ^ 2 ∂haarK α := by
      congr 1; funext y; congr 2; ring
    simp only [Pi.neg_apply, norm_neg] at this
    rw [e2] at this
    linarith [hGQ.le]
  have hGQ' : ∫ z, ‖G z - ∑ χ ∈ t, b χ * χ z‖ ^ 2 ∂haarK α ≤ δ := hGQ.le
  have hfin : 2 * B ^ 2 * δ + 4 * M * δ ≤ ε := by
    rw [hδ, ← add_mul, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hGQ' (sq_nonneg B)]

/-- The trigonometric part: for a trigonometric polynomial `P`, the averages
`𝔼_γ P(x₀ + α γ) G(z + α γ)` converge in `L²(m_K)` to `∫ P(v) G(v + z - x₀) dm(v)`. -/
theorem tendsto_trig_weighted {P : KG α → ℂ} (hP : IsTrig α P) {G : KG α → ℂ} (hG : Bdd G)
    (x0 : KG α) {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) :
    Tendsto (fun N => ∫ z, ‖avg (Φ N) (fun γ => P (x0 + kα α γ) * G (z + kα α γ)) -
      ∫ v, P v * G (v + (z - x0)) ∂haarK α‖ ^ 2 ∂haarK α) atTop (𝓝 0) := by
  obtain ⟨t, c, ht, rfl⟩ := hP
  have hχb : ∀ χ ∈ t, Bdd fun z : KG α => χ z := fun χ hχ =>
    ⟨χ.continuous.measurable, 1, fun z => (Chars.norm_eq (ht hχ) z).le⟩
  set D : C(KG α, ℂ) → ℕ → KG α → ℂ := fun χ N z =>
    avg (Φ N) (fun γ => χ (z + kα α γ) * G (z + kα α γ)) - ∫ u, χ u * G u ∂haarK α with hD
  have hDl : ∀ χ ∈ t, Tendsto (fun N => ∫ z, ‖D χ N z‖ ^ 2 ∂haarK α) atTop (𝓝 0) := fun χ hχ =>
    tendsto_rotation_avg_l2 ((hχb χ hχ).mul hG) hΦ
  have hDb : ∀ χ ∈ t, ∀ N, Bdd (D χ N) := fun χ hχ N =>
    (Bdd.avg _ fun γ _ => ((hχb χ hχ).mul hG).comp (measurable_add_const _)).sub (Bdd.const _)
  -- the pointwise identity
  have hid : ∀ N z, avg (Φ N) (fun γ => (∑ χ ∈ t, c χ * χ (x0 + kα α γ)) * G (z + kα α γ)) -
      ∫ v, (∑ χ ∈ t, c χ * χ v) * G (v + (z - x0)) ∂haarK α =
      ∑ χ ∈ t, c χ * χ x0 * conj (χ z) * D χ N z := by
    intro N z
    have e1 : ∀ χ ∈ t, ∀ γ, χ (x0 + kα α γ) * G (z + kα α γ) =
        χ x0 * conj (χ z) * (χ (z + kα α γ) * G (z + kα α γ)) := by
      intro χ hχ γ
      rw [Chars.map_add (ht hχ) x0, Chars.map_add (ht hχ) z]
      have := Chars.mul_conj_self (ht hχ) z
      linear_combination (χ x0 * χ (kα α γ) * G (z + kα α γ)) * this.symm
    have e2 : ∀ χ ∈ t, ∫ v, χ v * G (v + (z - x0)) ∂haarK α =
        χ x0 * conj (χ z) * ∫ u, χ u * G u ∂haarK α := by
      intro χ hχ
      rw [← integral_haarK_add (fun v => χ v * G (v + (z - x0))) (x0 - z), ← integral_const_mul]
      congr 1; funext v
      rw [show v + (x0 - z) + (z - x0) = v by abel, Chars.map_add (ht hχ) v (x0 - z),
        sub_eq_add_neg x0 z, Chars.map_add (ht hχ) x0 (-z), ← Chars.conj_eq_inv (ht hχ)]
      ring
    have hint : ∀ χ ∈ t, Integrable (fun v => c χ * χ v * G (v + (z - x0))) (haarK α) :=
      fun χ hχ => (((Bdd.const (c χ)).mul (hχb χ hχ)).mul
        (hG.comp (measurable_add_const _))).integrable
    simp only [Finset.sum_mul]
    rw [integral_finsetSum _ hint]
    simp only [avg, Finset.smul_sum]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have e3 : ∫ v, c χ * χ v * G (v + (z - x0)) ∂haarK α =
        c χ * (χ x0 * conj (χ z) * ∫ u, χ u * G u ∂haarK α) := by
      rw [← e2 χ hχ, ← integral_const_mul]; congr 1; funext v; ring
    rw [e3, hD]
    simp only [avg, Finset.smul_sum, mul_sub, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun γ _ => ?_
      rw [mul_assoc (c χ), e1 χ hχ γ]
      simp only [Complex.real_smul]
      ring
    · ring
  -- the bound
  have hbound : ∀ N, ∫ z, ‖∑ χ ∈ t, c χ * χ x0 * conj (χ z) * D χ N z‖ ^ 2 ∂haarK α ≤
      #t * ∑ χ ∈ t, ‖c χ‖ ^ 2 * ∫ z, ‖D χ N z‖ ^ 2 ∂haarK α := by
    intro N
    have hint : ∀ χ ∈ t, Integrable (fun z => ‖D χ N z‖ ^ 2) (haarK α) := fun χ hχ =>
      (memLp_two_iff_integrable_sq_norm (hDb χ hχ N).meas.aestronglyMeasurable).1
        ((hDb χ hχ N).memLp 2)
    calc _ ≤ ∫ z, (#t : ℝ) * ∑ χ ∈ t, ‖c χ‖ ^ 2 * ‖D χ N z‖ ^ 2 ∂haarK α := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
            ((integrable_finsetSum _ fun χ hχ => (hint χ hχ).const_mul _).const_mul _)
            (Eventually.of_forall fun z => ?_)
          have h1 := norm_sum_le t fun χ => c χ * χ x0 * conj (χ z) * D χ N z
          have h2 := sq_sum_le_card_mul_sum_sq (s := t)
            (f := fun χ => ‖c χ * χ x0 * conj (χ z) * D χ N z‖)
          have h3 : ∀ χ ∈ t, ‖c χ * χ x0 * conj (χ z) * D χ N z‖ ^ 2 = ‖c χ‖ ^ 2 * ‖D χ N z‖ ^ 2 :=
            fun χ hχ => by
              rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Chars.norm_eq (ht hχ),
                Chars.norm_eq (ht hχ)]; ring
          rw [Finset.sum_congr rfl h3] at h2
          calc _ ≤ (∑ χ ∈ t, ‖c χ * χ x0 * conj (χ z) * D χ N z‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) h1 2
            _ ≤ _ := h2
      _ = _ := by
          rw [integral_const_mul, integral_finsetSum _ fun χ hχ => (hint χ hχ).const_mul _]
          simp only [integral_const_mul]
  have hlim : Tendsto (fun N => (#t : ℝ) * ∑ χ ∈ t, ‖c χ‖ ^ 2 * ∫ z, ‖D χ N z‖ ^ 2 ∂haarK α)
      atTop (𝓝 0) := by
    have := (tendsto_finsetSum t fun χ hχ => (hDl χ hχ).const_mul (‖c χ‖ ^ 2)).const_mul
      (#t : ℝ)
    simpa using this
  refine squeeze_zero (fun N => integral_nonneg fun z => by positivity) (fun N => ?_) hlim
  simp only [hid]
  exact hbound N

end Weighted

/-! ## Correlations of perturbed functions and the van der Corput bound along an orbit -/

section Perturb

variable {Γ : Type*} [AddCommGroup Γ]
variable {Y : Type*} [MeasurableSpace Y] [AddAction Γ Y] [MeasurableConstVAdd Γ Y]
variable {μ : Measure Y} [IsProbabilityMeasure μ] [VAddInvariantMeasure Γ Y μ]

lemma norm_integral_mul_conj_le {f g : Y → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ y, f y * conj (g y) ∂μ‖ ≤
      Real.sqrt (∫ y, ‖f y‖ ^ 2 ∂μ) * Real.sqrt (∫ y, ‖g y‖ ^ 2 ∂μ) := by
  rw [← Real.sqrt_mul (integral_nonneg fun y => by positivity)]
  exact Real.le_sqrt_of_sq_le (norm_integral_mul_conj_sq_le hf hg)

/-- Correlations depend continuously on the function in `L²`. -/
lemma norm_corr_sub_le {a b : Y → ℂ} (ha : Bdd a) (hb : Bdd b) (δ : Γ) :
    ‖corr μ a δ - corr μ b δ‖ ≤ Real.sqrt (∫ y, ‖a y - b y‖ ^ 2 ∂μ) *
      (Real.sqrt (∫ y, ‖a y‖ ^ 2 ∂μ) + Real.sqrt (∫ y, ‖b y‖ ^ 2 ∂μ)) := by
  have hc : Bdd fun y => a y - b y := ha.sub hb
  have hcδ : Bdd fun y => a (δ +ᵥ y) - b (δ +ᵥ y) := hc.comp (measurable_const_vadd δ)
  have hbδ : Bdd fun y => b (δ +ᵥ y) := hb.comp (measurable_const_vadd δ)
  have i1 : Integrable (fun y => (a (δ +ᵥ y) - b (δ +ᵥ y)) * conj (a y)) μ :=
    (hcδ.mul ha.conj').integrable
  have i2 : Integrable (fun y => b (δ +ᵥ y) * conj (a y - b y)) μ := (hbδ.mul hc.conj').integrable
  have i3 : Integrable (fun y => a (δ +ᵥ y) * conj (a y)) μ :=
    ((ha.comp (measurable_const_vadd δ)).mul ha.conj').integrable
  have i4 : Integrable (fun y => b (δ +ᵥ y) * conj (b y)) μ := (hbδ.mul hb.conj').integrable
  have e : corr μ a δ - corr μ b δ =
      ∫ y, (a (δ +ᵥ y) - b (δ +ᵥ y)) * conj (a y) ∂μ + ∫ y, b (δ +ᵥ y) * conj (a y - b y) ∂μ := by
    simp only [corr]
    rw [← integral_add i1 i2, ← integral_sub i3 i4]
    congr 1; funext y; simp only [map_sub]; ring
  have hshift : ∀ {c : Y → ℂ}, Bdd c → ∫ y, ‖c (δ +ᵥ y)‖ ^ 2 ∂μ = ∫ y, ‖c y‖ ^ 2 ∂μ :=
    fun _ => integral_vadd_eq_self (fun y => ‖_‖ ^ 2)
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_integral_mul_conj_le (μ := μ) (hcδ.memLp 2) (ha.memLp 2)
  have h2 := norm_integral_mul_conj_le (μ := μ) (hbδ.memLp 2) (hc.memLp 2)
  rw [hshift hc] at h1
  rw [hshift hb] at h2
  nlinarith [Real.sqrt_nonneg (∫ y, ‖a y - b y‖ ^ 2 ∂μ), Real.sqrt_nonneg (∫ y, ‖a y‖ ^ 2 ∂μ),
    Real.sqrt_nonneg (∫ y, ‖b y‖ ^ 2 ∂μ)]

end Perturb

section VdCOrbit

variable {Γ : Type*} [AddCommGroup Γ] [Countable Γ]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [AddAction Γ Y] [ContinuousConstVAdd Γ Y]
variable {μ : Measure Y} [IsProbabilityMeasure μ] [VAddInvariantMeasure Γ Y μ]

/-- Along a generic orbit, character-twisted averages of `F''(T^γ y₀)` are eventually small,
uniformly in the character, provided `F''` has correlations within `ε₁` of a weakly mixing
function. -/
theorem eventually_twisted_avg_le {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) {y0 : Y}
    (hy0 : IsGeneric μ Φ y0) (F'' : C(Y, ℂ)) {W : Y → ℂ} (hWb : Bdd W) (hwm : WeakMixing Γ μ W)
    {ε₁ : ℝ} (hε₁ : ∀ δ : Γ, ‖corr μ F'' δ - corr μ W δ‖ ≤ ε₁) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N in atTop, ∀ ψ : Γ → ℂ, (∀ a b, ψ (a + b) = ψ a * ψ b) → (∀ a, ‖ψ a‖ = 1) →
      ‖avg (Φ N) (fun γ => F'' (γ +ᵥ y0) * ψ γ)‖ ^ 2 ≤ ε₁ + η := by
  obtain ⟨Θ, hΘ⟩ := Q516.exists_folner (G := Γ)
  have hd := tendsto_double_avg (c := fun β => ‖corr (Γ := Γ) μ W β‖) (fun _ => norm_nonneg _)
    hwm hΘ
  obtain ⟨M, hM⟩ := (hd.eventually (gt_mem_nhds (show (0 : ℝ) < η / 3 by positivity))).exists
  set H := Θ M
  have hH : H.Nonempty := hΘ.1 M
  set B := ‖F''‖
  have hB : ∀ y, ‖F'' y‖ ≤ B := fun y => F''.norm_coe_le_norm y
  -- convergence of the inner averages
  have hinner : ∀ h h' : Γ, Tendsto (fun N => avg (Φ N) fun γ =>
      F'' ((γ + h) +ᵥ y0) * conj (F'' ((γ + h') +ᵥ y0))) atTop (𝓝 (corr μ F'' (h - h'))) := by
    intro h h'
    let φ : C(Y, ℂ) := ⟨fun y => F'' (h +ᵥ y) * conj (F'' (h' +ᵥ y)),
      (F''.continuous.comp (continuous_const_vadd h)).mul
        (Complex.continuous_conj.comp (F''.continuous.comp (continuous_const_vadd h')))⟩
    have := hy0.tendsto_complex φ
    rw [show ∫ x, φ x ∂μ = corr μ F'' (h - h') from integral_shift_mul_conj (μ := μ) F'' h h']
      at this
    refine this.congr fun N => ?_
    congr 1; funext γ
    simp only [φ, ContinuousMap.coe_mk, vadd_vadd, add_comm h, add_comm h']
  set V : ℕ → ℝ := fun N => avg H fun h => avg H fun h' =>
    ‖avg (Φ N) fun γ => F'' ((γ + h) +ᵥ y0) * conj (F'' ((γ + h') +ᵥ y0))‖ with hV
  have hVlim : Tendsto V atTop (𝓝 (avg H fun h => avg H fun h' => ‖corr μ F'' (h - h')‖)) := by
    simp only [hV, avg]
    refine tendsto_const_nhds.smul (tendsto_finsetSum _ fun h _ =>
      tendsto_const_nhds.smul (tendsto_finsetSum _ fun h' _ => (hinner h h').norm))
  have hVbound : (avg H fun h => avg H fun h' => ‖corr μ F'' (h - h')‖) < ε₁ + η / 3 := by
    calc (avg H fun h => avg H fun h' => ‖corr μ F'' (h - h')‖)
        ≤ avg H fun h => avg H fun h' => ‖corr (Γ := Γ) μ W (h - h')‖ + ε₁ :=
          avg_real_mono fun h _ => avg_real_mono fun h' _ => by
            have := hε₁ (h - h')
            have := norm_sub_norm_le (corr μ F'' (h - h')) (corr μ W (h - h'))
            linarith
      _ = (avg H fun h => avg H fun h' => ‖corr (Γ := Γ) μ W (h - h')‖) + ε₁ := by
          simp only [avg_add', avg_const hH]
      _ < ε₁ + η / 3 := by linarith
  set e : ℕ → ℝ := fun N => 2 * B * (2 * B * ∑ h ∈ H, (#(Φ N \ (Φ N).image (h + ·)) : ℝ) / #(Φ N)) +
    (2 * B * ∑ h ∈ H, (#(Φ N \ (Φ N).image (h + ·)) : ℝ) / #(Φ N)) ^ 2 with he
  have helim : Tendsto e atTop (𝓝 0) := by
    have h0 : Tendsto (fun N => ∑ h ∈ H, (#(Φ N \ (Φ N).image (h + ·)) : ℝ) / #(Φ N)) atTop
        (𝓝 0) := by
      simpa using tendsto_finsetSum H fun h _ => hΦ.tendsto_defect h
    have := ((h0.const_mul (2 * B)).const_mul (2 * B)).add ((h0.const_mul (2 * B)).pow 2)
    rw [show (0 : ℝ) = 2 * B * (2 * B * 0) + (2 * B * 0) ^ 2 by ring]
    exact this
  filter_upwards [hVlim.eventually (gt_mem_nhds hVbound),
    helim.eventually (gt_mem_nhds (show (0 : ℝ) < 2 * η / 3 by positivity))] with N hN1 hN2
  intro ψ hψ hψ1
  have := vdc_estimate (Φ N) H (hΦ.1 N) hH (fun γ => F'' (γ +ᵥ y0)) ψ (fun γ => hB _) hψ hψ1
  simp only at this
  have hVN : (avg H fun h => avg H fun h' =>
      ‖avg (Φ N) fun γ => F'' ((γ + h) +ᵥ y0) * conj (F'' ((γ + h') +ᵥ y0))‖) = V N := rfl
  rw [hVN] at this
  linarith

end VdCOrbit

/-! ## The Kronecker part of the generic-pairs lemma -/

section KronPart

lemma integral_add3 {X : Type*} [MeasurableSpace X] {μ : Measure X} {f₁ f₂ f₃ : X → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) :
    ∫ x, (f₁ x + f₂ x + f₃ x) ∂μ = ∫ x, f₁ x ∂μ + ∫ x, f₂ x ∂μ + ∫ x, f₃ x ∂μ := by
  rw [integral_add (f := fun x => f₁ x + f₂ x) (h₁.add h₂) h₃, integral_add h₁ h₂]

lemma norm_add3_sq_le {E : Type*} [NormedAddCommGroup E] (a b c : E) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_add₃_le
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖b‖ - ‖c‖)]

lemma Bdd.integral_translate {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus} {F G : KG α → ℂ}
    (hF : Bdd F) (hG : Bdd G) (x0 : KG α) :
    Bdd fun z => ∫ v, F v * G (v + (z - x0)) ∂haarK α := by
  obtain ⟨CF, hCF0, hCF⟩ := hF.exists_bound_nonneg
  obtain ⟨CG, hCG0, hCG⟩ := hG.exists_bound_nonneg
  refine ⟨?_, CF * CG, fun z => Bdd.norm_integral_le fun v => ?_⟩
  · have : StronglyMeasurable fun q : KG α × KG α => F q.2 * G (q.2 + (q.1 - x0)) :=
      ((hF.meas.comp measurable_snd).mul (hG.meas.comp (measurable_snd.add
        (measurable_fst.sub_const _)))).stronglyMeasurable
    exact (this.integral_prod_right' (ν := haarK α)).measurable
  · rw [norm_mul]; exact mul_le_mul (hCF _) (hCG _) (norm_nonneg _) hCF0

/-- For a continuous Kronecker map `π` and a generic point `y₀`, the averages
`𝔼_γ f(T^γ y₀) G(z + α γ)` converge in `L²(m_K)` to `∫ f̃(v) G(v + z - π y₀) dm(v)`. -/
theorem tendsto_weighted_l2 {Γ Y : Type u} [AddCommGroup Γ] [Countable Γ] {α : Γ →+ Torus}
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y] [ContinuousConstVAdd Γ Y] [Nonempty Y]
    {μ : Measure Y} [IsProbabilityMeasure μ] [VAddInvariantMeasure Γ Y μ] {π : Y → KG α}
    (hW : WienerKoopman.{u}) (hπc : Continuous π) (hπe : ∀ (γ : Γ) y, π (γ +ᵥ y) = π y + kα α γ)
    (hπ : IsKroneckerMap μ α π) {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) {y0 : Y}
    (hy0 : IsGeneric μ Φ y0) (f : C(Y, ℂ)) {G : KG α → ℂ} (hG : Bdd G) :
    Tendsto (fun N => ∫ z, ‖avg (Φ N) (fun γ => f (γ +ᵥ y0) * G (z + kα α γ)) -
      ∫ v, tilde μ π f v * G (v + (z - π y0)) ∂haarK α‖ ^ 2 ∂haarK α) atTop (𝓝 0) := by
  have hR := hπ.toRotFactor
  have hfb : Bdd fun y => f y := ⟨f.continuous.measurable, ‖f‖, fun y => f.norm_coe_le_norm y⟩
  set Cf := ‖f‖ with hCf
  have hCf0 : 0 ≤ Cf := norm_nonneg _
  obtain ⟨CG, hCG0, hCG⟩ := hG.exists_bound_nonneg
  have hft : Bdd (tilde μ π f) := hfb.tilde
  have hftC : ∀ v, ‖tilde μ π f v‖ ≤ Cf := fun v =>
    Bdd.norm_integral_le (μ := dis μ π v) fun y => f.norm_coe_le_norm y
  have hIG : ∫ z, ‖G z‖ ^ 2 ∂haarK α ≤ CG ^ 2 := by
    calc ∫ z, ‖G z‖ ^ 2 ∂haarK α ≤ ∫ _z, CG ^ 2 ∂haarK α :=
          integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
            (integrable_const _) (Eventually.of_forall fun z =>
              pow_le_pow_left₀ (norm_nonneg _) (hCG z) 2)
      _ = CG ^ 2 := by simp
  refine tendsto_zero_of_forall_eventually_le (fun N => integral_nonneg fun z => by positivity)
    fun ε hε => ?_
  -- choice of `τ`
  set K1 : ℝ := Real.sqrt (8 * Cf ^ 2 + 2) + 2 * Cf with hK1
  have hK10 : 0 ≤ K1 := by positivity
  set τ : ℝ := min 1 (ε / (6 * (4 * K1 + 1) * (CG ^ 2 + 1))) with hτ
  have hτ0 : 0 < τ := lt_min one_pos (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : τ ≤ ε / (6 * (4 * K1 + 1) * (CG ^ 2 + 1)) := min_le_right _ _
  obtain ⟨P, hP, hfP⟩ := exists_trig_l2_approx hft (show (0 : ℝ) < τ ^ 2 by positivity)
  have hPc := hP.continuous
  have hPb := hP.bdd
  -- the decomposition `f = P ∘ π + f''`
  set f'' : C(Y, ℂ) := f - ⟨fun y => P (π y), hPc.comp hπc⟩ with hf''
  have hf''b : Bdd fun y => f'' y := ⟨f''.continuous.measurable, ‖f''‖,
    fun y => f''.norm_coe_le_norm y⟩
  set fperp : Y → ℂ := fun y => f y - tilde μ π f (π y) with hfperp
  have hfperpb : Bdd fperp := hfb.sub (hft.comp hπ.measurable)
  have hwm : WeakMixing Γ μ fperp := hπ.weakMixing_sub_tilde hW hfb
  -- the correlation perturbation
  have hdiff : ∫ y, ‖f'' y - fperp y‖ ^ 2 ∂μ < τ ^ 2 := by
    have e : ∀ y, f'' y - fperp y = tilde μ π f (π y) - P (π y) := fun y => by
      simp [hf'', hfperp]
    simp only [e]
    have := integral_map (μ := μ) hπ.measurable.aemeasurable
      (((hft.sub hPb).meas.norm.pow_const 2).aestronglyMeasurable)
      (f := fun v => ‖tilde μ π f v - P v‖ ^ 2)
    rw [hπ.map_eq] at this
    rw [← this]
    exact hfP
  have hperp2 : ∫ y, ‖fperp y‖ ^ 2 ∂μ ≤ (2 * Cf) ^ 2 := by
    calc ∫ y, ‖fperp y‖ ^ 2 ∂μ ≤ ∫ _y, (2 * Cf) ^ 2 ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity)
            (integrable_const _) (Eventually.of_forall fun y => by
              refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
              refine (norm_sub_le _ _).trans ?_
              have := f.norm_coe_le_norm y; have := hftC (π y); linarith)
      _ = (2 * Cf) ^ 2 := by simp
  have hf''2 : ∫ y, ‖f'' y‖ ^ 2 ∂μ ≤ 8 * Cf ^ 2 + 2 := by
    have := integral_norm_add_sq_le (μ := μ) (((hf''b.sub hfperpb)).memLp 2) (hfperpb.memLp 2)
    simp only [sub_add_cancel] at this
    nlinarith
  have hε₁ : ∀ δ : Γ, ‖corr μ f'' δ - corr μ fperp δ‖ ≤ τ * K1 := by
    intro δ
    refine (norm_corr_sub_le hf''b hfperpb δ).trans ?_
    have h1 : Real.sqrt (∫ y, ‖f'' y - fperp y‖ ^ 2 ∂μ) ≤ τ := by
      rw [show τ = Real.sqrt (τ ^ 2) from (Real.sqrt_sq hτ0.le).symm]
      exact Real.sqrt_le_sqrt hdiff.le
    have h2 : Real.sqrt (∫ y, ‖f'' y‖ ^ 2 ∂μ) ≤ Real.sqrt (8 * Cf ^ 2 + 2) :=
      Real.sqrt_le_sqrt hf''2
    have h3 : Real.sqrt (∫ y, ‖fperp y‖ ^ 2 ∂μ) ≤ 2 * Cf := by
      rw [show 2 * Cf = Real.sqrt ((2 * Cf) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hperp2
    calc _ ≤ τ * (Real.sqrt (∫ y, ‖f'' y‖ ^ 2 ∂μ) + Real.sqrt (∫ y, ‖fperp y‖ ^ 2 ∂μ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ τ * K1 := mul_le_mul_of_nonneg_left (by rw [hK1]; linarith) hτ0.le
  -- the three estimates
  set η : ℝ := ε / (48 * (CG ^ 2 + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hev1 := eventually_twisted_avg_le hΦ hy0 f'' hfperpb hwm hε₁ hη0
  have hev2 := (tendsto_trig_weighted hP hG (π y0) hΦ).eventually
    (ge_mem_nhds (show (0 : ℝ) < ε / 12 by positivity))
  filter_upwards [hev1, hev2] with N hN1 hN2
  -- pointwise decomposition
  have hdec : ∀ z, avg (Φ N) (fun γ => f (γ +ᵥ y0) * G (z + kα α γ)) -
      ∫ v, tilde μ π f v * G (v + (z - π y0)) ∂haarK α =
      (avg (Φ N) (fun γ => P (π y0 + kα α γ) * G (z + kα α γ)) -
        ∫ v, P v * G (v + (z - π y0)) ∂haarK α) +
      avg (Φ N) (fun γ => f'' (γ +ᵥ y0) * G (z + kα α γ)) +
      ((∫ v, P v * G (v + (z - π y0)) ∂haarK α) -
        ∫ v, tilde μ π f v * G (v + (z - π y0)) ∂haarK α) := by
    intro z
    have : (fun γ => f (γ +ᵥ y0) * G (z + kα α γ)) = fun γ =>
        P (π y0 + kα α γ) * G (z + kα α γ) + f'' (γ +ᵥ y0) * G (z + kα α γ) := by
      funext γ
      simp only [hf'', ContinuousMap.sub_apply, ContinuousMap.coe_mk, hπe]
      ring
    rw [this, avg_add']
    ring
  -- bound for the `Λ` difference
  have hΛ : ∀ z, ‖(∫ v, P v * G (v + (z - π y0)) ∂haarK α) -
      ∫ v, tilde μ π f v * G (v + (z - π y0)) ∂haarK α‖ ^ 2 ≤ τ ^ 2 * CG ^ 2 := by
    intro z
    have hGs : Bdd fun v => G (v + (z - π y0)) := hG.comp (measurable_add_const _)
    rw [← integral_sub (hPb.mul hGs).integrable (hft.mul hGs).integrable]
    have e : (fun v => P v * G (v + (z - π y0)) - tilde μ π f v * G (v + (z - π y0))) =
        fun v => (P v - tilde μ π f v) * conj (conj (G (v + (z - π y0)))) := by
      funext v; simp only [Complex.conj_conj]; ring
    rw [e]
    have hcs := norm_integral_mul_conj_sq_le (μ := haarK α) ((hPb.sub hft).memLp 2)
      (hGs.conj'.memLp 2)
    refine hcs.trans ?_
    have e1 : ∫ v, ‖P v - tilde μ π f v‖ ^ 2 ∂haarK α ≤ τ ^ 2 := by
      have : ∫ v, ‖P v - tilde μ π f v‖ ^ 2 ∂haarK α = ∫ v, ‖tilde μ π f v - P v‖ ^ 2 ∂haarK α := by
        congr 1; funext v; rw [norm_sub_rev]
      rw [this]; exact hfP.le
    have e2 : ∫ v, ‖conj (G (v + (z - π y0)))‖ ^ 2 ∂haarK α ≤ CG ^ 2 := by
      simp only [Complex.norm_conj]
      rw [integral_haarK_add_real (fun v => ‖G v‖ ^ 2)]
      exact hIG
    exact mul_le_mul e1 e2 (integral_nonneg fun v => by positivity) (by positivity)
  -- the weakly mixing part via Parseval
  have hwp : ∫ z, ‖avg (Φ N) (fun γ => f'' (γ +ᵥ y0) * G (z + kα α γ))‖ ^ 2 ∂haarK α ≤
      4 * (τ * K1 + η) * CG ^ 2 := by
    have := integral_weighted_avg_le hG (Φ N) (fun γ => f'' (γ +ᵥ y0)) (B := ‖f''‖)
      (fun γ => f''.norm_coe_le_norm _) (M := τ * K1 + η) (by positivity) fun χ hχ =>
        hN1 (fun γ => χ (kα α γ)) (fun a b => by rw [(kα α).map_add, Chars.map_add hχ])
          (fun a => Chars.norm_eq hχ _)
    exact this.trans (mul_le_mul_of_nonneg_left hIG (by positivity))
  -- combine
  have hb1 : Bdd fun z => avg (Φ N) (fun γ => P (π y0 + kα α γ) * G (z + kα α γ)) -
      ∫ v, P v * G (v + (z - π y0)) ∂haarK α :=
    (Bdd.avg _ fun γ _ => (Bdd.const _).mul (hG.comp (measurable_add_const _))).sub
      (hPb.integral_translate hG _)
  have hb2 : Bdd fun z => avg (Φ N) (fun γ => f'' (γ +ᵥ y0) * G (z + kα α γ)) :=
    Bdd.avg _ fun γ _ => (Bdd.const _).mul (hG.comp (measurable_add_const _))
  have hb3 : Bdd fun z => (∫ v, P v * G (v + (z - π y0)) ∂haarK α) -
      ∫ v, tilde μ π f v * G (v + (z - π y0)) ∂haarK α :=
    (hPb.integral_translate hG _).sub (hft.integral_translate hG _)
  have hsq : ∀ {F : KG α → ℂ}, Bdd F → Integrable (fun z => ‖F z‖ ^ 2) (haarK α) := fun hF =>
    (memLp_two_iff_integrable_sq_norm hF.meas.aestronglyMeasurable).1 (hF.memLp 2)
  have h3 : ∫ z, ‖(∫ v, P v * G (v + (z - π y0)) ∂haarK α) -
      ∫ v, tilde μ π f v * G (v + (z - π y0)) ∂haarK α‖ ^ 2 ∂haarK α ≤ τ ^ 2 * CG ^ 2 := by
    calc _ ≤ ∫ _z, τ ^ 2 * CG ^ 2 ∂haarK α :=
          integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
            (integrable_const _) (Eventually.of_forall hΛ)
      _ = τ ^ 2 * CG ^ 2 := by simp
  calc ∫ z, ‖avg (Φ N) (fun γ => f (γ +ᵥ y0) * G (z + kα α γ)) -
        ∫ v, tilde μ π f v * G (v + (z - π y0)) ∂haarK α‖ ^ 2 ∂haarK α
      ≤ ∫ z, 3 * (‖avg (Φ N) (fun γ => P (π y0 + kα α γ) * G (z + kα α γ)) -
          ∫ v, P v * G (v + (z - π y0)) ∂haarK α‖ ^ 2 +
          ‖avg (Φ N) (fun γ => f'' (γ +ᵥ y0) * G (z + kα α γ))‖ ^ 2 +
          ‖(∫ v, P v * G (v + (z - π y0)) ∂haarK α) -
            ∫ v, tilde μ π f v * G (v + (z - π y0)) ∂haarK α‖ ^ 2) ∂haarK α := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
          ((((hsq hb1).add (hsq hb2)).add (hsq hb3)).const_mul 3)
          (Eventually.of_forall fun z => ?_)
        dsimp only
        rw [hdec z]
        exact norm_add3_sq_le _ _ _
    _ = 3 * ((∫ z, ‖avg (Φ N) (fun γ => P (π y0 + kα α γ) * G (z + kα α γ)) -
          ∫ v, P v * G (v + (z - π y0)) ∂haarK α‖ ^ 2 ∂haarK α) +
        (∫ z, ‖avg (Φ N) (fun γ => f'' (γ +ᵥ y0) * G (z + kα α γ))‖ ^ 2 ∂haarK α) +
        ∫ z, ‖(∫ v, P v * G (v + (z - π y0)) ∂haarK α) -
            ∫ v, tilde μ π f v * G (v + (z - π y0)) ∂haarK α‖ ^ 2 ∂haarK α) := by
        rw [integral_const_mul, integral_add3 (hsq hb1) (hsq hb2) (hsq hb3)]
    _ ≤ 3 * (ε / 12 + 4 * (τ * K1 + η) * CG ^ 2 + τ ^ 2 * CG ^ 2) := by
        gcongr
    _ ≤ ε := by
        have hτ2 : τ ^ 2 ≤ τ := by nlinarith
        have h1 : 12 * η * CG ^ 2 ≤ ε / 4 := by
          rw [hη]
          rw [show 12 * (ε / (48 * (CG ^ 2 + 1))) * CG ^ 2 = ε / 4 * (CG ^ 2 / (CG ^ 2 + 1)) by
            field_simp; ring]
          exact mul_le_of_le_one_right (by positivity)
            ((div_le_one (by positivity)).2 (by linarith))
        have h2 : 3 * τ * (4 * K1 + 1) * CG ^ 2 ≤ ε / 2 := by
          have := mul_le_mul_of_nonneg_left hτε (show (0 : ℝ) ≤ 3 * (4 * K1 + 1) * CG ^ 2 by
            positivity)
          refine le_trans (by nlinarith) (this.trans ?_)
          rw [show 3 * (4 * K1 + 1) * CG ^ 2 * (ε / (6 * (4 * K1 + 1) * (CG ^ 2 + 1))) =
            ε / 2 * (CG ^ 2 / (CG ^ 2 + 1)) by field_simp; ring]
          exact mul_le_of_le_one_right (by positivity)
            ((div_le_one (by positivity)).2 (by linarith))
        nlinarith [sq_nonneg CG]

/-- Paper, proof of Lemma \ref{K:lem:pairs}, equation \eqref{K:eq:L2conv}: for continuous `f` and
bounded `g`, `𝔼_γ f(T^γ y₀) g(T^γ y) → J_{π y - π y₀}(f ⊗ g)` in `L²(λ)`. -/
theorem tendsto_pair_l2 {Γ Y : Type u} [AddCommGroup Γ] [Countable Γ] {α : Γ →+ Torus}
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y] [ContinuousConstVAdd Γ Y] [Nonempty Y]
    {μ : Measure Y} [IsProbabilityMeasure μ] [VAddInvariantMeasure Γ Y μ] {π : Y → KG α}
    (hW : WienerKoopman.{u}) (hπc : Continuous π) (hπe : ∀ (γ : Γ) y, π (γ +ᵥ y) = π y + kα α γ)
    (hπ : IsKroneckerMap μ α π) {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) {y0 : Y}
    (hy0 : IsGeneric μ Φ y0) (f : C(Y, ℂ)) {g : Y → ℂ} (hg : Bdd g) :
    Tendsto (fun N => ∫ y, ‖avg (Φ N) (fun γ => f (γ +ᵥ y0) * g (γ +ᵥ y)) -
      cJ μ π f g (π y - π y0)‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hR := hπ.toRotFactor
  set G := tilde μ π g with hGdef
  have hGb : Bdd G := hg.tilde
  have hft : Bdd (tilde μ π f) := (⟨f.continuous.measurable, ‖f‖, fun y => f.norm_coe_le_norm y⟩ :
    Bdd fun y => f y).tilde
  set g₁ : Y → ℂ := fun y => g y - G (π y) with hg₁
  have hg₁b : Bdd g₁ := hg.sub (hGb.comp hπ.measurable)
  have hwm : WeakMixing Γ μ g₁ := hπ.weakMixing_sub_tilde hW hg
  -- the Kronecker part
  have hK := tendsto_weighted_l2 hW hπc hπe hπ hΦ hy0 f hGb
  have hK' : Tendsto (fun N => ∫ y, ‖avg (Φ N) (fun γ => f (γ +ᵥ y0) * G (π y + kα α γ)) -
      cJ μ π f g (π y - π y0)‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    refine hK.congr fun N => ?_
    have hm : Measurable fun z => ‖avg (Φ N) (fun γ => f (γ +ᵥ y0) * G (z + kα α γ)) -
        ∫ v, tilde μ π f v * G (v + (z - π y0)) ∂haarK α‖ ^ 2 :=
      (((Bdd.avg _ fun γ _ => (Bdd.const _).mul (hGb.comp (measurable_add_const _))).sub
        (hft.integral_translate hGb _)).meas.norm.pow_const 2)
    have e := integral_map (μ := μ) hπ.measurable.aemeasurable hm.aestronglyMeasurable
    rw [hπ.map_eq] at e
    rw [e]
    rfl
  -- the weakly mixing part
  set C := ‖f‖ + 1 with hC
  have hC0 : 0 < C := by positivity
  have hwml := hwm.tendsto_l2_avg hg₁b hΦ (fun _ γ => f (γ +ᵥ y0) / C) fun _ γ => by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC0, div_le_one hC0]
    have := f.norm_coe_le_norm (γ +ᵥ y0); linarith
  have hwml' : Tendsto (fun N => ∫ y, ‖avg (Φ N) (fun γ => f (γ +ᵥ y0) * g₁ (γ +ᵥ y))‖ ^ 2 ∂μ)
      atTop (𝓝 0) := by
    have := hwml.const_mul (C ^ 2)
    rw [mul_zero] at this
    refine this.congr fun N => ?_
    rw [← integral_const_mul]
    congr 1; funext y
    have e : avg (Φ N) (fun γ => f (γ +ᵥ y0) * g₁ (γ +ᵥ y)) =
        (C : ℂ) * avg (Φ N) (fun γ => f (γ +ᵥ y0) / C * g₁ (γ +ᵥ y)) := by
      simp only [avg, Complex.real_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      have hCne : (C : ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
      field_simp
    rw [e, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- combine
  have hsum := (hK'.const_mul 2).add (hwml'.const_mul 2)
  simp only [mul_zero, add_zero] at hsum
  refine squeeze_zero (fun N => integral_nonneg fun y => by positivity) (fun N => ?_) hsum
  have hdec : ∀ y, avg (Φ N) (fun γ => f (γ +ᵥ y0) * g (γ +ᵥ y)) - cJ μ π f g (π y - π y0) =
      (avg (Φ N) (fun γ => f (γ +ᵥ y0) * G (π y + kα α γ)) - cJ μ π f g (π y - π y0)) +
        avg (Φ N) (fun γ => f (γ +ᵥ y0) * g₁ (γ +ᵥ y)) := by
    intro y
    have : (fun γ => f (γ +ᵥ y0) * g (γ +ᵥ y)) = fun γ =>
        f (γ +ᵥ y0) * G (π y + kα α γ) + f (γ +ᵥ y0) * g₁ (γ +ᵥ y) := by
      funext γ; simp only [hg₁, hπe]; ring
    rw [this, avg_add']; ring
  have hb1 : Bdd fun y => avg (Φ N) (fun γ => f (γ +ᵥ y0) * G (π y + kα α γ)) -
      cJ μ π f g (π y - π y0) :=
    (Bdd.avg _ fun γ _ => (Bdd.const _).mul (hGb.comp (hπ.measurable.add_const _))).sub
      ((⟨f.continuous.measurable, ‖f‖, fun y => f.norm_coe_le_norm y⟩ : Bdd fun y => f y).cJ hg
        |>.comp (hπ.measurable.sub_const _))
  have hb2 : Bdd fun y => avg (Φ N) (fun γ => f (γ +ᵥ y0) * g₁ (γ +ᵥ y)) :=
    Bdd.avg _ fun γ _ => (Bdd.const _).mul (hg₁b.comp (measurable_const_vadd γ))
  have := integral_norm_add_sq_le (μ := μ) (hb1.memLp 2) (hb2.memLp 2)
  simp only [← hdec] at this
  exact this

end KronPart

/-! ## A common subsequence with a.e. convergence -/

section Subseq

/-- From countably many sequences converging to `0` in `L²`, extract one subsequence along which
all of them converge to `0` almost everywhere. -/
theorem exists_subseq_ae_tendsto_zero {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
    (b : ℕ → ℕ → Y → ℂ) (hm : ∀ k N, Measurable (b k N))
    (hint : ∀ k N, Integrable (fun y => ‖b k N y‖ ^ 2) μ)
    (hb : ∀ k, Tendsto (fun N => ∫ y, ‖b k N y‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ y ∂μ, ∀ k, Tendsto (fun j => b k (φ j) y) atTop (𝓝 0) := by
  set c : ℕ → ℕ → ℝ := fun k N => ∫ y, ‖b k N y‖ ^ 2 ∂μ with hc
  have hc0 : ∀ k N, 0 ≤ c k N := fun k N => integral_nonneg fun y => by positivity
  have hN : ∀ j, ∃ N₀, ∀ N ≥ N₀, ∀ k ∈ Finset.range (j + 1), c k N < (1 / 2) ^ j := by
    intro j
    have : ∀ᶠ N in atTop, ∀ k ∈ Finset.range (j + 1), c k N < (1 / 2) ^ j := by
      rw [eventually_all_finset]
      intro k _
      exact (hb k).eventually (gt_mem_nhds (by positivity))
    exact this.exists_forall_of_atTop
  choose N₀ hN₀ using hN
  set φ : ℕ → ℕ := fun j => Nat.rec (N₀ 0) (fun j acc => max (acc + 1) (N₀ (j + 1))) j with hφ
  have hφs : ∀ j, φ (j + 1) = max (φ j + 1) (N₀ (j + 1)) := fun j => rfl
  have hφmono : StrictMono φ := strictMono_nat_of_lt_succ fun j => by
    rw [hφs]; exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hφN : ∀ j, N₀ j ≤ φ j := by
    intro j; cases j with
    | zero => exact le_rfl
    | succ j => rw [hφs]; exact le_max_right _ _
  refine ⟨φ, hφmono, ?_⟩
  rw [ae_all_iff]
  intro k
  -- summability of `c k (φ j)`
  have hsum : ∑' j, ENNReal.ofReal (c k (φ j)) ≠ ⊤ := by
    have hle : ∀ j, ENNReal.ofReal (c k (φ j)) ≤
        (if j < k then ENNReal.ofReal (c k (φ j)) else 0) + (2⁻¹ : ENNReal) ^ j := by
      intro j
      split_ifs with hj
      · exact le_self_add
      · rw [zero_add]
        have := hN₀ j (φ j) (hφN j) k (Finset.mem_range.2 (by omega))
        have e : ENNReal.ofReal ((1 / 2 : ℝ) ^ j) = (2⁻¹ : ENNReal) ^ j := by
          rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos]
          simp
        rw [← e]
        exact ENNReal.ofReal_le_ofReal this.le
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_add, ENNReal.tsum_geometric]
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · rw [tsum_eq_sum (s := Finset.range k) fun j hj => by
        simp only [Finset.mem_range] at hj; simp [hj]]
      exact ENNReal.sum_ne_top.2 fun j _ => by split_ifs <;> simp
    · simp
  have hlint : ∫⁻ y, ∑' j, ENNReal.ofReal (‖b k (φ j) y‖ ^ 2) ∂μ ≠ ⊤ := by
    rw [lintegral_tsum (f := fun j y => ENNReal.ofReal (‖b k (φ j) y‖ ^ 2)) fun j =>
      (ENNReal.measurable_ofReal.comp ((hm k (φ j)).norm.pow_const 2)).aemeasurable]
    convert hsum using 1
    refine tsum_congr fun j => ?_
    rw [hc, ofReal_integral_eq_lintegral_ofReal (hint k (φ j))
      (Eventually.of_forall fun y => by positivity)]
  filter_upwards [ae_lt_top' (Measurable.aemeasurable (Measurable.ennreal_tsum fun j =>
    ENNReal.measurable_ofReal.comp ((hm k (φ j)).norm.pow_const 2))) hlint] with y hy
  have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hy.ne
  have h2 : Tendsto (fun j => ‖b k (φ j) y‖ ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    rw [ENNReal.toReal_zero] at this
    refine this.congr fun j => ?_
    simp only [Function.comp]
    exact ENNReal.toReal_ofReal (sq_nonneg _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at this
  refine this.congr fun j => ?_
  simp only [Function.comp]
  exact Real.sqrt_sq (norm_nonneg _)

end Subseq

/-! ## From product test functions to genericity -/

section Extend

variable {Γ : Type*} [AddCommGroup Γ]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y]

/-- The product test function `(y, y') ↦ f(y) g(y')`. -/
def tensorC (f g : C(Y, ℝ)) : C(Y × Y, ℝ) := f.comp ⟨Prod.fst, continuous_fst⟩ * g.comp ⟨Prod.snd, continuous_snd⟩

@[simp] lemma tensorC_apply (f g : C(Y, ℝ)) (p : Y × Y) : tensorC f g p = f p.1 * g p.2 := rfl

/-- If the averages converge for all product test functions built from a dense set, then the
point is generic. -/
theorem isGeneric_of_dense_prod {ν : Measure (Y × Y)} [IsProbabilityMeasure ν]
    {Ψ : ℕ → Finset Γ} (hΨ : ∀ N, (Ψ N).Nonempty) {x : Y × Y} {D : Set C(Y, ℝ)}
    (hD : Dense D)
    (h : ∀ f ∈ D, ∀ g ∈ D, Tendsto (fun N => avg (Ψ N) fun γ => f (γ +ᵥ x.1) * g (γ +ᵥ x.2))
      atTop (𝓝 (∫ p, f p.1 * g p.2 ∂ν))) :
    IsGeneric ν Ψ x := by
  have hintF : ∀ F : C(Y × Y, ℝ), Integrable (fun p => F p) ν := fun F =>
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- the closed subspace of good test functions
  let S : Submodule ℝ C(Y × Y, ℝ) :=
    { carrier := {F | Tendsto (fun N => avg (Ψ N) fun γ => F (γ +ᵥ x)) atTop (𝓝 (∫ p, F p ∂ν))}
      add_mem' := by
        intro F G hF hG
        simp only [Set.mem_setOf_eq, ContinuousMap.add_apply] at hF hG ⊢
        rw [integral_add (hintF F) (hintF G)]
        exact (hF.add hG).congr fun N => (avg_add' _ _ _).symm
      zero_mem' := by
        simp only [Set.mem_setOf_eq, ContinuousMap.zero_apply, integral_zero]
        exact tendsto_const_nhds.congr fun N => by simp [avg]
      smul_mem' := by
        intro c F hF
        simp only [Set.mem_setOf_eq, ContinuousMap.smul_apply, smul_eq_mul] at hF ⊢
        rw [integral_const_mul]
        exact (hF.const_mul c).congr fun N => by simp [avg, Finset.mul_sum, mul_left_comm] }
  have hSmem : ∀ F, F ∈ S ↔
      Tendsto (fun N => avg (Ψ N) fun γ => F (γ +ᵥ x)) atTop (𝓝 (∫ p, F p ∂ν)) := fun F => Iff.rfl
  -- `S` is closed
  have hSc : IsClosed (S : Set C(Y × Y, ℝ)) := by
    refine isClosed_of_closure_subset fun F hF => ?_
    rw [SetLike.mem_coe, hSmem, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨G, hG, hFG⟩ := Metric.mem_closure_iff.1 hF (ε / 3) (by positivity)
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 ((hSmem G).1 hG) (ε / 3) (by positivity)
    refine ⟨N0, fun N hN => ?_⟩
    have hpt : ∀ p, ‖F p - G p‖ ≤ dist F G := fun p => by
      rw [← dist_eq_norm]; exact ContinuousMap.dist_apply_le_dist p
    have e1 : ‖(avg (Ψ N) fun γ => F (γ +ᵥ x)) - avg (Ψ N) fun γ => G (γ +ᵥ x)‖ ≤ dist F G := by
      rw [← avg_sub']
      exact norm_avg_le _ (fun γ _ => hpt _) dist_nonneg
    have e2 : ‖(∫ p, F p ∂ν) - ∫ p, G p ∂ν‖ ≤ dist F G := by
      rw [← integral_sub (hintF F) (hintF G)]
      have := norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hpt)
      simpa using this
    have := hN0 N hN
    rw [Real.dist_eq] at this ⊢
    rw [Real.norm_eq_abs] at e1 e2
    have h3 : dist F G < ε / 3 := hFG
    calc |(avg (Ψ N) fun γ => F (γ +ᵥ x)) - ∫ p, F p ∂ν|
        ≤ |(avg (Ψ N) fun γ => F (γ +ᵥ x)) - avg (Ψ N) fun γ => G (γ +ᵥ x)| +
          |(avg (Ψ N) fun γ => G (γ +ᵥ x)) - ∫ p, G p ∂ν| + |(∫ p, F p ∂ν) - ∫ p, G p ∂ν| := by
          have := abs_sub_le ((avg (Ψ N) fun γ => F (γ +ᵥ x)))
            ((avg (Ψ N) fun γ => G (γ +ᵥ x))) (∫ p, F p ∂ν)
          have := abs_sub_le ((avg (Ψ N) fun γ => G (γ +ᵥ x))) (∫ p, G p ∂ν) (∫ p, F p ∂ν)
          rw [abs_sub_comm (∫ p, G p ∂ν)] at this
          linarith
      _ < ε := by linarith
  -- product test functions lie in `S`
  have hT : ∀ f g : C(Y, ℝ), tensorC f g ∈ S := by
    intro f g
    show tensorC f g ∈ (S : Set C(Y × Y, ℝ))
    rw [← hSc.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min 1 (ε / (2 * (‖f‖ + ‖g‖ + 2))) with hδ
    have hδ0 : 0 < δ := lt_min one_pos (by positivity)
    obtain ⟨d, hdD, hfd⟩ : ∃ d ∈ D, dist f d < δ := by
      obtain ⟨d, hd1, hd2⟩ := Metric.dense_iff.1 hD f δ hδ0
      exact ⟨d, hd2, by rw [dist_comm]; exact hd1⟩
    obtain ⟨e, heD, hge⟩ : ∃ e ∈ D, dist g e < δ := by
      obtain ⟨e, he1, he2⟩ := Metric.dense_iff.1 hD g δ hδ0
      exact ⟨e, he2, by rw [dist_comm]; exact he1⟩
    refine ⟨tensorC d e, ?_, ?_⟩
    · rw [SetLike.mem_coe, hSmem]
      exact (h d hdD e heD).congr fun N => rfl
    · have hδ1 : δ ≤ 1 := min_le_left _ _
      have hδε : δ ≤ ε / (2 * (‖f‖ + ‖g‖ + 2)) := min_le_right _ _
      have he : ‖e‖ ≤ ‖g‖ + 1 := by
        have := norm_sub_norm_le e g
        rw [← dist_eq_norm, dist_comm] at this
        linarith
      have hbound : dist (tensorC f g) (tensorC d e) ≤ ‖f‖ * δ + δ * (‖g‖ + 1) := by
        refine (ContinuousMap.dist_le (by positivity)).2 fun p => ?_
        simp only [tensorC_apply, Real.dist_eq]
        have h1 : |f p.1| ≤ ‖f‖ := by
          rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
        have h2 : |g p.2 - e p.2| ≤ δ := by
          rw [← Real.dist_eq]; exact (ContinuousMap.dist_apply_le_dist _).trans hge.le
        have h3 : |f p.1 - d p.1| ≤ δ := by
          rw [← Real.dist_eq]; exact (ContinuousMap.dist_apply_le_dist _).trans hfd.le
        have h4 : |e p.2| ≤ ‖g‖ + 1 := by
          rw [← Real.norm_eq_abs]; exact (e.norm_coe_le_norm _).trans he
        calc |f p.1 * g p.2 - d p.1 * e p.2| = |f p.1 * (g p.2 - e p.2) + (f p.1 - d p.1) * e p.2| := by
              congr 1; ring
          _ ≤ |f p.1| * |g p.2 - e p.2| + |f p.1 - d p.1| * |e p.2| := by
              rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
          _ ≤ ‖f‖ * δ + δ * (‖g‖ + 1) := by
              gcongr
      calc dist (tensorC f g) (tensorC d e) ≤ ‖f‖ * δ + δ * (‖g‖ + 1) := hbound
        _ = δ * (‖f‖ + ‖g‖ + 1) := by ring
        _ < ε := by
            calc δ * (‖f‖ + ‖g‖ + 1) ≤ ε / (2 * (‖f‖ + ‖g‖ + 2)) * (‖f‖ + ‖g‖ + 2) :=
                  mul_le_mul hδε (by linarith) (by positivity) (by positivity)
              _ = ε / 2 := by field_simp
              _ < ε := half_lt_self hε
  -- the subalgebra generated by product test functions
  let A : Subalgebra ℝ C(Y × Y, ℝ) :=
    { carrier := Submodule.span ℝ (Set.range fun fg : C(Y, ℝ) × C(Y, ℝ) => tensorC fg.1 fg.2)
      mul_mem' := by
        intro a b ha hb
        have : a * b ∈ Submodule.span ℝ (Set.range fun fg : C(Y, ℝ) × C(Y, ℝ) => tensorC fg.1 fg.2) *
            Submodule.span ℝ (Set.range fun fg : C(Y, ℝ) × C(Y, ℝ) => tensorC fg.1 fg.2) :=
          Submodule.mul_mem_mul ha hb
        rw [Submodule.span_mul_span] at this
        refine Submodule.span_mono ?_ this
        rintro _ ⟨_, ⟨fg, rfl⟩, _, ⟨fg', rfl⟩, rfl⟩
        exact ⟨(fg.1 * fg'.1, fg.2 * fg'.2), by ext p; simp; ring⟩
      one_mem' := Submodule.subset_span ⟨(1, 1), by ext p; simp⟩
      add_mem' := Submodule.add_mem _
      zero_mem' := Submodule.zero_mem _
      algebraMap_mem' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(1, 1), by ext p; simp⟩) }
  have hAS : (A : Set C(Y × Y, ℝ)) ⊆ S := by
    intro F hF
    have hsp : Submodule.span ℝ (Set.range fun fg : C(Y, ℝ) × C(Y, ℝ) => tensorC fg.1 fg.2) ≤ S :=
      Submodule.span_le.2 (by rintro _ ⟨fg, rfl⟩; exact hT fg.1 fg.2)
    exact hsp hF
  have hsep : A.SeparatesPoints := by
    intro p q hpq
    have hsep1 : ∀ a b : Y, a ≠ b → ∃ f : C(Y, ℝ), f a ≠ f b := by
      intro a b hab
      obtain ⟨f, hf0, hf1, -⟩ := exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := a))
        (isClosed_singleton (x := b)) (Set.disjoint_singleton.2 hab)
      refine ⟨f, ?_⟩
      rw [hf0 rfl, hf1 rfl]; norm_num
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
      obtain ⟨g, hg⟩ := hsep1 _ _ h2
      refine ⟨_, ⟨tensorC 1 g, Submodule.subset_span ⟨(1, g), rfl⟩, rfl⟩, ?_⟩
      simpa using hg
    · obtain ⟨f, hf⟩ := hsep1 _ _ h1
      refine ⟨_, ⟨tensorC f 1, Submodule.subset_span ⟨(f, 1), rfl⟩, rfl⟩, ?_⟩
      simpa using hf
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  intro F
  have hF : F ∈ A.topologicalClosure := by rw [htop]; trivial
  have : F ∈ closure (S : Set C(Y × Y, ℝ)) := closure_mono hAS hF
  rw [hSc.closure_eq] at this
  exact this

end Extend

/-! ## The generic-pairs lemma -/

/-- The complex-valued version of a real continuous function. -/
def toC {Y : Type*} [TopologicalSpace Y] (f : C(Y, ℝ)) : C(Y, ℂ) :=
  ⟨fun y => (f y : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

/-- The error term in the generic-pairs lemma for the `k`-th pair of test functions. -/
def pairErr {Γ Y : Type*} [AddCommGroup Γ] {α : Γ →+ Torus} [TopologicalSpace Y]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] [AddAction Γ Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (π : Y → KG α) (Φ : ℕ → Finset Γ) (y0 : Y)
    (e : ℕ → C(Y, ℝ) × C(Y, ℝ)) (k N : ℕ) (y : Y) : ℂ :=
  avg (Φ N) (fun γ => toC (e k).1 (γ +ᵥ y0) * ((e k).2 (γ +ᵥ y) : ℂ)) -
    cJ μ π (toC (e k).1) (fun y => ((e k).2 y : ℂ)) (π y - π y0)

/-- Paper, Lemma \ref{K:lem:pairs} (generic pairs): if `π` is a continuous, everywhere
equivariant Kronecker map for `λ` and `y₀` is generic for `λ` along `Φ`, then along a subsequence
`Φ ∘ φ`, for `λ`-a.e. `y` the pair `(y₀, y)` is generic for `J_{π y - π y₀}`. -/
theorem generic_pairs {Γ Y : Type u} [AddCommGroup Γ] [Countable Γ] {α : Γ →+ Torus}
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [AddAction Γ Y] [ContinuousConstVAdd Γ Y] [Nonempty Y]
    {μ : Measure Y} [IsProbabilityMeasure μ] [VAddInvariantMeasure Γ Y μ] {π : Y → KG α}
    (hW : WienerKoopman.{u}) (hπc : Continuous π) (hπe : ∀ (γ : Γ) y, π (γ +ᵥ y) = π y + kα α γ)
    (hπ : IsKroneckerMap μ α π) {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) {y0 : Y}
    (hy0 : IsGeneric μ Φ y0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ y ∂μ, IsGeneric (relJ μ π (π y - π y0)) (Φ ∘ φ) (y0, y) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense C(Y, ℝ)
  have hDne : (D ×ˢ D).Nonempty := by
    obtain ⟨d, hd⟩ := hDd.nonempty
    exact ⟨(d, d), hd, hd⟩
  obtain ⟨e, he⟩ := (hDc.prod hDc).exists_eq_range hDne
  have hgb : ∀ k, Bdd fun y => ((e k).2 y : ℂ) := fun k =>
    ⟨Complex.continuous_ofReal.measurable.comp (e k).2.continuous.measurable, ‖(e k).2‖,
      fun y => by simpa using (e k).2.norm_coe_le_norm y⟩
  have hfb : ∀ k, Bdd fun y => ((e k).1 y : ℂ) := fun k =>
    ⟨Complex.continuous_ofReal.measurable.comp (e k).1.continuous.measurable, ‖(e k).1‖,
      fun y => by simpa using (e k).1.norm_coe_le_norm y⟩
  have hbb : ∀ k N, Bdd (pairErr μ π Φ y0 e k N) := fun k N =>
    (Bdd.avg _ fun γ _ => (Bdd.const _).mul ((hgb k).comp (measurable_const_vadd γ))).sub
      (((hfb k).cJ (hgb k)).comp (hπ.measurable.sub_const _))
  obtain ⟨φ, hφ, hae⟩ := exists_subseq_ae_tendsto_zero (pairErr μ π Φ y0 e)
    (fun k N => (hbb k N).meas)
    (fun k N => (memLp_two_iff_integrable_sq_norm (hbb k N).meas.aestronglyMeasurable).1
      ((hbb k N).memLp 2))
    (fun k => by
      have := tendsto_pair_l2 hW hπc hπe hπ hΦ hy0 (toC (e k).1) (hgb k)
      unfold pairErr
      exact this)
  refine ⟨φ, hφ, hae.mono fun y hy => ?_⟩
  refine isGeneric_of_dense_prod (fun N => hΦ.1 _) hDd fun f hf g hg => ?_
  obtain ⟨k, hk⟩ : ∃ k, e k = (f, g) := by
    have : (f, g) ∈ Set.range e := he ▸ ⟨hf, hg⟩
    exact this
  have hbdR : ∀ h : C(Y, ℝ), Bdd fun y => (h y : ℂ) := fun h =>
    ⟨Complex.continuous_ofReal.measurable.comp h.continuous.measurable, ‖h‖,
      fun y => by simpa using h.norm_coe_le_norm y⟩
  have hlim := hy k
  simp only [pairErr, hk] at hlim
  -- identify the limit
  have hJ : cJ μ π (toC f) (fun y => (g y : ℂ)) (π y - π y0) =
      ((∫ p, f p.1 * g p.2 ∂relJ μ π (π y - π y0) : ℝ) : ℂ) := by
    rw [cJ, ← integral_relJ_mul (f := toC f) (hbdR f) (hbdR g), ← integral_complex_ofReal]
    congr 1; funext p
    simp [toC]
  rw [hJ] at hlim
  have hav : ∀ j, avg (Φ (φ j)) (fun γ => toC f (γ +ᵥ y0) * (g (γ +ᵥ y) : ℂ)) =
      ((avg (Φ (φ j)) fun γ => f (γ +ᵥ y0) * g (γ +ᵥ y) : ℝ) : ℂ) := fun j => by
    rw [← avg_ofReal]; congr 1; funext γ; simp [toC]
  simp only [hav] at hlim
  have hlim' : Tendsto (fun j => (avg (Φ (φ j)) fun γ => f (γ +ᵥ y0) * g (γ +ᵥ y)) -
      ∫ p, f p.1 * g p.2 ∂relJ μ π (π y - π y0)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hlim ⊢
    refine hlim.congr fun j => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real]
  have := hlim'.add_const (∫ p, f p.1 * g p.2 ∂relJ μ π (π y - π y0))
  simp only [sub_add_cancel, zero_add] at this
  exact this

end Kmrr25.ThmK
