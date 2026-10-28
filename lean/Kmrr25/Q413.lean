import Kmrr25.Basic

/-!
# Sumsets in the sets `A_x = {n : {n^γ x} ≤ 1 / log n}` (paper, Section \ref{IB:sec:q413})

For `γ > 0` and `x ∈ ℝ` let `A_x = {n ∈ ℕ : {n^γ x} ≤ 1 / log n}`, where `{t}` is the
fractional part. Question 4.13 of the survey asks for which `γ` the set `A_x` contains a sumset
`B + C` with `B, C` infinite for almost every `x`.

## Main results

* `thm413b` — Theorem \ref{IB:thm:413}\ref{IB:413b}: if `γ = d` is an integer and `x` is
  irrational, then `A_x` contains no set `B + F` with `B ⊆ ℕ` infinite and `F ⊆ ℤ`, `|F| = d + 1`.
* `thm413b_sumset` — the "in particular" clause: `A_x` contains no `B + C` with `B, C ⊆ ℕ`
  infinite.
* `divided_difference` — the divided-difference identity used in the proof: for distinct
  integers `c_0, …, c_d`, `∑_i (b + c_i)^d / ∏_{j ≠ i} (c_i - c_j) = 1`.
* `lem_thick` — Lemma \ref{IB:lem:thick}: a thick set contains `B + C` with `B, C` infinite.
* `rational_mem`, `rational_sumset` — the accompanying remark: for integer `γ = d ≥ 1` and
  rational `x = p/q` (`q ≥ 1`) one has `qℕ ⊆ A_x`, so `A_x` contains an infinite sumset.

## Conventions

* The paper's `ℕ` is `{1, 2, …}`. The set `A_x` is a subset of Lean's `ℕ` not containing `0`.
  For `n = 1` the condition `{n^γ x} ≤ 1/log n` is void (`1 / log 1 = +∞`), so `1 ∈ A_x` by
  definition; this only enlarges `A_x`, and the paper notes that it is irrelevant.
* `n^γ` is the real power `(n : ℝ) ^ γ`; for `γ = d ∈ ℕ` it is the ordinary power.
* `B + F` with `B ⊆ ℕ` and `F ⊆ ℤ` is the sumset `Kmrr25.sumset` of their images in `ℤ`, and
  `B + F ⊆ A_x` means inclusion in `ℤ`.
* The hypothesis `γ > 0` of the paper, i.e. `d ≥ 1`, is not needed for part (b): the proof
  works for every `d ∈ ℕ`, so it is omitted.

## Part (a)

Theorem \ref{IB:thm:413}\ref{IB:413a} (for non-integer `γ`, `A_x` is thick for almost every `x`,
proved by the second-moment method) is formalized in `Kmrr25.Q413a` (the deduction from the
second-moment estimate) and `Kmrr25.Q413SecondMoment` (the estimate itself, and the final
"if and only if" of Theorem \ref{IB:thm:413} as `Kmrr25.Q413SM.thm413_iff`). This file contains
Lemma \ref{IB:lem:thick} (`lem_thick`: a thick set contains `B + C` with `B, C` infinite).
-/

open Real Finset Polynomial

namespace Kmrr25.Q413

/-- The set `A_x = {n ∈ ℕ : {n^γ x} ≤ 1 / log n}` (paper notation). Here `ℕ = {1, 2, …}`, and for
`n = 1` the condition is void, so `1 ∈ A_x`. -/
def Ax (γ x : ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ (2 ≤ n → Int.fract ((n : ℝ) ^ γ * x) ≤ 1 / Real.log n)}

/-- Paper, proof of Theorem \ref{IB:thm:413}\ref{IB:413b}: the `d`-th divided difference of
`c ↦ (b + c)^d` at `d + 1` distinct nodes equals its leading coefficient `1`. -/
theorem divided_difference (d : ℕ) (F : Finset ℤ) (hF : F.card = d + 1) (b : ℝ) :
    ∑ c ∈ F, ((b + c) ^ d) / ∏ j ∈ F.erase c, ((c : ℝ) - j) = 1 := by
  have hinj : Set.InjOn (fun c : ℤ => (c : ℝ)) (F : Set ℤ) := fun a _ b _ h => by
    simpa using h
  have hdeg : ((X + C b) ^ d : ℝ[X]).degree < F.card := by
    rw [hF, degree_pow, degree_X_add_C, nsmul_eq_mul, mul_one]
    exact_mod_cast Nat.lt_succ_self d
  have h := Lagrange.coeff_eq_sum hinj hdeg
  rw [hF, Nat.add_sub_cancel] at h
  have h1 : ((X + C b) ^ d : ℝ[X]).coeff d = 1 := by
    have := (monic_X_add_C b).pow d
    simpa [natDegree_pow, natDegree_X_add_C] using this.coeff_natDegree
  rw [h1] at h
  rw [h]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [eval_pow, add_comm]

/-- The integer `∏_{c ∈ F} ∏_{j ∈ F, j ≠ c} (c - j)`, a common denominator of the weights of
the divided difference. -/
def denom (F : Finset ℤ) : ℤ := ∏ c ∈ F, ∏ j ∈ F.erase c, (c - j)

/-- The integer weights `μ_c = denom F / ∏_{j ≠ c} (c - j)`. -/
def mu (F : Finset ℤ) (c : ℤ) : ℤ := ∏ c' ∈ F.erase c, ∏ j ∈ F.erase c', (c' - j)

lemma prod_erase_ne_zero (F : Finset ℤ) (c : ℤ) : ∏ j ∈ F.erase c, ((c : ℝ) - j) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have : j ≠ c := Finset.ne_of_mem_erase hj
  rw [sub_ne_zero]
  exact_mod_cast this.symm

lemma denom_ne_zero (F : Finset ℤ) : denom F ≠ 0 := by
  have : ((denom F : ℤ) : ℝ) ≠ 0 := by
    unfold denom
    push_cast
    rw [Finset.prod_ne_zero_iff]
    exact fun c _ => prod_erase_ne_zero F c
  exact_mod_cast this

lemma mu_eq (F : Finset ℤ) {c : ℤ} (hc : c ∈ F) :
    ((mu F c : ℤ) : ℝ) = (denom F : ℝ) / ∏ j ∈ F.erase c, ((c : ℝ) - j) := by
  rw [eq_div_iff (prod_erase_ne_zero F c)]
  unfold mu denom
  push_cast
  exact Finset.prod_erase_mul F (fun c' => ∏ j ∈ F.erase c', ((c' : ℝ) - j)) hc

/-- The integer form of the divided-difference identity:
`∑_{c ∈ F} μ_c (b + c)^d = denom F`. -/
lemma sum_mu (d : ℕ) (F : Finset ℤ) (hF : F.card = d + 1) (b : ℝ) :
    ∑ c ∈ F, (mu F c : ℝ) * (b + c) ^ d = denom F := by
  have h := divided_difference d F hF b
  calc ∑ c ∈ F, (mu F c : ℝ) * (b + c) ^ d
      = ∑ c ∈ F, (denom F : ℝ) * ((b + c) ^ d / ∏ j ∈ F.erase c, ((c : ℝ) - j)) := by
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [mu_eq F hc]
        ring
    _ = denom F := by rw [← Finset.mul_sum, h, mul_one]

/-- Every integer is at distance at least `min({y}, 1 - {y})` from `y`; this is positive when
`y` is irrational (`min_fract_pos`). -/
lemma dist_int_ge {y : ℝ} (m : ℤ) :
    min (Int.fract y) (1 - Int.fract y) ≤ |y - m| := by
  have hf := Int.floor_add_fract y
  rcases le_or_gt m ⌊y⌋ with h | h
  · have : (m : ℝ) ≤ ⌊y⌋ := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith [Int.fract_nonneg y])]
    exact (min_le_left _ _).trans (by linarith)
  · have : (⌊y⌋ : ℝ) + 1 ≤ m := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith [Int.fract_lt_one y])]
    exact (min_le_right _ _).trans (by linarith)

lemma min_fract_pos {y : ℝ} (hy : Irrational y) : 0 < min (Int.fract y) (1 - Int.fract y) := by
  have h0 : Int.fract y ≠ 0 := by
    intro h
    rw [Int.fract, sub_eq_zero] at h
    exact hy.ne_int _ h
  exact lt_min (lt_of_le_of_ne (Int.fract_nonneg y) (Ne.symm h0))
    (by linarith [Int.fract_lt_one y])

/-- Paper, Theorem \ref{IB:thm:413}\ref{IB:413b}. Let `γ = d ∈ ℕ` and `x ∉ ℚ`. Then `A_x` contains
no set `B + F` with `B ⊆ ℕ` infinite and `F ⊆ ℤ`, `|F| = d + 1`. -/
theorem thm413b (d : ℕ) (x : ℝ) (hx : Irrational x) (B : Set ℕ) (hB : B.Infinite)
    (F : Finset ℤ) (hF : F.card = d + 1) :
    ¬ sumset (((↑) : ℕ → ℤ) '' B) (F : Set ℤ) ⊆ ((↑) : ℕ → ℤ) '' Ax (d : ℝ) x := by
  intro hsub
  set D := denom F
  have hD : D ≠ 0 := denom_ne_zero F
  have hDx : Irrational ((D : ℝ) * x) := hx.intCast_mul hD
  set ε := min (Int.fract ((D : ℝ) * x)) (1 - Int.fract ((D : ℝ) * x))
  have hε : 0 < ε := min_fract_pos hDx
  set K : ℝ := ∑ c ∈ F, |(mu F c : ℝ)|
  have hK : 0 ≤ K := Finset.sum_nonneg fun c _ => abs_nonneg _
  set η : ℝ := ε / (K + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  set T : ℝ := Real.exp (1 / η) + 2 + ∑ c ∈ F, |(c : ℝ)|
  obtain ⟨b, hbB, hbT⟩ := hB.exists_gt ⌈T⌉₊
  have hbT' : T < b := by
    have := Nat.le_ceil T
    have : (⌈T⌉₊ : ℝ) < b := by exact_mod_cast hbT
    linarith
  -- each `b + c` is a large element of `A_x`
  have hfr : ∀ c ∈ F, Int.fract (((b : ℝ) + c) ^ d * x) ≤ η := by
    intro c hc
    have hcabs : |(c : ℝ)| ≤ ∑ c ∈ F, |(c : ℝ)| :=
      Finset.single_le_sum (f := fun c : ℤ => |(c : ℝ)|) (fun _ _ => abs_nonneg _) hc
    have hcge : -(∑ c ∈ F, |(c : ℝ)|) ≤ c := by
      have := neg_abs_le (c : ℝ)
      linarith
    have hbig : Real.exp (1 / η) + 2 ≤ (b : ℝ) + c := by linarith
    obtain ⟨n, hn, hneq⟩ := hsub ⟨(b : ℤ), ⟨b, hbB, rfl⟩, c, hc, rfl⟩
    have hnR : (n : ℝ) = (b : ℝ) + c := by exact_mod_cast hneq
    have hexp := Real.exp_pos (1 / η)
    have hn2 : 2 ≤ n := by
      have : (2 : ℝ) ≤ n := by linarith
      exact_mod_cast this
    have hcond := hn.2 hn2
    rw [Real.rpow_natCast, hnR] at hcond
    have hlog : 1 / η ≤ Real.log ((b : ℝ) + c) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith
    have hlogpos : 0 < Real.log ((b : ℝ) + c) := lt_of_lt_of_le (by positivity) hlog
    calc Int.fract (((b : ℝ) + c) ^ d * x) ≤ 1 / Real.log ((b : ℝ) + c) := hcond
      _ ≤ 1 / (1 / η) := one_div_le_one_div_of_le (by positivity) hlog
      _ = η := by rw [one_div_one_div]
  -- the integer `m = ∑ μ_c ⌊(b + c)^d x⌋` is within `K η < ε` of `D x`
  set m : ℤ := ∑ c ∈ F, mu F c * ⌊((b : ℝ) + c) ^ d * x⌋
  have hsum : (D : ℝ) * x - m = ∑ c ∈ F, (mu F c : ℝ) * Int.fract (((b : ℝ) + c) ^ d * x) := by
    have h1 := sum_mu d F hF (b : ℝ)
    have h2 : (D : ℝ) * x = ∑ c ∈ F, (mu F c : ℝ) * (((b : ℝ) + c) ^ d * x) := by
      rw [← h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [h2]
    simp only [m]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Int.fract]
    ring
  have hle : |(D : ℝ) * x - m| ≤ K * η := by
    rw [hsum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c hc => ?_
    rw [abs_mul, abs_of_nonneg (Int.fract_nonneg (((b : ℝ) + c) ^ d * x))]
    exact mul_le_mul_of_nonneg_left (hfr c hc) (abs_nonneg _)
  have hKη : K * η < ε := by
    have : K * η = ε * (K / (K + 1)) := by simp only [η]; field_simp
    rw [this]
    have : K / (K + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  have := dist_int_ge (y := (D : ℝ) * x) m
  linarith

/-- Paper, Theorem \ref{IB:thm:413}\ref{IB:413b}, "in particular": for `γ = d ∈ ℕ` and
`x ∉ ℚ`, the set `A_x` contains no `B + C` with `B, C ⊆ ℕ` infinite. -/
theorem thm413b_sumset (d : ℕ) (x : ℝ) (hx : Irrational x) (B C : Set ℕ) (hB : B.Infinite)
    (hC : C.Infinite) : ¬ sumset B C ⊆ Ax (d : ℝ) x := by
  intro hsub
  obtain ⟨F₀, hF₀C, hF₀card⟩ := hC.exists_subset_card_eq (d + 1)
  set F : Finset ℤ := F₀.map Nat.castEmbedding
  have hF : F.card = d + 1 := by simp [F, hF₀card]
  refine thm413b d x hx B hB F hF ?_
  rintro z ⟨_, ⟨b, hb, rfl⟩, c, hc, rfl⟩
  simp only [F, Finset.coe_map, Set.mem_image, Finset.mem_coe] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  exact ⟨b + c', hsub ⟨b, hb, c', hF₀C hc', rfl⟩, by simp⟩

/-- Paper, remark after Theorem \ref{IB:thm:413}: for `γ = d ∈ ℕ`, `d ≥ 1`, and rational
`x = p/q` (`q ≥ 1`), every positive multiple of `q` lies in `A_x`. -/
theorem rational_mem (d : ℕ) (hd : 1 ≤ d) (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (k : ℕ) (hk : 1 ≤ k) :
    q * k ∈ Ax (d : ℝ) ((p : ℝ) / q) := by
  refine ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), fun hn => ?_⟩
  rw [Real.rpow_natCast]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hint : ((q * k : ℕ) : ℝ) ^ (e + 1) * ((p : ℝ) / q) =
      (((q : ℤ) ^ e * (k : ℤ) ^ (e + 1) * p : ℤ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [hint, Int.fract_intCast]
  exact div_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q * k)))

/-- Paper, remark after Theorem \ref{IB:thm:413}: for `γ = d ∈ ℕ`, `d ≥ 1`, and rational
`x = p/q`, the set `A_x` contains `B + C` for infinite `B = C = qℕ`. -/
theorem rational_sumset (d : ℕ) (hd : 1 ≤ d) (p : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ Ax (d : ℝ) ((p : ℝ) / q) := by
  set Q : Set ℕ := {n | ∃ k, 1 ≤ k ∧ n = q * k}
  have hQ : Q.Infinite := by
    have : Set.range (fun k : ℕ => q * (k + 1)) ⊆ Q := by
      rintro _ ⟨k, rfl⟩
      exact ⟨k + 1, by omega, rfl⟩
    refine Set.Infinite.mono this (Set.infinite_range_of_injective fun a b h => ?_)
    have := Nat.eq_of_mul_eq_mul_left (by omega) h
    omega
  refine ⟨Q, Q, hQ, hQ, ?_⟩
  rintro _ ⟨_, ⟨k, hk, rfl⟩, _, ⟨l, hl, rfl⟩, rfl⟩
  rw [← mul_add]
  exact rational_mem d hd p q hq (k + l) (by omega)

/-! ## Lemma \ref{IB:lem:thick} -/

/-- `A ⊆ ℕ` is thick if it contains arbitrarily long intervals of consecutive integers. -/
def Thick (A : Set ℕ) : Prop := ∀ L : ℕ, ∃ n, ∀ h ≤ L, n + h ∈ A

lemma Thick.exists_gt {A : Set ℕ} (hA : Thick A) (M L : ℕ) : ∃ n, M < n ∧ ∀ h ≤ L, n + h ∈ A := by
  obtain ⟨n, hn⟩ := hA (M + 1 + L)
  exact ⟨n + (M + 1), by omega, fun h hh => by rw [add_assoc]; exact hn _ (by omega)⟩

/-- Paper, Lemma \ref{IB:lem:thick}: a thick set `A ⊆ ℕ` contains `B + C` for some infinite
`B, C ⊆ ℕ`. -/
theorem lem_thick {A : Set ℕ} (hA : Thick A) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ A := by
  -- `nb c`: some `b > c` starting an interval `[b, b + c] ⊆ A`
  choose nb hnb using fun c : ℕ => hA.exists_gt c c
  -- the pairs `(b_j, c_j)`, with `b_{j+1} = nb c_j` and `c_{j+1} = nb b_{j+1}`
  let seq : ℕ → ℕ × ℕ := fun j => Nat.rec (nb 0, nb (nb 0))
    (fun _ x => (nb x.2, nb (nb x.2))) j
  have hs0 : seq 0 = (nb 0, nb (nb 0)) := rfl
  have hs : ∀ j, seq (j + 1) = (nb (seq j).2, nb (nb (seq j).2)) := fun j => rfl
  set b : ℕ → ℕ := fun j => (seq j).1
  set c : ℕ → ℕ := fun j => (seq j).2
  have hcb : ∀ j, c j = nb (b j) := by
    intro j; cases j with
    | zero => rfl
    | succ j => simp only [c, b, hs]
  have hbc : ∀ j, b (j + 1) = nb (c j) := fun j => by simp only [b, c, hs]
  have hb_lt_c : ∀ j, b j < c j := fun j => by rw [hcb]; exact (hnb _).1
  have hc_lt_b : ∀ j, c j < b (j + 1) := fun j => by rw [hbc]; exact (hnb _).1
  have hbmono : StrictMono b := strictMono_nat_of_lt_succ fun j =>
    (hb_lt_c j).trans (hc_lt_b j)
  have hcmono : StrictMono c := strictMono_nat_of_lt_succ fun j =>
    (hc_lt_b j).trans (hb_lt_c (j + 1))
  -- intervals: `[b_{j+1}, b_{j+1} + c_j] ⊆ A` and `[c_j, c_j + b_j] ⊆ A`
  have hIb : ∀ j, ∀ h ≤ c j, b (j + 1) + h ∈ A := fun j => by rw [hbc]; exact (hnb _).2
  have hIc : ∀ j, ∀ h ≤ b j, c j + h ∈ A := fun j => by rw [hcb]; exact (hnb _).2
  refine ⟨Set.range b, Set.range c, Set.infinite_range_of_injective hbmono.injective,
    Set.infinite_range_of_injective hcmono.injective, ?_⟩
  rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨i, rfl⟩, rfl⟩
  rcases lt_or_ge i j with hij | hij
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact hIb j' (c i) (hcmono.monotone (by omega))
  · rw [add_comm]
    exact hIc i (b j) (hbmono.monotone hij)

end Kmrr25.Q413
