import Kmrr25.Basic

/-!
# Sums and shifted products at logarithmic scale (Question 5.4)

Paper, Section \ref{SP:sec:q54}. Let `I = [7/20, 13/20)` and
`A = {n ∈ ℕ : {log₂ n} ∈ I}`, where `{·}` is the fractional part (`Int.fract`).

Main results:
* `shiftphase` : Lemma \ref{SP:lem:shiftphase} (with the hypothesis `M ≥ 4`, see below);
* `no_ratio58_config` : Theorem \ref{SP:thm:q54}(a);
* `no_shifted_config` : Theorem \ref{SP:thm:q54}(b), for arbitrary shifts `t₁, t₂ ∈ ℤ`;
* `no_sum_and_shifted_product` : the final statement of Theorem \ref{SP:thm:q54}: there are no
  infinite `B, C ⊆ ℕ` with `B + C ⊆ A` and `BC + 1 ⊆ A`;
* `no_sum_and_product` : the case `t₁ = t₂ = 0` (Remark \ref{SP:rem:q52});
* `logDensity_A` : Proposition \ref{SP:prop:Aprops}(i), the logarithmic density of `A` exists
  and equals `3/10`, i.e. `(1 / log N) Σ_{n=1}^N 1_A(n)/n → 3/10`;
* `q54_negative` : the combination (negative answer to Question \ref{SP:q:54}).

Remarks on the statements.
* Sets `B, C` are subsets of `ℕ` including `0`; this only strengthens the non-existence
  statements, since `0 ∉ A`.
* Lemma \ref{SP:lem:shiftphase} needs `ε_M = log₂(1 + 1/M) < 7/20`, i.e. `M ≥ 4`; the paper
  states it for every `M ∈ ℕ`, but for `M ≤ 3` it is false: `(x, y) = (8, 13)` for `M = 1`,
  `(6, 15)` for `M = 2`, `(10, 31)` for `M = 3` satisfy `y ≥ M x`, `x + y ∈ A` and
  `{log₂ y} ≥ 13/20`. The paper uses the lemma only with `M = 58`.
* In part (a) the numbers `b₀, c₀` are positive, as in the paper (`ℕ = {1, 2, …}`).

Not covered: Proposition \ref{SP:prop:Aprops}(ii) (aperiodicity) and (iii) (upper and lower
natural densities of `A`).
-/

open Real

namespace Kmrr25.Q54

/-- The interval `I = [7/20, 13/20)`. -/
def I : Set ℝ := Set.Ico (7 / 20) (13 / 20)

/-- The set `A = {n ∈ ℕ : {log₂ n} ∈ [7/20, 13/20)}`. -/
def A : Set ℕ := {n | Int.fract (Real.logb 2 n) ∈ I}

lemma zero_not_mem_A : (0 : ℕ) ∉ A := by
  simp [A, I]

/-! ### Elementary estimates -/

/-- If `r^n < 2^m` then `log₂ r < m / n`. -/
lemma logb_two_lt_of_pow_lt {r : ℝ} (hr : 0 < r) {n m : ℕ} (hn : 0 < n) (h : r ^ n < 2 ^ m) :
    Real.logb 2 r < m / n := by
  have h1 : Real.logb 2 (r ^ n) < Real.logb 2 (2 ^ m) :=
    Real.logb_lt_logb one_lt_two (pow_pos hr n) h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h1
  rw [lt_div_iff₀ (by exact_mod_cast hn)]
  linarith

/-- If `r^n ≤ 2^m` then `log₂ r ≤ m / n`. -/
lemma logb_two_le_of_pow_le {r : ℝ} (hr : 0 < r) {n m : ℕ} (hn : 0 < n) (h : r ^ n ≤ 2 ^ m) :
    Real.logb 2 r ≤ m / n := by
  have h1 : Real.logb 2 (r ^ n) ≤ Real.logb 2 (2 ^ m) :=
    Real.logb_le_logb_of_le one_lt_two (pow_pos hr n) h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h1
  rw [le_div_iff₀ (by exact_mod_cast hn)]
  linarith

/-- `{w + e} = {w} + e` when `0 ≤ {w} + e < 1`. -/
lemma fract_add_eq {w e : ℝ} (h0 : 0 ≤ Int.fract w + e) (h1 : Int.fract w + e < 1) :
    Int.fract (w + e) = Int.fract w + e :=
  Int.fract_eq_iff.2 ⟨h0, h1, ⌊w⌋, by rw [← Int.self_sub_fract]; ring⟩

/-- The arithmetic core of the obstruction: if `z ≡ u (mod 1)` with `13/20 ≤ u < 27/20`,
then `{z} ∉ I`. -/
lemma fract_not_mem_I {z u : ℝ} (hzu : ∃ k : ℤ, z - u = k) (h1 : 13 / 20 ≤ u)
    (h2 : u < 27 / 20) : Int.fract z ∉ I := by
  obtain ⟨k, hk⟩ := hzu
  rcases lt_or_ge u 1 with hu | hu
  · have : Int.fract z = u := Int.fract_eq_iff.2 ⟨by linarith, hu, k, hk⟩
    rw [this]
    exact fun h => absurd h.2 (not_lt.2 h1)
  · have : Int.fract z = u - 1 :=
      Int.fract_eq_iff.2 ⟨by linarith, by linarith, k + 1, by push_cast; linarith⟩
    rw [this]
    exact fun h => by linarith [h.1]

/-- `ε_M = log₂(1 + 1/M) < 7/20` for `M ≥ 4`. -/
lemma eps_lt (M : ℕ) (hM : 4 ≤ M) : Real.logb 2 (1 + 1 / (M : ℝ)) < 7 / 20 := by
  have hM' : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : Real.logb 2 (1 + 1 / (M : ℝ)) ≤ Real.logb 2 (5 / 4) := by
    apply Real.logb_le_logb_of_le one_lt_two (by positivity)
    have : 1 / (M : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hM'
    linarith
  have h2 : Real.logb 2 (5 / 4) < (7 : ℕ) / (20 : ℕ) :=
    logb_two_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
  push_cast at h2
  linarith

/-- `ε_58 = log₂(1 + 1/58) < 1/40`. -/
lemma eps58_lt : Real.logb 2 (1 + 1 / (58 : ℝ)) < 1 / 40 := by
  have h := logb_two_lt_of_pow_lt (r := 1 + 1 / (58 : ℝ)) (n := 40) (m := 1) (by norm_num)
    (by norm_num) (by norm_num)
  push_cast at h
  exact h

/-- If `0 < y` and `100 |s| ≤ y`, then `|log₂(y + s) - log₂ y| ≤ 1/60`. -/
lemma abs_logb_add_sub_le {y s : ℝ} (hy : 0 < y) (hs : 100 * |s| ≤ y) :
    |Real.logb 2 (y + s) - Real.logb 2 y| ≤ 1 / 60 := by
  have hs' := abs_le.1 (show |s| ≤ y / 100 by linarith)
  have hys : 0 < y + s := by linarith
  rw [← Real.logb_div hys.ne' hy.ne']
  have hr0 : 0 < (y + s) / y := div_pos hys hy
  have hup : (y + s) / y ≤ 101 / 100 := by
    rw [div_le_iff₀ hy]; linarith
  have hlo : 99 / 100 ≤ (y + s) / y := by
    rw [le_div_iff₀ hy]; linarith
  rw [abs_le]
  constructor
  · have h1 : Real.logb 2 (99 / 100) ≤ Real.logb 2 ((y + s) / y) :=
      Real.logb_le_logb_of_le one_lt_two (by norm_num) hlo
    have h2 : Real.logb 2 (100 / 99) ≤ (1 : ℕ) / (60 : ℕ) :=
      logb_two_le_of_pow_le (by norm_num) (by norm_num) (by norm_num)
    have h3 : Real.logb 2 (99 / 100) = - Real.logb 2 (100 / 99) := by
      rw [← Real.logb_inv]; norm_num
    push_cast at h2
    linarith
  · have h1 : Real.logb 2 ((y + s) / y) ≤ Real.logb 2 (101 / 100) :=
      Real.logb_le_logb_of_le one_lt_two hr0 hup
    have h2 : Real.logb 2 (101 / 100) ≤ (1 : ℕ) / (60 : ℕ) :=
      logb_two_le_of_pow_le (by norm_num) (by norm_num) (by norm_num)
    push_cast at h2
    linarith

/-- If `|z - w| ≤ δ ≤ 7/20` and `{w} ∈ I`, then `{z} = {w} + (z - w)`, so
`7/20 - δ ≤ {z} < 13/20 + δ`. -/
lemma fract_near {z w δ : ℝ} (hw : Int.fract w ∈ I) (hzw : |z - w| ≤ δ) (hδ : δ ≤ 7 / 20) :
    7 / 20 - δ ≤ Int.fract z ∧ Int.fract z < 13 / 20 + δ := by
  have h := abs_le.1 hzw
  obtain ⟨hw1, hw2⟩ := hw
  have e : Int.fract z = Int.fract w + (z - w) := by
    rw [← fract_add_eq (by linarith) (by linarith)]
    ring_nf
  rw [e]
  constructor <;> linarith

/-! ### Lemma \ref{SP:lem:shiftphase} -/

/-- Paper, Lemma \ref{SP:lem:shiftphase}, for `M ≥ 4`. Let `ε_M = log₂(1 + 1/M)`. If
`x, y ∈ ℕ` satisfy `y ≥ M x` and `x + y ∈ A`, then `{log₂ y} ∈ [7/20 - ε_M, 13/20)`.
(For `M ≤ 3` the statement is false; see the module docstring.) -/
theorem shiftphase (M : ℕ) (hM : 4 ≤ M) {x y : ℕ} (hxy : M * x ≤ y) (h : x + y ∈ A) :
    Int.fract (Real.logb 2 y) ∈ Set.Ico (7 / 20 - Real.logb 2 (1 + 1 / (M : ℝ))) (13 / 20) := by
  have hy : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · subst h0
      have : x = 0 := by
        have : M * x = 0 := by omega
        rcases Nat.mul_eq_zero.1 this with h1 | h1
        · omega
        · exact h1
      subst this
      exact absurd h zero_not_mem_A
    · exact h0
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hxyR : (M : ℝ) * x ≤ y := by exact_mod_cast hxy
  have hA : Int.fract (Real.logb 2 ((x : ℝ) + y)) ∈ I := by
    have := h
    simp only [A, Set.mem_ofPred_eq, Nat.cast_add] at this
    exact this
  -- `ε' = log₂((x + y) / y)`
  set e := Real.logb 2 (((x : ℝ) + y) / y) with he
  have hxy_pos : (0 : ℝ) < x + y := by positivity
  have hsplit : Real.logb 2 ((x : ℝ) + y) = Real.logb 2 y + e := by
    rw [he, Real.logb_div hxy_pos.ne' hyR.ne']; ring
  have he0 : 0 ≤ e := by
    apply Real.logb_nonneg one_lt_two
    rw [le_div_iff₀ hyR]; simp
  have heM : e ≤ Real.logb 2 (1 + 1 / (M : ℝ)) := by
    apply Real.logb_le_logb_of_le one_lt_two (div_pos hxy_pos hyR)
    rw [div_le_iff₀ hyR, add_mul, one_mul, add_comm (y : ℝ), one_div, inv_mul_eq_div,
      add_le_add_iff_right, le_div_iff₀ hMR, mul_comm]
    exact hxyR
  have heps := eps_lt M hM
  obtain ⟨h1, h2⟩ := hA
  have e1 : Int.fract (Real.logb 2 (y : ℝ)) = Int.fract (Real.logb 2 ((x : ℝ) + y)) + (-e) := by
    rw [← fract_add_eq (by linarith) (by linarith), hsplit]
    ring_nf
  rw [e1]
  constructor <;> linarith

/-! ### Theorem \ref{SP:thm:q54} -/

/-- Paper, Theorem \ref{SP:thm:q54}(a). There are no `b₀, c₀, b, c ∈ ℕ = {1, 2, …}` and
`τ ∈ {0, 1}` with `b ≥ 58 c₀` and `c ≥ 58 b₀` such that `b₀ + c ∈ A`, `c₀ + b ∈ A` and
`bc + τ ∈ A`. -/
theorem no_ratio58_config (b₀ c₀ b c τ : ℕ) (hb₀ : 0 < b₀) (hc₀ : 0 < c₀)
    (hτ : τ = 0 ∨ τ = 1) (hb : 58 * c₀ ≤ b) (hc : 58 * b₀ ≤ c) :
    ¬ (b₀ + c ∈ A ∧ c₀ + b ∈ A ∧ b * c + τ ∈ A) := by
  rintro ⟨h1, h2, h3⟩
  have hc' := shiftphase 58 (by norm_num) hc h1
  have hb' := shiftphase 58 (by norm_num) hb h2
  have hε := eps58_lt
  push_cast at hc' hb'
  have hbR : (58 : ℝ) ≤ b := by exact_mod_cast (show 58 ≤ b by omega)
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast (show 1 ≤ c by omega)
  have hτR : (τ : ℝ) ≤ 1 := by rcases hτ with h | h <;> simp [h]
  have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
  have hbc : (58 : ℝ) ≤ b * c := by nlinarith
  have hbc0 : (0 : ℝ) < b * c := by linarith
  set η := Real.logb 2 (((b : ℝ) * c + τ) / (b * c)) with hη
  have hη0 : 0 ≤ η := by
    apply Real.logb_nonneg one_lt_two
    rw [le_div_iff₀ hbc0]; linarith
  have hηε : η ≤ Real.logb 2 (1 + 1 / (58 : ℝ)) := by
    apply Real.logb_le_logb_of_le one_lt_two (by positivity)
    rw [div_le_iff₀ hbc0]
    nlinarith
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hc0 : (c : ℝ) ≠ 0 := by positivity
  have hz : Real.logb 2 ((b : ℝ) * c + τ) = Real.logb 2 b + Real.logb 2 c + η := by
    rw [hη, Real.logb_div (by positivity) hbc0.ne', Real.logb_mul hb0 hc0]; ring
  have h3' : Int.fract (Real.logb 2 ((b : ℝ) * c + τ)) ∈ I := by
    have := h3
    simp only [A, Set.mem_ofPred_eq] at this
    push_cast at this
    exact this
  refine fract_not_mem_I (u := Int.fract (Real.logb 2 b) + Int.fract (Real.logb 2 c) + η)
    ⟨⌊Real.logb 2 (b : ℝ)⌋ + ⌊Real.logb 2 (c : ℝ)⌋, ?_⟩ ?_ ?_ h3'
  · have e1 := Int.self_sub_fract (Real.logb 2 (b : ℝ))
    have e2 := Int.self_sub_fract (Real.logb 2 (c : ℝ))
    rw [hz]; push_cast; linarith
  · linarith [hb'.1, hc'.1]
  · linarith [hb'.2, hc'.2]

/-- Paper, Theorem \ref{SP:thm:q54}(b). Let `t₁, t₂ ∈ ℤ`. There are no infinite sets
`B, C ⊆ ℕ` with `b + c + t₁ ∈ A` and `bc + t₂ ∈ A` for all `b ∈ B` and `c ∈ C`. -/
theorem no_shifted_config (t₁ t₂ : ℤ) :
    ¬ ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧
      (∀ b ∈ B, ∀ c ∈ C, ∃ n ∈ A, (n : ℤ) = b + c + t₁) ∧
      (∀ b ∈ B, ∀ c ∈ C, ∃ n ∈ A, (n : ℤ) = b * c + t₂) := by
  rintro ⟨B, C, hB, hC, hsum, hprod⟩
  obtain ⟨b₀, hb₀⟩ := hB.nonempty
  obtain ⟨c₀, hc₀⟩ := hC.nonempty
  set S : ℝ := |(b₀ : ℝ) + t₁| + |(c₀ : ℝ) + t₁| + |(t₂ : ℝ)| with hS
  obtain ⟨c, hcC, hcS⟩ := hC.exists_gt ⌈100 * S⌉₊
  obtain ⟨b, hbB, hbS⟩ := hB.exists_gt ⌈100 * S⌉₊
  have hcS' : 100 * S < c := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hcS)
  have hbS' : 100 * S < b := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hbS)
  have hS1 : |(b₀ : ℝ) + t₁| ≤ S := by
    rw [hS]; linarith [abs_nonneg ((c₀ : ℝ) + t₁), abs_nonneg (t₂ : ℝ)]
  have hS2 : |(c₀ : ℝ) + t₁| ≤ S := by
    rw [hS]; linarith [abs_nonneg ((b₀ : ℝ) + t₁), abs_nonneg (t₂ : ℝ)]
  have hS3 : |(t₂ : ℝ)| ≤ S := by
    rw [hS]; linarith [abs_nonneg ((b₀ : ℝ) + t₁), abs_nonneg ((c₀ : ℝ) + t₁)]
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hS3
  have hcpos : (0 : ℝ) < c := lt_of_le_of_lt (by positivity) hcS'
  have hbpos : (0 : ℝ) < b := lt_of_le_of_lt (by positivity) hbS'
  have hc1 : (1 : ℝ) ≤ c := by
    have : 0 < c := by exact_mod_cast hcpos
    exact_mod_cast this
  -- phase of `c`
  obtain ⟨n₁, hn₁A, hn₁⟩ := hsum b₀ hb₀ c hcC
  have hn₁R : (n₁ : ℝ) = c + ((b₀ : ℝ) + t₁) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hn₁
    push_cast at this
    linarith
  have hc_near := fract_near (z := Real.logb 2 c) (w := Real.logb 2 n₁) (δ := 1 / 60) hn₁A
    (by
      rw [abs_sub_comm, hn₁R]
      exact abs_logb_add_sub_le hcpos (by linarith))
    (by norm_num)
  -- phase of `b`
  obtain ⟨n₂, hn₂A, hn₂⟩ := hsum b hbB c₀ hc₀
  have hn₂R : (n₂ : ℝ) = b + ((c₀ : ℝ) + t₁) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hn₂
    push_cast at this
    linarith
  have hb_near := fract_near (z := Real.logb 2 b) (w := Real.logb 2 n₂) (δ := 1 / 60) hn₂A
    (by
      rw [abs_sub_comm, hn₂R]
      exact abs_logb_add_sub_le hbpos (by linarith))
    (by norm_num)
  -- the product
  obtain ⟨n₃, hn₃A, hn₃⟩ := hprod b hbB c hcC
  have hn₃R : (n₃ : ℝ) = b * c + t₂ := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hn₃
    push_cast at this
    linarith
  have hbc : (b : ℝ) ≤ b * c := by nlinarith
  have hη := abs_logb_add_sub_le (y := (b : ℝ) * c) (s := t₂) (by positivity) (by linarith)
  have hη' := abs_le.1 hη
  set η := Real.logb 2 ((b : ℝ) * c + t₂) - Real.logb 2 ((b : ℝ) * c) with hηdef
  have hz : Real.logb 2 (n₃ : ℝ) = Real.logb 2 b + Real.logb 2 c + η := by
    rw [hηdef, hn₃R, Real.logb_mul hbpos.ne' hcpos.ne']; ring
  refine fract_not_mem_I (z := Real.logb 2 (n₃ : ℝ))
    (u := Int.fract (Real.logb 2 b) + Int.fract (Real.logb 2 c) + η)
    ⟨⌊Real.logb 2 (b : ℝ)⌋ + ⌊Real.logb 2 (c : ℝ)⌋, ?_⟩ ?_ ?_ hn₃A
  · have e1 := Int.self_sub_fract (Real.logb 2 (b : ℝ))
    have e2 := Int.self_sub_fract (Real.logb 2 (c : ℝ))
    rw [hz]; push_cast; linarith
  · linarith [hb_near.1, hc_near.1]
  · linarith [hb_near.2, hc_near.2]

/-- Paper, Theorem \ref{SP:thm:q54}, final statement (negative answer to Question
\ref{SP:q:54}, together with Proposition \ref{SP:prop:Aprops}(i), which is not formalized here):
there are no infinite sets `B, C ⊆ ℕ` with `B + C ⊆ A` and `BC + 1 ⊆ A`. -/
theorem no_sum_and_shifted_product :
    ¬ ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ A ∧
      {x | ∃ b ∈ B, ∃ c ∈ C, x = b * c + 1} ⊆ A := by
  rintro ⟨B, C, hB, hC, hs, hp⟩
  refine no_shifted_config 0 1 ⟨B, C, hB, hC, fun b hb c hc => ?_, fun b hb c hc => ?_⟩
  · exact ⟨b + c, hs ⟨b, hb, c, hc, rfl⟩, by push_cast; ring⟩
  · exact ⟨b * c + 1, hp ⟨b, hb, c, hc, rfl⟩, by push_cast; ring⟩

/-- Paper, Remark \ref{SP:rem:q52}: the case `t₁ = t₂ = 0` of Theorem \ref{SP:thm:q54}(b):
there are no infinite sets `B, C ⊆ ℕ` with `B + C ⊆ A` and `BC ⊆ A`. -/
theorem no_sum_and_product :
    ¬ ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ A ∧
      {x | ∃ b ∈ B, ∃ c ∈ C, x = b * c} ⊆ A := by
  rintro ⟨B, C, hB, hC, hs, hp⟩
  refine no_shifted_config 0 0 ⟨B, C, hB, hC, fun b hb c hc => ?_, fun b hb c hc => ?_⟩
  · exact ⟨b + c, hs ⟨b, hb, c, hc, rfl⟩, by push_cast; ring⟩
  · exact ⟨b * c, hp ⟨b, hb, c, hc, rfl⟩, by push_cast; ring⟩

/-! ### Proposition \ref{SP:prop:Aprops}(i): the logarithmic density of `A` -/

section LogDensity

open Filter Topology Finset
open scoped Classical

/-- The logarithmic partial sum `Σ_{n=1}^N 1_S(n) / n`. The logarithmic density of `S` is the
limit of `logSum S N / log N` as `N → ∞` (when it exists). -/
noncomputable def logSum (S : Set ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, if n ∈ S then (1 : ℝ) / n else 0

/-- For `2^k ≤ n < 2^{k+1}`, `n ∈ A` iff `2^{k + 7/20} ≤ n < 2^{k + 13/20}`. -/
lemma mem_A_iff {k n : ℕ} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) :
    n ∈ A ↔ (2 : ℝ) ^ ((k : ℝ) + 7 / 20) ≤ n ∧ (n : ℝ) < 2 ^ ((k : ℝ) + 13 / 20) := by
  have hn : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le (pow_pos two_pos k) h1
    exact_mod_cast this
  have hk1 : (k : ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hn, Real.rpow_natCast]
    exact_mod_cast h1
  have hk2 : Real.logb 2 n < (k : ℝ) + 1 := by
    rw [Real.logb_lt_iff_lt_rpow one_lt_two hn]
    have : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
    exact_mod_cast h2
  have hfl : ⌊Real.logb 2 n⌋ = k := by
    rw [Int.floor_eq_iff]
    push_cast
    exact ⟨hk1, hk2⟩
  have hfr : Int.fract (Real.logb 2 n) = Real.logb 2 n - k := by
    rw [← Int.self_sub_floor, hfl]
    push_cast
    ring
  simp only [A, I, Set.mem_ofPred_eq, Set.mem_Ico, hfr]
  rw [← Real.le_logb_iff_rpow_le one_lt_two hn, ← Real.logb_lt_iff_lt_rpow one_lt_two hn]
  constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith

/-- `U k = ⌈2^{k + 7/20}⌉`, the least element of `A ∩ [2^k, 2^{k+1})`. -/
noncomputable def U (k : ℕ) : ℕ := ⌈(2 : ℝ) ^ ((k : ℝ) + 7 / 20)⌉₊

/-- `V k = ⌈2^{k + 13/20}⌉`, so that `A ∩ [2^k, 2^{k+1}) = [U k, V k)`. -/
noncomputable def V (k : ℕ) : ℕ := ⌈(2 : ℝ) ^ ((k : ℝ) + 13 / 20)⌉₊

lemma two_pow_le_rpow (k : ℕ) {c : ℝ} (hc : 0 ≤ c) : (2 : ℝ) ^ k ≤ 2 ^ ((k : ℝ) + c) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)

lemma rpow_le_two_pow_succ (k : ℕ) {c : ℝ} (hc : c ≤ 1) :
    (2 : ℝ) ^ ((k : ℝ) + c) ≤ 2 ^ (k + 1) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two (by push_cast; linarith)

lemma pow_le_ceil (k : ℕ) {c : ℝ} (hc : 0 ≤ c) : 2 ^ k ≤ ⌈(2 : ℝ) ^ ((k : ℝ) + c)⌉₊ := by
  have := (two_pow_le_rpow k hc).trans (Nat.le_ceil _)
  exact_mod_cast this

lemma ceil_le_pow (k : ℕ) {c : ℝ} (hc : c ≤ 1) : ⌈(2 : ℝ) ^ ((k : ℝ) + c)⌉₊ ≤ 2 ^ (k + 1) := by
  rw [Nat.ceil_le]
  exact_mod_cast rpow_le_two_pow_succ k hc

/-- The dyadic block sum `Σ_{2^k ≤ n < 2^{k+1}} 1_A(n)/n` equals `Σ_{U_k ≤ n < V_k} 1/n`. -/
lemma block_eq (k : ℕ) :
    ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), (if n ∈ A then (1 : ℝ) / n else 0) =
      ∑ n ∈ Ico (U k) (V k), (1 : ℝ) / n := by
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Ico, U, V]
  constructor
  · rintro ⟨⟨h1, h2⟩, hA⟩
    rw [mem_A_iff h1 h2] at hA
    exact ⟨Nat.ceil_le.2 hA.1, Nat.lt_ceil.2 hA.2⟩
  · rintro ⟨h1, h2⟩
    have h1' : 2 ^ k ≤ n := (pow_le_ceil k (by norm_num)).trans h1
    have h2' : n < 2 ^ (k + 1) := lt_of_lt_of_le h2 (ceil_le_pow k (by norm_num))
    refine ⟨⟨h1', h2'⟩, ?_⟩
    rw [mem_A_iff h1' h2']
    exact ⟨Nat.ceil_le.1 h1, Nat.lt_ceil.1 h2⟩

/-- `G m = Σ_{1 ≤ n < m} 1/n`. -/
noncomputable def G (m : ℕ) : ℝ := ∑ n ∈ Ico 1 m, (1 : ℝ) / n

lemma G_succ (m : ℕ) : G (m + 1) = harmonic m := by
  rw [G, sum_Ico_eq_sum_range, harmonic]
  push_cast
  refine sum_congr (by simp) fun i _ => ?_
  rw [one_div, add_comm]

lemma tendsto_G_sub_log :
    Tendsto (fun m : ℕ => G m - Real.log m) atTop (𝓝 Real.eulerMascheroniConstant) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  simp only [G_succ, Nat.cast_add, Nat.cast_one]
  exact Real.tendsto_harmonic_sub_log_add_one

lemma sum_Ico_eq_G_sub {u v : ℕ} (hu : 1 ≤ u) (huv : u ≤ v) :
    ∑ n ∈ Ico u v, (1 : ℝ) / n = G v - G u := by
  rw [G, G, ← sum_Ico_consecutive _ hu huv]
  ring

lemma log_ceil_sub_log {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ Real.log ⌈x⌉₊ - Real.log x ∧ Real.log ⌈x⌉₊ - Real.log x ≤ 1 / x := by
  have hx0 : 0 < x := by linarith
  have h1 : x ≤ ⌈x⌉₊ := Nat.le_ceil x
  have h2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hc0 : (0 : ℝ) < ⌈x⌉₊ := lt_of_lt_of_le hx0 h1
  constructor
  · linarith [Real.log_le_log hx0 h1]
  · rw [← Real.log_div hc0.ne' hx0.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < (⌈x⌉₊ : ℝ) / x by positivity)
    have h3 : (⌈x⌉₊ : ℝ) / x - 1 ≤ 1 / x := by
      rw [div_sub_one hx0.ne', div_le_div_iff_of_pos_right hx0]
      linarith
    linarith

/-- `|log ⌈2^{k+c}⌉ - (k + c) log 2| ≤ 2^{-k}` for `0 ≤ c`. -/
lemma abs_log_ceil_rpow (k : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    |Real.log ⌈(2 : ℝ) ^ ((k : ℝ) + c)⌉₊ - ((k : ℝ) + c) * Real.log 2| ≤ (1 / 2) ^ k := by
  have hx : (2 : ℝ) ^ k ≤ 2 ^ ((k : ℝ) + c) := two_pow_le_rpow k hc
  have hx1 : (1 : ℝ) ≤ 2 ^ ((k : ℝ) + c) := (one_le_pow₀ one_le_two).trans hx
  have h := log_ceil_sub_log hx1
  rw [Real.log_rpow two_pos] at h
  rw [abs_le]
  have h4 : 1 / (2 : ℝ) ^ ((k : ℝ) + c) ≤ (1 / 2) ^ k := by
    rw [one_div_pow]
    exact one_div_le_one_div_of_le (by positivity) hx
  constructor <;> linarith [h.1, h.2]

lemma tendsto_ceil_rpow (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun k : ℕ => ⌈(2 : ℝ) ^ ((k : ℝ) + c)⌉₊) atTop atTop :=
  tendsto_atTop_mono (fun k => pow_le_ceil k hc)
    (tendsto_pow_atTop_atTop_of_one_lt (r := 2) one_lt_two)

lemma tendsto_log_ceil_rpow (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun k : ℕ => Real.log ⌈(2 : ℝ) ^ ((k : ℝ) + c)⌉₊ - ((k : ℝ) + c) * Real.log 2)
      atTop (𝓝 0) :=
  squeeze_zero_norm (fun k => abs_log_ceil_rpow k hc)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- The dyadic block sums `Σ_{2^k ≤ n < 2^{k+1}} 1_A(n)/n` tend to `(3/10) log 2`. -/
lemma tendsto_block :
    Tendsto (fun k : ℕ => ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), (if n ∈ A then (1 : ℝ) / n else 0))
      atTop (𝓝 (3 / 10 * Real.log 2)) := by
  have hV := (tendsto_G_sub_log.comp (tendsto_ceil_rpow (13 / 20) (by norm_num)))
  have hU := (tendsto_G_sub_log.comp (tendsto_ceil_rpow (7 / 20) (by norm_num)))
  have hlV := tendsto_log_ceil_rpow (13 / 20) (by norm_num)
  have hlU := tendsto_log_ceil_rpow (7 / 20) (by norm_num)
  have h := (((hV.sub hU).add hlV).sub hlU).add_const (3 / 10 * Real.log 2)
  simp only [sub_self, add_zero, zero_add] at h
  refine h.congr fun k => ?_
  rw [block_eq, sum_Ico_eq_G_sub]
  · simp only [Function.comp, U, V]
    ring
  · exact le_trans (Nat.one_le_two_pow) (pow_le_ceil k (by norm_num))
  · exact Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith))

/-- Paper, Proposition \ref{SP:prop:Aprops}(i). The logarithmic density of `A` exists and
equals `3/10`: `(1 / log N) Σ_{n=1}^N 1_A(n)/n → 3/10`. -/
theorem logDensity_A :
    Tendsto (fun N : ℕ => logSum A N / Real.log N) atTop (𝓝 (3 / 10)) := by
  set f : ℕ → ℝ := fun n => if n ∈ A then (1 : ℝ) / n else 0 with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by
    simp only [hf]; split_ifs <;> positivity
  set blk : ℕ → ℝ := fun k => ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), f n with hblk
  have hdec : ∀ K, ∑ n ∈ Ico 1 (2 ^ K), f n = ∑ k ∈ range K, blk k := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ, ← ih, sum_Ico_consecutive _ Nat.one_le_two_pow
        (Nat.pow_le_pow_right two_pos (Nat.le_succ K))]
  have hblk1 : ∀ k, blk k ≤ 1 := by
    intro k
    have hle : ∀ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), f n ≤ (1 / 2) ^ k := by
      intro n hn
      have hn1 : (2 : ℝ) ^ k ≤ n := by exact_mod_cast (mem_Ico.1 hn).1
      simp only [hf]
      split_ifs
      · rw [one_div_pow]
        exact one_div_le_one_div_of_le (by positivity) hn1
      · positivity
    refine (sum_le_card_nsmul _ _ _ hle).trans ?_
    rw [Nat.card_Ico, nsmul_eq_mul, show 2 ^ (k + 1) - 2 ^ k = 2 ^ k by rw [pow_succ]; omega]
    push_cast
    rw [← mul_pow]
    norm_num
  have hblim : Tendsto blk atTop (𝓝 (3 / 10 * Real.log 2)) := tendsto_block
  set K : ℕ → ℕ := fun N => Nat.log 2 N with hK
  have hKt : Tendsto K atTop atTop :=
    tendsto_atTop.2 fun m => eventually_atTop.2 ⟨2 ^ m, fun N hN =>
      Nat.le_log_of_pow_le one_lt_two hN⟩
  have hK1 : ∀ N, 1 ≤ N → 2 ^ K N ≤ N := fun N hN => Nat.pow_log_le_self 2 (by omega)
  have hK2 : ∀ N, N < 2 ^ (K N + 1) := fun N => Nat.lt_pow_succ_log_self one_lt_two N
  set P : ℕ → ℝ := fun N => ∑ n ∈ Ico (2 ^ K N) (N + 1), f n with hP
  have hS : ∀ N, 1 ≤ N → logSum A N = ∑ k ∈ range (K N), blk k + P N := by
    intro N hN
    have e : Icc 1 N = Ico 1 (N + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
    rw [logSum, e, ← sum_Ico_consecutive _ (Nat.one_le_two_pow (n := K N))
      (show 2 ^ K N ≤ N + 1 by have := hK1 N hN; omega), hdec]
  have hPb : ∀ N, 1 ≤ N → 0 ≤ P N ∧ P N ≤ 1 := by
    intro N hN
    refine ⟨sum_nonneg fun n _ => hf0 n, le_trans ?_ (hblk1 (K N))⟩
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_Ico] at hn ⊢
      exact ⟨hn.1, by have := hK2 N; omega⟩
    · exact fun n _ _ => hf0 n
  have hc : Tendsto (fun N => ((K N : ℝ)⁻¹ * ∑ k ∈ range (K N), blk k)) atTop
      (𝓝 (3 / 10 * Real.log 2)) := hblim.cesaro.comp hKt
  have hinvK : Tendsto (fun N => 1 / (K N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hKt
  have hKpos : ∀ᶠ N in atTop, 1 ≤ K N := hKt.eventually (eventually_ge_atTop 1)
  have hPK : Tendsto (fun N => P N / K N) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinvK ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact div_nonneg (hPb N hN).1 (Nat.cast_nonneg _)
    · filter_upwards [eventually_ge_atTop 1, hKpos] with N hN hKN
      exact div_le_div_of_nonneg_right (hPb N hN).2 (Nat.cast_nonneg _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogb : ∀ N, 1 ≤ N → (K N : ℝ) * Real.log 2 ≤ Real.log N ∧
      Real.log N < ((K N : ℝ) + 1) * Real.log 2 := by
    intro N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    constructor
    · rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hK1 N hN)
    · have : ((K N : ℝ) + 1) = ((K N + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [this, ← Real.log_pow]
      exact Real.log_lt_log hN0 (by exact_mod_cast hK2 N)
  have hlogK : Tendsto (fun N : ℕ => Real.log N / K N) atTop (𝓝 (Real.log 2)) := by
    have hup : Tendsto (fun N : ℕ => Real.log 2 + Real.log 2 * (1 / (K N : ℝ))) atTop
        (𝓝 (Real.log 2)) := by
      simpa using tendsto_const_nhds.add (hinvK.const_mul (Real.log 2))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 1, hKpos] with N hN hKN
      have hKN' : (0 : ℝ) < K N := by exact_mod_cast hKN
      rw [le_div_iff₀ hKN', mul_comm]
      exact (hlogb N hN).1
    · filter_upwards [eventually_ge_atTop 1, hKpos] with N hN hKN
      have hKN' : (0 : ℝ) < K N := by exact_mod_cast hKN
      rw [div_le_iff₀ hKN']
      have := (hlogb N hN).2
      have e : (Real.log 2 + Real.log 2 * (1 / (K N : ℝ))) * K N = ((K N : ℝ) + 1) * Real.log 2 := by
        field_simp
      rw [e]
      exact this.le
  have hlim := (hc.add hPK).div hlogK hlog2.ne'
  rw [add_zero, mul_div_assoc, div_self hlog2.ne', mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hKpos] with N hN hKN
  have hKN' : (0 : ℝ) < K N := by exact_mod_cast hKN
  have hlogN : 0 < Real.log N := lt_of_lt_of_le (by positivity) (hlogb N hN).1
  simp only [Pi.div_apply]
  rw [hS N hN]
  field_simp

end LogDensity

/-- Paper, Theorem \ref{SP:thm:q54}, "in particular" (negative answer to Question \ref{SP:q:54}):
the set `A` has logarithmic density `3/10 > 0`, but there are no infinite sets `B, C ⊆ ℕ` with
`B + C ⊆ A` and `BC + 1 ⊆ A`. -/
theorem q54_negative :
    Filter.Tendsto (fun N : ℕ => logSum A N / Real.log N) Filter.atTop (nhds (3 / 10)) ∧
      ¬ ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ A ∧
        {x | ∃ b ∈ B, ∃ c ∈ C, x = b * c + 1} ⊆ A :=
  ⟨logDensity_A, no_sum_and_shifted_product⟩

end Kmrr25.Q54
