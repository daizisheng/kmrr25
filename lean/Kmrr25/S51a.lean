import Kmrr25.Basic

/-!
# Sums and products in Bohr sets, Beatty sequences and `{λ = 1}`

Paper, Section \ref{SP:sec:u51a}: Theorem \ref{SP:thm:bohr}, Corollary \ref{SP:cor:beatty} and
Theorem \ref{SP:thm:liouville}, which together answer Question \ref{SP:q:u51a} positively.

## Main results

* `bohr` : Theorem \ref{SP:thm:bohr}. If `ϑ` is irrational, `δ ∈ ℝ`, `J ⊆ 𝕋 = ℝ/ℤ` is nonempty
  and open, `M₀ ∈ ℕ`, and `A ⊆ ℕ` contains every `m ≥ M₀` with `m ϑ + δ mod 1 ∈ J`, then there
  is an infinite set `Z` of positive integers with `z + z' ∈ A` and `z z' ∈ A` for all distinct
  `z, z' ∈ Z`, and there are disjoint infinite sets `B, C` of positive integers with
  `B + C ⊆ A` and `BC ⊆ A`.
* `beatty_sum_prod` : Corollary \ref{SP:cor:beatty}. For irrational `α > 0` and `γ ∈ ℝ`, the
  Beatty sequence `{⌊n α + γ⌋ : n ≥ 1}` contains `B + C` and `BC` for infinite sets `B, C` of
  positive integers.
* `liouville`, `liouville_Lplus`, `liouville_Lplus'` : Theorem \ref{SP:thm:liouville}, for both
  `L₊ = {n ≥ 1 : Ω(n) even}` and `L'₊ = {n ≥ 1 : ω(n) even}`.
* `ramsey_pairs` : the infinite Ramsey theorem for pairs with two colours (for a symmetric
  colouring), which is not available in Mathlib and is proved here.

## Conventions

* The paper's `ℕ` is `{1, 2, …}`. The sets `B, C, Z` produced here consist of positive integers
  (this is part of each statement). In `bohr` the threshold `M₀` ranges over Lean's `ℕ`, so the
  case `M₀ = 0` is included as well; for `M₀ ≥ 1` the hypothesis is exactly the paper's.
* `𝕋` is `UnitAddCircle = ℝ/ℤ`, and `m ϑ + δ mod 1 ∈ J` is `((m ϑ + δ : ℝ) : 𝕋) ∈ J`.
* The Beatty sequence is a set of integers (`beatty α γ : Set ℤ`), indexed by `n ≥ 1`; the
  conclusion says that `b + c` and `b c` (for `b ∈ B`, `c ∈ C`) belong to it.
* For the infinitude of primes `p ≡ 5 (mod 6)` (proved by a Euclid-type argument in the paper) we
  use Dirichlet's theorem from Mathlib.
* In the proof of `bohr` the auxiliary modulus is `q > 8/ℓ` (the paper takes `q ≥ 4/ℓ` and rounds
  to the nearest point of `(2/q)ℤ`; we take the point below, which needs the larger `q`).

## Not covered

Proposition \ref{SP:prop:finitegroup} (completely multiplicative maps to finite abelian groups,
via Hindman's theorem) is not formalized.
-/

open Filter Topology

noncomputable section

namespace Kmrr25.S51a

/-- The product set `BC = {b c | b ∈ B, c ∈ C}`. -/
def prodset {α : Type*} [Mul α] (B C : Set α) : Set α := {x | ∃ b ∈ B, ∃ c ∈ C, x = b * c}

/-! ## Forward density of an irrational rotation -/

/-- For irrational `α`, every target `t` is approximated modulo `1` by `k α` with `k > K`. -/
lemma exists_nat_gt_abs_mul_sub_lt {α : ℝ} (hα : Irrational α) (t : ℝ) {ε : ℝ} (hε : 0 < ε)
    (K : ℕ) : ∃ k : ℕ, K < k ∧ ∃ j : ℤ, |k * α - j - t| < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_trans (by positivity) hn
    exact_mod_cast this
  obtain ⟨j0, k0, hk0, -, hj0⟩ := Real.exists_int_int_abs_mul_sub_le α hn0
  set η : ℝ := k0 * α - j0 with hη
  have hηε : |η| < ε := by
    refine lt_of_le_of_lt hj0 ?_
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hn
    nlinarith
  have hη0 : η ≠ 0 := by
    intro h
    have : α = (j0 : ℝ) / k0 := by
      have hk : (k0 : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
      field_simp
      linarith
    exact hα ⟨(j0 : ℚ) / k0, by push_cast; exact this.symm⟩
  set c : ℝ := (K + 1 : ℕ) * α - t with hc
  -- find `i : ℕ` and `m : ℤ` with `|c + i η - m| < ε`
  obtain ⟨i, m, him⟩ : ∃ (i : ℕ) (m : ℤ), |c + i * η - m| < ε := by
    rcases lt_or_gt_of_ne hη0 with hneg | hpos
    · refine ⟨⌈(c - ⌊c⌋) / (-η)⌉₊, ⌊c⌋, ?_⟩
      have h1 := Nat.le_ceil ((c - ⌊c⌋) / (-η))
      have h2 := Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.2 (Int.floor_le c)) (neg_pos.2 hneg).le)
      rw [div_le_iff₀ (neg_pos.2 hneg)] at h1
      rw [← sub_lt_iff_lt_add, lt_div_iff₀ (neg_pos.2 hneg)] at h2
      rw [abs_of_neg hneg] at hηε
      rw [abs_lt]
      constructor <;> nlinarith
    · refine ⟨⌈(⌈c⌉ - c) / η⌉₊, ⌈c⌉, ?_⟩
      have h1 := Nat.le_ceil ((⌈c⌉ - c) / η)
      have h2 := Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.2 (Int.le_ceil c)) hpos.le)
      rw [div_le_iff₀ hpos] at h1
      rw [← sub_lt_iff_lt_add, lt_div_iff₀ hpos] at h2
      rw [abs_of_pos hpos] at hηε
      rw [abs_lt]
      constructor <;> nlinarith
  refine ⟨K + 1 + i * k0.toNat, by omega, m + i * j0, ?_⟩
  have hk0' : ((k0.toNat : ℕ) : ℝ) = k0 := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk0.le]
  have e : ((K + 1 + i * k0.toNat : ℕ) : ℝ) * α - ((m + i * j0 : ℤ) : ℝ) - t =
      c + i * η - m := by
    rw [hc, hη]
    push_cast
    rw [hk0']
    ring
  rw [e]
  exact him

/-- `((y + n : ℝ) : 𝕋) = (y : 𝕋)` for every integer `n`. -/
lemma coe_add_int (y : ℝ) (n : ℤ) : (((y + n : ℝ)) : UnitAddCircle) = (y : UnitAddCircle) := by
  rw [AddCircle.coe_add, ← zsmul_one, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero,
    add_zero]

/-! ## Bohr sets -/

/-- Paper, Theorem \ref{SP:thm:bohr}. Let `ϑ` be irrational, `δ ∈ ℝ`, let `J ⊆ 𝕋 = ℝ/ℤ` be a
nonempty open set and `M₀ ∈ ℕ`, and let `A ⊆ ℕ` contain every `m ≥ M₀` with
`m ϑ + δ mod 1 ∈ J`. Then there is an infinite set `Z` of positive integers such that `z + z' ∈ A`
and `z z' ∈ A` for all distinct `z, z' ∈ Z`, and there are disjoint infinite sets `B, C` of
positive integers with `B + C ⊆ A` and `BC ⊆ A`. -/
theorem bohr {ϑ : ℝ} (hϑ : Irrational ϑ) (δ : ℝ) {J : Set UnitAddCircle} (hJ : IsOpen J)
    (hJne : J.Nonempty) (M₀ : ℕ) {A : Set ℕ}
    (hA : ∀ m : ℕ, M₀ ≤ m → (((m * ϑ + δ : ℝ)) : UnitAddCircle) ∈ J → m ∈ A) :
    (∃ Z : Set ℕ, Z.Infinite ∧ (∀ z ∈ Z, 0 < z) ∧
      ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → z + z' ∈ A ∧ z * z' ∈ A) ∧
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ Disjoint B C ∧ (∀ b ∈ B, 0 < b) ∧
      (∀ c ∈ C, 0 < c) ∧ sumset B C ⊆ A ∧ prodset B C ⊆ A := by
  -- a ball `(ξ₀ - ℓ/2, ξ₀ + ℓ/2)` whose image lies in `J`
  obtain ⟨ξ₀, ℓ, hℓ, hball⟩ : ∃ ξ₀ ℓ : ℝ, 0 < ℓ ∧
      ∀ y : ℝ, |y - ξ₀| < ℓ / 2 → (y : UnitAddCircle) ∈ J := by
    obtain ⟨w, hw⟩ := hJne
    obtain ⟨ξ₀, rfl⟩ := QuotientAddGroup.mk_surjective w
    have hU : IsOpen ((fun y : ℝ => (y : UnitAddCircle)) ⁻¹' J) :=
      hJ.preimage (AddCircle.continuous_mk' 1)
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hU ξ₀ hw
    refine ⟨ξ₀, 2 * ε, by positivity, fun y hy => hsub ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    linarith
  -- `q ≥ 8/ℓ`, `r = ⌊q(ξ₀ - δ)/2⌋`, `ξ = 2r/q + δ`
  set q : ℕ := ⌈8 / ℓ⌉₊ + 1 with hqdef
  have hq : 8 / ℓ < q := by
    rw [hqdef]
    push_cast
    linarith [Nat.le_ceil (8 / ℓ)]
  have hqpos : 0 < q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hq2 : 2 / (q : ℝ) < ℓ / 4 := by
    rw [div_lt_iff₀ hℓ] at hq
    rw [div_lt_iff₀ hq0]
    linarith
  set r : ℤ := ⌊q * (ξ₀ - δ) / 2⌋ with hrdef
  have hr1 : (r : ℝ) ≤ q * (ξ₀ - δ) / 2 := Int.floor_le _
  have hr2 : q * (ξ₀ - δ) / 2 < r + 1 := Int.lt_floor_add_one _
  have hξ : |2 * r / q + δ - ξ₀| < ℓ / 4 := by
    have e1 : 2 * (r : ℝ) / q ≤ ξ₀ - δ := by
      rw [div_le_iff₀ hq0]
      linarith
    have e2 : ξ₀ - δ < 2 * r / q + 2 / q := by
      rw [← add_div, lt_div_iff₀ hq0]
      linarith
    rw [abs_lt]
    constructor <;> linarith
  have hJ' : ∀ (y : ℝ) (n : ℤ), |y - n - (2 * r / q + δ)| < ℓ / 4 →
      (y : UnitAddCircle) ∈ J := by
    intro y n hy
    have h := hball (y - n) (by
      calc |y - n - ξ₀| = |(y - n - (2 * r / q + δ)) + (2 * r / q + δ - ξ₀)| := by ring_nf
        _ ≤ |y - n - (2 * r / q + δ)| + |2 * r / q + δ - ξ₀| := abs_add_le _ _
        _ < ℓ / 4 + ℓ / 4 := add_lt_add hy hξ
        _ = ℓ / 2 := by ring)
    rwa [← coe_add_int (y - n) n, sub_add_cancel] at h
  -- the recursive step
  have hstep : ∀ P : ℕ, ∃ z k : ℕ, z = q * k + 2 ∧ max P M₀ < z ∧
      ∃ K : ℤ, |z * ϑ - K - r / q| < ℓ / (8 * (P + 1)) := by
    intro P
    obtain ⟨k, hk, j, hj⟩ := exists_nat_gt_abs_mul_sub_lt (hϑ.natCast_mul hqpos.ne')
      (r / q - 2 * ϑ) (ε := ℓ / (8 * (P + 1))) (by positivity) (P + M₀)
    refine ⟨q * k + 2, k, rfl, ?_, j, ?_⟩
    · have : k ≤ q * k := Nat.le_mul_of_pos_left k hqpos
      omega
    · convert hj using 2
      push_cast
      ring
  choose step kk hkk hmax KK hKK using hstep
  -- the pair property
  have hpair : ∀ P P' : ℕ, step P' ≤ P → step P' + step P ∈ A ∧ step P' * step P ∈ A := by
    intro P P' hle
    set a := step P' with ha
    set b := step P with hb
    have hMb : M₀ < b := lt_of_le_of_lt (le_max_right _ _) (hmax P)
    have ha2 : 2 ≤ a := by rw [ha, hkk P']; omega
    set ea : ℝ := a * ϑ - KK P' - r / q with hea
    set eb : ℝ := b * ϑ - KK P - r / q with heb
    have hea' : |ea| < ℓ / 8 := by
      refine lt_of_lt_of_le (hKK P') ?_
      rw [div_le_div_iff_of_pos_left hℓ (by positivity) (by positivity)]
      have : (0 : ℝ) ≤ P' := by positivity
      linarith
    have heb' : |eb| < ℓ / (8 * (P + 1)) := hKK P
    constructor
    · apply hA _ (by omega)
      apply hJ' _ (KK P' + KK P)
      have e : ((a + b : ℕ) : ℝ) * ϑ + δ - ((KK P' + KK P : ℤ) : ℝ) - (2 * r / q + δ) =
          ea + eb := by
        rw [hea, heb]
        push_cast
        ring
      rw [e]
      have heb'' : |eb| ≤ ℓ / 8 := by
        refine le_trans heb'.le ?_
        rw [div_le_div_iff_of_pos_left hℓ (by positivity) (by positivity)]
        have : (0 : ℝ) ≤ P := by positivity
        linarith
      calc |ea + eb| ≤ |ea| + |eb| := abs_add_le _ _
        _ < ℓ / 8 + ℓ / 8 := add_lt_add_of_lt_of_le hea' heb''
        _ = ℓ / 4 := by ring
    · apply hA _ (by nlinarith)
      apply hJ' _ (a * KK P + kk P' * r)
      have hka : (a : ℝ) = q * kk P' + 2 := by rw [ha, hkk P']; push_cast; ring
      have e : ((a * b : ℕ) : ℝ) * ϑ + δ - ((a * KK P + kk P' * r : ℤ) : ℝ) - (2 * r / q + δ) =
          a * eb := by
        rw [heb]
        push_cast
        rw [hka]
        field_simp
        ring
      rw [e, abs_mul, Nat.abs_cast]
      have hP : (a : ℝ) ≤ P := by exact_mod_cast hle
      calc (a : ℝ) * |eb| ≤ P * |eb| := by gcongr
        _ ≤ P * (ℓ / (8 * (P + 1))) := by gcongr
        _ < ℓ / 4 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  -- the sequence `z_n = w_{n+1}`, where `w_0 = 0` and `w_{n+1} = step w_n`
  set w : ℕ → ℕ := fun n => step^[n] 0 with hwdef
  have hw : ∀ n, w (n + 1) = step (w n) := fun n => Function.iterate_succ_apply' step n 0
  have hwmono : StrictMono w := strictMono_nat_of_lt_succ fun n => by
    rw [hw]
    exact lt_of_le_of_lt (le_max_left _ _) (hmax (w n))
  set z : ℕ → ℕ := fun n => w (n + 1) with hzdef
  have hzmono : StrictMono z := fun i j hij => hwmono (by omega)
  have hzpos : ∀ n, 0 < z n := fun n => by
    simp only [hzdef, hw, hkk]
    omega
  have hZ : ∀ i j, i < j → z i + z j ∈ A ∧ z i * z j ∈ A := by
    intro i j hij
    have h1 : z i = step (w i) := hw i
    have h2 : z j = step (w (j)) := hw j
    rw [h1, h2]
    refine hpair (w j) (w i) ?_
    rw [← h1]
    exact hwmono.monotone (by omega)
  have hZ' : ∀ i j, i ≠ j → z i + z j ∈ A ∧ z i * z j ∈ A := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hZ i j h
    · rw [add_comm, mul_comm]
      exact hZ j i h
  refine ⟨⟨Set.range z, Set.infinite_range_of_injective hzmono.injective, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact hzpos n
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hZ' i j fun h => hne (by rw [h])
  refine ⟨Set.range fun n => z (2 * n), Set.range fun n => z (2 * n + 1),
    Set.infinite_range_of_injective (fun a b h => by have := hzmono.injective h; omega),
    Set.infinite_range_of_injective (fun a b h => by have := hzmono.injective h; omega), ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    have := hzmono.injective hj
    omega
  · rintro _ ⟨n, rfl⟩
    exact hzpos _
  · rintro _ ⟨n, rfl⟩
    exact hzpos _
  · rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact (hZ' _ _ (by omega)).1
  · rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact (hZ' _ _ (by omega)).2

/-! ## Beatty sequences -/

/-- The Beatty sequence `{⌊n α + γ⌋ : n ∈ ℕ, n ≥ 1}`, as a set of integers. -/
def beatty (α γ : ℝ) : Set ℤ := {m | ∃ n : ℕ, 0 < n ∧ ⌊n * α + γ⌋ = m}

/-- For `0 < α < 1`, the Beatty sequence contains every integer `m ≥ ⌊α + γ⌋`. -/
lemma mem_beatty_of_lt_one {α γ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {m : ℤ} (hm : ⌊α + γ⌋ ≤ m) :
    m ∈ beatty α γ := by
  have hex : ∃ n : ℕ, m ≤ ⌊((n : ℝ) + 1) * α + γ⌋ := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((m - γ) / α)
    refine ⟨n, Int.le_floor.2 ?_⟩
    rw [div_lt_iff₀ hα0] at hn
    nlinarith
  classical
  have hn0 := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · refine ⟨1, one_pos, le_antisymm ?_ ?_⟩
    · simpa using hm
    · rw [h] at hn0
      simpa using hn0
  · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : ¬ m ≤ ⌊((j : ℝ) + 1) * α + γ⌋ := Nat.find_min hex (by omega)
    rw [hj] at hn0
    push_cast at hn0
    have hstep : ⌊((j : ℝ) + 1 + 1) * α + γ⌋ ≤ ⌊((j : ℝ) + 1) * α + γ⌋ + 1 := by
      rw [← Int.floor_add_one]
      apply Int.floor_mono
      nlinarith
    refine ⟨j + 2, by omega, ?_⟩
    push_cast
    rw [show ((j : ℝ) + 2) = (j : ℝ) + 1 + 1 by ring]
    omega

/-- Paper, Corollary \ref{SP:cor:beatty}. Let `α > 0` be irrational, `γ ∈ ℝ`, and let
`A = {⌊n α + γ⌋ : n ∈ ℕ}`. Then there are infinite sets `B, C` of positive integers with
`B + C ⊆ A` and `BC ⊆ A`. -/
theorem beatty_sum_prod {α : ℝ} (hα : Irrational α) (hα0 : 0 < α) (γ : ℝ) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ (∀ c ∈ C, 0 < c) ∧
      sumset B C ⊆ {m : ℕ | (m : ℤ) ∈ beatty α γ} ∧
      prodset B C ⊆ {m : ℕ | (m : ℤ) ∈ beatty α γ} := by
  rcases lt_or_gt_of_ne hα.ne_one with hα1 | hα1
  · -- `α < 1`: the Beatty sequence contains all large integers
    set M : ℕ := ⌊α + γ⌋.toNat + 1 with hM
    have hM' : ⌊α + γ⌋ < (M : ℤ) := by
      have := Int.self_le_toNat ⌊α + γ⌋
      rw [hM]
      push_cast
      omega
    refine ⟨Set.Ici M, Set.Ici M, Set.Ici_infinite M, Set.Ici_infinite M,
      fun b hb => by simp only [Set.mem_Ici] at hb; omega,
      fun b hb => by simp only [Set.mem_Ici] at hb; omega, ?_, ?_⟩
    · rintro _ ⟨b, hb, c, hc, rfl⟩
      simp only [Set.mem_Ici] at hb hc
      refine mem_beatty_of_lt_one hα0 hα1 ?_
      push_cast
      omega
    · rintro _ ⟨b, hb, c, hc, rfl⟩
      simp only [Set.mem_Ici] at hb hc
      refine mem_beatty_of_lt_one hα0 hα1 ?_
      have : M ≤ b * c := le_trans hb (Nat.le_mul_of_pos_right b (by omega))
      have : (M : ℤ) ≤ ((b * c : ℕ) : ℤ) := by exact_mod_cast this
      omega
  · -- `α > 1`: reduce to an inhomogeneous Bohr set with frequency `-1/α`
    set β := α⁻¹ with hβ
    have hβ0 : 0 < β := inv_pos.2 hα0
    have hαβ : α * β = 1 := mul_inv_cancel₀ hα0.ne'
    set J : Set UnitAddCircle := (fun y : ℝ => (y : UnitAddCircle)) '' Set.Ioo 0 β with hJ
    have hJo : IsOpen J := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
    have hJne : J.Nonempty := ⟨_, ⟨β / 2, ⟨by positivity, by linarith⟩, rfl⟩⟩
    have hA : ∀ m : ℕ, ⌊γ⌋₊ + 1 ≤ m → ((((m : ℝ) * (-β) + γ * β : ℝ)) : UnitAddCircle) ∈ J →
        m ∈ {m : ℕ | (m : ℤ) ∈ beatty α γ} := by
      intro m hm hmem
      obtain ⟨t, ⟨ht0, htβ⟩, ht⟩ := hmem
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 ht)
      rw [zsmul_one] at hk
      have hmγ : γ < m := by
        have := Nat.lt_floor_add_one γ
        have : ((⌊γ⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
        push_cast at this
        linarith
      -- `n = -k` satisfies `n = t + (m - γ) β > 0` and `n α + γ = m + t α`
      have hn : ((-k : ℤ) : ℝ) = t + (m - γ) * β := by
        push_cast
        linarith
      have hnpos : 0 < -k := by
        have : (0 : ℝ) < ((-k : ℤ) : ℝ) := by
          rw [hn]
          have : 0 < (m - γ) * β := mul_pos (by linarith) hβ0
          linarith
        exact_mod_cast this
      refine ⟨(-k).toNat, by omega, ?_⟩
      have hcast : (((-k).toNat : ℕ) : ℝ) = ((-k : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hnpos.le]
      rw [hcast, hn, Int.floor_eq_iff]
      have e : (t + (m - γ) * β) * α + γ = m + t * α := by
        linear_combination ((m : ℝ) - γ) * hαβ
      have htα : t * α < 1 := by
        have := mul_lt_mul_of_pos_right htβ hα0
        rw [mul_comm β α, hαβ] at this
        exact this
      have htα0 : 0 < t * α := mul_pos ht0 hα0
      rw [e]
      push_cast
      constructor <;> linarith
    obtain ⟨-, B, C, hB, hC, -, hBpos, hCpos, hs, hp⟩ :=
      bohr hα.inv.neg (γ * β) hJo hJne (⌊γ⌋₊ + 1) hA
    exact ⟨B, C, hB, hC, hBpos, hCpos, hs, hp⟩

/-! ## Ramsey's theorem for pairs -/

/-- The infinite Ramsey theorem for pairs with two colours, for a symmetric relation `c`: every
infinite `S ⊆ ℕ` contains an infinite sequence of distinct elements `x n` such that either
`c (x n) (x m)` holds for all `n ≠ m`, or it fails for all `n ≠ m`. -/
lemma ramsey_pairs {S : Set ℕ} (hS : S.Infinite) (c : ℕ → ℕ → Prop)
    (hc : ∀ a b, c a b → c b a) :
    ∃ x : ℕ → ℕ, Function.Injective x ∧ (∀ n, x n ∈ S) ∧
      ((∀ n m, n ≠ m → c (x n) (x m)) ∨ (∀ n m, n ≠ m → ¬ c (x n) (x m))) := by
  classical
  have key : ∀ T : Set ℕ, T.Infinite → ∃ (b : Bool) (T' : Set ℕ), T'.Infinite ∧
      T' ⊆ T \ {sInf T} ∧ ∀ y ∈ T', (c (sInf T) y ↔ b = true) := by
    intro T hT
    have h := hT.sdiff (Set.finite_singleton (sInf T))
    have hu : T \ {sInf T} = {y | y ∈ T \ {sInf T} ∧ c (sInf T) y} ∪
        {y | y ∈ T \ {sInf T} ∧ ¬ c (sInf T) y} := by
      ext y
      by_cases hy : c (sInf T) y <;> simp [hy]
    rw [hu] at h
    rcases Set.infinite_union.1 h with h1 | h1
    · exact ⟨true, _, h1, fun y hy => hy.1, fun y hy => by simpa using hy.2⟩
    · exact ⟨false, _, h1, fun y hy => hy.1, fun y hy => by simpa using hy.2⟩
  choose b T' hT' hsub hcol using key
  let seq : ℕ → {T : Set ℕ // T.Infinite} := fun n =>
    Nat.rec (motive := fun _ => {T : Set ℕ // T.Infinite}) ⟨S, hS⟩
      (fun _ T => ⟨T' T.1 T.2, hT' T.1 T.2⟩) n
  set x : ℕ → ℕ := fun n => sInf (seq n).1 with hxdef
  set col : ℕ → Bool := fun n => b (seq n).1 (seq n).2 with hcoldef
  have hxmem : ∀ n, x n ∈ (seq n).1 := fun n => Nat.sInf_mem (seq n).2.nonempty
  have hanti : ∀ n k, (seq (n + k)).1 ⊆ (seq n).1 := by
    intro n k
    induction k with
    | zero => exact subset_rfl
    | succ k ih =>
      intro y hy
      exact ih (hsub (seq (n + k)).1 (seq (n + k)).2 hy).1
  have hpair : ∀ n m, n < m → x m ≠ x n ∧ (c (x n) (x m) ↔ col n = true) := by
    intro n m h
    obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - n - 1, by omega⟩
    have hm : x (n + 1 + k) ∈ T' (seq n).1 (seq n).2 := hanti (n + 1) k (hxmem _)
    have h2 := hsub _ _ hm
    exact ⟨fun e => h2.2 (by rw [e]; rfl), hcol _ _ _ hm⟩
  have hinj : Function.Injective x := by
    intro n m h
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact (hpair n m h').1 h.symm
    · exact (hpair m n h').1 h
  have hS' : ∀ n, x n ∈ S := fun n => by
    have := hanti 0 n (by rw [zero_add]; exact hxmem n)
    exact this
  have hI : {n | col n = true}.Infinite ∨ {n | col n = false}.Infinite := by
    apply Set.infinite_union.1
    have : {n | col n = true} ∪ {n | col n = false} = Set.univ := by
      ext n
      cases col n <;> simp
    rw [this]
    exact Set.infinite_univ
  rcases hI with hI | hI
  · refine ⟨x ∘ Nat.nth (fun n => col n = true), hinj.comp (Nat.nth_injective hI),
      fun n => hS' _, Or.inl fun n m hnm => ?_⟩
    have hne : Nat.nth (fun n => col n = true) n ≠ Nat.nth (fun n => col n = true) m :=
      fun h => hnm (Nat.nth_injective hI h)
    simp only [Function.comp]
    rcases lt_or_gt_of_ne hne with h | h
    · exact ((hpair _ _ h).2).2 (Nat.nth_mem_of_infinite hI n)
    · exact hc _ _ (((hpair _ _ h).2).2 (Nat.nth_mem_of_infinite hI m))
  · refine ⟨x ∘ Nat.nth (fun n => col n = false), hinj.comp (Nat.nth_injective hI),
      fun n => hS' _, Or.inr fun n m hnm => ?_⟩
    have hne : Nat.nth (fun n => col n = false) n ≠ Nat.nth (fun n => col n = false) m :=
      fun h => hnm (Nat.nth_injective hI h)
    simp only [Function.comp]
    have hn := Nat.nth_mem_of_infinite hI n
    have hm := Nat.nth_mem_of_infinite hI m
    rcases lt_or_gt_of_ne hne with h | h
    · intro hcxy
      have := ((hpair _ _ h).2).1 hcxy
      rw [hn] at this
      exact Bool.false_ne_true this
    · intro hcxy
      have := ((hpair _ _ h).2).1 (hc _ _ hcxy)
      rw [hm] at this
      exact Bool.false_ne_true this

/-! ## The Liouville function -/

section Liouville

open ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

/-- `L₊ = {n ∈ ℕ : Ω(n) is even} = {n : λ(n) = 1}`, where `Ω(n)` counts prime factors with
multiplicity (`n ≥ 1`). -/
def Lplus : Set ℕ := {n | 0 < n ∧ Even (Ω n)}

/-- `L'₊ = {n ∈ ℕ : ω(n) is even}`, where `ω(n)` counts distinct prime factors (`n ≥ 1`). -/
def Lplus' : Set ℕ := {n | 0 < n ∧ Even (ω n)}

/-- The primes `p ≡ 5 (mod 6)`. -/
def S5 : Set ℕ := {p | p.Prime ∧ p % 6 = 5}

lemma S5_infinite : S5.Infinite := by
  refine (Nat.infinite_setOfPred_prime_and_eq_mod (q := 6)
    (IsUnit.of_mul_eq_one (a := (5 : ZMod 6)) (b := 5) (by decide))).mono ?_
  rintro p ⟨hp, h⟩
  refine ⟨hp, ?_⟩
  have := (ZMod.natCast_eq_natCast_iff' p 5 6).1 (by simpa using h)
  simpa using this

/-- The common skeleton of the proof of Theorem \ref{SP:thm:liouville}: if `bc ∈ E` and
`(db)(dc) ∈ E` for distinct `b, c ∈ S`, and `db + dc ∈ E` whenever `b + c ∉ E`, then `E` contains
`B + C` and `BC` for infinite sets `B, C` of positive integers. -/
lemma sum_prod_of_ramsey (E : Set ℕ) {d : ℕ} (hd : 0 < d)
    (hprod : ∀ b ∈ S5, ∀ c ∈ S5, b ≠ c → b * c ∈ E ∧ (d * b) * (d * c) ∈ E)
    (hsum : ∀ b ∈ S5, ∀ c ∈ S5, b ≠ c → b + c ∉ E → d * b + d * c ∈ E) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ (∀ c ∈ C, 0 < c) ∧
      sumset B C ⊆ E ∧ prodset B C ⊆ E := by
  obtain ⟨x, hxinj, hxS, hx⟩ := ramsey_pairs S5_infinite (fun a b => a + b ∈ E)
    (fun a b h => by rwa [add_comm])
  have hpos : ∀ n, 0 < x n := fun n => (hxS n).1.pos
  have hev : Function.Injective fun n : ℕ => 2 * n := fun a b h => by simp at h; omega
  have hod : Function.Injective fun n : ℕ => 2 * n + 1 := fun a b h => by simp at h; omega
  have hB0 : (Set.range fun n => x (2 * n)).Infinite :=
    Set.infinite_range_of_injective (hxinj.comp hev)
  have hC0 : (Set.range fun n => x (2 * n + 1)).Infinite :=
    Set.infinite_range_of_injective (hxinj.comp hod)
  have hne : ∀ i j, x (2 * i) ≠ x (2 * j + 1) := fun i j h => by
    have := hxinj h
    omega
  rcases hx with hx | hx
  · refine ⟨_, _, hB0, hC0, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨n, rfl⟩
      exact hpos _
    · rintro _ ⟨n, rfl⟩
      exact hpos _
    · rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      exact hx _ _ (by omega)
    · rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      exact (hprod _ (hxS _) _ (hxS _) (hne i j)).1
  · have hdinj : Function.Injective fun n : ℕ => d * n := fun a b h => by
      simpa [hd.ne'] using h
    refine ⟨(fun n => d * n) '' Set.range fun n => x (2 * n),
      (fun n => d * n) '' Set.range fun n => x (2 * n + 1),
      hB0.image hdinj.injOn, hC0.image hdinj.injOn, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      exact Nat.mul_pos hd (hpos _)
    · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      exact Nat.mul_pos hd (hpos _)
    · rintro _ ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, _, ⟨_, ⟨j, rfl⟩, rfl⟩, rfl⟩
      exact hsum _ (hxS _) _ (hxS _) (hne i j) (hx _ _ (by omega))
    · rintro _ ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, _, ⟨_, ⟨j, rfl⟩, rfl⟩, rfl⟩
      exact (hprod _ (hxS _) _ (hxS _) (hne i j)).2

lemma omega_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]

/-- `ω(2s) = ω(s)` if `s` is even. -/
lemma omega_two_mul_of_even {s : ℕ} (hs0 : s ≠ 0) (hs : 2 ∣ s) : ω (2 * s) = ω s := by
  rw [omega_eq_card, omega_eq_card, Nat.primeFactors_mul two_ne_zero hs0,
    Nat.prime_two.primeFactors]
  congr 1
  refine Finset.union_eq_right.2 (Finset.singleton_subset_iff.2 ?_)
  exact Nat.mem_primeFactors.2 ⟨Nat.prime_two, hs, hs0⟩

lemma coprime_36 {p : ℕ} (hp : p ∈ S5) : Nat.Coprime 36 p := by
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.1).2 fun h => ?_)
  have hle := Nat.le_of_dvd (by norm_num) h
  have h5 := hp.2
  interval_cases p <;> omega

/-- Paper, Theorem \ref{SP:thm:liouville}, for `E = L₊`. -/
theorem liouville_Lplus :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ (∀ c ∈ C, 0 < c) ∧
      sumset B C ⊆ Lplus ∧ prodset B C ⊆ Lplus := by
  refine sum_prod_of_ramsey Lplus (d := 2) (by norm_num) ?_ ?_
  · intro b hb c hc _
    have hb0 := hb.1.pos
    have hc0 := hc.1.pos
    refine ⟨⟨Nat.mul_pos hb0 hc0, ?_⟩, ⟨by positivity, ?_⟩⟩
    · rw [cardFactors_mul hb0.ne' hc0.ne', cardFactors_apply_prime hb.1,
        cardFactors_apply_prime hc.1]
      decide
    · rw [cardFactors_mul (by positivity) (by positivity), cardFactors_mul (by norm_num) hb0.ne',
        cardFactors_mul (by norm_num) hc0.ne', cardFactors_apply_prime hb.1,
        cardFactors_apply_prime hc.1, cardFactors_apply_prime Nat.prime_two]
      decide
  · intro b hb c hc _ hbc
    have hs0 : b + c ≠ 0 := by have := hb.1.pos; omega
    refine ⟨by omega, ?_⟩
    have hodd : ¬ Even (Ω (b + c)) := fun h => hbc ⟨Nat.pos_of_ne_zero hs0, h⟩
    rw [← mul_add, cardFactors_mul two_ne_zero hs0, cardFactors_apply_prime Nat.prime_two]
    rw [Nat.not_even_iff_odd] at hodd
    rw [add_comm]
    exact hodd.add_one

/-- Paper, Theorem \ref{SP:thm:liouville}, for `E = L'₊`. -/
theorem liouville_Lplus' :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ (∀ c ∈ C, 0 < c) ∧
      sumset B C ⊆ Lplus' ∧ prodset B C ⊆ Lplus' := by
  refine sum_prod_of_ramsey Lplus' (d := 6) (by norm_num) ?_ ?_
  · intro b hb c hc hbc
    have hb0 := hb.1.pos
    have hc0 := hc.1.pos
    have hcop : Nat.Coprime b c := (Nat.coprime_primes hb.1 hc.1).2 hbc
    refine ⟨⟨Nat.mul_pos hb0 hc0, ?_⟩, ⟨by positivity, ?_⟩⟩
    · rw [cardDistinctFactors_mul hcop, cardDistinctFactors_apply_prime hb.1,
        cardDistinctFactors_apply_prime hc.1]
      decide
    · have e : 6 * b * (6 * c) = 36 * (b * c) := by ring
      have h36 : ω 36 = 2 := by
        rw [show (36 : ℕ) = 2 ^ 2 * 3 ^ 2 by norm_num, cardDistinctFactors_mul (by norm_num),
          cardDistinctFactors_apply_prime_pow Nat.prime_two (by norm_num),
          cardDistinctFactors_apply_prime_pow Nat.prime_three (by norm_num)]
      rw [e, cardDistinctFactors_mul (Nat.Coprime.mul_right (coprime_36 hb) (coprime_36 hc)),
        cardDistinctFactors_mul hcop, cardDistinctFactors_apply_prime hb.1,
        cardDistinctFactors_apply_prime hc.1, h36]
      decide
  · intro b hb c hc _ hbc
    have hb5 := hb.2
    have hc5 := hc.2
    have hs0 : b + c ≠ 0 := by omega
    refine ⟨by omega, ?_⟩
    have hodd : ¬ Even (ω (b + c)) := fun h => hbc ⟨Nat.pos_of_ne_zero hs0, h⟩
    have h3 : Nat.Coprime 3 (2 * (b + c)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    rw [← mul_add, show (6 : ℕ) * (b + c) = 3 * (2 * (b + c)) by ring,
      cardDistinctFactors_mul h3, cardDistinctFactors_apply_prime Nat.prime_three,
      omega_two_mul_of_even hs0 (by omega)]
    rw [Nat.not_even_iff_odd] at hodd
    rw [add_comm]
    exact hodd.add_one

/-- Paper, Theorem \ref{SP:thm:liouville}. For each `E ∈ {L₊, L'₊}` there are infinite sets
`B, C` of positive integers with `B + C ⊆ E` and `BC ⊆ E`. -/
theorem liouville : ∀ E ∈ ({Lplus, Lplus'} : Set (Set ℕ)),
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ (∀ c ∈ C, 0 < c) ∧
      sumset B C ⊆ E ∧ prodset B C ⊆ E := by
  rintro E (rfl | rfl)
  · exact liouville_Lplus
  · exact liouville_Lplus'

end Liouville

end Kmrr25.S51a

end
