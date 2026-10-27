import Kmrr25.Basic

/-!
# Colourings and Question 3.20 (paper, Section \ref{IA:sec:q320})

For a colouring `χ` of `ℕ`, an integer `m` is *bad* if no infinite `B ⊆ ℕ` has `B + mB`
monochromatic, and *strongly bad* if no infinite `B` has the restricted sumset
`B ⊕ mB = {b + m b' : b, b' ∈ B, b ≠ b'}` monochromatic.

## Main results

* `prop320A` — Proposition \ref{IA:prop:320A}: for `ρ > 1`, `χ(n) = ⌊log_ρ n⌋ mod r`, `m ≥ 2` with
  `log_ρ m ∉ ℤ` and `k = ⌊log_ρ m⌋ ≢ 0, -1 (mod r)`, `m` is strongly bad.
* `prop320B` — Proposition \ref{IA:prop:320B}: for `m ≥ 2`, `ρ > 1 + 1/m` and an odd integer `j`
  with `m < ρ^j < m + 1`, `m` is bad for `⌊log_ρ n⌋ mod 2`.
* `lem_nested` — Lemma \ref{IA:lem:nested}.
* `thm320A` — Theorem \ref{IA:thm:320A}, all three claims (strong badness, logarithmic density
  `1 - 2/r`, infinitely many primes), with the colouring `n ↦ Nat.log 2 n mod r`; `chiR_two`
  shows that this is the colouring `⌊log₂ n⌋ mod r` defined with the real logarithm.
* `thm320B` — Theorem \ref{IA:thm:320B}, both parts, with the real-logarithm colourings
  `⌊log_φ n⌋ mod 2` and `⌊log_ρ n⌋ mod 2`.
* `cor320` — Corollary \ref{IA:cor:320}, and `q320_negative`, `q320_negative_ge_two`,
  `q320_negative_prime` — the resulting negative answers to Question \ref{IA:q:320} for every
  number `r ≥ 2` of colours (for all `m`, for `m ≥ 2`, and for prime `m`).

## Conventions

* The paper's `ℕ` is `{1, 2, …}`. Colourings here are maps on Lean's `ℕ = {0, 1, …}`; the value
  at `0` plays no role. Badness is stated for *all* infinite `B ⊆ {0, 1, 2, …}`, which contains
  the paper's statement (about infinite `B ⊆ {1, 2, …}`) as a special case. In
  Question \ref{IA:q:320} the quantity `q` ranges over `q ≥ 1` and `B` over subsets of
  `{1, 2, …}`, as in the paper.
* `⌊log_ρ n⌋` is `⌊Real.logb ρ n⌋`; colours `⌊log_ρ n⌋ mod r` are integers in `{0, …, r-1}`
  (`Int.emod`). For the corollary the colourings are repackaged as maps `ℕ → Fin r`.
* The Lucas numbers are `L_0 = 2, L_1 = 1, L_{n+2} = L_{n+1} + L_n`, so `L_1 = 1, L_2 = 3` as in
  the paper.
* Logarithmic density: `HasLogDensity A d` means `(1/log N) ∑_{n=1}^{N} 𝟙_A(n)/n → d`.
* Proposition \ref{IA:prop:320A} is proved without the assumption `r ≥ 3` (its other hypotheses
  cannot hold for `r ≤ 2`). Lemma \ref{IA:lem:floor} is `floor_sub_mem`; the estimates of
  Lemma \ref{IA:lem:asym} are used inline in the proofs.

## Not covered

Hindman's `3`-colouring with no infinite `B` such that `B + B` is monochromatic (cited from the
literature in the paper to settle the case `m = 1`) is not formalized; it is not needed for the
negative answers proved here, which come from bad primes `m ≥ 2`.
-/

open Real Filter Topology Finset

namespace Kmrr25.Q320

/-! ## Definitions -/

/-- The dilate `mB = {m b | b ∈ B}`. -/
def dilate (m : ℕ) (B : Set ℕ) : Set ℕ := (fun b => m * b) '' B

/-- The restricted sumset `B ⊕ mB = {b + m b' | b, b' ∈ B, b ≠ b'}`. -/
def restrSumset (B : Set ℕ) (m : ℕ) : Set ℕ :=
  {x | ∃ b ∈ B, ∃ b' ∈ B, b ≠ b' ∧ x = b + m * b'}

/-- A set `A` is monochromatic for the colouring `χ` if it is contained in a single colour
class. -/
def IsMonochromatic {ι : Type*} (χ : ℕ → ι) (A : Set ℕ) : Prop := ∃ c, ∀ x ∈ A, χ x = c

/-- `m` is *bad* for `χ` if no infinite `B` has `B + mB` monochromatic. -/
def IsBad {ι : Type*} (χ : ℕ → ι) (m : ℕ) : Prop :=
  ∀ B : Set ℕ, B.Infinite → ¬ IsMonochromatic χ (sumset B (dilate m B))

/-- `m` is *strongly bad* for `χ` if no infinite `B` has `B ⊕ mB` monochromatic. -/
def IsStronglyBad {ι : Type*} (χ : ℕ → ι) (m : ℕ) : Prop :=
  ∀ B : Set ℕ, B.Infinite → ¬ IsMonochromatic χ (restrSumset B m)

lemma restrSumset_subset (B : Set ℕ) (m : ℕ) : restrSumset B m ⊆ sumset B (dilate m B) := by
  rintro x ⟨b, hb, b', hb', -, rfl⟩
  exact ⟨b, hb, m * b', ⟨b', hb', rfl⟩, rfl⟩

/-- Strongly bad integers are bad. -/
lemma IsStronglyBad.isBad {ι : Type*} {χ : ℕ → ι} {m : ℕ} (h : IsStronglyBad χ m) :
    IsBad χ m := fun B hB ⟨c, hc⟩ => h B hB ⟨c, fun x hx => hc x (restrSumset_subset B m hx)⟩

lemma not_mono_of_ne {ι : Type*} {χ : ℕ → ι} {A : Set ℕ} {x y : ℕ} (hx : x ∈ A) (hy : y ∈ A)
    (hne : χ x ≠ χ y) : ¬ IsMonochromatic χ A := by
  rintro ⟨c, hc⟩
  exact hne ((hc x hx).trans (hc y hy).symm)

lemma IsMonochromatic.of_comp {ι κ : Type*} {χ : ℕ → ι} {χ' : ℕ → κ} {A : Set ℕ}
    (h : ∀ x y, χ' x = χ' y → χ x = χ y) (hA : IsMonochromatic χ' A) (x : ℕ) (hx : x ∈ A) :
    IsMonochromatic χ A := by
  obtain ⟨c, hc⟩ := hA
  exact ⟨χ x, fun y hy => h y x ((hc y hy).trans (hc x hx).symm)⟩

lemma IsBad.of_comp {ι κ : Type*} {χ : ℕ → ι} {χ' : ℕ → κ} {m : ℕ}
    (h : ∀ x y, χ' x = χ' y → χ x = χ y) (hb : IsBad χ m) : IsBad χ' m := by
  intro B hB hmono
  obtain ⟨b, hbB⟩ := hB.nonempty
  exact hb B hB (hmono.of_comp h (b + m * b) ⟨b, hbB, m * b, ⟨b, hbB, rfl⟩, rfl⟩)

lemma IsStronglyBad.of_comp {ι κ : Type*} {χ : ℕ → ι} {χ' : ℕ → κ} {m : ℕ}
    (h : ∀ x y, χ' x = χ' y → χ x = χ y) (hb : IsStronglyBad χ m) : IsStronglyBad χ' m := by
  intro B hB hmono
  obtain ⟨b, hbB, b', hb'B, hne⟩ := hB.nontrivial
  exact hb B hB (hmono.of_comp h (b + m * b') ⟨b, hbB, b', hb'B, hne, rfl⟩)

/-- `λ_ρ(n) = ⌊log_ρ n⌋`. -/
noncomputable def lam (ρ : ℝ) (n : ℕ) : ℤ := ⌊Real.logb ρ n⌋

/-- The colouring `χ(n) = ⌊log_ρ n⌋ mod r` (values in `{0, …, r-1}` for `r ≥ 1`). -/
noncomputable def chiR (ρ : ℝ) (r : ℕ) (n : ℕ) : ℤ := lam ρ n % (r : ℤ)

/-! ## Elementary lemmas -/

/-- Paper, Lemma \ref{IA:lem:floor}. -/
lemma floor_sub_mem {x y : ℝ} {k : ℤ} (h1 : (k : ℝ) < y - x) (h2 : y - x < k + 1) :
    ⌊y⌋ - ⌊x⌋ = k ∨ ⌊y⌋ - ⌊x⌋ = k + 1 := by
  have a1 := Int.floor_le x
  have a2 := Int.lt_floor_add_one x
  have a3 := Int.floor_le y
  have a4 := Int.lt_floor_add_one y
  have b1 : ((k - 1 : ℤ) : ℝ) < ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) := by push_cast; linarith
  have b2 : ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) < ((k + 2 : ℤ) : ℝ) := by push_cast; linarith
  have c1 := Int.cast_lt.mp b1
  have c2 := Int.cast_lt.mp b2
  omega

/-- In an infinite set of naturals there is a positive element. -/
lemma exists_pos_mem {B : Set ℕ} (hB : B.Infinite) : ∃ b ∈ B, 0 < b := by
  obtain ⟨b, hb, hb0⟩ := hB.exists_gt 0
  exact ⟨b, hb, hb0⟩

/-! ## Proposition \ref{IA:prop:320A} -/

/-- Paper, Proposition \ref{IA:prop:320A}: let `ρ > 1`, `χ(n) = ⌊log_ρ n⌋ mod r`, `m ≥ 2` with
`L = log_ρ m ∉ ℤ` and `k = ⌊L⌋` with `k ≢ 0` and `k + 1 ≢ 0 (mod r)`. Then `m` is strongly bad
for `χ`. (The paper assumes `r ≥ 3`; the hypotheses on `k` are unsatisfiable for `r ≤ 2`, so we do
not need this assumption.) -/
theorem prop320A (ρ : ℝ) (hρ : 1 < ρ) (r : ℕ) (m : ℕ) (hm : 2 ≤ m)
    (hL : ∀ z : ℤ, Real.logb ρ m ≠ z)
    (hk0 : ¬ (r : ℤ) ∣ ⌊Real.logb ρ m⌋) (hk1 : ¬ (r : ℤ) ∣ ⌊Real.logb ρ m⌋ + 1) :
    IsStronglyBad (chiR ρ r) m := by
  intro B hB
  set L := Real.logb ρ m with hLdef
  set k := ⌊L⌋ with hkdef
  have hkL : (k : ℝ) < L := lt_of_le_of_ne (Int.floor_le L) (fun h => hL k h.symm)
  have hLk : L < k + 1 := Int.lt_floor_add_one L
  set ε := L - k with hε
  have hε0 : 0 < ε := by linarith
  have hρε : 1 < ρ ^ ε := Real.one_lt_rpow hρ hε0
  obtain ⟨b, hbB, hb0⟩ := exists_pos_mem hB
  obtain ⟨N, hN⟩ := exists_nat_gt ((m : ℝ) * b / (ρ ^ ε - 1) + b)
  obtain ⟨b', hb'B, hb'N⟩ := hB.exists_gt N
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  have hb'R : (N : ℝ) < b' := by exact_mod_cast hb'N
  have hb'big : (m : ℝ) * b / (ρ ^ ε - 1) < b' := by
    have : (0 : ℝ) ≤ b := hbR.le
    linarith
  have hbb' : (b : ℝ) < b' := by
    have : 0 ≤ (m : ℝ) * b / (ρ ^ ε - 1) := by
      apply div_nonneg <;> nlinarith
    linarith
  have hne : b ≠ b' := by
    intro h; rw [h] at hbb'; exact lt_irrefl _ hbb'
  have hb'0 : (0 : ℝ) < b' := hbR.trans hbb'
  -- X = b' + m b, Y = b + m b'
  have hXmem : b' + m * b ∈ restrSumset B m := ⟨b', hb'B, b, hbB, hne.symm, rfl⟩
  have hYmem : b + m * b' ∈ restrSumset B m := ⟨b, hbB, b', hb'B, hne, rfl⟩
  refine not_mono_of_ne hXmem hYmem ?_
  set X : ℝ := b' + m * b with hX
  set Y : ℝ := b + m * b' with hY
  have hX0 : 0 < X := by positivity
  have hY0 : 0 < Y := by positivity
  have hm0 : (0 : ℝ) < m := by linarith
  -- Y < m X
  have h1 : Y < m * X := by
    rw [hX, hY]
    have := mul_le_mul_of_nonneg_right hmR (le_of_lt (mul_pos hm0 hbR))
    nlinarith
  -- X < ρ^ε b'
  have h2 : X < ρ ^ ε * b' := by
    have := (div_lt_iff₀ (by linarith : (0 : ℝ) < ρ ^ ε - 1)).mp hb'big
    rw [hX]; nlinarith
  -- m b' < Y
  have h3 : (m : ℝ) * b' < Y := by rw [hY]; linarith
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : ρ ≠ 1 := ne_of_gt hρ
  have e1 : Real.logb ρ (m * X) = L + Real.logb ρ X :=
    Real.logb_mul hm0.ne' hX0.ne'
  have e2 : Real.logb ρ (ρ ^ ε * b') = ε + Real.logb ρ b' := by
    rw [Real.logb_mul (by positivity) hb'0.ne', Real.logb_rpow hρ0 hρ1]
  have e3 : Real.logb ρ (m * b') = L + Real.logb ρ b' := Real.logb_mul hm0.ne' hb'0.ne'
  have i1 := Real.logb_lt_logb hρ hY0 h1
  have i2 := Real.logb_lt_logb hρ hX0 h2
  have i3 := Real.logb_lt_logb hρ (by positivity) h3
  rw [e1] at i1; rw [e2] at i2; rw [e3] at i3
  have hfl := floor_sub_mem (x := Real.logb ρ X) (y := Real.logb ρ Y) (k := k)
    (by linarith) (by linarith)
  intro hc
  simp only [chiR, lam] at hc
  push_cast at hc
  have hd := Int.ModEq.dvd hc
  rcases hfl with h | h
  · exact hk0 (h ▸ hd)
  · exact hk1 (h ▸ hd)

/-! ## Proposition \ref{IA:prop:320B} -/

/-- Paper, Proposition \ref{IA:prop:320B}: let `m ≥ 2` and `ρ > 1 + 1/m`, and suppose there is an
odd integer `j` with `m < ρ^j < m + 1`. Then `m` is bad for `χ(n) = ⌊log_ρ n⌋ mod 2`. -/
theorem prop320B (ρ : ℝ) (m : ℕ) (hm : 2 ≤ m) (hρ : 1 + 1 / (m : ℝ) < ρ) (j : ℤ) (hj : Odd j)
    (hj1 : (m : ℝ) < ρ ^ j) (hj2 : ρ ^ j < m + 1) :
    IsBad (chiR ρ 2) m := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hρ1 : 1 < ρ := by
    have : 0 < 1 / (m : ℝ) := by positivity
    linarith
  have hρ0 : 0 < ρ := by linarith
  -- `j` is positive
  have hjpos : 0 < j := by
    by_contra h
    have := zpow_le_one_of_nonpos₀ hρ1.le (not_lt.mp h)
    linarith
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n := ⟨j.toNat, (Int.toNat_of_nonneg hjpos.le).symm⟩
  rw [zpow_natCast] at hj1 hj2
  set R := ρ ^ n with hR
  intro B hB
  obtain ⟨b, hbB, hb0⟩ := exists_pos_mem hB
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  have hgap : 0 < (m : ℝ) + 1 - R := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((m : ℝ) * b * R / ((m : ℝ) + 1 - R) + b)
  obtain ⟨b', hb'B, hb'N⟩ := hB.exists_gt N
  have hb'R : (N : ℝ) < b' := by exact_mod_cast hb'N
  have hR0 : 0 < R := by linarith
  have hq0 : 0 ≤ (m : ℝ) * b * R / ((m : ℝ) + 1 - R) := by positivity
  have hb'big : (m : ℝ) * b * R / ((m : ℝ) + 1 - R) < b' := by linarith
  have hbb' : (b : ℝ) < b' := by linarith
  have hb'0 : (0 : ℝ) < b' := hbR.trans hbb'
  have hne : b ≠ b' := by
    intro h; rw [h] at hbb'; exact lt_irrefl _ hbb'
  have hXmem : b' + m * b ∈ sumset B (dilate m B) := ⟨b', hb'B, m * b, ⟨b, hbB, rfl⟩, rfl⟩
  have hYmem : b + m * b' ∈ sumset B (dilate m B) := ⟨b, hbB, m * b', ⟨b', hb'B, rfl⟩, rfl⟩
  have hZmem : b' + m * b' ∈ sumset B (dilate m B) := ⟨b', hb'B, m * b', ⟨b', hb'B, rfl⟩, rfl⟩
  rintro ⟨c, hc⟩
  have cX := hc _ hXmem
  have cY := hc _ hYmem
  have cZ := hc _ hZmem
  simp only [chiR, lam] at cX cY cZ
  push_cast at cX cY cZ
  set X : ℝ := b' + m * b with hX
  set Y : ℝ := b + m * b' with hY
  set Z : ℝ := b' + m * b' with hZ
  have hX0 : 0 < X := by positivity
  have hY0 : 0 < Y := by positivity
  -- the four inequalities
  have h1 : Y < R * X := by
    rw [hX, hY]
    have := mul_le_mul_of_nonneg_right hmR (le_of_lt (mul_pos hm0 hbR))
    nlinarith
  have h2 : R * X < Z := by
    have := (div_lt_iff₀ hgap).mp hb'big
    rw [hX, hZ]; nlinarith
  have h3 : Y < Z := by rw [hY, hZ]; linarith
  have h4 : Z < ρ * Y := by
    have hρm : (m : ℝ) + 1 < ρ * m := by
      have := (div_lt_iff₀ hm0).mp (by linarith : 1 / (m : ℝ) < ρ - 1)
      nlinarith
    rw [hY, hZ]; nlinarith
  have hρne : ρ ≠ 1 := ne_of_gt hρ1
  have eR : Real.logb ρ (R * X) = n + Real.logb ρ X := by
    rw [Real.logb_mul hR0.ne' hX0.ne', hR, Real.logb_pow, Real.logb_self_eq_one hρ1, mul_one]
  have eρ : Real.logb ρ (ρ * Y) = 1 + Real.logb ρ Y := by
    rw [Real.logb_mul hρ0.ne' hY0.ne', Real.logb_self_eq_one hρ1]
  have i1 := Real.logb_lt_logb hρ1 hY0 h1
  have i2 := Real.logb_lt_logb hρ1 (by positivity) h2
  have i3 := Real.logb_lt_logb hρ1 hY0 h3
  have i4 := Real.logb_lt_logb hρ1 (by positivity) h4
  rw [eR] at i1 i2; rw [eρ] at i4
  set x := Real.logb ρ X
  set y := Real.logb ρ Y
  set z := Real.logb ρ Z
  have hzy := floor_sub_mem (x := y) (y := z) (k := 0) (by push_cast; linarith)
    (by push_cast; linarith)
  have hYZ : ⌊y⌋ = ⌊z⌋ := by
    have := cY.trans cZ.symm
    omega
  -- `⌊x + n⌋ = ⌊y⌋`
  have hxn : ⌊x + (n : ℝ)⌋ = ⌊y⌋ := by
    rw [Int.floor_eq_iff]
    have a1 := Int.floor_le y
    have a2 := Int.lt_floor_add_one z
    rw [← hYZ] at a2
    constructor <;> linarith
  have : ⌊x⌋ + n = ⌊y⌋ := by
    have := Int.floor_add_natCast x n
    omega
  obtain ⟨t, ht⟩ := hj
  have := cX.trans cY.symm
  omega

/-! ## Theorem \ref{IA:thm:320A} -/

/-- The colouring `χ_r(n) = ⌊log₂ n⌋ mod r`, written with the integer logarithm `Nat.log 2`
(for `n ≥ 1`, `Nat.log 2 n = ⌊log₂ n⌋`, see `chiR_two`). It takes values in `{0, …, r-1}`. -/
def chiA (r : ℕ) (n : ℕ) : ℕ := Nat.log 2 n % r

/-- `Nat.log 2 n = ⌊log₂ n⌋` for all `n` (both sides are `0` at `n = 0`). -/
lemma lam_two (n : ℕ) : lam 2 n = Nat.log 2 n := by
  have h := Real.floor_logb_natCast (b := 2) (r := (n : ℝ)) (Nat.cast_nonneg n)
  rw [Int.log_natCast] at h
  simpa [lam] using h

/-- The real-logarithm colouring `⌊log₂ n⌋ mod r` coincides with `chiA r`. -/
lemma chiR_two (r n : ℕ) : chiR 2 r n = (chiA r n : ℤ) := by
  simp [chiR, chiA, lam_two]

/-- The set of `m` with `2^k < m < 2^(k+1)` for some `k ≥ 1`, `k ≢ 0, -1 (mod r)`. -/
def S320A (r : ℕ) : Set ℕ :=
  {m | ∃ k : ℕ, 1 ≤ k ∧ 2 ^ k < m ∧ m < 2 ^ (k + 1) ∧ ¬ r ∣ k ∧ ¬ r ∣ k + 1}

/-- Paper, Theorem \ref{IA:thm:320A}, first claim: every `m ∈ S320A r` is strongly bad for
`χ_r(n) = ⌊log₂ n⌋ mod r`. -/
theorem thm320A_stronglyBad (r : ℕ) {m : ℕ} (hm : m ∈ S320A r) :
    IsStronglyBad (chiA r) m := by
  obtain ⟨k, hk1, hkm, hmk, hr0, hr1⟩ := hm
  have hm2 : 2 ≤ m := by
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    omega
  have hlog : Nat.log 2 m = k := Nat.log_eq_of_pow_le_of_lt_pow hkm.le hmk
  have hfl : ⌊Real.logb 2 m⌋ = k := by
    have := lam_two m
    simp only [lam] at this
    rw [this, hlog]
  have hS : IsStronglyBad (chiR 2 r) m := by
    apply prop320A 2 (by norm_num) r m hm2
    · intro z hz
      have hzk : z = k := by
        rw [hz, Int.floor_intCast] at hfl
        exact hfl
      rw [hzk] at hz
      have h2 := Real.rpow_logb (b := 2) (x := (m : ℝ)) (by norm_num) (by norm_num)
        (by exact_mod_cast (by omega : 0 < m))
      rw [hz] at h2
      norm_num at h2
      have : 2 ^ k = m := by exact_mod_cast h2
      omega
    · rw [hfl]; exact_mod_cast hr0
    · rw [hfl]; exact_mod_cast hr1
  exact hS.of_comp (fun x y h => by rw [chiR_two, chiR_two, h])

/-- Paper, Theorem \ref{IA:thm:320A}, last claim: `S320A r` contains infinitely many primes
(`r ≥ 3`). -/
theorem thm320A_primes (r : ℕ) (hr : 3 ≤ r) : {p | p.Prime ∧ p ∈ S320A r}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  set k := r * a + 1 with hk
  have hk1 : 1 ≤ k := by omega
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ k) (by positivity)
  have hpne : p ≠ 2 ^ (k + 1) := by
    rintro rfl
    have := Nat.Prime.eq_one_of_pow hp
    omega
  have hp3 : p < 2 ^ (k + 1) := by
    rw [pow_succ]; omega
  refine ⟨p, ⟨hp, k, hk1, hp1, hp3, ?_, ?_⟩, ?_⟩
  · intro h
    rw [hk, Nat.dvd_add_right (dvd_mul_right r a)] at h
    have := Nat.le_of_dvd one_pos h
    omega
  · intro h
    rw [hk, add_assoc, Nat.dvd_add_right (dvd_mul_right r a)] at h
    have := Nat.le_of_dvd two_pos h
    omega
  · have h1 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2 : 2 ^ a ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega

/-! ## Lucas numbers -/

/-- The Lucas numbers `L_0 = 2, L_1 = 1, L_{n+2} = L_{n+1} + L_n` (so `L_2 = 3`, `L_3 = 4`). -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

lemma lucas_add_two (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := rfl

open goldenRatio in
/-- Binet's formula `L_n = φ^n + ψ^n`. -/
lemma lucas_binet (n : ℕ) : (lucas n : ℝ) = φ ^ n + ψ ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => norm_num [lucas]
    | 1, _ => simp [lucas, Real.goldenRatio_add_goldenConj]
    | (n + 2), ih =>
      rw [lucas_add_two]; push_cast
      rw [ih (n + 1) (by omega), ih n (by omega)]
      have h1 : φ ^ (n + 2) = φ ^ n * φ ^ 2 := by ring
      have h2 : ψ ^ (n + 2) = ψ ^ n * ψ ^ 2 := by ring
      rw [h1, h2, Real.goldenRatio_sq, Real.goldenConj_sq]; ring

lemma lucas_ge_four (n : ℕ) (hn : 3 ≤ n) : 4 ≤ lucas n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ | 1, _ | 2, _ => omega
    | 3, _ => decide
    | (n + 4), ih =>
      show 4 ≤ lucas (n + 3) + lucas (n + 2)
      have := ih (n + 3) (by omega) (by omega)
      omega

open goldenRatio in
lemma lucas_lt_goldenRatio_pow {n : ℕ} (hn : Odd n) :
    (lucas n : ℝ) < φ ^ n ∧ φ ^ n < lucas n + 1 := by
  rw [lucas_binet]
  have hneg : ψ ^ n < 0 := hn.pow_neg Real.goldenConj_neg
  have habs : |ψ| < 1 := by
    rw [abs_lt]; exact ⟨Real.neg_one_lt_goldenConj, Real.goldenConj_neg.trans one_pos⟩
  have h1 : |ψ ^ n| < 1 := by
    rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg _) habs (by rintro rfl; simp at hn)
  have h2 := (abs_lt.mp h1).1
  constructor <;> linarith

/-- Paper, Theorem \ref{IA:thm:320B}(i), first claim: for every odd `n ≥ 3`, `L_n` is bad for
`χ^{(φ)}(n) = ⌊log_φ n⌋ mod 2`. -/
theorem thm320B_lucas_bad (n : ℕ) (hn : Odd n) (hn3 : 3 ≤ n) :
    IsBad (chiR Real.goldenRatio 2) (lucas n) := by
  have h4 := lucas_ge_four n hn3
  have h4R : (4 : ℝ) ≤ lucas n := by exact_mod_cast h4
  obtain ⟨hl, hu⟩ := lucas_lt_goldenRatio_pow hn
  apply prop320B _ _ (by omega) _ n (by exact_mod_cast hn)
    (by rw [zpow_natCast]; exact hl) (by rw [zpow_natCast]; exact hu)
  -- `φ > 1.6 > 1 + 1/L_n`
  have hφ : (1.6 : ℝ) < Real.goldenRatio := by
    rw [Real.goldenRatio]
    have : (2.2 : ℝ) < √5 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  have : 1 / (lucas n : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4R
  linarith

/-- Paper, Theorem \ref{IA:thm:320B}(i), second claim: for every `q ∈ ℕ = {1, 2, …}` there are
infinitely many odd `n ≥ 3` with `L_n ≡ 1 (mod q)`. -/
theorem thm320B_lucas_mod (q : ℕ) (hq : 0 < q) :
    {n : ℕ | Odd n ∧ 3 ≤ n ∧ lucas n ≡ 1 [MOD q]}.Infinite := by
  have : NeZero q := ⟨hq.ne'⟩
  let T : Equiv.Perm (ZMod q × ZMod q) :=
    { toFun := fun p => (p.2, p.1 + p.2)
      invFun := fun p => (p.2 - p.1, p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  let v : ℕ → ZMod q × ZMod q := fun n => ((lucas n : ZMod q), (lucas (n + 1) : ZMod q))
  have hv : ∀ n, v n = (T ^ n) (v 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ← ih]
      simp only [v, T, Equiv.coe_fn_mk, Prod.mk.injEq, true_and]
      rw [lucas_add_two]; push_cast; ring
  set P := orderOf T with hP
  have hP0 : 0 < P := orderOf_pos T
  have hper : ∀ t, v (1 + 2 * P * t) = v 1 := by
    intro t
    have hTP : T ^ P = 1 := pow_orderOf_eq_one T
    have e : 1 + 2 * P * t = 1 + P * (2 * t) := by ring
    rw [hv, hv 1, e, pow_add, pow_mul, hTP, one_pow, mul_one]
  let f : ℕ → ℕ := fun t => 1 + 2 * P * (t + 1)
  have hf : Function.Injective f := by
    intro a b h
    simp only [f] at h
    have := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * P) (by omega : 2 * P * (a + 1) =
      2 * P * (b + 1))
    omega
  apply Set.infinite_of_injective_forall_mem hf
  intro t
  refine ⟨⟨P * (t + 1), by simp only [f]; ring⟩, by simp only [f]; nlinarith, ?_⟩
  have := congrArg Prod.fst (hper (t + 1))
  simp only [v] at this
  rw [← ZMod.natCast_eq_natCast_iff]
  simpa [lucas] using this

/-! ## Lemma \ref{IA:lem:nested} and Theorem \ref{IA:thm:320B}(ii) -/

/-- One step of the nested-interval construction in Lemma \ref{IA:lem:nested}. -/
lemma nested_step (α β : ℝ) (P J : ℕ) (hα : 3 / 2 ≤ α) (hαβ : α < β) :
    ∃ α' β' : ℝ, ∃ j p : ℕ, α < α' ∧ α' < β' ∧ β' < β ∧ J < j ∧ Odd j ∧ P < p ∧ p.Prime ∧
      ∀ s ∈ Set.Icc α' β', (p : ℝ) < s ^ j ∧ s ^ j < p + 1 := by
  have hα1 : 1 < α := by linarith
  have hα0 : 0 < α := by linarith
  have hβα : 1 < β / α := by rw [one_lt_div hα0]; exact hαβ
  have e1 := (tendsto_pow_atTop_atTop_of_one_lt hα1).eventually_ge_atTop ((P : ℝ) + 2)
  have e2 := (tendsto_pow_atTop_atTop_of_one_lt hβα).eventually_ge_atTop (4 : ℝ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (Filter.eventually_gt_atTop J)))
  set j := 2 * N + 1 with hj
  obtain ⟨hxj, hβj, hJj⟩ := hN j (by omega)
  have hj0 : j ≠ 0 := by omega
  set x := α ^ j with hx
  have hx2 : (2 : ℝ) ≤ x := by
    have : (0 : ℝ) ≤ P := Nat.cast_nonneg P
    linarith
  have hβx : 4 * x ≤ β ^ j := by
    rw [div_pow, le_div_iff₀ (by positivity)] at hβj
    linarith
  set n := ⌈x⌉₊ with hn
  have hn0 : n ≠ 0 := by
    have : 0 < n := Nat.ceil_pos.mpr (by linarith)
    omega
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n hn0
  have hxn : x ≤ n := Nat.le_ceil x
  have hnx : (n : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hnpR : (n : ℝ) < p := by exact_mod_cast hnp
  have hp2nR : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2n
  have hpP : P < p := by
    have : (P : ℝ) < p := by linarith
    exact_mod_cast this
  have hpβ : (p : ℝ) + 1 < β ^ j := by linarith
  have hβ0 : 0 < β := by linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set α' := ((p : ℝ) + 1 / 3) ^ ((j : ℝ)⁻¹) with hα'
  set β' := ((p : ℝ) + 2 / 3) ^ ((j : ℝ)⁻¹) with hβ'
  have hα'j : α' ^ j = p + 1 / 3 := Real.rpow_inv_natCast_pow (by positivity) hj0
  have hβ'j : β' ^ j = p + 2 / 3 := Real.rpow_inv_natCast_pow (by positivity) hj0
  have hα'0 : 0 ≤ α' := by positivity
  have hβ'0 : 0 ≤ β' := by positivity
  refine ⟨α', β', j, p, ?_, ?_, ?_, hJj, ⟨N, by omega⟩, hpP, hp, ?_⟩
  · rw [← pow_lt_pow_iff_left₀ hα0.le hα'0 hj0, hα'j]; linarith
  · rw [← pow_lt_pow_iff_left₀ hα'0 hβ'0 hj0, hα'j, hβ'j]; linarith
  · rw [← pow_lt_pow_iff_left₀ hβ'0 hβ0.le hj0, hβ'j]; linarith
  · rintro s ⟨hs1, hs2⟩
    have a1 : α' ^ j ≤ s ^ j := pow_le_pow_left₀ hα'0 hs1 j
    have a2 : s ^ j ≤ β' ^ j := pow_le_pow_left₀ (hα'0.trans hs1) hs2 j
    rw [hα'j] at a1; rw [hβ'j] at a2
    constructor <;> linarith

/-- State of the nested-interval construction: an interval `[α, β]`, an exponent and a prime. -/
structure NestState where
  α : ℝ
  β : ℝ
  j : ℕ
  p : ℕ

/-- The invariant `3/2 ≤ α < β`. -/
def NestState.Inv (s : NestState) : Prop := 3 / 2 ≤ s.α ∧ s.α < s.β

/-- The relation between consecutive states. -/
def NestState.Rel (s t : NestState) : Prop :=
  s.α < t.α ∧ t.β < s.β ∧ s.j < t.j ∧ s.p < t.p ∧ Odd t.j ∧ t.p.Prime ∧
    ∀ x ∈ Set.Icc t.α t.β, (t.p : ℝ) < x ^ t.j ∧ x ^ t.j < t.p + 1

lemma NestState.exists_next (s : NestState) (h : s.Inv) : ∃ t : NestState, t.Inv ∧ s.Rel t := by
  obtain ⟨α', β', j, p, h1, h2, h3, h4, h5, h6, h7, h8⟩ := nested_step s.α s.β s.p s.j h.1 h.2
  exact ⟨⟨α', β', j, p⟩, ⟨by linarith [h.1], h2⟩, h1, h3, h4, h6, h5, h7, h8⟩

/-- The nested sequence of states. -/
noncomputable def nestSeq : ℕ → {s : NestState // s.Inv}
  | 0 => ⟨⟨3 / 2, 2, 0, 1⟩, by norm_num [NestState.Inv]⟩
  | (k + 1) => ⟨Classical.choose ((nestSeq k).1.exists_next (nestSeq k).2),
      (Classical.choose_spec ((nestSeq k).1.exists_next (nestSeq k).2)).1⟩

lemma nestSeq_rel (k : ℕ) : (nestSeq k).1.Rel (nestSeq (k + 1)).1 :=
  (Classical.choose_spec ((nestSeq k).1.exists_next (nestSeq k).2)).2

/-- Paper, Lemma \ref{IA:lem:nested}: there are `ρ ∈ (3/2, 2)`, odd integers `j_1 < j_2 < ⋯`
and primes `p_1 < p_2 < ⋯` with `p_k < ρ^{j_k} < p_k + 1` for all `k`. -/
theorem lem_nested : ∃ ρ : ℝ, 3 / 2 < ρ ∧ ρ < 2 ∧ ∃ j p : ℕ → ℕ, StrictMono j ∧ StrictMono p ∧
    ∀ k, Odd (j k) ∧ (p k).Prime ∧ (p k : ℝ) < ρ ^ (j k) ∧ ρ ^ (j k) < p k + 1 := by
  let a : ℕ → ℝ := fun k => (nestSeq k).1.α
  let b : ℕ → ℝ := fun k => (nestSeq k).1.β
  have ha : StrictMono a := strictMono_nat_of_lt_succ fun k => (nestSeq_rel k).1
  have hb : StrictAnti b := strictAnti_nat_of_succ_lt fun k => (nestSeq_rel k).2.1
  have hab : ∀ k, a k < b k := fun k => (nestSeq k).2.2
  have hab' : ∀ k l, a l ≤ b k := by
    intro k l
    rcases le_total l k with h | h
    · exact (ha.monotone h).trans (hab k).le
    · exact (hab l).le.trans (hb.antitone h)
  have hbdd : BddAbove (Set.range a) := ⟨b 0, by rintro _ ⟨l, rfl⟩; exact hab' 0 l⟩
  set ρ := ⨆ k, a k with hρ
  have hρa : ∀ k, a k ≤ ρ := fun k => le_ciSup hbdd k
  have hρb : ∀ k, ρ ≤ b k := fun k => ciSup_le fun l => hab' k l
  have ha0 : a 0 = 3 / 2 := rfl
  have hb0 : b 0 = 2 := rfl
  refine ⟨ρ, ?_, ?_, fun k => (nestSeq (k + 1)).1.j, fun k => (nestSeq (k + 1)).1.p,
    strictMono_nat_of_lt_succ fun k => (nestSeq_rel (k + 1)).2.2.1,
    strictMono_nat_of_lt_succ fun k => (nestSeq_rel (k + 1)).2.2.2.1, fun k => ?_⟩
  · have := ha (Nat.zero_lt_one); linarith [hρa 1]
  · have := hb (Nat.zero_lt_one); linarith [hρb 1]
  · obtain ⟨-, -, -, -, h5, h6, h7⟩ := nestSeq_rel k
    exact ⟨h5, h6, h7 ρ ⟨hρa (k + 1), hρb (k + 1)⟩⟩

/-- Paper, Theorem \ref{IA:thm:320B}(ii): there are `ρ ∈ (3/2, 2)` and infinitely many primes
that are bad for `χ^{(ρ)}(n) = ⌊log_ρ n⌋ mod 2`. -/
theorem thm320B_primes : ∃ ρ : ℝ, 3 / 2 < ρ ∧ ρ < 2 ∧
    {p : ℕ | p.Prime ∧ IsBad (chiR ρ 2) p}.Infinite := by
  obtain ⟨ρ, hρ1, hρ2, j, p, -, hp, h⟩ := lem_nested
  refine ⟨ρ, hρ1, hρ2, Set.infinite_of_injective_forall_mem hp.injective fun k => ?_⟩
  obtain ⟨hj, hpr, h1, h2⟩ := h k
  refine ⟨hpr, prop320B ρ (p k) hpr.two_le ?_ (j k) (by exact_mod_cast hj)
    (by rw [zpow_natCast]; exact h1) (by rw [zpow_natCast]; exact h2)⟩
  have : (2 : ℝ) ≤ p k := by exact_mod_cast hpr.two_le
  have : 1 / (p k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
  linarith

/-! ## Corollary \ref{IA:cor:320} -/

lemma exists_coprime_of_infinite {S : Set ℕ} (hS : {p | p.Prime ∧ p ∈ S}.Infinite) (q : ℕ)
    (hq : 0 < q) : ∃ m ∈ S, m.Prime ∧ m.Coprime q := by
  obtain ⟨p, ⟨hp, hpS⟩, hpq⟩ := hS.exists_gt q
  refine ⟨p, hpS, hp, (Nat.coprime_comm).mp ?_⟩
  exact (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
    fun h => absurd (Nat.le_of_dvd hq h) (by omega))

/-- Paper, Corollary \ref{IA:cor:320}: for every `r ≥ 2` there is an `r`-colouring of `ℕ` such
that for every `q ∈ ℕ = {1, 2, …}` some prime `m ≥ 2` with `gcd(m, q) = 1` is bad. -/
theorem cor320 (r : ℕ) (hr : 2 ≤ r) :
    ∃ χ : ℕ → Fin r, ∀ q : ℕ, 0 < q → ∃ m : ℕ, m.Prime ∧ m.Coprime q ∧ IsBad χ m := by
  rcases Nat.lt_or_ge r 3 with h | h
  · obtain rfl : r = 2 := by omega
    obtain ⟨ρ, -, -, hinf⟩ := thm320B_primes
    refine ⟨fun n => ⟨(chiR ρ 2 n).toNat, ?_⟩, fun q hq => ?_⟩
    · have h1 := Int.emod_nonneg (lam ρ n) (by norm_num : (2 : ℤ) ≠ 0)
      have h2 := Int.emod_lt_of_pos (lam ρ n) (by norm_num : (0 : ℤ) < 2)
      simp only [chiR]; push_cast; omega
    obtain ⟨m, hmS, hm, hmq⟩ := exists_coprime_of_infinite (S := {p | IsBad (chiR ρ 2) p})
      (by simpa using hinf) q hq
    refine ⟨m, hm, hmq, IsBad.of_comp (fun x y hxy => ?_) hmS⟩
    have hx := Int.emod_nonneg (lam ρ x) (by norm_num : (2 : ℤ) ≠ 0)
    have hy := Int.emod_nonneg (lam ρ y) (by norm_num : (2 : ℤ) ≠ 0)
    simp only [Fin.mk.injEq, chiR] at hxy ⊢
    push_cast at hx hy ⊢
    omega
  · refine ⟨fun n => ⟨chiA r n, Nat.mod_lt _ (by omega)⟩, fun q hq => ?_⟩
    obtain ⟨m, hmS, hm, hmq⟩ := exists_coprime_of_infinite (thm320A_primes r h) q hq
    exact ⟨m, hm, hmq, IsBad.of_comp (fun x y hxy => congrArg Fin.val hxy)
      (thm320A_stronglyBad r hmS).isBad⟩

/-- Paper, Corollary \ref{IA:cor:320}, "in particular" part: Question \ref{IA:q:320} has a negative
answer for every number `r ≥ 2` of colours, also when the condition is imposed only for prime `m`.
Here `B ⊆ ℕ = {1, 2, …}`; a colouring of `{0, 1, 2, …}` restricts to one of `{1, 2, …}` and the
sumsets `B + mB` (with `m ≥ 1`, `B ⊆ {1, 2, …}`) never contain `0`. -/
theorem q320_negative_prime (r : ℕ) (hr : 2 ≤ r) :
    ¬ ∀ χ : ℕ → Fin r, ∃ q : ℕ, 0 < q ∧ ∀ m : ℕ, m.Prime → m.Coprime q →
      ∃ B : Set ℕ, B.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ IsMonochromatic χ (sumset B (dilate m B)) := by
  intro H
  obtain ⟨χ, hχ⟩ := cor320 r hr
  obtain ⟨q, hq, hQ⟩ := H χ
  obtain ⟨m, hm, hmq, hbad⟩ := hχ q hq
  obtain ⟨B, hB, -, hmono⟩ := hQ m hm hmq
  exact hbad B hB hmono

/-- Question \ref{IA:q:320} has a negative answer for every `r ≥ 2`, also when the condition is
imposed only for `m ≥ 2`. -/
theorem q320_negative_ge_two (r : ℕ) (hr : 2 ≤ r) :
    ¬ ∀ χ : ℕ → Fin r, ∃ q : ℕ, 0 < q ∧ ∀ m : ℕ, 2 ≤ m → m.Coprime q →
      ∃ B : Set ℕ, B.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ IsMonochromatic χ (sumset B (dilate m B)) :=
  fun H => q320_negative_prime r hr fun χ => by
    obtain ⟨q, hq, hQ⟩ := H χ
    exact ⟨q, hq, fun m hm => hQ m hm.two_le⟩

/-- Question \ref{IA:q:320} as literally stated (all `m ∈ ℕ = {1, 2, …}`) has a negative answer for
every number `r ≥ 2` of colours. -/
theorem q320_negative (r : ℕ) (hr : 2 ≤ r) :
    ¬ ∀ χ : ℕ → Fin r, ∃ q : ℕ, 0 < q ∧ ∀ m : ℕ, 1 ≤ m → m.Coprime q →
      ∃ B : Set ℕ, B.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ IsMonochromatic χ (sumset B (dilate m B)) :=
  fun H => q320_negative_prime r hr fun χ => by
    obtain ⟨q, hq, hQ⟩ := H χ
    exact ⟨q, hq, fun m hm => hQ m hm.one_lt.le⟩

/-! ## Logarithmic density of `S320A r` (Theorem \ref{IA:thm:320A}, second claim) -/

/-- `A ⊆ ℕ` has logarithmic density `d`:
`(1 / log N) ∑_{n=1}^{N} 𝟙_A(n) / n → d` as `N → ∞`. -/
def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, A.indicator (fun n : ℕ => (1 : ℝ) / n) n) /
    Real.log N) atTop (𝓝 d)

section LogDensity

variable (r : ℕ)

/-- `k` is admissible: `k ≢ 0, -1 (mod r)`. -/
abbrev Adm (k : ℕ) : Prop := ¬ r ∣ k ∧ ¬ r ∣ k + 1

/-- Indicator of admissibility. -/
noncomputable def ind (k : ℕ) : ℝ := if Adm r k then 1 else 0

lemma mem_S320A_iff {n k : ℕ} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) :
    n ∈ S320A r ↔ 2 ^ k < n ∧ Adm r k := by
  constructor
  · rintro ⟨k', -, hlt, hlt2, h0, h1'⟩
    have e1 : Nat.log 2 n = k' := Nat.log_eq_of_pow_le_of_lt_pow hlt.le hlt2
    have e2 : Nat.log 2 n = k := Nat.log_eq_of_pow_le_of_lt_pow h1 h2
    rw [e1] at e2
    subst e2
    exact ⟨hlt, h0, h1'⟩
  · rintro ⟨hlt, h0, h1'⟩
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · exact absurd (dvd_zero r) h0
      · exact h
    exact ⟨k, hk, hlt, h2, h0, h1'⟩

/-- The weight `𝟙_S(n) / n`. -/
noncomputable def wt (n : ℕ) : ℝ := (S320A r).indicator (fun n : ℕ => (1 : ℝ) / n) n

lemma wt_nonneg (n : ℕ) : 0 ≤ wt r n := by
  unfold wt; apply Set.indicator_nonneg; intro _ _; positivity

/-- Partial sums `T(N) = ∑_{n < N} 𝟙_S(n) / n`. -/
noncomputable def Tsum (N : ℕ) : ℝ := ∑ n ∈ range N, wt r n

lemma Tsum_mono {M N : ℕ} (h : M ≤ N) : Tsum r M ≤ Tsum r N :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ => wt_nonneg r i

lemma Tsum_nonneg (N : ℕ) : 0 ≤ Tsum r N := Finset.sum_nonneg fun i _ => wt_nonneg r i

/-- `∑_{2^k < n < 2^{k+1}} 1/n`. -/
noncomputable def cBlock (k : ℕ) : ℝ :=
  ∑ n ∈ Ico (2 ^ k : ℕ) (2 ^ (k + 1)), (1 : ℝ) / (n : ℝ) - 1 / ((2 ^ k : ℕ) : ℝ)

lemma block_sum (k : ℕ) : ∑ n ∈ Ico (2 ^ k) (2 ^ (k + 1)), wt r n = ind r k * cBlock k := by
  have h : ∀ n ∈ Ico (2 ^ k) (2 ^ (k + 1)),
      wt r n = ind r k * ((1 : ℝ) / n - if n = 2 ^ k then (1 : ℝ) / n else 0) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hiff := mem_S320A_iff r hn.1 hn.2
    simp only [wt, Set.indicator, ind]
    by_cases ha : Adm r k <;> by_cases hn0 : n = 2 ^ k
    · subst hn0; simp [hiff]
    · have : 2 ^ k < n := lt_of_le_of_ne hn.1 (Ne.symm hn0)
      simp [hiff, hn0, this]
    · simp [hiff, ha]
    · simp [hiff, ha]
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  have hmem : 2 ^ k ∈ Ico (2 ^ k) (2 ^ (k + 1)) := by
    rw [Finset.mem_Ico]; exact ⟨le_rfl, Nat.pow_lt_pow_right (by norm_num) (by omega)⟩
  rw [if_pos hmem, cBlock]

lemma Tsum_pow (K : ℕ) : Tsum r (2 ^ K) = ∑ k ∈ range K, ind r k * cBlock k := by
  induction K with
  | zero => simp [Tsum, wt, Set.indicator]
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih, ← block_sum, Tsum, Tsum,
      ← Finset.sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K))]

/-- `F(n) = ∑_{i < n} 1/i`. -/
noncomputable def Fh (n : ℕ) : ℝ := ∑ i ∈ range n, (1 : ℝ) / i

lemma harmonic_eq_Fh (n : ℕ) : (harmonic n : ℝ) = Fh n + 1 / n := by
  have h1 : Fh (n + 1) = Fh n + 1 / n := by rw [Fh, Finset.sum_range_succ]; rfl
  have h2 : Fh (n + 1) = ∑ i ∈ range n, (1 : ℝ) / ((i + 1 : ℕ) : ℝ) := by
    rw [Fh, Finset.sum_range_succ']; simp
  rw [← h1, h2, harmonic]; push_cast; simp

lemma tendsto_Fh_sub_log :
    Tendsto (fun n : ℕ => Fh n - Real.log n) atTop (𝓝 eulerMascheroniConstant) := by
  have h := Real.tendsto_harmonic_sub_log.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [sub_zero] at h
  refine h.congr fun n => ?_
  rw [harmonic_eq_Fh]; ring

lemma tendsto_two_pow_nat : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => ?_⟩
  exact (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) ha)

lemma cBlock_eq (k : ℕ) : cBlock k =
    (Fh (2 ^ (k + 1)) - Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) -
      (Fh (2 ^ k) - Real.log ((2 ^ k : ℕ) : ℝ)) + Real.log 2 - 1 / ((2 ^ k : ℕ) : ℝ) := by
  rw [cBlock, Finset.sum_Ico_eq_sub _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))]
  push_cast
  rw [Real.log_pow, Real.log_pow, Fh, Fh]
  push_cast; ring

lemma tendsto_cBlock : Tendsto cBlock atTop (𝓝 (Real.log 2)) := by
  have h1 := tendsto_Fh_sub_log.comp (tendsto_two_pow_nat.comp (tendsto_add_atTop_nat 1))
  have h2 := tendsto_Fh_sub_log.comp tendsto_two_pow_nat
  have h3 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp tendsto_two_pow_nat
  have h := ((h1.sub h2).add_const (Real.log 2)).sub h3
  simp only [sub_self, zero_add, sub_zero] at h
  refine h.congr fun k => ?_
  rw [cBlock_eq]; rfl

/-- The admissible-count `#{k < K : k admissible}`. -/
noncomputable def cnt (K : ℕ) : ℝ := ∑ k ∈ range K, ind r k

lemma ind_nonneg (k : ℕ) : 0 ≤ ind r k := by unfold ind; split_ifs <;> norm_num

lemma ind_le_one (k : ℕ) : ind r k ≤ 1 := by unfold ind; split_ifs <;> norm_num

lemma cnt_mono {M N : ℕ} (h : M ≤ N) : cnt r M ≤ cnt r N :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ => ind_nonneg r i

lemma ind_add_mul (t i : ℕ) : ind r (r * t + i) = ind r i := by
  simp only [ind, Adm, add_assoc, Nat.dvd_add_right (dvd_mul_right r t)]

lemma sum_ind_block (hr : 2 ≤ r) : ∑ i ∈ range r, ind r i = r - 2 := by
  have hfilt : (range r).filter (fun i => Adm r i) = Finset.Ioo 0 (r - 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo, Adm]
    constructor
    · rintro ⟨hi, h0, h1⟩
      refine ⟨Nat.pos_of_ne_zero fun h => h0 (h ▸ dvd_zero r), ?_⟩
      by_contra hc
      exact h1 (by rw [show i + 1 = r by omega])
    · rintro ⟨h0, h1⟩
      refine ⟨by omega, fun h => ?_, fun h => ?_⟩
      · have := Nat.le_of_dvd h0 h; omega
      · have := Nat.le_of_dvd (by omega) h; omega
  simp only [ind]
  rw [Finset.sum_boole, hfilt, Nat.card_Ioo, show r - 1 - 0 - 1 = r - 2 by omega,
    Nat.cast_sub hr]
  push_cast; ring

lemma cnt_mul (hr : 2 ≤ r) (t : ℕ) : cnt r (r * t) = (r - 2) * t := by
  induction t with
  | zero => simp [cnt]
  | succ t ih =>
    rw [cnt, mul_add, mul_one, Finset.sum_range_add, ← cnt, ih]
    simp only [ind_add_mul]
    rw [sum_ind_block r hr]; push_cast; ring

lemma tendsto_cnt (hr : 3 ≤ r) :
    Tendsto (fun K : ℕ => cnt r K * (K : ℝ)⁻¹) atTop (𝓝 ((r - 2) / r)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr2 : (0 : ℝ) ≤ r - 2 := by
    have : (3 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hlim := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlo : Tendsto (fun K : ℕ => (r - 2) / r - (r - 2) * (K : ℝ)⁻¹) atTop
      (𝓝 ((r - 2) / r)) := by
    simpa using (hlim.const_mul ((r : ℝ) - 2)).const_sub (((r : ℝ) - 2) / r)
  have hhi : Tendsto (fun K : ℕ => (r - 2) / r + (r - 2) * (K : ℝ)⁻¹) atTop
      (𝓝 ((r - 2) / r)) := by
    simpa using (hlim.const_mul ((r : ℝ) - 2)).const_add (((r : ℝ) - 2) / r)
  have key : ∀ K : ℕ, 0 < K → (r - 2) * ((K : ℝ) - r) ≤ r * cnt r K ∧
      r * cnt r K ≤ (r - 2) * ((K : ℝ) + r) := by
    intro K hK
    have h1 : r * (K / r) ≤ K := Nat.mul_div_le K r
    have h2 : K < r * (K / r) + r := by
      have := Nat.div_add_mod K r
      have := Nat.mod_lt K (by omega : 0 < r)
      omega
    have h3 : K ≤ r * (K / r + 1) := by rw [mul_add, mul_one]; omega
    have c1 := cnt_mono r h1
    have c2 := cnt_mono r h3
    rw [cnt_mul r (by omega)] at c1 c2
    generalize K / r = t at *
    have h1R : (r : ℝ) * t ≤ K := by exact_mod_cast h1
    have h2R : (K : ℝ) < r * t + r := by exact_mod_cast h2
    push_cast at c1 c2
    constructor <;> nlinarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with K hK
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    obtain ⟨k1, -⟩ := key K hK
    rw [← sub_nonneg]
    have e : cnt r K * (K : ℝ)⁻¹ - ((r - 2) / r - (r - 2) * (K : ℝ)⁻¹) =
        (r * cnt r K - (r - 2) * (K - r)) / (r * K) := by field_simp
    rw [e]
    apply div_nonneg (by linarith) (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with K hK
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    obtain ⟨-, k2⟩ := key K hK
    rw [← sub_nonneg]
    have e : (r - 2) / r + (r - 2) * (K : ℝ)⁻¹ - cnt r K * (K : ℝ)⁻¹ =
        ((r - 2) * (K + r) - r * cnt r K) / (r * K) := by field_simp
    rw [e]
    apply div_nonneg (by linarith) (by positivity)

lemma tendsto_Tsum_pow (hr : 3 ≤ r) :
    Tendsto (fun K : ℕ => Tsum r (2 ^ K) * (K : ℝ)⁻¹) atTop
      (𝓝 (Real.log 2 * ((r - 2) / r))) := by
  set u : ℕ → ℝ := fun k => ind r k * (cBlock k - Real.log 2) with hu
  have hu0 : Tendsto u atTop (𝓝 0) := by
    have h := (tendsto_cBlock.sub_const (Real.log 2)).norm
    rw [sub_self, norm_zero] at h
    refine squeeze_zero_norm (fun k => ?_) h
    rw [hu, norm_mul]
    have : ‖ind r k‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (ind_nonneg r k)]; exact ind_le_one r k
    nlinarith [norm_nonneg (cBlock k - Real.log 2), norm_nonneg (ind r k)]
  have h := ((tendsto_cnt r hr).const_mul (Real.log 2)).add hu0.cesaro
  rw [add_zero] at h
  refine h.congr fun K => ?_
  rw [Tsum_pow, cnt]
  simp only [hu, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

lemma tendsto_natLog_two : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun M => ⟨2 ^ M, fun N hN => ?_⟩
  exact Nat.le_log_of_pow_le (by norm_num) hN

/-- Paper, Theorem \ref{IA:thm:320A}, second claim: `S320A r` has logarithmic density `1 - 2/r`
(`r ≥ 3`). -/
theorem thm320A_logDensity (hr : 3 ≤ r) : HasLogDensity (S320A r) (1 - 2 / r) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have ha := tendsto_Tsum_pow r hr
  have hval : Real.log 2 * ((r - 2) / r) * 1 / Real.log 2 = 1 - 2 / (r : ℝ) := by
    field_simp
  -- lower and upper bounds as functions of `K`
  have hlo : Tendsto (fun K : ℕ => Tsum r (2 ^ K) / ((K + 1) * Real.log 2)) atTop
      (𝓝 (1 - 2 / (r : ℝ))) := by
    have h := (ha.mul (tendsto_natCast_div_add_atTop (1 : ℝ))).div_const (Real.log 2)
    rw [hval] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with K hK
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    field_simp
  have hhi : Tendsto (fun K : ℕ => Tsum r (2 ^ (K + 1)) / (K * Real.log 2)) atTop
      (𝓝 (1 - 2 / (r : ℝ))) := by
    have ha' := (tendsto_add_atTop_iff_nat 1).mpr ha
    have h1 : Tendsto (fun K : ℕ => 1 + (K : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    have h := (ha'.mul h1).div_const (Real.log 2)
    rw [hval] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with K hK
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    push_cast
    field_simp
  have hsum : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, (S320A r).indicator (fun n : ℕ => (1 : ℝ) / n) n =
      Tsum r (N + 1) := by
    intro N
    rw [Tsum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
    simp [wt, Set.indicator, Finset.Ico_add_one_right_eq_Icc]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlo.comp tendsto_natLog_two)
    (hhi.comp tendsto_natLog_two) ?_ ?_
  all_goals
    filter_upwards [eventually_ge_atTop 2] with N hN
    simp only [Function.comp, hsum]
    set K := Nat.log 2 N with hK
    have hK1 : 1 ≤ K := Nat.log_pos (by norm_num) hN
    have hp1 : 2 ^ K ≤ N := Nat.pow_log_le_self 2 (by omega)
    have hp2 : N < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hlogN1 : (K : ℝ) * Real.log 2 ≤ Real.log N := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hp1)
    have hlogN2 : Real.log N < ((K : ℝ) + 1) * Real.log 2 := by
      rw [← Nat.cast_succ, ← Real.log_pow]
      exact Real.log_lt_log hNR (by exact_mod_cast hp2)
    have hlogN0 : 0 < Real.log N := by nlinarith
    have hT1 := Tsum_mono r (by omega : 2 ^ K ≤ N + 1)
    have hT2 := Tsum_mono r (by omega : N + 1 ≤ 2 ^ (K + 1))
  · exact div_le_div₀ (Tsum_nonneg r _) hT1 hlogN0 hlogN2.le
  · exact div_le_div₀ (Tsum_nonneg r _) hT2 (by positivity) hlogN1

end LogDensity

/-- Paper, Theorem \ref{IA:thm:320A} (all three claims): for `r ≥ 3` and
`χ_r(n) = ⌊log₂ n⌋ mod r`, every `m` with `2^k < m < 2^(k+1)` for some `k ≥ 1` with
`k ≢ 0, -1 (mod r)` is strongly bad for `χ_r`; the set of these `m` has logarithmic density
`1 - 2/r` and contains infinitely many primes. -/
theorem thm320A (r : ℕ) (hr : 3 ≤ r) :
    (∀ m ∈ S320A r, IsStronglyBad (chiA r) m) ∧ HasLogDensity (S320A r) (1 - 2 / r) ∧
      {p | p.Prime ∧ p ∈ S320A r}.Infinite :=
  ⟨fun _ hm => thm320A_stronglyBad r hm, thm320A_logDensity r hr, thm320A_primes r hr⟩

/-- Paper, Theorem \ref{IA:thm:320B} (both parts). -/
theorem thm320B :
    (∀ n : ℕ, Odd n → 3 ≤ n → IsBad (chiR Real.goldenRatio 2) (lucas n)) ∧
    (∀ q : ℕ, 0 < q → {n : ℕ | Odd n ∧ 3 ≤ n ∧ lucas n ≡ 1 [MOD q]}.Infinite) ∧
    (∃ ρ : ℝ, 3 / 2 < ρ ∧ ρ < 2 ∧ {p : ℕ | p.Prime ∧ IsBad (chiR ρ 2) p}.Infinite) :=
  ⟨thm320B_lucas_bad, thm320B_lucas_mod, thm320B_primes⟩

end Kmrr25.Q320
