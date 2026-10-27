import Kmrr25.Basic

/-!
# Logarithmic density and Question 3.23

Paper, Section \ref{IA:sec:q323}, Theorem \ref{IA:thm:323}.

Fix `η ∈ (0, 1/6)`, let `U_η = (1/3 + η, 2/3 - η)`, `T_k = 2^{2^k}`, `X_k = k T_k`,
`Y_k = T_{k+1}/k` (a real number), `R_k = {s ∈ {0, …, k-1} : s/k ∈ U_η}` and
`A_η = ⋃_{k ≥ 1} {n : X_k ≤ n < Y_k, n mod k ∈ R_k}`.

## Main results

* `logDensity_A` — Theorem \ref{IA:thm:323}(a): for `0 < η < 1/6` the logarithmic density of
  `A_η` exists and equals `1/3 - 2η`, i.e. `(1 / log N) ∑_{n=1}^{N} 𝟙_{A_η}(n)/n → 1/3 - 2η`.
* `no_linSumset` — Theorem \ref{IA:thm:323}(b): for all integers `ℓ, m ≥ 1`, all `t ∈ ℤ` and
  every infinite `B ⊆ ℕ`, `ℓB + mB + t ⊄ A_η`, where `ℓB + mB + t = {ℓ b + m b' + t : b, b' ∈ B}`
  is the unrestricted sumset (the diagonal `b = b'` is included).
* `finite_bad` — the "more precisely" statement of (b): for every `c`, only finitely many `b`
  satisfy `ℓ b + m c + t, ℓ c + m b + t, (ℓ + m) b + t ∈ A_η`.
* `thm323` — both parts together.
* `q323_negative` — the negative answer to Question \ref{IA:q:323} (stated as the `Prop`
  `Question323`, with the upper logarithmic density `udlog` and the unrestricted sumset
  `B + mB`), witnessed by `A_{1/12}`, simultaneously for all `m ≥ 2` and `t ≥ 0`.
* Auxiliary lemmas: `sumfree` (Lemma \ref{IA:lem:sumfree}), `block_sep` and `block_ge`
  (Lemma \ref{IA:lem:blocksep}), `abs_sum_mod_le` (Lemma \ref{IA:lem:perblock} in the case
  `J = 1`, `g ≡ 1`, which is the case used in the proof of (a)), `card_R`
  (`||R_k| - k(1/3 - 2η)| ≤ 1`).

## Conventions

* The paper's `ℕ` is `{1, 2, …}`. Here `A_η ⊆ ℕ` contains no `0` (every element is
  `≥ X_1 = 4`), while the sets `B` in (b) range over all subsets of `{0, 1, 2, …}`, which
  contains the paper's statement as a special case. Elements of `ℓB + mB + t` are integers;
  `InA η z` means that the integer `z` is (the image of) an element of `A_η`.
* Part (b) is proved for every `η > 0`; only part (a) uses `η < 1/6`.
* The proof of (a) follows the paper's decomposition into transition intervals and blocks, with
  cruder (but sufficient) error terms: the contribution of the `k`-th transition interval and
  block is at most `3 + 4k² + 2^k/k`, and `∑_{k ≤ K} 2^k/k ≤ 4 · 2^K / K`, while
  `log N ≥ 2^K log 2` for `N ≥ T_K`.

## Not covered

Remark \ref{IA:rem:323} (the construction of infinite `B` with `B ⊕ mB ⊆ A_η` for odd `m ≥ 3`,
and the open restricted question) is not formalized. Lemma \ref{IA:lem:perblock} is formalized
only for `J = 1` and `g ≡ 1`.
-/

open Real Filter Topology Finset

namespace Kmrr25.Q323

/-! ## The set `A_η` -/

/-- `T_k = 2^{2^k}`. -/
def T (k : ℕ) : ℕ := 2 ^ 2 ^ k

/-- `X_k = k T_k`. -/
def X (k : ℕ) : ℕ := k * T k

/-- `Y_k = T_{k+1} / k` (a real number). -/
noncomputable def Y (k : ℕ) : ℝ := (T (k + 1) : ℝ) / k

/-- `U_η = (1/3 + η, 2/3 - η)`. -/
def U (η : ℝ) : Set ℝ := Set.Ioo (1 / 3 + η) (2 / 3 - η)

open scoped Classical in
/-- `R_k = {s ∈ {0, …, k-1} : s / k ∈ U_η}`. -/
noncomputable def R (η : ℝ) (k : ℕ) : Finset ℕ := (range k).filter fun s => (s : ℝ) / k ∈ U η

/-- `A_η = ⋃_{k ≥ 1} {n : X_k ≤ n < Y_k, n mod k ∈ R_k}`. -/
def A (η : ℝ) : Set ℕ := {n | ∃ k, 1 ≤ k ∧ X k ≤ n ∧ (n : ℝ) < Y k ∧ n % k ∈ R η k}

/-- An integer belongs to `A_η`. -/
def InA (η : ℝ) (z : ℤ) : Prop := ∃ n ∈ A η, (n : ℤ) = z

/-- `ℓB + mB + t = {ℓ b + m b' + t : b, b' ∈ B}` (unrestricted: `b = b'` is allowed), as a set
of integers. -/
def linSumset (ℓ m : ℕ) (B : Set ℕ) (t : ℤ) : Set ℤ :=
  {x | ∃ b ∈ B, ∃ b' ∈ B, x = ℓ * b + m * b' + t}

/-! ## Blocks -/

lemma T_succ (k : ℕ) : T (k + 1) = T k ^ 2 := by
  unfold T; rw [pow_succ, pow_mul]

lemma T_pos (k : ℕ) : 0 < T k := by unfold T; positivity

lemma T_mono {k k' : ℕ} (h : k ≤ k') : T k ≤ T k' :=
  Nat.pow_le_pow_right two_pos (Nat.pow_le_pow_right two_pos h)

lemma lt_Y_iff {k n : ℕ} (hk : 1 ≤ k) : (n : ℝ) < Y k ↔ n * k < T k ^ 2 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Y, lt_div_iff₀ hk', T_succ]
  exact_mod_cast Iff.rfl

/-- `n` lies in the block of index `k`: `k ≥ 1` and `X_k ≤ n < Y_k`. -/
def InBlock (k n : ℕ) : Prop := 1 ≤ k ∧ X k ≤ n ∧ n * k < T k ^ 2

lemma mem_A_iff {η : ℝ} {n : ℕ} : n ∈ A η ↔ ∃ k, InBlock k n ∧ n % k ∈ R η k := by
  constructor
  · rintro ⟨k, hk, hX, hY, hR⟩
    exact ⟨k, ⟨hk, hX, (lt_Y_iff hk).1 hY⟩, hR⟩
  · rintro ⟨k, ⟨hk, hX, hY⟩, hR⟩
    exact ⟨k, hk, hX, (lt_Y_iff hk).2 hY, hR⟩

/-- Paper, Lemma \ref{IA:lem:blocksep}, first part (in the form `n k (k+1) < n'`). -/
lemma block_sep {k k' n n' : ℕ} (h : InBlock k n) (h' : InBlock k' n') (hkk : k < k') :
    n * k * (k + 1) < n' := by
  obtain ⟨-, -, h3⟩ := h
  obtain ⟨-, h2', -⟩ := h'
  have e1 : T k ^ 2 ≤ T k' := by rw [← T_succ]; exact T_mono hkk
  have e2 : n * k < T k' := lt_of_lt_of_le h3 e1
  have e3 : (k + 1) * T k' ≤ X k' := Nat.mul_le_mul_right _ hkk
  calc n * k * (k + 1) < T k' * (k + 1) := Nat.mul_lt_mul_of_pos_right e2 (Nat.succ_pos k)
    _ = (k + 1) * T k' := mul_comm _ _
    _ ≤ n' := e3.trans h2'

lemma block_unique {k k' n : ℕ} (h : InBlock k n) (h' : InBlock k' n) : k = k' := by
  have key : ∀ {a b : ℕ}, InBlock a n → InBlock b n → ¬ a < b := by
    intro a b ha hb hab
    have := block_sep ha hb hab
    have h1 : 1 ≤ a := ha.1
    have : n ≤ n * a * (a + 1) := by
      calc n = n * 1 * 1 := by ring
        _ ≤ n * a * (a + 1) := by gcongr; omega
    omega
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd hlt (key h h')
  · exact heq
  · exact absurd hgt (key h' h)

/-- Paper, Lemma \ref{IA:lem:blocksep}, second part. -/
lemma block_ge {k K n : ℕ} (h : InBlock k n) (hn : T (K + 1) ≤ n) : K + 1 ≤ k := by
  by_contra hcon
  obtain ⟨h1, -, h3⟩ := h
  have e1 : T k ^ 2 ≤ T (K + 1) := by rw [← T_succ]; exact T_mono (by omega)
  have : n ≤ n * k := Nat.le_mul_of_pos_right n h1
  omega

/-- Two elements of `A_η` whose ratio is at most `2C`, lying in blocks of index `> 2C`, lie in
the same block. -/
lemma same_block {x y kx ky C : ℕ} (hx : InBlock kx x) (hy : InBlock ky y) (hxy : y ≤ 2 * C * x)
    (hyx : x ≤ 2 * C * y) (hkx : 2 * C < kx) (hky : 2 * C < ky) : kx = ky := by
  have key : ∀ {a b ka kb : ℕ}, InBlock ka a → InBlock kb b → b ≤ 2 * C * a → 2 * C < ka →
      ¬ ka < kb := by
    intro a b ka kb ha hb hba hka hlt
    have h1 := block_sep ha hb hlt
    have h2 : a * (2 * C + 1) ≤ a * ka * (ka + 1) := by
      calc a * (2 * C + 1) ≤ a * ka := Nat.mul_le_mul_left _ hka
        _ = a * ka * 1 := by ring
        _ ≤ a * ka * (ka + 1) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  rcases lt_trichotomy kx ky with hlt | heq | hgt
  · exact absurd hlt (key hx hy hxy hkx)
  · exact heq
  · exact absurd hgt (key hy hx hyx hky)

/-- Paper, Lemma \ref{IA:lem:sumfree}: for `s₁, s₂, s₃ ∈ R_k` and `|s| < η k`,
`s₁ + s₂ - s₃ ≢ s (mod k)`. -/
lemma sumfree {η : ℝ} {k : ℕ} (hk : 1 ≤ k) {s₁ s₂ s₃ : ℕ} (h₁ : s₁ ∈ R η k)
    (h₂ : s₂ ∈ R η k) (h₃ : s₃ ∈ R η k) {s : ℤ} (hs : |(s : ℝ)| < η * k) :
    ¬ (k : ℤ) ∣ (s₁ + s₂ - s₃ - s : ℤ) := by
  rintro ⟨q, hq⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have bnd : ∀ {x : ℕ}, x ∈ R η k → k * (1 / 3 + η) < x ∧ (x : ℝ) < k * (2 / 3 - η) := by
    intro x hx
    simp only [R, mem_filter, U, Set.mem_Ioo] at hx
    obtain ⟨-, a, b⟩ := hx
    rw [lt_div_iff₀ hk'] at a
    rw [div_lt_iff₀ hk'] at b
    constructor <;> linarith
  obtain ⟨a1, b1⟩ := bnd h₁
  obtain ⟨a2, b2⟩ := bnd h₂
  obtain ⟨a3, b3⟩ := bnd h₃
  have hs1 := neg_abs_le (s : ℝ)
  have hs2 := le_abs_self (s : ℝ)
  have hq' : ((s₁ : ℝ) + s₂ - s₃ - s) = k * q := by exact_mod_cast hq
  have l1 : (0 : ℝ) < k * q := by rw [← hq']; nlinarith
  have l2 : (k : ℝ) * q < k * 1 := by rw [← hq']; nlinarith
  have q1 : (0 : ℝ) < q := pos_of_mul_pos_right l1 hk'.le
  have q2 : (q : ℝ) < 1 := lt_of_mul_lt_mul_left l2 hk'.le
  have : (0 : ℤ) < q := by exact_mod_cast q1
  have : q < (1 : ℤ) := by exact_mod_cast q2
  omega

/-! ## Theorem \ref{IA:thm:323}(b): no `ℓB + mB + t` -/

/-- Paper, Theorem \ref{IA:thm:323}(b), "more precisely" part, in a slightly stronger form: for
`η > 0`, integers `ℓ, m ≥ 1`, `t ∈ ℤ` and any `c ∈ ℕ`, only finitely many `b ∈ ℕ` satisfy
`ℓ b + m c + t, ℓ c + m b + t, (ℓ + m) b + t ∈ A_η`. -/
theorem finite_bad {η : ℝ} (hη : 0 < η) {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) (t : ℤ) (c : ℕ) :
    {b : ℕ | InA η (ℓ * b + m * c + t) ∧ InA η (ℓ * c + m * b + t) ∧
      InA η ((ℓ + m) * b + t)}.Finite := by
  set s : ℤ := (ℓ + m) * c + t with hs
  set C : ℕ := ℓ + m + 1 with hC
  set K : ℕ := ⌈|(s : ℝ)| / η⌉₊ + 2 * C with hK
  set b₀ : ℕ := 2 * (t.natAbs + (ℓ + m) * c) + 2 * T (K + 1) with hb₀
  refine (Set.finite_Iio b₀).subset fun b hb => ?_
  simp only [Set.mem_Iio]
  by_contra hlt
  push Not at hlt
  obtain ⟨⟨nu, hu, eu⟩, ⟨nv, hv, ev⟩, ⟨nw, hw, ew⟩⟩ := hb
  obtain ⟨ku, hku, ru⟩ := mem_A_iff.1 hu
  obtain ⟨kv, hkv, rv⟩ := mem_A_iff.1 hv
  obtain ⟨kw, hkw, rw'⟩ := mem_A_iff.1 hw
  -- size estimates: `b ≤ 2 n` and `n ≤ C b` for `n ∈ {u, v, w}`
  have hb' : (2 * (t.natAbs + (ℓ + m) * c) + 2 * T (K + 1) : ℤ) ≤ b := by exact_mod_cast hlt
  have hta : |t| = (t.natAbs : ℤ) := Int.abs_eq_natAbs t
  have ht1 := neg_abs_le t
  have ht2 := le_abs_self t
  have hbℓ : (b : ℤ) ≤ ℓ * b := by
    have : (1 : ℤ) ≤ ℓ := by exact_mod_cast hℓ
    nlinarith [(Nat.cast_nonneg b : (0 : ℤ) ≤ b)]
  have hbm : (b : ℤ) ≤ m * b := by
    have : (1 : ℤ) ≤ m := by exact_mod_cast hm
    nlinarith [(Nat.cast_nonneg b : (0 : ℤ) ≤ b)]
  have hmc : (0 : ℤ) ≤ m * c := by positivity
  have hℓc : (0 : ℤ) ≤ ℓ * c := by positivity
  have hlmc : ((ℓ : ℤ) + m) * c = ℓ * c + m * c := by ring
  have hTK : (0 : ℤ) ≤ T (K + 1) := by positivity
  push_cast at hb'
  have hCb : ((C * b : ℕ) : ℤ) = ℓ * b + m * b + b := by simp only [hC]; push_cast; ring
  have bnds : ∀ n : ℕ, (n : ℤ) = ℓ * b + m * c + t ∨ (n : ℤ) = ℓ * c + m * b + t ∨
      (n : ℤ) = ℓ * b + m * b + t → b ≤ 2 * n ∧ n ≤ C * b ∧ T (K + 1) ≤ n := by
    intro n hn
    have h1 : (b : ℤ) ≤ 2 * n ∧ (n : ℤ) ≤ ((C * b : ℕ) : ℤ) ∧ (T (K + 1) : ℤ) ≤ n := by
      rw [hCb]
      rcases hn with e | e | e <;> rw [e] <;>
        exact ⟨by linarith, by linarith, by linarith⟩
    exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2.1, by exact_mod_cast h1.2.2⟩
  obtain ⟨u1, u2, u3⟩ := bnds nu (Or.inl eu)
  obtain ⟨v1, v2, v3⟩ := bnds nv (Or.inr (Or.inl ev))
  obtain ⟨w1, w2, w3⟩ := bnds nw (Or.inr (Or.inr (by rw [ew]; ring)))
  -- the three blocks have index `> K`
  have gu := block_ge hku u3
  have gv := block_ge hkv v3
  have gw := block_ge hkw w3
  have ratio : ∀ {x y : ℕ}, b ≤ 2 * x → y ≤ C * b → y ≤ 2 * C * x := by
    intro x y h1 h2
    calc y ≤ C * b := h2
      _ ≤ C * (2 * x) := Nat.mul_le_mul_left _ h1
      _ = 2 * C * x := by ring
  have euv : ku = kv := same_block hku hkv (ratio u1 v2) (ratio v1 u2) (by omega) (by omega)
  have euw : ku = kw := same_block hku hkw (ratio u1 w2) (ratio w1 u2) (by omega) (by omega)
  subst euv euw
  -- `|s| < η k`
  have hsk : |(s : ℝ)| < η * ku := by
    have h1 : |(s : ℝ)| / η ≤ ⌈|(s : ℝ)| / η⌉₊ := Nat.le_ceil _
    have h2 : (⌈|(s : ℝ)| / η⌉₊ : ℝ) < ku := by exact_mod_cast (by omega : ⌈|(s : ℝ)| / η⌉₊ < ku)
    rw [div_le_iff₀ hη] at h1
    nlinarith
  apply sumfree hku.1 ru rv rw' hsk
  -- the residues satisfy `(u mod k) + (v mod k) - (w mod k) ≡ s`
  have duv : (nu : ℤ) + nv - nw = s := by
    rw [eu, ev, ew, hs]; ring
  refine ⟨-((nu / ku : ℕ) + (nv / ku : ℕ) - (nw / ku : ℕ) : ℤ), ?_⟩
  have m1 := Nat.mod_add_div nu ku
  have m2 := Nat.mod_add_div nv ku
  have m3 := Nat.mod_add_div nw ku
  have m1' : ((nu % ku : ℕ) : ℤ) + ku * (nu / ku : ℕ) = nu := by exact_mod_cast m1
  have m2' : ((nv % ku : ℕ) : ℤ) + ku * (nv / ku : ℕ) = nv := by exact_mod_cast m2
  have m3' : ((nw % ku : ℕ) : ℤ) + ku * (nw / ku : ℕ) = nw := by exact_mod_cast m3
  rw [← duv]
  linear_combination m1' + m2' - m3'

/-- Paper, Theorem \ref{IA:thm:323}(b). For `η > 0`, all integers `ℓ, m ≥ 1`, all `t ∈ ℤ` and
every infinite `B ⊆ ℕ`, the (unrestricted) sumset `ℓB + mB + t` is not contained in `A_η`. -/
theorem no_linSumset {η : ℝ} (hη : 0 < η) {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) (t : ℤ)
    {B : Set ℕ} (hB : B.Infinite) : ¬ linSumset ℓ m B t ⊆ InA η := by
  intro hsub
  obtain ⟨c, hc⟩ := hB.nonempty
  obtain ⟨b, hbB, hbF⟩ := (hB.sdiff (finite_bad hη hℓ hm t c)).nonempty
  apply hbF
  refine ⟨hsub ⟨b, hbB, c, hc, rfl⟩, hsub ⟨c, hc, b, hbB, rfl⟩, hsub ⟨b, hbB, b, hbB, ?_⟩⟩
  ring

/-! ## Theorem \ref{IA:thm:323}(a): logarithmic density -/

section LogDensity

/-- `A ⊆ ℕ` has logarithmic density `d`:
`(1 / log N) ∑_{n=1}^{N} 𝟙_A(n) / n → d` as `N → ∞`. -/
def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, A.indicator (fun n : ℕ => (1 : ℝ) / n) n) /
    Real.log N) atTop (𝓝 d)

/-! ### Harmonic sums -/

/-- `H(a, b) = Σ_{a ≤ n < b} 1/n`. -/
noncomputable def H (a b : ℕ) : ℝ := ∑ n ∈ Ico a b, (1 : ℝ) / n

lemma sum_Icc_eq_harmonic (N : ℕ) : ∑ n ∈ Icc 1 N, (1 : ℝ) / n = harmonic N := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp only [one_div]

/-- `H(a, b) ≤ 1 + log b - log a` for `1 ≤ a ≤ b`. -/
lemma H_le {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : H a b ≤ 1 + Real.log b - Real.log a := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have e : H (a' + 1) (b' + 1) = harmonic b' - harmonic a' := by
    rw [← sum_Icc_eq_harmonic, ← sum_Icc_eq_harmonic, H, ← Finset.Ico_add_one_right_eq_Icc,
      ← Finset.Ico_add_one_right_eq_Icc, ← sum_Ico_consecutive _ (by omega : 1 ≤ a' + 1)
      (by omega : a' + 1 ≤ b' + 1)]
    ring
  rw [e]
  have h1 := harmonic_le_one_add_log b'
  have h2 := log_add_one_le_harmonic a'
  have h3 : Real.log b' ≤ Real.log ((b' + 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos b' with h0 | h0
    · subst h0; simp
    · exact Real.log_le_log (by exact_mod_cast h0) (by push_cast; linarith)
  linarith

lemma H_mono {a b b' : ℕ} (hbb : b ≤ b') : H a b ≤ H a b' := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn; simp only [mem_Ico] at hn ⊢; omega
  · intro n _ _; positivity

/-! ### Sums of periodic sequences against `1/n` -/

/-- `k` consecutive integers run through all residues modulo `k`. -/
lemma sum_Ico_mod (φ : ℕ → ℝ) (k c : ℕ) :
    ∑ n ∈ Ico c (c + k), φ (n % k) = ∑ r ∈ range k, φ r := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  induction c with
  | zero =>
    rw [zero_add, ← range_eq_Ico]
    exact sum_congr rfl fun n hn => by rw [Nat.mod_eq_of_lt (mem_range.1 hn)]
  | succ c ih =>
    rw [← ih, sum_eq_sum_Ico_succ_bot (by omega : c < c + k),
      show c + 1 + k = c + k + 1 by ring, sum_Ico_succ_top (by omega : c + 1 ≤ c + k),
      Nat.add_mod_right]
    ring

variable {k : ℕ} {φ : ℕ → ℝ}

/-- One period: `|Σ_{c ≤ n < c+k} φ(n mod k)/n| ≤ k (1/c - 1/(c+k))` when the period sum of
`φ` vanishes and `|φ| ≤ 1`. -/
lemma abs_sum_period (hφ : ∀ r, |φ r| ≤ 1) (h0 : ∑ r ∈ range k, φ r = 0) {c : ℕ} (hc : 1 ≤ c) :
    |∑ n ∈ Ico c (c + k), φ (n % k) * (1 / n)| ≤ k * (1 / c - 1 / (c + k)) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have e : ∑ n ∈ Ico c (c + k), φ (n % k) * (1 / n) =
      ∑ n ∈ Ico c (c + k), φ (n % k) * (1 / n - 1 / c) := by
    have : ∑ n ∈ Ico c (c + k), φ (n % k) * (1 / c) = 0 := by
      rw [← sum_mul, sum_Ico_mod, h0, zero_mul]
    rw [← sub_zero (∑ n ∈ Ico c (c + k), φ (n % k) * (1 / n)), ← this, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [e]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ n ∈ Ico c (c + k), |φ (n % k) * (1 / n - 1 / c)| ≤ 1 / c - 1 / (c + k) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Ico.1 hn
    have h1' : (c : ℝ) ≤ n := by exact_mod_cast h1
    have h2' : (n : ℝ) < c + k := by exact_mod_cast h2
    have hn0 : (0 : ℝ) < n := by linarith
    rw [abs_mul]
    have i1 : 1 / (n : ℝ) ≤ 1 / c := one_div_le_one_div_of_le hc' h1'
    have i2 : 1 / ((c : ℝ) + k) < 1 / n := one_div_lt_one_div_of_lt hn0 h2'
    have : |1 / (n : ℝ) - 1 / c| = 1 / c - 1 / n := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [this]
    have := hφ (n % k)
    nlinarith [abs_nonneg (φ (n % k))]
  refine (sum_le_card_nsmul _ _ _ hb).trans ?_
  rw [Nat.card_Ico, nsmul_eq_mul, show c + k - c = k by omega]

/-- `q` periods, by telescoping. -/
lemma abs_sum_periods (hφ : ∀ r, |φ r| ≤ 1) (h0 : ∑ r ∈ range k, φ r = 0) (q : ℕ) :
    ∀ c : ℕ, 1 ≤ c →
      |∑ n ∈ Ico c (c + q * k), φ (n % k) * (1 / n)| ≤ k * (1 / c - 1 / (c + q * k)) := by
  induction q with
  | zero => intro c _; simp
  | succ q ih =>
    intro c hc
    have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    rw [← sum_Ico_consecutive _ (by omega : c ≤ c + k) (by nlinarith : c + k ≤ c + (q + 1) * k),
      show c + (q + 1) * k = c + k + q * k by ring]
    refine (abs_add_le _ _).trans ?_
    have e1 := abs_sum_period hφ h0 hc
    have e2 := ih (c + k) (by omega)
    push_cast at e1 e2 ⊢
    have : (k : ℝ) * (1 / c - 1 / (c + k)) + k * (1 / (c + k) - 1 / (c + k + q * k)) =
        k * (1 / c - 1 / (c + k + q * k)) := by ring
    rw [show (c : ℝ) + ((q : ℝ) + 1) * k = c + k + q * k by ring]
    linarith

/-- Paper, Lemma \ref{IA:lem:perblock} (for `g ≡ 1`, `J = 1`), in the form: if the period sum of
`φ` vanishes and `|φ| ≤ 1`, then `|Σ_{c ≤ n < d} φ(n mod k)/n| ≤ 2k/c`. -/
lemma abs_sum_mod_le (hk : 1 ≤ k) (hφ : ∀ r, |φ r| ≤ 1) (h0 : ∑ r ∈ range k, φ r = 0)
    {c d : ℕ} (hc : 1 ≤ c) (hcd : c ≤ d) :
    |∑ n ∈ Ico c d, φ (n % k) * (1 / n)| ≤ 2 * k / c := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  set q := (d - c) / k with hq
  have hqk : q * k ≤ d - c := Nat.div_mul_le_self _ _
  have hrem : d - (c + q * k) < k := by
    have := Nat.lt_div_mul_add (a := d - c) (by omega : 0 < k)
    rw [← hq] at this
    omega
  rw [← sum_Ico_consecutive _ (by omega : c ≤ c + q * k) (by omega : c + q * k ≤ d)]
  refine (abs_add_le _ _).trans ?_
  have e1 := abs_sum_periods hφ h0 q c hc
  have e1' : (k : ℝ) * (1 / c - 1 / ((c : ℝ) + ((q * k : ℕ) : ℝ))) ≤ k / c := by
    have : (0 : ℝ) ≤ 1 / ((c : ℝ) + ((q * k : ℕ) : ℝ)) := by positivity
    rw [mul_sub, mul_one_div]
    linarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) this]
  have e2 : |∑ n ∈ Ico (c + q * k) d, φ (n % k) * (1 / n)| ≤ k / c := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ n ∈ Ico (c + q * k) d, |φ (n % k) * (1 / n)| ≤ 1 / c := by
      intro n hn
      have h1' : (c : ℝ) ≤ n := by exact_mod_cast (show c ≤ n by simp only [mem_Ico] at hn; omega)
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / n)]
      have i1 : 1 / (n : ℝ) ≤ 1 / c := one_div_le_one_div_of_le hc' h1'
      have := hφ (n % k)
      nlinarith [abs_nonneg (φ (n % k)), (by positivity : (0 : ℝ) ≤ 1 / n)]
    refine (sum_le_card_nsmul _ _ _ hb).trans ?_
    rw [Nat.card_Ico, nsmul_eq_mul, mul_one_div]
    gcongr
  have : (2 : ℝ) * k / c = k / c + k / c := by ring
  push_cast at e1 e1'
  linarith

/-! ### The density of `R_k` -/

variable {η : ℝ}

/-- `|R_k| = k (1/3 - 2η) + O(1)`: precisely `||R_k| - k (1/3 - 2η)| ≤ 1`. -/
lemma card_R (hη0 : 0 < η) (hη1 : η < 1 / 6) (hk : 1 ≤ k) :
    |((R η k).card : ℝ) - k * (1 / 3 - 2 * η)| ≤ 1 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set α : ℝ := k * (1 / 3 + η) with hα
  set β : ℝ := k * (2 / 3 - η) with hβ
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := mul_nonneg hk'.le (by linarith)
  have hβk : β < k := by nlinarith
  have hαβ : α < β := by nlinarith
  have key : R η k = Ioo ⌊α⌋₊ ⌈β⌉₊ := by
    ext s
    simp only [R, mem_filter, mem_range, U, Set.mem_Ioo, mem_Ioo]
    rw [lt_div_iff₀ hk', div_lt_iff₀ hk', Nat.floor_lt hα0, Nat.lt_ceil]
    constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, by linarith, by linarith⟩
      exact_mod_cast (show (s : ℝ) < k by linarith)
  rw [key, Nat.card_Ioo]
  have f1 := Nat.floor_le hα0
  have f2 := Nat.lt_floor_add_one α
  have c1 := Nat.le_ceil β
  have c2 := Nat.ceil_lt_add_one hβ0
  have hlt : ⌊α⌋₊ < ⌈β⌉₊ := by exact_mod_cast (show (⌊α⌋₊ : ℝ) < ⌈β⌉₊ by linarith)
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  have e : (k : ℝ) * (1 / 3 - 2 * η) = β - α := by rw [hα, hβ]; ring
  rw [e, abs_le]
  constructor <;> linarith

/-! ### Block and gap estimates -/

/-- `μ = |U_η| = 1/3 - 2η`. -/
noncomputable def μ (η : ℝ) : ℝ := 1 / 3 - 2 * η

/-- The summand `(𝟙_{A_η}(n) - μ)/n`. -/
noncomputable def dd (η : ℝ) (n : ℕ) : ℝ :=
  (A η).indicator (fun n : ℕ => (1 : ℝ) / n) n - μ η * (1 / n)

/-- `⌈Y_k⌉`: the integers of the block `k` are those `n` with `X_k ≤ n < ⌈Y_k⌉`. -/
noncomputable def Yn (k : ℕ) : ℕ := ⌈Y k⌉₊

lemma abs_dd_le (hη0 : 0 < η) (hη1 : η < 1 / 6) (n : ℕ) : |dd η n| ≤ 1 / n := by
  have hx : (0 : ℝ) ≤ 1 / n := by positivity
  have hμ0 : 0 < μ η := by unfold μ; linarith
  have hμ1 : μ η < 1 := by unfold μ; linarith
  unfold dd
  by_cases hn : n ∈ A η
  · rw [Set.indicator_of_mem hn, abs_le]
    constructor <;> nlinarith
  · rw [Set.indicator_of_notMem hn, abs_le]
    constructor <;> nlinarith

lemma T_ge_two (k : ℕ) : 2 ≤ T k := by
  unfold T
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ 2 ^ k := Nat.pow_le_pow_right two_pos Nat.one_le_two_pow

lemma log_T (k : ℕ) : Real.log (T k) = 2 ^ k * Real.log 2 := by
  unfold T
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

lemma Y_pos {k : ℕ} (hk : 1 ≤ k) : 0 < Y k := by
  unfold Y
  have : (0 : ℝ) < T (k + 1) := by exact_mod_cast T_pos _
  have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- Paper's estimate on a block: for `X_k ≤ b ≤ ⌈Y_k⌉`,
`|Σ_{X_k ≤ n < b} (𝟙_{A_η}(n) - μ)/n| ≤ 2k/X_k + H(X_k, b)/k`. -/
lemma block_sum (hη0 : 0 < η) (hη1 : η < 1 / 6) (hk : 1 ≤ k) {b : ℕ} (hb : b ≤ Yn k) :
    |∑ n ∈ Ico (X k) b, dd η n| ≤ 2 * k / X k + H (X k) b / k := by
  classical
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set ρ : ℝ := (R η k).card / k with hρ
  set φ : ℕ → ℝ := fun r => (if r ∈ R η k then 1 else 0) - ρ with hφ
  have hRk : (R η k).card ≤ k := by
    unfold R; exact (card_filter_le _ _).trans (card_range k).le
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one hk']; exact_mod_cast hRk
  have hφ1 : ∀ r, |φ r| ≤ 1 := by
    intro r
    simp only [hφ]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hφ0 : ∑ r ∈ range k, φ r = 0 := by
    simp only [hφ]
    rw [sum_sub_distrib, sum_boole, sum_const, card_range, nsmul_eq_mul, hρ,
      filter_mem_eq_inter, inter_eq_right.2 (by unfold R; exact filter_subset _ _)]
    field_simp
    ring
  -- on the block, `dd η n = φ(n mod k)/n + (ρ - μ)/n`
  have hdd : ∀ n ∈ Ico (X k) b, dd η n = φ (n % k) * (1 / n) + (ρ - μ η) * (1 / n) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Ico.1 hn
    have hblk : InBlock k n := by
      refine ⟨hk, h1, (lt_Y_iff hk).1 ?_⟩
      exact Nat.lt_ceil.1 (lt_of_lt_of_le h2 hb)
    have hmem : n ∈ A η ↔ n % k ∈ R η k := by
      rw [mem_A_iff]
      constructor
      · rintro ⟨j, hj, hR⟩
        rwa [block_unique hblk hj]
      · exact fun h => ⟨k, hblk, h⟩
    unfold dd
    simp only [hφ]
    by_cases hR : n % k ∈ R η k
    · rw [Set.indicator_of_mem (hmem.2 hR), if_pos hR]; ring
    · rw [Set.indicator_of_notMem (fun h => hR (hmem.1 h)), if_neg hR]; ring
  rw [sum_congr rfl hdd, sum_add_distrib, ← mul_sum]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rcases le_or_gt (X k) b with hXb | hXb
    · exact abs_sum_mod_le hk hφ1 hφ0 (by unfold X; nlinarith [T_pos k]) hXb
    · rw [Ico_eq_empty (by omega), sum_empty, abs_zero]; positivity
  · rw [abs_mul, abs_of_nonneg (sum_nonneg fun n _ => by positivity :
      (0 : ℝ) ≤ ∑ n ∈ Ico (X k) b, (1 : ℝ) / n), ← H, div_eq_mul_inv,
      mul_comm (H (X k) b)]
    refine mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun n _ => by positivity)
    have hc := card_R hη0 hη1 hk
    have e : ρ - μ η = (((R η k).card : ℝ) - k * (1 / 3 - 2 * η)) / k := by
      rw [hρ, μ]; field_simp
    rw [e, abs_div, abs_of_pos hk', ← one_div]
    exact div_le_div_of_nonneg_right hc hk'.le

/-- The per-index bound `c_k = 3 + 4k² + 2^k/k`. -/
noncomputable def cb (k : ℕ) : ℝ := 3 + 4 * (k : ℝ) ^ 2 + 2 ^ k / k

lemma cb_nonneg (k : ℕ) : 0 ≤ cb k := by unfold cb; positivity

/-- One gap followed by (part of) one block: if `1 ≤ g ≤ X_k ≤ 4k²g` and `g ≤ b ≤ ⌈Y_k⌉`, then
`|Σ_{g ≤ n < b} (𝟙_{A_η}(n) - μ)/n| ≤ c_k`. -/
lemma piece (hη0 : 0 < η) (hη1 : η < 1 / 6) (hk : 1 ≤ k) {g b : ℕ} (hg : 1 ≤ g)
    (hgX : g ≤ X k) (hXg : X k ≤ 4 * k ^ 2 * g) (hgb : g ≤ b) (hbY : b ≤ Yn k) :
    |∑ n ∈ Ico g b, dd η n| ≤ cb k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hT2 : (2 : ℝ) ≤ T k := by exact_mod_cast T_ge_two k
  have hX : (X k : ℝ) = k * T k := by unfold X; push_cast; ring
  have hXpos : (0 : ℝ) < X k := by rw [hX]; positivity
  rw [← sum_Ico_consecutive _ (le_min hgb hgX : g ≤ min b (X k)) (min_le_left b (X k))]
  refine (abs_add_le _ _).trans ?_
  -- the gap
  have gap : |∑ n ∈ Ico g (min b (X k)), dd η n| ≤ 4 * (k : ℝ) ^ 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum fun n _ => abs_dd_le hη0 hη1 n).trans ?_
    refine (H_mono (min_le_right b (X k))).trans ?_
    refine (H_le hg hgX).trans ?_
    have h1 : Real.log (X k) ≤ Real.log (4 * k ^ 2) + Real.log g := by
      rw [← Real.log_mul (by positivity) hg'.ne']
      exact Real.log_le_log hXpos (by exact_mod_cast hXg)
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 * k ^ 2 by positivity)
    linarith
  -- the block
  have blk : |∑ n ∈ Ico (min b (X k)) b, dd η n| ≤ 3 + 2 ^ k / k := by
    rcases le_or_gt b (X k) with hbX | hbX
    · rw [min_eq_left hbX, Ico_self, sum_empty, abs_zero]; positivity
    rw [min_eq_right hbX.le]
    refine (block_sum hη0 hη1 hk hbY).trans ?_
    have e1 : 2 * (k : ℝ) / X k ≤ 1 := by
      rw [hX, div_le_one (by positivity)]; nlinarith
    have hb1 : 1 ≤ b := by unfold X at hbX; nlinarith [T_pos k]
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb1
    have e2 : H (X k) b ≤ 2 + 2 ^ k := by
      refine (H_le (by unfold X; nlinarith [T_pos k]) hbX.le).trans ?_
      have hbT : (b : ℝ) ≤ 2 * T k * X k := by
        have i1 : (b : ℝ) ≤ Yn k := by exact_mod_cast hbY
        have i2 : (Yn k : ℝ) < Y k + 1 := Nat.ceil_lt_add_one (Y_pos hk).le
        have i3 : Y k ≤ (T k : ℝ) ^ 2 := by
          unfold Y; rw [T_succ]; push_cast
          exact div_le_self (by positivity) (by exact_mod_cast hk)
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have hkT : (T k : ℝ) ^ 2 ≤ k * (T k) ^ 2 := le_mul_of_one_le_left (by positivity) hk1
        have hT4 : (1 : ℝ) ≤ (T k) ^ 2 := by nlinarith
        rw [hX]; nlinarith
      have h1 : Real.log b ≤ Real.log 2 + Real.log (T k) + Real.log (X k) := by
        rw [← Real.log_mul (by norm_num) (by positivity), ← Real.log_mul (by positivity)
          hXpos.ne']
        exact Real.log_le_log hb' hbT
      have hl2 := Real.log_two_lt_d9
      rw [log_T] at h1
      have : (2 : ℝ) ^ k * Real.log 2 ≤ 2 ^ k := by
        have : (0 : ℝ) < 2 ^ k := by positivity
        nlinarith
      linarith
    have e3 : H (X k) b / k ≤ 2 + 2 ^ k / k := by
      rw [div_le_iff₀ hk', add_mul, div_mul_cancel₀ _ hk'.ne']
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    linarith
  unfold cb
  linarith

lemma Yn_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ Yn k := Nat.one_le_iff_ne_zero.2 (by
  unfold Yn; exact (Nat.ceil_pos.2 (Y_pos hk)).ne')

lemma Yn_le_X {K : ℕ} (hK : 1 ≤ K) : Yn K ≤ X (K + 1) := by
  unfold Yn
  rw [Nat.ceil_le, Y, div_le_iff₀ (by exact_mod_cast hK)]
  unfold X
  push_cast
  have hT : (0 : ℝ) ≤ T (K + 1) := by positivity
  have : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : (1 : ℝ) ≤ (K + 1) * K := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hT]

lemma X_le_Yn {K : ℕ} (hK : 1 ≤ K) : X (K + 1) ≤ 4 * (K + 1) ^ 2 * Yn K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 : (X (K + 1) : ℝ) = (K + 1) * K * Y K := by
    unfold X Y; push_cast; field_simp
  have h2 : Y K ≤ Yn K := Nat.le_ceil _
  have h3 := Y_pos hK
  have : (X (K + 1) : ℝ) ≤ 4 * (K + 1) ^ 2 * Yn K := by
    rw [h1]; nlinarith
  exact_mod_cast this

/-- `|Σ_{1 ≤ n < M} (𝟙_{A_η}(n) - μ)/n| ≤ Σ_{k=1}^{K} c_k` for `1 ≤ M ≤ ⌈Y_K⌉`. -/
lemma E_bound (hη0 : 0 < η) (hη1 : η < 1 / 6) {K : ℕ} (hK : 1 ≤ K) :
    ∀ M, 1 ≤ M → M ≤ Yn K → |∑ n ∈ Ico 1 M, dd η n| ≤ ∑ k ∈ Icc 1 K, cb k := by
  induction K, hK using Nat.le_induction with
  | base =>
    intro M hM hMY
    rw [Icc_self, sum_singleton]
    exact piece hη0 hη1 le_rfl le_rfl (by unfold X T; norm_num) (by unfold X T; norm_num) hM hMY
  | succ K hK ih =>
    intro M hM hMY
    rw [sum_Icc_succ_top (by omega)]
    rcases le_or_gt M (Yn K) with h | h
    · linarith [ih M hM h, cb_nonneg (K + 1)]
    · rw [← sum_Ico_consecutive _ (Yn_pos hK) h.le]
      refine (abs_add_le _ _).trans (add_le_add (ih _ (Yn_pos hK) le_rfl) ?_)
      exact piece hη0 hη1 (by omega) (Yn_pos hK) (Yn_le_X hK) (X_le_Yn hK) h.le hMY

/-- `Σ_{k=1}^{K} 2^k/k ≤ 4 · 2^K / K`. -/
lemma sum_pow_div_le {K : ℕ} (hK : 1 ≤ K) :
    ∑ k ∈ Icc 1 K, (2 : ℝ) ^ k / k ≤ 4 * 2 ^ K / K := by
  rcases Nat.lt_or_ge K 2 with h | h
  · obtain rfl : K = 1 := by omega
    norm_num
  clear hK
  induction K, h using Nat.le_induction with
  | base => norm_num [sum_Icc_succ_top]
  | succ K hK ih =>
    rw [sum_Icc_succ_top (by omega)]
    have ih' := ih
    have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
    have hx : (0 : ℝ) < 2 ^ K := by positivity
    have : (4 : ℝ) * 2 ^ K / K + 2 ^ (K + 1) / ((K + 1 : ℕ) : ℝ) ≤
        4 * 2 ^ (K + 1) / ((K + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity), pow_succ]
      nlinarith [mul_pos hx (show (0 : ℝ) < K by positivity)]
    linarith

/-- `Σ_{k=1}^{K} c_k ≤ 3K + 4K³ + 4·2^K/K`. -/
lemma sum_cb_le {K : ℕ} (hK : 1 ≤ K) :
    ∑ k ∈ Icc 1 K, cb k ≤ 3 * K + 4 * (K : ℝ) ^ 3 + 4 * 2 ^ K / K := by
  unfold cb
  rw [sum_add_distrib, sum_add_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul]
  have h1 : ∑ k ∈ Icc 1 K, 4 * (k : ℝ) ^ 2 ≤ 4 * (K : ℝ) ^ 3 := by
    have hb : ∀ k ∈ Icc 1 K, 4 * (k : ℝ) ^ 2 ≤ 4 * (K : ℝ) ^ 2 := by
      intro k hk
      have : (k : ℝ) ≤ K := by exact_mod_cast (mem_Icc.1 hk).2
      have : (0 : ℝ) ≤ k := by positivity
      nlinarith
    refine (sum_le_card_nsmul _ _ _ hb).trans (le_of_eq ?_)
    rw [Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  have h2 := sum_pow_div_le hK
  push_cast [show K + 1 - 1 = K by omega]
  linarith

/-- The level `K(N) = ⌊log₂ ⌊log₂ N⌋⌋`, so that `T_{K} ≤ N < T_{K+1}` for `N ≥ 2`. -/
def lev (N : ℕ) : ℕ := Nat.log 2 (Nat.log 2 N)

lemma T_lev_le {N : ℕ} (hN : 2 ≤ N) : T (lev N) ≤ N := by
  have h1 : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le one_lt_two (by simpa using hN)
  unfold T lev
  calc 2 ^ 2 ^ Nat.log 2 (Nat.log 2 N) ≤ 2 ^ Nat.log 2 N :=
        Nat.pow_le_pow_right two_pos (Nat.pow_log_le_self 2 (by omega))
    _ ≤ N := Nat.pow_log_le_self 2 (by omega)

lemma lt_T_lev (N : ℕ) : N < T (lev N + 1) := by
  have h1 := Nat.lt_pow_succ_log_self one_lt_two N
  have h2 := Nat.lt_pow_succ_log_self one_lt_two (Nat.log 2 N)
  unfold T lev
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right two_pos h2)

lemma tendsto_lev : Tendsto lev atTop atTop := by
  refine tendsto_atTop.2 fun m => eventually_atTop.2 ⟨2 ^ 2 ^ m, fun N hN => ?_⟩
  exact Nat.le_log_of_pow_le one_lt_two (Nat.le_log_of_pow_le one_lt_two hN)

lemma succ_le_T (k : ℕ) : k + 1 ≤ T k := by
  unfold T
  have h1 := Nat.lt_two_pow_self (n := k)
  have h2 := Nat.lt_two_pow_self (n := 2 ^ k)
  omega

lemma T_le_Yn (K : ℕ) : T (K + 1) ≤ Yn (K + 1) := by
  have h : (T (K + 1) : ℝ) ≤ Y (K + 1) := by
    unfold Y
    rw [le_div_iff₀ (by positivity), T_succ (K + 1)]
    push_cast
    have : ((K + 1 : ℕ) : ℝ) ≤ T (K + 1) := by
      exact_mod_cast (by have := succ_le_T (K + 1); omega : K + 1 ≤ T (K + 1))
    push_cast at this
    have : (0 : ℝ) ≤ T (K + 1) := by positivity
    nlinarith
  exact_mod_cast h.trans (Nat.le_ceil _)

/-- The error bound `φ(K) = (14 (K+1)³ / 2^{K+1} + 8/(K+1)) / log 2`. -/
noncomputable def errB (K : ℕ) : ℝ :=
  (14 * ((K + 1 : ℕ) : ℝ) ^ 3 / 2 ^ (K + 1) + 8 / ((K + 1 : ℕ) : ℝ)) / Real.log 2

lemma tendsto_errB : Tendsto errB atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 3 one_lt_two
  have h2 : Tendsto (fun n : ℕ => 8 / (n : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ))
  have h3 : Tendsto (fun n : ℕ => (14 * (n : ℝ) ^ 3 / 2 ^ n + 8 / (n : ℝ)) / Real.log 2) atTop
      (𝓝 0) := by
    have := ((h1.const_mul 14).add h2).div_const (Real.log 2)
    simpa [mul_div_assoc] using this
  exact (tendsto_add_atTop_iff_nat 1).2 h3

/-- The main estimate: `|Σ_{n ≤ N} (𝟙_{A_η}(n) - μ)/n| / log N ≤ φ(K(N))` for `N ≥ 16`. -/
lemma E_div_log_le (hη0 : 0 < η) (hη1 : η < 1 / 6) {N : ℕ} (hN : 1 ≤ lev N) (hN2 : 2 ≤ N) :
    |∑ n ∈ Ico 1 (N + 1), dd η n| / Real.log N ≤ errB (lev N) := by
  set K := lev N with hKdef
  have hTN := T_lev_le hN2
  have hlog : (2 : ℝ) ^ K * Real.log 2 ≤ Real.log N := by
    rw [← log_T]
    exact Real.log_le_log (by exact_mod_cast T_pos K) (by exact_mod_cast hTN)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpos : 0 < (2 : ℝ) ^ K * Real.log 2 := by positivity
  have hE := E_bound hη0 hη1 (K := K + 1) (by omega) (N + 1) (by omega)
    ((lt_T_lev N).trans_le (T_le_Yn K))
  have hF := sum_cb_le (K := K + 1) (by omega)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hN
  -- `F(K+1) ≤ 7 (K+1)³ + 8 · 2^K / (K+1)`
  have hF' : 3 * ((K + 1 : ℕ) : ℝ) + 4 * ((K + 1 : ℕ) : ℝ) ^ 3 +
      4 * 2 ^ (K + 1) / ((K + 1 : ℕ) : ℝ) ≤
      7 * ((K + 1 : ℕ) : ℝ) ^ 3 + 8 * 2 ^ K / ((K + 1 : ℕ) : ℝ) := by
    push_cast
    have hK2 : (1 : ℝ) ≤ (K + 1) ^ 2 := by nlinarith
    have : (K + 1 : ℝ) ≤ (K + 1) ^ 3 := by
      have := mul_le_mul_of_nonneg_left hK2 (by positivity : (0 : ℝ) ≤ K + 1)
      nlinarith
    have : 4 * (2 : ℝ) ^ (K + 1) / (K + 1) = 8 * 2 ^ K / (K + 1) := by ring
    linarith
  have hEF : |∑ n ∈ Ico 1 (N + 1), dd η n| ≤
      7 * ((K + 1 : ℕ) : ℝ) ^ 3 + 8 * 2 ^ K / ((K + 1 : ℕ) : ℝ) := by linarith
  have hnum : 0 ≤ 7 * ((K + 1 : ℕ) : ℝ) ^ 3 + 8 * 2 ^ K / ((K + 1 : ℕ) : ℝ) := by positivity
  calc |∑ n ∈ Ico 1 (N + 1), dd η n| / Real.log N
      ≤ (7 * ((K + 1 : ℕ) : ℝ) ^ 3 + 8 * 2 ^ K / ((K + 1 : ℕ) : ℝ)) / Real.log N :=
        div_le_div_of_nonneg_right hEF (hpos.le.trans hlog)
    _ ≤ (7 * ((K + 1 : ℕ) : ℝ) ^ 3 + 8 * 2 ^ K / ((K + 1 : ℕ) : ℝ)) /
        (2 ^ K * Real.log 2) := div_le_div_of_nonneg_left hnum hpos hlog
    _ = errB K := by
        unfold errB
        rw [pow_succ]
        field_simp
        ring

/-- Paper, Theorem \ref{IA:thm:323}(a). For `0 < η < 1/6`, the logarithmic density of `A_η`
exists and equals `1/3 - 2η`. -/
theorem logDensity_A (hη0 : 0 < η) (hη1 : η < 1 / 6) : HasLogDensity (A η) (1 / 3 - 2 * η) := by
  -- decomposition `Σ 𝟙_A(n)/n = Σ dd η n + μ H_N`
  have hdec : ∀ N : ℕ, ∑ n ∈ Icc 1 N, (A η).indicator (fun n : ℕ => (1 : ℝ) / n) n =
      ∑ n ∈ Ico 1 (N + 1), dd η n + μ η * harmonic N := by
    intro N
    rw [← sum_Icc_eq_harmonic, mul_sum, Finset.Ico_add_one_right_eq_Icc, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by unfold dd; ring
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- the error term
  have hE : Tendsto (fun N : ℕ => (∑ n ∈ Ico 1 (N + 1), dd η n) / Real.log N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_errB.comp tendsto_lev)
    filter_upwards [tendsto_lev.eventually (eventually_ge_atTop 1), eventually_ge_atTop 2]
      with N hN hN2
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hl]
    exact E_div_log_le hη0 hη1 hN hN2
  -- the harmonic term
  have hH : Tendsto (fun N : ℕ => (harmonic N : ℝ) / Real.log N) atTop (𝓝 1) := by
    have hup : Tendsto (fun N : ℕ => 1 + 1 / Real.log N) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (hlogN.inv_tendsto_atTop.congr fun N => by simp)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      rw [le_div_iff₀ hl, one_mul]
      have := log_add_one_le_harmonic N
      have : Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by push_cast; linarith)
      linarith
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      rw [div_le_iff₀ hl, add_mul, one_mul, one_div, inv_mul_cancel₀ hl.ne']
      have := harmonic_le_one_add_log N
      linarith
  have hlim := hE.add (hH.const_mul (μ η))
  rw [zero_add, mul_one] at hlim
  unfold HasLogDensity
  rw [show (1 / 3 - 2 * η : ℝ) = μ η from rfl]
  refine hlim.congr fun N => ?_
  rw [hdec N, add_div, mul_div_assoc]

end LogDensity

/-! ## Theorem \ref{IA:thm:323} and Question \ref{IA:q:323} -/

/-- Paper, Theorem \ref{IA:thm:323}, both parts, for `0 < η < 1/6`:
(a) `A_η` has logarithmic density `1/3 - 2η`;
(b) for all integers `ℓ, m ≥ 1`, `t ∈ ℤ` and infinite `B ⊆ ℕ`, `ℓB + mB + t ⊄ A_η`; more
precisely, for every `c ∈ B` only finitely many `b ∈ B` satisfy
`ℓ b + m c + t, ℓ c + m b + t, (ℓ + m) b + t ∈ A_η`. -/
theorem thm323 {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 6) :
    HasLogDensity (A η) (1 / 3 - 2 * η) ∧
    (∀ ℓ m : ℕ, 1 ≤ ℓ → 1 ≤ m → ∀ t : ℤ, ∀ B : Set ℕ, B.Infinite →
      ¬ linSumset ℓ m B t ⊆ InA η) ∧
    (∀ ℓ m : ℕ, 1 ≤ ℓ → 1 ≤ m → ∀ t : ℤ, ∀ B : Set ℕ, ∀ c ∈ B,
      {b ∈ B | InA η (ℓ * b + m * c + t) ∧ InA η (ℓ * c + m * b + t) ∧
        InA η ((ℓ + m) * b + t)}.Finite) :=
  ⟨logDensity_A hη0 hη1, fun _ _ hℓ hm t _ hB => no_linSumset hη0 hℓ hm t hB,
    fun _ _ hℓ hm t _ c _ => (finite_bad hη0 hℓ hm t c).subset fun _ hb => hb.2⟩

/-- The upper logarithmic density
`limsup_{N → ∞} (1 / log N) ∑_{n=1}^{N} 𝟙_S(n) / n` (the sequence is bounded, so this is the
usual `limsup`). -/
noncomputable def udlog (S : Set ℕ) : ℝ :=
  limsup (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, S.indicator (fun n : ℕ => (1 : ℝ) / n) n) /
    Real.log N) atTop

/-- Question 3.23 of the survey (Question \ref{IA:q:323}), with the unrestricted sumset
`B + mB = {b + m b' : b, b' ∈ B}`: does every `A ⊆ ℕ = {1, 2, …}` with `d̄_log(A) > 0` contain
`B + mB + t` for some `m ≥ 2`, `t ≥ 0` and some infinite `B ⊆ ℕ`? -/
def Question323 : Prop :=
  ∀ A : Set ℕ, 0 ∉ A → 0 < udlog A → ∃ m : ℕ, 2 ≤ m ∧ ∃ t : ℕ, ∃ B : Set ℕ, B.Infinite ∧
    (∀ b ∈ B, 0 < b) ∧ {x | ∃ b ∈ B, ∃ b' ∈ B, x = b + m * b' + t} ⊆ A

/-- Paper, Theorem \ref{IA:thm:323}, "in particular": the answer to Question \ref{IA:q:323} is
negative; `A_{1/12}` (logarithmic density `1/6`) is a counterexample, simultaneously for all
`m`. -/
theorem q323_negative : ¬ Question323 := by
  intro hQ
  have hη0 : (0 : ℝ) < 1 / 12 := by norm_num
  have hη1 : (1 / 12 : ℝ) < 1 / 6 := by norm_num
  have h0 : (0 : ℕ) ∉ A (1 / 12) := by
    rintro ⟨k, hk, hX, -⟩
    have : 1 ≤ X k := by unfold X; nlinarith [T_pos k]
    omega
  have hd : 0 < udlog (A (1 / 12)) := by
    rw [udlog, (logDensity_A hη0 hη1).limsup_eq]
    norm_num
  obtain ⟨m, hm, t, B, hB, -, hsub⟩ := hQ _ h0 hd
  apply no_linSumset hη0 le_rfl (by omega : 1 ≤ m) (t : ℤ) hB
  rintro _ ⟨b, hb, b', hb', rfl⟩
  exact ⟨b + m * b' + t, hsub ⟨b, hb, b', hb', rfl⟩, by push_cast; ring⟩

end Kmrr25.Q323
