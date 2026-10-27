import Kmrr25.Basic

/-!
# Generalisations of Question 3.18 (Question §3.3(e))

Paper, Section \ref{IA:sec:u33e}: Proposition \ref{IA:prop:u33e} and the remark following it.

Question 3.18 of the survey asks whether every `A ⊆ ℕ` of positive upper Banach density contains
`{b_i b_j + b_k : i < j < k} + t` for some infinite `B = {b₁ < b₂ < ⋯}` and `t ≥ 0`. Its faithful
analogues are (F1) (adding the base point: `{b_k, b_i b_j + b_k : i < j < k}`) and (F2) (polynomial
families `{p_ℓ(b_i, b_j) + b_k : ℓ ≤ r, i < j < k}` with `p_ℓ ∈ ℤ[x, y]`, `p_ℓ(0, 0) = 0`).

## Main results

* `prop_u33e_of` — Proposition \ref{IA:prop:u33e} as the reduction in the paper, **conditional on**
  Ackelsberg's Theorem 1.7 (`AckelsbergThm17`, the quoted theorem as a `Prop`): for every `ε > 0`
  there is `A ⊆ ℕ` with `d^*(A) > 1 - ε` such that no `A - t` (`t ∈ ℤ`) contains the configuration
  (F1), or the configuration (F2) for `p₁ = x y`, for an infinite `B`.
* `F2_sq_of` — the remark after the proposition, **conditional on** Ackelsberg's Theorem 1.5 for
  `P(x) = x²` (`AckelsbergThm15Sq`): the same for (F2) with `p₁ = x²`, via the odd-indexed
  subsequence `{b₁, b₃, b₅, …}` (`exists_interleaved`).
* `ackelsberg_thm17`, `ackelsberg_thm15_sq` — both quoted theorems are elementary and are
  **proved** here (`exists_set_avoiding`), following Ackelsberg's proof: the sets
  `D_k = ⋃_n (kℤ + n² + n)` are inherited by the configurations (if `B` lies in one residue class
  `n` modulo `k`, then `b₁ b₂ + b₃ ≡ b₁² + b₂ ≡ n² + n`), they have density `|R_k|/k` with
  `|R_{kp}| ≤ |R_k| (p + 1)/2` for odd primes `p ∤ k` (`card_R_mul_le`,
  `two_mul_card_R_le_of_odd`), and a Straus-type construction removes a tail of `D_{k_t} + t` for
  every `t ∈ ℤ` at total density `< ε`. Hence:
* `prop_u33e`, `F2_sq` — the unconditional versions, and the negative answers `not_questionF1`,
  `not_questionF2` (family `{x y}`), `not_questionF2'` (family `{x²}`) to the questions
  `QuestionF1`, `QuestionF2`, as well as `not_question318` (Question 3.18 itself, Ackelsberg).

## Conventions

* The paper's `ℕ` is `{1, 2, …}`: the sets `A` satisfy `0 ∉ A`, and in the quoted theorems and the
  questions `B ⊆ {1, 2, …}`. In the conclusions of `prop_u33e`, `F2_sq` the set `B` ranges over all
  infinite subsets of `{0, 1, 2, …}`, which contains the paper's statement.
* A set `B = {b₁ < b₂ < ⋯}` is a set of naturals; `{b_i b_j + b_k : i < j < k}` is
  `{x y + z : x, y, z ∈ B, x < y < z}` (`prodConfig`), and similarly for the other configurations.
  An integer `z` lies in `A` when it is the image of an element of `A` (`InA`), so `C + t ⊆ A` for
  `t ∈ ℤ` reads `∀ w ∈ C, InA A (w + t)`.
* The upper Banach density is `d^*(A) = limsup_{N → ∞} sup_M |A ∩ [M, M + N)| / N`
  (`upperBanachDensity`).
* Polynomials `p ∈ ℤ[x, y]` are `MvPolynomial (Fin 2) ℤ`, evaluated at `![x, y]`; `p(0, 0) = 0`
  is `MvPolynomial.eval 0 p = 0`.
-/

open Finset Filter Topology

namespace Kmrr25.S33e

/-- `R_k = {(n² + n) mod k : 0 ≤ n < k}`, the residues modulo `k` of the numbers `n² + n`. -/
def R (k : ℕ) : Finset ℕ := (range k).image fun n => (n * n + n) % k

lemma card_R_le (k : ℕ) : (R k).card ≤ k := by
  unfold R; exact (card_image_le).trans (by simp)

lemma R_one : (R 1).card ≤ 1 := card_R_le 1

lemma mem_R_of (k n : ℕ) (hk : 0 < k) : (n * n + n) % k ∈ R k := by
  refine mem_image.2 ⟨n % k, mem_range.2 (Nat.mod_lt _ hk), ?_⟩
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  conv_rhs => rw [Nat.add_mod, Nat.mul_mod]

/-- For odd `k`, `n ↦ k - 1 - n` preserves `n² + n` modulo `k`, so `|R_k| ≤ (k + 1) / 2`. -/
lemma two_mul_card_R_le_of_odd {k : ℕ} (hk : Odd k) : 2 * (R k).card ≤ k + 1 := by
  obtain ⟨j, rfl⟩ := hk
  have hsub : R (2 * j + 1) ⊆ (range (j + 1)).image fun n => (n * n + n) % (2 * j + 1) := by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hr
    rw [mem_range] at hn
    by_cases hnj : n ≤ j
    · exact mem_image.2 ⟨n, mem_range.2 (by omega), rfl⟩
    · refine mem_image.2 ⟨2 * j - n, mem_range.2 (by omega), ?_⟩
      rw [← ZMod.natCast_eq_natCast_iff']
      push_cast
      have e : ((2 * j - n : ℕ) : ZMod (2 * j + 1)) = -1 - (n : ZMod (2 * j + 1)) := by
        have h1 : ((2 * j - n : ℕ) : ZMod (2 * j + 1)) + n + 1 =
            ((2 * j + 1 : ℕ) : ZMod (2 * j + 1)) := by
          rw [← Nat.cast_add, ← Nat.cast_add_one]; congr 1; omega
        rw [ZMod.natCast_self] at h1
        linear_combination h1
      rw [e]; ring
  have := (card_le_card hsub).trans card_image_le
  simp only [card_range] at this
  omega

/-- If `k` and `p` are coprime, then `|R_{kp}| ≤ |R_k| |R_p|` (Chinese remainder theorem). -/
lemma card_R_mul_le {k p : ℕ} (hk : 0 < k) (hp : 0 < p) (hkp : k.Coprime p) :
    (R (k * p)).card ≤ (R k).card * (R p).card := by
  rw [← card_product]
  refine card_le_card_of_injOn (fun r => (r % k, r % p)) ?_ ?_
  · intro r hr
    obtain ⟨n, -, rfl⟩ := mem_image.1 (mem_coe.1 hr)
    simp only [coe_product, Set.mem_prod, mem_coe]
    rw [Nat.mod_mod_of_dvd _ (Dvd.intro p rfl), Nat.mod_mod_of_dvd _ (Dvd.intro_left k rfl)]
    exact ⟨mem_R_of k n hk, mem_R_of p n hp⟩
  · intro r hr r' hr' h
    simp only [Prod.mk.injEq] at h
    have hlt : ∀ x ∈ (R (k * p) : Set ℕ), x < k * p := by
      intro x hx
      obtain ⟨n, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
      exact Nat.mod_lt _ (Nat.mul_pos hk hp)
    have hm : r ≡ r' [MOD k * p] := (Nat.modEq_and_modEq_iff_modEq_mul hkp).1 ⟨h.1, h.2⟩
    rw [Nat.ModEq, Nat.mod_eq_of_lt (hlt r hr), Nat.mod_eq_of_lt (hlt r' hr')] at hm
    exact hm

/-- For every `s` there is `k ≥ 1` with `3^s |R_k| ≤ 2^s k`. -/
lemma exists_R_small (s : ℕ) : ∃ k : ℕ, 0 < k ∧ 3 ^ s * (R k).card ≤ 2 ^ s * k := by
  induction s with
  | zero => exact ⟨1, one_pos, by simpa using R_one⟩
  | succ s ih =>
    obtain ⟨k, hk, hks⟩ := ih
    obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (k + 3)
    have hp2 : p ≠ 2 := by omega
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hcop : k.Coprime p := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 (fun hd => by
        have := Nat.le_of_dvd hk hd; omega)
    refine ⟨k * p, Nat.mul_pos hk hp.pos, ?_⟩
    have h1 := card_R_mul_le hk hp.pos hcop
    have h2 := two_mul_card_R_le_of_odd hpodd
    -- `2 |R_{kp}| 3^{s+1} ≤ |R_k| 3^s · 3 (p+1) ≤ k 2^s · 3 (p + 1) ≤ k 2^s · 4 p`
    have h3 : 2 * (3 ^ (s + 1) * (R (k * p)).card) ≤ 2 * (2 ^ (s + 1) * (k * p)) := by
      calc 2 * (3 ^ (s + 1) * (R (k * p)).card)
          ≤ 2 * (3 ^ (s + 1) * ((R k).card * (R p).card)) := by gcongr
        _ = 3 * (3 ^ s * (R k).card) * (2 * (R p).card) := by ring
        _ ≤ 3 * (2 ^ s * k) * (p + 1) := by gcongr
        _ ≤ 2 * (2 ^ (s + 1) * (k * p)) := by
          have : 3 * (p + 1) ≤ 4 * p := by omega
          calc 3 * (2 ^ s * k) * (p + 1) = 2 ^ s * k * (3 * (p + 1)) := by ring
            _ ≤ 2 ^ s * k * (4 * p) := by gcongr
            _ = 2 * (2 ^ (s + 1) * (k * p)) := by ring
    omega

/-- For every `δ > 0` there is `k ≥ 1` with `|R_k| < δ k`. -/
lemma exists_R_lt {δ : ℝ} (hδ : 0 < δ) : ∃ k : ℕ, 0 < k ∧ ((R k).card : ℝ) < δ * k := by
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 / 3 : ℝ) < 1)
  obtain ⟨k, hk, hks⟩ := exists_R_small s
  refine ⟨k, hk, ?_⟩
  have hks' : (3 : ℝ) ^ s * (R k).card ≤ 2 ^ s * k := by exact_mod_cast hks
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h3 : (0 : ℝ) < 3 ^ s := by positivity
  have e : (2 / 3 : ℝ) ^ s = 2 ^ s / 3 ^ s := by rw [div_pow]
  rw [e] at hs
  calc ((R k).card : ℝ) = (3 ^ s * (R k).card) / 3 ^ s := by field_simp
    _ ≤ (2 ^ s * k) / 3 ^ s := by gcongr
    _ = (2 ^ s / 3 ^ s) * k := by ring
    _ < δ * k := by gcongr


/-! ## Upper Banach density -/

open scoped Classical in
/-- The number of elements of `A` in the window `[M, M + N)`. -/
noncomputable def windowCount (A : Set ℕ) (M N : ℕ) : ℕ := ((Ico M (M + N)).filter (· ∈ A)).card

/-- The upper Banach density `d^*(A) = limsup_{N → ∞} sup_M |A ∩ [M, M + N)| / N`. -/
noncomputable def upperBanachDensity (A : Set ℕ) : ℝ :=
  limsup (fun N : ℕ => ⨆ M : ℕ, (windowCount A M N : ℝ) / N) atTop

lemma windowCount_le (A : Set ℕ) (M N : ℕ) : windowCount A M N ≤ N := by
  classical
  unfold windowCount
  exact (card_filter_le _ _).trans (by simp)

lemma ratio_le_one (A : Set ℕ) (M N : ℕ) : (windowCount A M N : ℝ) / N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast windowCount_le A M N

lemma bddAbove_ratio (A : Set ℕ) (N : ℕ) :
    BddAbove (Set.range fun M : ℕ => (windowCount A M N : ℝ) / N) :=
  ⟨1, by rintro _ ⟨M, rfl⟩; exact ratio_le_one A M N⟩

/-- If `|A ∩ [0, N)| / N ≥ c` for infinitely many `N`, then `d^*(A) ≥ c`. -/
lemma le_upperBanachDensity {A : Set ℕ} {c : ℝ}
    (h : ∃ᶠ N in atTop, c ≤ (windowCount A 0 N : ℝ) / N) : c ≤ upperBanachDensity A := by
  apply le_limsup_of_frequently_le
  · exact h.mono fun N hN => hN.trans (le_ciSup (bddAbove_ratio A N) 0)
  · exact isBoundedUnder_of ⟨1, fun N => ciSup_le fun M => ratio_le_one A M N⟩

/-! ## The sets `D_k` and counting -/

/-- The integer `z` is (the image of) an element of `A`. -/
def InA (A : Set ℕ) (z : ℤ) : Prop := ∃ n ∈ A, (n : ℤ) = z

/-- `z ∈ D_k = ⋃_n (kℤ + n² + n)`: `z` is congruent modulo `k` to some `n² + n`. -/
def InD (k : ℕ) (z : ℤ) : Prop := ∃ r ∈ R k, z ≡ r [ZMOD k]

lemma card_filter_modEq_le (N k : ℕ) (c : ℤ) :
    ((range N).filter fun m : ℕ => (m : ℤ) ≡ c [ZMOD k]).card ≤ N / k + 1 := by
  classical
  calc _ ≤ (range (N / k + 1)).card := by
        refine card_le_card_of_injOn (fun m => m / k) ?_ ?_
        · intro m hm
          simp only [coe_filter, mem_range] at hm
          simp only [coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hm.1.le)
        · intro m hm m' hm' h
          simp only [coe_filter, mem_range] at hm hm'
          have h1 : m ≡ m' [MOD k] := Int.natCast_modEq_iff.1 (hm.2.trans hm'.2.symm)
          have h2 : m / k = m' / k := h
          rw [← Nat.div_add_mod m k, ← Nat.div_add_mod m' k, h2, h1]
    _ = N / k + 1 := card_range _

open scoped Classical in
lemma card_filter_InD_le (N k : ℕ) (t : ℤ) :
    ((range N).filter fun m : ℕ => InD k ((m : ℤ) - t)).card ≤ (R k).card * (N / k + 1) := by
  classical
  have hsub : ((range N).filter fun m : ℕ => InD k ((m : ℤ) - t)) ⊆
      (R k).biUnion fun r => (range N).filter fun m : ℕ => (m : ℤ) ≡ r + t [ZMOD k] := by
    intro m hm
    simp only [mem_filter] at hm
    obtain ⟨hmN, r, hr, hmr⟩ := hm
    refine mem_biUnion.2 ⟨r, hr, mem_filter.2 ⟨hmN, ?_⟩⟩
    have := hmr.add_right t
    simpa using this
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc _ ≤ ∑ _r ∈ R k, (N / k + 1) := sum_le_sum fun r _ => card_filter_modEq_le N k _
    _ = (R k).card * (N / k + 1) := by rw [sum_const, smul_eq_mul]

open scoped Classical in
lemma card_filter_InD_le_real (N k : ℕ) (hk : 0 < k) (t : ℤ) :
    (((range N).filter fun m : ℕ => InD k ((m : ℤ) - t)).card : ℝ) ≤
      (R k).card / k * N + k := by
  have h1 : (((range N).filter fun m : ℕ => InD k ((m : ℤ) - t)).card : ℝ) ≤
      (R k).card * ((N / k : ℕ) + 1 : ℝ) := by exact_mod_cast card_filter_InD_le N k t
  have h2 : ((N / k : ℕ) : ℝ) ≤ N / k := Nat.cast_div_le
  have h3 : ((R k).card : ℝ) ≤ k := by exact_mod_cast card_R_le k
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  calc _ ≤ (R k).card * ((N / k : ℕ) + 1 : ℝ) := h1
    _ ≤ (R k).card * (N / k + 1) := by gcongr
    _ = (R k).card / k * N + (R k).card := by field_simp
    _ ≤ (R k).card / k * N + k := by linarith


/-! ## The construction (Straus, Ackelsberg) -/

section Construction

variable {ε : ℝ} (hε : 0 < ε)

/-- `δ_j = (ε/8) 2^{-(j+1)}`. -/
noncomputable def δ (ε : ℝ) (j : ℕ) : ℝ := ε / 8 * (1 / 2) ^ (j + 1)

include hε in
lemma δ_pos (j : ℕ) : 0 < δ ε j := by unfold δ; positivity

/-- A modulus `k_j ≥ 1` with `|R_{k_j}| < δ_j k_j`. -/
noncomputable def kk (j : ℕ) : ℕ := (exists_R_lt (δ_pos hε j)).choose

lemma kk_spec (j : ℕ) : 0 < kk hε j ∧ ((R (kk hε j)).card : ℝ) < δ ε j * kk hε j :=
  (exists_R_lt (δ_pos hε j)).choose_spec

/-- The thresholds `N_j = 2^j (k_0 + ⋯ + k_{j-1}) + j`. -/
noncomputable def NN (j : ℕ) : ℕ := 2 ^ j * (∑ i ∈ range j, kk hε i) + j

lemma NN_strictMono : StrictMono (NN hε) := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  unfold NN
  rw [sum_range_succ, pow_succ]
  have : 2 ^ j * ∑ i ∈ range j, kk hε i ≤ 2 ^ j * 2 * (∑ i ∈ range j, kk hε i + kk hε j) := by
    calc 2 ^ j * ∑ i ∈ range j, kk hε i = 2 ^ j * 1 * ∑ i ∈ range j, kk hε i := by ring
      _ ≤ 2 ^ j * 2 * (∑ i ∈ range j, kk hε i + kk hε j) := by gcongr <;> omega
  omega

/-- The `j`-th shift, an enumeration `j ↦ t_j` of `ℤ`. -/
def tt (j : ℕ) : ℤ := Equiv.intEquivNat.symm j

/-- `E_j = (D_{k_j} + t_j) ∩ ℕ`. -/
def E (j : ℕ) : Set ℕ := {m | InD (kk hε j) ((m : ℤ) - tt j)}

/-- The exceptional set `S = ⋃_j (E_j ∩ [N_j, ∞))`. -/
def S : Set ℕ := {m | ∃ j, NN hε j ≤ m ∧ m ∈ E hε j}

/-- The set `A = ℕ_{≥1} \ S`. -/
def Aε : Set ℕ := {m | 0 < m ∧ m ∉ S hε}

lemma zero_not_mem_Aε : 0 ∉ Aε hε := fun h => (lt_irrefl 0) h.1

/-- For every shift `t ∈ ℤ` there is `k ≥ 1` such that `(A - t) ∩ D_k` is finite. -/
lemma finite_shift (t : ℤ) :
    ∃ k : ℕ, 0 < k ∧ {z : ℤ | InD k z ∧ InA (Aε hε) (z + t)}.Finite := by
  set j := Equiv.intEquivNat t with hj
  have htj : tt j = t := by simp [tt, hj]
  refine ⟨kk hε j, (kk_spec hε j).1, (Set.finite_Ico (-t) (NN hε j - t)).subset ?_⟩
  rintro z ⟨hz, m, hmA, hm⟩
  have hmE : m ∈ E hε j := by
    show InD (kk hε j) ((m : ℤ) - tt j)
    rw [htj, hm]; simpa using hz
  have hlt : m < NN hε j := by
    by_contra hge
    exact hmA.2 ⟨j, not_lt.1 hge, hmE⟩
  simp only [Set.mem_Ico]
  constructor <;> omega

open scoped Classical in
/-- The counting estimate at `N = N_{J+1}`:
`|A ∩ [0, N)| ≥ N - 1 - (ε/8) N - N / 2^{J+1}`. -/
lemma count_lower (J : ℕ) :
    (NN hε (J + 1) : ℝ) - 1 - ε / 8 * NN hε (J + 1) - NN hε (J + 1) / 2 ^ (J + 1) ≤
      (windowCount (Aε hε) 0 (NN hε (J + 1)) : ℝ) := by
  set N := NN hε (J + 1) with hN
  set F := (range N).filter (· ∈ Aε hε)
  set G := (range N).filter (· ∈ S hε)
  have hW : windowCount (Aε hε) 0 N = F.card := by
    unfold windowCount; rw [zero_add, ← range_eq_Ico]
  -- `range N ⊆ {0} ∪ F ∪ G`
  have h1 : N ≤ 1 + F.card + G.card := by
    have hsub : range N ⊆ ({0} ∪ F) ∪ G := by
      intro m hm
      by_cases h0 : m = 0
      · simp [h0]
      · by_cases hS : m ∈ S hε
        · exact mem_union_right _ (mem_filter.2 ⟨hm, hS⟩)
        · exact mem_union_left _ (mem_union_right _
            (mem_filter.2 ⟨hm, Nat.pos_of_ne_zero h0, hS⟩))
    have e1 := card_le_card hsub
    have e2 := card_union_le ({0} ∪ F) G
    have e3 := card_union_le ({0} : Finset ℕ) F
    simp only [card_singleton] at e3
    rw [card_range] at e1
    omega
  -- `G ⊆ ⋃_{j ≤ J} E_j ∩ [0, N)`
  have h2 : G ⊆ (range (J + 1)).biUnion fun j => (range N).filter fun m : ℕ =>
      InD (kk hε j) ((m : ℤ) - tt j) := by
    intro m hm
    obtain ⟨hmN, j, hj, hmE⟩ := mem_filter.1 hm
    have hjJ : j < J + 1 := by
      by_contra hcon
      have := (NN_strictMono hε).monotone (not_lt.1 hcon)
      rw [mem_range] at hmN
      omega
    exact mem_biUnion.2 ⟨j, mem_range.2 hjJ, mem_filter.2 ⟨hmN, hmE⟩⟩
  have h3 : (G.card : ℝ) ≤ ∑ j ∈ range (J + 1), (δ ε j * N + kk hε j) := by
    have := (card_le_card h2).trans card_biUnion_le
    calc (G.card : ℝ) ≤ ∑ j ∈ range (J + 1), (((range N).filter fun m : ℕ =>
          InD (kk hε j) ((m : ℤ) - tt j)).card : ℝ) := by exact_mod_cast this
      _ ≤ _ := by
        refine sum_le_sum fun j _ => ?_
        refine (card_filter_InD_le_real N _ (kk_spec hε j).1 _).trans ?_
        have hk := (kk_spec hε j)
        have hk0 : (0 : ℝ) < kk hε j := by exact_mod_cast hk.1
        have : ((R (kk hε j)).card : ℝ) / kk hε j ≤ δ ε j := by
          rw [div_le_iff₀ hk0]; exact hk.2.le
        have hN0 : (0 : ℝ) ≤ N := by positivity
        nlinarith
  have h4 : ∑ j ∈ range (J + 1), δ ε j ≤ ε / 8 := by
    unfold δ
    rw [← mul_sum]
    have : ∑ j ∈ range (J + 1), (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := by
      have := sum_geometric_two_le (J + 1)
      calc ∑ j ∈ range (J + 1), (1 / 2 : ℝ) ^ (j + 1)
          = (1 / 2) * ∑ j ∈ range (J + 1), (1 / 2 : ℝ) ^ j := by
            rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
        _ ≤ (1 / 2) * 2 := by gcongr
        _ = 1 := by norm_num
    calc ε / 8 * ∑ j ∈ range (J + 1), (1 / 2 : ℝ) ^ (j + 1) ≤ ε / 8 * 1 := by gcongr
      _ = ε / 8 := mul_one _
  have h5 : (∑ j ∈ range (J + 1), (kk hε j : ℝ)) ≤ N / 2 ^ (J + 1) := by
    rw [le_div_iff₀ (by positivity)]
    have : 2 ^ (J + 1) * (∑ i ∈ range (J + 1), kk hε i) ≤ N := by
      rw [hN]; unfold NN; omega
    calc (∑ j ∈ range (J + 1), (kk hε j : ℝ)) * 2 ^ (J + 1)
        = ((2 ^ (J + 1) * (∑ i ∈ range (J + 1), kk hε i) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ N := by exact_mod_cast this
  have h6 : (G.card : ℝ) ≤ ε / 8 * N + N / 2 ^ (J + 1) := by
    rw [sum_add_distrib, ← sum_mul] at h3
    have hN0 : (0 : ℝ) ≤ N := by positivity
    nlinarith
  have h1' : (N : ℝ) ≤ 1 + F.card + G.card := by exact_mod_cast h1
  rw [hW]
  linarith

/-- `d^*(A) > 1 - ε`. -/
lemma upperBanachDensity_Aε : 1 - ε < upperBanachDensity (Aε hε) := by
  have key : 1 - ε / 2 ≤ upperBanachDensity (Aε hε) := by
    apply le_upperBanachDensity
    rw [frequently_atTop]
    intro N0
    obtain ⟨n1, hn1⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ε / 8)
      (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨n2, hn2⟩ := exists_nat_gt (8 / ε)
    set J := max (max N0 n1) n2 with hJ
    refine ⟨NN hε (J + 1), ?_, ?_⟩
    · have h0 : N0 ≤ J := le_trans (le_max_left _ _) (le_max_left _ _)
      exact le_trans (by omega : N0 ≤ J + 1) ((NN_strictMono hε).id_le (J + 1))
    · have hc := count_lower hε J
      set N := NN hε (J + 1)
      have hNJ : J + 1 ≤ N := (NN_strictMono hε).id_le (J + 1)
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hNJ' : ((J + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNJ
      have hJn2 : (n2 : ℝ) ≤ J := by exact_mod_cast (le_max_right _ _)
      have hinvN : 1 / (N : ℝ) ≤ ε / 8 := by
        rw [div_le_iff₀ hN0]
        have : 8 / ε < N := by push_cast at hNJ'; linarith
        rw [div_lt_iff₀ hε] at this
        linarith
      have hpow : (1 / 2 : ℝ) ^ (J + 1) ≤ ε / 8 := by
        refine le_trans ?_ hn1.le
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (by have := le_max_right N0 n1; have := le_max_left (max N0 n1) n2; omega)
      have e : (N : ℝ) / 2 ^ (J + 1) = N * (1 / 2) ^ (J + 1) := by
        rw [div_eq_mul_inv, one_div, inv_pow]
      rw [le_div_iff₀ hN0]
      have : (N : ℝ) * (1 / 2) ^ (J + 1) ≤ N * (ε / 8) := by gcongr
      have h1N : (1 : ℝ) ≤ N * (ε / 8) := by
        rw [div_le_iff₀ hN0] at hinvN; linarith
      nlinarith
  linarith

end Construction


/-! ## Divisibility of the configurations (Ackelsberg, Lemmas 4.2 and 4.5) -/

lemma exists_infinite_residue {B : Set ℕ} (hB : B.Infinite) {k : ℕ} (hk : 0 < k) :
    ∃ n < k, {b ∈ B | b % k = n}.Infinite := by
  by_contra h
  simp only [not_exists, not_and, Set.not_infinite] at h
  apply hB
  refine ((Set.finite_lt_nat k).biUnion fun n hn => h n hn).subset ?_
  intro b hb
  exact Set.mem_biUnion (Nat.mod_lt b hk) ⟨hb, rfl⟩

lemma inD_of_modEq {k n : ℕ} (hk : 0 < k) {w : ℕ} (hw : w ≡ n * n + n [MOD k]) : InD k w :=
  ⟨(n * n + n) % k, mem_R_of k n hk,
    Int.natCast_modEq_iff.2 (hw.trans (Nat.mod_modEq _ _).symm)⟩

/-- For a fixed shift `t`, if `x y + z + t ∈ A` for all `x < y < z` in `B`, then `B` is finite. -/
lemma prod_finite {ε : ℝ} (hε : 0 < ε) (t : ℤ) (B : Set ℕ)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x < y → y < z → InA (Aε hε) ((x * y + z : ℕ) + t)) :
    B.Finite := by
  by_contra hinf
  obtain ⟨k, hk, hfin⟩ := finite_shift hε t
  obtain ⟨n, hn, hB'⟩ := exists_infinite_residue hinf hk
  obtain ⟨x, hx⟩ := hB'.nonempty
  obtain ⟨y, hy, hxy⟩ := hB'.exists_gt x
  have hZ : ({z ∈ B | z % k = n} \ {z | z ≤ y}).Infinite := hB'.sdiff (Set.finite_le_nat y)
  apply (hZ.image (f := fun z : ℕ => ((x * y + z : ℕ) : ℤ)) ?_) (hfin.subset ?_)
  · intro a _ b _ hab
    simp only [Nat.cast_add, Nat.cast_mul] at hab
    omega
  · rintro _ ⟨z, ⟨⟨hzB, hzk⟩, hzy⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, not_le] at hzy
    refine ⟨inD_of_modEq hk (n := n) ?_, hB x hx.1 y hy.1 z hzB hxy hzy⟩
    have hx' : x ≡ n [MOD k] := by rw [Nat.ModEq, hx.2, Nat.mod_eq_of_lt hn]
    have hy' : y ≡ n [MOD k] := by rw [Nat.ModEq, hy.2, Nat.mod_eq_of_lt hn]
    have hz' : z ≡ n [MOD k] := by rw [Nat.ModEq, hzk, Nat.mod_eq_of_lt hn]
    exact (hx'.mul hy').add hz'

/-- For a fixed shift `t`, if `x² + y + t ∈ A` for all `x < y` in `B`, then `B` is finite. -/
lemma sq_finite {ε : ℝ} (hε : 0 < ε) (t : ℤ) (B : Set ℕ)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x < y → InA (Aε hε) ((x ^ 2 + y : ℕ) + t)) : B.Finite := by
  by_contra hinf
  obtain ⟨k, hk, hfin⟩ := finite_shift hε t
  obtain ⟨n, hn, hB'⟩ := exists_infinite_residue hinf hk
  obtain ⟨x, hx⟩ := hB'.nonempty
  have hZ : ({z ∈ B | z % k = n} \ {z | z ≤ x}).Infinite := hB'.sdiff (Set.finite_le_nat x)
  apply (hZ.image (f := fun y : ℕ => ((x ^ 2 + y : ℕ) : ℤ)) ?_) (hfin.subset ?_)
  · intro a _ b _ hab
    simp only [Nat.cast_add, Nat.cast_pow] at hab
    omega
  · rintro _ ⟨y, ⟨⟨hyB, hyk⟩, hxy⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, not_le] at hxy
    refine ⟨inD_of_modEq hk (n := n) ?_, hB x hx.1 y hyB hxy⟩
    have hx' : x ≡ n [MOD k] := by rw [Nat.ModEq, hx.2, Nat.mod_eq_of_lt hn]
    have hy' : y ≡ n [MOD k] := by rw [Nat.ModEq, hyk, Nat.mod_eq_of_lt hn]
    rw [pow_two]
    exact (hx'.mul hx').add hy'


/-! ## Configurations and the quoted theorems of Ackelsberg -/

/-- The configuration of Question 3.18 of the survey,
`{b_i b_j + b_k : i < j < k} = {x y + z : x, y, z ∈ B, x < y < z}`. -/
def prodConfig (B : Set ℕ) : Set ℕ :=
  {w | ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, x < y ∧ y < z ∧ w = x * y + z}

/-- The configuration of Question 3.13 of the survey,
`{b_i² + b_j : i < j} = {x² + y : x, y ∈ B, x < y}`. -/
def sqConfig (B : Set ℕ) : Set ℕ := {w | ∃ x ∈ B, ∃ y ∈ B, x < y ∧ w = x ^ 2 + y}

/-- The configuration in (F1): `{b_k, b_i b_j + b_k : i < j < k}`. -/
def configF1 (B : Set ℕ) : Set ℕ :=
  {w | ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, x < y ∧ y < z ∧ (w = z ∨ w = x * y + z)}

/-- The configuration in (F2) for one polynomial `p ∈ ℤ[x, y]`:
`{p(b_i, b_j) + b_k : i < j < k}`, a set of integers. -/
def configPoly (p : MvPolynomial (Fin 2) ℤ) (B : Set ℕ) : Set ℤ :=
  {w | ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, x < y ∧ y < z ∧
    w = MvPolynomial.eval ![(x : ℤ), (y : ℤ)] p + z}

/-- Ackelsberg, *Counterexamples to generalizations of the Erdős `B + B + t` problem*,
arXiv:2404.17383, Theorem 1.7, as quoted in the paper (proof of
Proposition \ref{IA:prop:u33e}): for every `ε > 0` there is `A ⊆ ℕ` with `d^*(A) > 1 - ε` such
that whenever `t ∈ ℤ` and `{b₁ b₂ + b₃ + t : b₁, b₂, b₃ ∈ B, b₁ < b₂ < b₃} ⊆ A`, the set `B` is
finite. (Here `ℕ = {1, 2, …}`.) It is proved below as `ackelsberg_thm17`. -/
def AckelsbergThm17 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : Set ℕ, 0 ∉ A ∧ 1 - ε < upperBanachDensity A ∧
    ∀ (B : Set ℕ) (t : ℤ), (∀ b ∈ B, 0 < b) → (∀ w ∈ prodConfig B, InA A ((w : ℤ) + t)) →
      B.Finite

/-- Ackelsberg, arXiv:2404.17383, Theorem 1.5, for the polynomial `P(x) = x²` (the case quoted in
the paper after Proposition \ref{IA:prop:u33e}): for every `ε > 0` there is `A ⊆ ℕ` with
`d^*(A) > 1 - ε` such that whenever `t ∈ ℤ` and `{b₁² + b₂ + t : b₁, b₂ ∈ B, b₁ < b₂} ⊆ A`, the
set `B` is finite. It is proved below as `ackelsberg_thm15_sq`. -/
def AckelsbergThm15Sq : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : Set ℕ, 0 ∉ A ∧ 1 - ε < upperBanachDensity A ∧
    ∀ (B : Set ℕ) (t : ℤ), (∀ b ∈ B, 0 < b) → (∀ w ∈ sqConfig B, InA A ((w : ℤ) + t)) →
      B.Finite

/-- Ackelsberg's Theorem 1.7 (`AckelsbergThm17`) holds, in the stronger form with one set `A`
serving for both configurations and `B` ranging over all subsets of `{0, 1, 2, …}`. The proof is
Ackelsberg's: `A = ℕ_{≥1} \ S`, where `S` contains a tail of `D_{k_t} + t` for every shift `t`, with
`D_k = ⋃_n (kℤ + n² + n)` of density `|R_k|/k → 0` along products of distinct odd primes. -/
theorem exists_set_avoiding {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set ℕ, 0 ∉ A ∧ 1 - ε < upperBanachDensity A ∧
      (∀ (B : Set ℕ) (t : ℤ), (∀ w ∈ prodConfig B, InA A ((w : ℤ) + t)) → B.Finite) ∧
      (∀ (B : Set ℕ) (t : ℤ), (∀ w ∈ sqConfig B, InA A ((w : ℤ) + t)) → B.Finite) := by
  refine ⟨Aε hε, zero_not_mem_Aε hε, upperBanachDensity_Aε hε, ?_, ?_⟩
  · intro B t hB
    exact prod_finite hε t B fun x hx y hy z hz hxy hyz =>
      hB _ ⟨x, hx, y, hy, z, hz, hxy, hyz, rfl⟩
  · intro B t hB
    exact sq_finite hε t B fun x hx y hy hxy => hB _ ⟨x, hx, y, hy, hxy, rfl⟩

/-- Ackelsberg, Theorem 1.7 (quoted in the paper), proved. -/
theorem ackelsberg_thm17 : AckelsbergThm17 := fun ε hε => by
  obtain ⟨A, h0, hd, hP, -⟩ := exists_set_avoiding hε
  exact ⟨A, h0, hd, fun B t _ hB => hP B t hB⟩

/-- Ackelsberg, Theorem 1.5 for `P(x) = x²` (quoted in the paper), proved. -/
theorem ackelsberg_thm15_sq : AckelsbergThm15Sq := fun ε hε => by
  obtain ⟨A, h0, hd, -, hS⟩ := exists_set_avoiding hε
  exact ⟨A, h0, hd, fun B t _ hB => hS B t hB⟩

/-! ## Proposition \ref{IA:prop:u33e} -/

lemma eval_xy (x y : ℤ) :
    MvPolynomial.eval ![x, y] (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) =
      x * y := by simp

lemma eval_xsq (x y : ℤ) :
    MvPolynomial.eval ![x, y] (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 2) ℤ) = x ^ 2 := by simp

lemma pos_part_infinite {B : Set ℕ} (hB : B.Infinite) : {b ∈ B | 0 < b}.Infinite := by
  have : {b ∈ B | 0 < b} = B \ {0} := by
    ext b; simp [Nat.pos_iff_ne_zero]
  rw [this]; exact hB.sdiff (Set.finite_singleton 0)

/-- Paper, Proposition \ref{IA:prop:u33e}, **conditional on Ackelsberg's Theorem 1.7**
(`AckelsbergThm17`): for every `ε > 0` there is `A ⊆ ℕ = {1, 2, …}` with `d^*(A) > 1 - ε` such
that for no `t ∈ ℤ` and no infinite `B` does `A - t` contain the configuration (F1)
`{b_k, b_i b_j + b_k : i < j < k}`, or the configuration (F2) `{p(b_i, b_j) + b_k : i < j < k}` for
the one-element family `p₁(x, y) = x y`. (Here `B` ranges over all infinite subsets of
`{0, 1, 2, …}`.) -/
theorem prop_u33e_of (h17 : AckelsbergThm17) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set ℕ, 0 ∉ A ∧ 1 - ε < upperBanachDensity A ∧
      ∀ (t : ℤ) (B : Set ℕ), B.Infinite →
        ¬ (∀ w ∈ configF1 B, InA A ((w : ℤ) + t)) ∧
        ¬ (∀ w ∈ configPoly (MvPolynomial.X 0 * MvPolynomial.X 1) B, InA A (w + t)) := by
  obtain ⟨A, h0, hd, hA⟩ := h17 ε hε
  refine ⟨A, h0, hd, fun t B hB => ⟨fun hF => ?_, fun hF => ?_⟩⟩
  · apply pos_part_infinite hB
    refine hA _ t (fun b hb => hb.2) fun w hw => ?_
    obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, rfl⟩ := hw
    exact hF _ ⟨x, hx.1, y, hy.1, z, hz.1, hxy, hyz, Or.inr rfl⟩
  · apply pos_part_infinite hB
    refine hA _ t (fun b hb => hb.2) fun w hw => ?_
    obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, rfl⟩ := hw
    have := hF _ ⟨x, hx.1, y, hy.1, z, hz.1, hxy, hyz, rfl⟩
    rw [eval_xy] at this
    simpa using this

/-- Paper, Proposition \ref{IA:prop:u33e}, unconditionally (Ackelsberg's Theorem 1.7 is proved
above). -/
theorem prop_u33e {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set ℕ, 0 ∉ A ∧ 1 - ε < upperBanachDensity A ∧
      ∀ (t : ℤ) (B : Set ℕ), B.Infinite →
        ¬ (∀ w ∈ configF1 B, InA A ((w : ℤ) + t)) ∧
        ¬ (∀ w ∈ configPoly (MvPolynomial.X 0 * MvPolynomial.X 1) B, InA A (w + t)) :=
  prop_u33e_of ackelsberg_thm17 hε

/-- The odd-indexed subsequence `C = {b₁, b₃, b₅, …}` of an infinite `B`: between any two
elements of `C` lies an element of `B`. -/
lemma exists_interleaved {B : Set ℕ} (hB : B.Infinite) :
    ∃ C ⊆ B, C.Infinite ∧ ∀ c ∈ C, ∀ c' ∈ C, c < c' → ∃ y ∈ B, c < y ∧ y < c' := by
  have hB' : (Set.ofPred fun n => n ∈ B).Infinite := hB
  have hmono := Nat.nth_strictMono hB'
  refine ⟨Set.range fun i => Nat.nth (· ∈ B) (2 * i), ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩; exact Nat.nth_mem_of_infinite hB' _
  · exact Set.infinite_range_of_injective fun i j h =>
      by have := hmono.injective h; omega
  · rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩ hlt
    have hii : 2 * i < 2 * i' := hmono.lt_iff_lt.1 hlt
    refine ⟨Nat.nth (· ∈ B) (2 * i + 1), Nat.nth_mem_of_infinite hB' _, hmono (by omega),
      hmono (by omega)⟩

/-- Paper, the remark after Proposition \ref{IA:prop:u33e}, **conditional on Ackelsberg's
Theorem 1.5 for `x²`** (`AckelsbergThm15Sq`): (F2) fails already for the one-element family
`p₁(x, y) = x²`. If `{b_i² + b_k : i < j < k} + t ⊆ A`, then the odd-indexed subsequence
`C = {b₁, b₃, …}` satisfies `{c² + c' : c < c' ∈ C} + t ⊆ A`, which Theorem 1.5 forbids. -/
theorem F2_sq_of (h15 : AckelsbergThm15Sq) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set ℕ, 0 ∉ A ∧ 1 - ε < upperBanachDensity A ∧
      ∀ (t : ℤ) (B : Set ℕ), B.Infinite →
        ¬ (∀ w ∈ configPoly (MvPolynomial.X 0 ^ 2) B, InA A (w + t)) := by
  obtain ⟨A, h0, hd, hA⟩ := h15 ε hε
  refine ⟨A, h0, hd, fun t B hB hF => ?_⟩
  obtain ⟨C, hCB, hC, hCint⟩ := exists_interleaved (pos_part_infinite hB)
  apply hC
  refine hA C t (fun c hc => (hCB hc).2) fun w hw => ?_
  obtain ⟨c, hc, c', hc', hcc, rfl⟩ := hw
  obtain ⟨y, hy, hcy, hyc⟩ := hCint c hc c' hc' hcc
  have := hF _ ⟨c, (hCB hc).1, y, hy.1, c', (hCB hc').1, hcy, hyc, rfl⟩
  rw [eval_xsq] at this
  simpa using this

/-- The remark after Proposition \ref{IA:prop:u33e}, unconditionally. -/
theorem F2_sq {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set ℕ, 0 ∉ A ∧ 1 - ε < upperBanachDensity A ∧
      ∀ (t : ℤ) (B : Set ℕ), B.Infinite →
        ¬ (∀ w ∈ configPoly (MvPolynomial.X 0 ^ 2) B, InA A (w + t)) :=
  F2_sq_of ackelsberg_thm15_sq hε

/-! ## The questions -/

/-- Question 3.18 of the survey (Question \ref{IA:q:318}): if `A ⊆ ℕ` has positive upper Banach
density, must there be an infinite `B = {b₁ < b₂ < ⋯} ⊆ ℕ` and `t ≥ 0` with
`{b_i b_j + b_k : i < j < k} ⊆ A - t`? -/
def Question318 : Prop :=
  ∀ A : Set ℕ, 0 ∉ A → 0 < upperBanachDensity A →
    ∃ B : Set ℕ, B.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ ∃ t : ℕ, ∀ w ∈ prodConfig B, w + t ∈ A

/-- The analogue (F1) of Question 3.18 (base point, as in Question 3.15): must every `A ⊆ ℕ` with
`d^*(A) > 0` contain `{b_k, b_i b_j + b_k : i < j < k} + t` for some infinite `B ⊆ ℕ` and
`t ≥ 0`? -/
def QuestionF1 : Prop :=
  ∀ A : Set ℕ, 0 ∉ A → 0 < upperBanachDensity A →
    ∃ B : Set ℕ, B.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ ∃ t : ℕ, ∀ w ∈ configF1 B, w + t ∈ A

/-- The analogue (F2) of Question 3.18 (polynomial family, as in Question 3.16): given
`p₁, …, p_r ∈ ℤ[x, y]` with `p_ℓ(0, 0) = 0`, must every `A ⊆ ℕ` with `d^*(A) > 0` contain
`{p_ℓ(b_i, b_j) + b_k : 1 ≤ ℓ ≤ r, i < j < k} + t` for some infinite `B ⊆ ℕ` and `t ≥ 0`?
As in the paper, this is a question about all such families. -/
def QuestionF2 : Prop :=
  ∀ (r : ℕ) (p : Fin r → MvPolynomial (Fin 2) ℤ), (∀ ℓ, MvPolynomial.eval 0 (p ℓ) = 0) →
    ∀ A : Set ℕ, 0 ∉ A → 0 < upperBanachDensity A →
      ∃ B : Set ℕ, B.Infinite ∧ (∀ b ∈ B, 0 < b) ∧ ∃ t : ℕ,
        ∀ ℓ, ∀ w ∈ configPoly (p ℓ) B, InA A (w + t)

/-- Question 3.18 has a negative answer (Ackelsberg, Theorem 1.7). -/
theorem not_question318 : ¬ Question318 := by
  intro hQ
  obtain ⟨A, h0, hd, hP, -⟩ := exists_set_avoiding (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨B, hB, -, t, hBt⟩ := hQ A h0 (by linarith)
  exact hB (hP B t fun w hw => ⟨w + t, hBt w hw, by push_cast; ring⟩)

/-- Paper, Proposition \ref{IA:prop:u33e}: (F1) has a negative answer. -/
theorem not_questionF1 : ¬ QuestionF1 := by
  intro hQ
  obtain ⟨A, h0, hd, hA⟩ := prop_u33e (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨B, hB, -, t, hBt⟩ := hQ A h0 (by linarith)
  exact (hA t B hB).1 fun w hw => ⟨w + t, hBt w hw, by push_cast; ring⟩

/-- Paper, Proposition \ref{IA:prop:u33e}: (F2) has a negative answer, witnessed by the
one-element family `p₁(x, y) = x y`. -/
theorem not_questionF2 : ¬ QuestionF2 := by
  intro hQ
  obtain ⟨A, h0, hd, hA⟩ := prop_u33e (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨B, hB, -, t, hBt⟩ := hQ 1 (fun _ => MvPolynomial.X 0 * MvPolynomial.X 1)
    (fun _ => by simp) A h0 (by linarith)
  exact (hA t B hB).2 (hBt 0)

/-- The remark after Proposition \ref{IA:prop:u33e}: (F2) has a negative answer, witnessed also by
the one-element family `p₁(x, y) = x²`. -/
theorem not_questionF2' : ¬ QuestionF2 := by
  intro hQ
  obtain ⟨A, h0, hd, hA⟩ := F2_sq (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨B, hB, -, t, hBt⟩ := hQ 1 (fun _ => MvPolynomial.X 0 ^ 2)
    (fun _ => by simp) A h0 (by linarith)
  exact hA t B hB (hBt 0)

end Kmrr25.S33e
