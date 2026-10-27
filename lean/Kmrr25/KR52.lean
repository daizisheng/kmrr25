import Kmrr25.Basic

/-!
# Unrestricted sums `B + B` and lower Banach density (Kousek–Radić, Question 5.2)

Paper, Section \ref{KR:sec:main}: Theorem \ref{KR:thm:main}, Corollary \ref{KR:cor:main} and
Lemma \ref{KR:lem:rot}.

Let `α` be irrational, `κ > 0` with `κ log 2 ≡ 1/2 (mod 1)`, `0 < δ < 1/4`, `c = 1/2 - 2δ`,
`φ(n) = n α - κ log n`, `E = {n ∈ ℕ : {φ(n)} ∈ [0, c)}` and `A' = (2ℕ - 1) ∪ 2E`
(`E`, `A'` below; `ℕ = {1, 2, …}` in the paper, so `0 ∉ E` is part of the definition).

## Main results

* `lem_rot` : Lemma \ref{KR:lem:rot}, `D_L → 0`, for the discrepancy `D_L` (`discrepancy`)
  defined as in the paper; `rot_uniform` is the same statement in `ε`-form.
* `E_uniform`, `A'_uniform` : Theorem \ref{KR:thm:main}(a), uniform density `c` of `E` and
  uniform density `3/4 - δ` of `A'` (for all `M ∈ ℕ`, in particular for all `M ≥ 1`).
* `banach_densities` : Theorem \ref{KR:thm:main}(a), "in particular":
  `d_*(E) = d^*(E) = 1/2 - 2δ` and `d_*(A') = d^*(A') = 3/4 - δ`.
* `no_BBt` : Theorem \ref{KR:thm:main}(b), for every `t ∈ ℤ` and every infinite `B ⊆ ℕ₀`,
  `B + B + t ⊄ E`.
* `no_BB` : Theorem \ref{KR:thm:main}(c), for every infinite `B ⊆ ℕ`, `B + B ⊄ A'`.
* `main` : Theorem \ref{KR:thm:main}, all three parts together.
* `q52_negative` : Corollary \ref{KR:cor:main}, negative answers to both parts of
  Question 5.2 of Kousek and Radić: a set of positive integers with `d_*(A) > 1/3` containing no
  `B + B + t` (`B` infinite, `t ∈ ℕ`), and a set with `d_*(A) > 2/3` containing no `B + B`.
* `sup_lower_bounds` : Corollary \ref{KR:cor:main}, the lower bounds `≥ 1/2` and `≥ 3/4` for the
  two suprema.

## Definitions and conventions

* Banach densities use the normalisation of Kousek and Radić:
  `d_*(A) = liminf_{N - M → ∞} |A ∩ [M, N]| / (N - M)` and `d^*(A)` the corresponding `limsup`,
  over pairs `(M, N)` of naturals with `M ≥ 1` (`banachFilter`, `banachRatio`,
  `lowerBanachDensity`, `upperBanachDensity`); `Filter.liminf`, `Filter.limsup` in `ℝ`.
* `B + B + t ⊆ E` for `t ∈ ℤ` is expressed as: every `b + b' + t` (`b, b' ∈ B`) is the image in
  `ℤ` of an element of `E`. Sets `B` are subsets of Lean's `ℕ`, which contains `0`; this only
  strengthens the non-existence statements.
* `{x}` is `Int.fract x`.

## Proofs

* Lemma \ref{KR:lem:rot} is proved without Weyl's equidistribution theorem (which is not in
  Mathlib): by Dirichlet's approximation theorem there is `q ≥ 1` with `s = qα - p` small and
  nonzero; with `K = ⌊1/|s|⌋`, an arithmetic progression `x + i s` (`i < K`) meets an interval
  `[a, b)` modulo `1` in `(b - a) K + O(1)` points (`count_AP`, via the identity
  `1[{y} ∈ [a, b)] = ⌊y - a⌋ - ⌊y - b⌋`), so every block `[m, m + qK)` meets it in
  `(b - a) q K + O(q)` points (`rot_superblock`), and long windows are unions of such blocks
  (`S_window`).
* In part (b) the convergent subsequence of `bα mod 1` is replaced by the pigeonhole principle:
  infinitely many `b ∈ B` have `{bα}` in a common interval of length `< η/2`.
* The upper bounds in Corollary \ref{KR:cor:main} (`sup ≤ 1/2`, `sup ≤ 3/4`) are Theorems 1.3 and
  1.2 of Kousek and Radić and are not formalized here.
-/

open Finset Filter Topology

noncomputable section

namespace Kmrr25.KR52

/-! ## Counting an arithmetic progression with small step in an interval mod `1` -/

/-- The indicator `1[{y} ∈ [a, b)]`, as a real number. -/
def ind (a b y : ℝ) : ℝ := by
  classical
  exact if Int.fract y ∈ Set.Ico a b then 1 else 0

lemma ind_nonneg (a b y : ℝ) : 0 ≤ ind a b y := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (a b y : ℝ) : ind a b y ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma ind_add_int (a b y : ℝ) (n : ℤ) : ind a b (y + n) = ind a b y := by
  simp only [ind, Int.fract_add_intCast]

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

/-- `P K s u = Σ_{i<K} ⌊u + i s⌋`. -/
def P (K : ℕ) (s u : ℝ) : ℤ := ∑ i ∈ range K, ⌊u + i * s⌋

lemma P_mono (K : ℕ) (s : ℝ) {u v : ℝ} (h : u ≤ v) : P K s u ≤ P K s v :=
  sum_le_sum fun i _ => Int.floor_mono (by linarith)

lemma P_add_one (K : ℕ) (s u : ℝ) : P K s (u + 1) = P K s u + K := by
  simp only [P]
  rw [show ((K : ℤ)) = ∑ i ∈ range K, (1 : ℤ) by simp, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [show u + 1 + i * s = (u + i * s) + 1 by ring, Int.floor_add_one]

lemma P_step {K : ℕ} {s : ℝ} (hK : K * s ≤ 1) (u : ℝ) : P K s (u + s) ≤ P K s u + 1 := by
  have h : P K s (u + s) - P K s u = ⌊u + K * s⌋ - ⌊u⌋ := by
    have := Finset.sum_range_sub (fun i : ℕ => ⌊u + i * s⌋) K
    simp only [Nat.cast_zero, zero_mul, add_zero] at this
    rw [← this, P, P, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    push_cast
    rw [show u + s + i * s = u + (i + 1) * s by ring]
  have h2 : ⌊u + K * s⌋ ≤ ⌊u⌋ + 1 := by
    rw [← Int.floor_add_one]; exact Int.floor_mono (by linarith)
  linarith

lemma P_add_nsmul {K : ℕ} {s : ℝ} (hK : K * s ≤ 1) (u : ℝ) (m : ℕ) :
    P K s (u + m * s) ≤ P K s u + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have := P_step hK (u + m * s)
    rw [show u + m * s + s = u + ((m + 1 : ℕ) : ℝ) * s by push_cast; ring] at this
    push_cast at this ⊢
    linarith

lemma P_sub_le {K : ℕ} {s : ℝ} (hs : 0 < s) (hK : K * s ≤ 1) {u v : ℝ} (h : v ≤ u) :
    ((P K s u - P K s v : ℤ) : ℝ) ≤ (u - v) / s + 1 := by
  set m := ⌈(u - v) / s⌉₊ with hm
  have h0 : 0 ≤ (u - v) / s := div_nonneg (by linarith) hs.le
  have h1 : (u - v) / s ≤ m := Nat.le_ceil _
  have h2 : (m : ℝ) < (u - v) / s + 1 := Nat.ceil_lt_add_one h0
  have h3 : u ≤ v + m * s := by
    rw [div_le_iff₀ hs] at h1; linarith
  have h4 := (P_mono K s h3).trans (P_add_nsmul hK v m)
  have h5 : ((P K s u : ℤ) : ℝ) ≤ P K s v + m := by exact_mod_cast h4
  push_cast
  linarith

lemma P_sub_ge {K : ℕ} {s : ℝ} (hs : 0 < s) (hK : K * s ≤ 1) (hK' : 1 < (K + 1) * s)
    {u v : ℝ} (h1 : u ≤ v + 1) :
    (u - v) / s - 2 ≤ ((P K s u - P K s v : ℤ) : ℝ) := by
  have h2 := P_sub_le hs hK h1
  rw [P_add_one] at h2
  push_cast at h2 ⊢
  have h3 : 1 / s < K + 1 := by rw [div_lt_iff₀ hs]; linarith
  have e : (v + 1 - u) / s = 1 / s - (u - v) / s := by ring
  rw [e] at h2
  linarith

/-- An arithmetic progression `x + i s` (`i < K`) with step `0 < s`, `K s ≤ 1 < (K + 1) s`,
meets every interval `[a, b) ⊆ [0, 1]` modulo `1` in `(b - a) K + O(1)` points. -/
lemma count_AP_pos {K : ℕ} {s : ℝ} (hs : 0 < s) (hK : K * s ≤ 1) (hK' : 1 < (K + 1) * s)
    (x : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |∑ i ∈ range K, ind a b (x + i * s) - (b - a) * K| ≤ 2 := by
  have e : ∑ i ∈ range K, ind a b (x + i * s) = ((P K s (x - a) - P K s (x - b) : ℤ) : ℝ) := by
    simp only [P, ind_eq_floor ha hab hb]
    push_cast
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [show x + i * s - a = x - a + i * s by ring, show x + i * s - b = x - b + i * s by ring]
  rw [e]
  have hup := P_sub_le hs hK (show x - b ≤ x - a by linarith)
  have hlo := P_sub_ge hs hK hK' (u := x - a) (v := x - b) (by linarith)
  have e2 : x - a - (x - b) = b - a := by ring
  rw [e2] at hup hlo
  have h3 : (b - a) * K ≤ (b - a) / s := by
    rw [le_div_iff₀ hs]; nlinarith
  have h4 : (b - a) / s ≤ (b - a) * K + 1 := by
    rw [div_le_iff₀ hs]; nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- The same count for a step `s ≠ 0` of either sign, with `K |s| ≤ 1 < (K + 1) |s|`. -/
lemma count_AP {K : ℕ} {s : ℝ} (hs : s ≠ 0) (hK : K * |s| ≤ 1) (hK' : 1 < (K + 1) * |s|)
    (x : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |∑ i ∈ range K, ind a b (x + i * s) - (b - a) * K| ≤ 2 := by
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · rw [abs_of_neg hneg] at hK hK'
    have h := count_AP_pos (neg_pos.2 hneg) hK hK' (x + (K - 1) * s) ha hab hb
    have e : ∑ i ∈ range K, ind a b (x + ((K : ℝ) - 1) * s + i * -s) =
        ∑ i ∈ range K, ind a b (x + i * s) := by
      rw [← Finset.sum_range_reflect]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.1 hj
      have e1 : K - 1 - j + j + 1 = K := by omega
      have e2 : ((K - 1 - j : ℕ) : ℝ) + j + 1 = K := by exact_mod_cast e1
      congr 1
      have : ((K - 1 - j : ℕ) : ℝ) = K - 1 - j := by linarith
      rw [this]
      ring
    rwa [e] at h
  · rw [abs_of_pos hpos] at hK hK'
    exact count_AP_pos hpos hK hK' x ha hab hb

/-! ## Windows and blocks -/

/-- The window sum `S f M H = Σ_{0 ≤ n < H} f (M + n) = Σ_{M ≤ n < M + H} f n`. -/
def S (f : ℕ → ℝ) (M H : ℕ) : ℝ := ∑ n ∈ range H, f (M + n)

lemma S_add (f : ℕ → ℝ) (M H₁ H₂ : ℕ) : S f M (H₁ + H₂) = S f M H₁ + S f (M + H₁) H₂ := by
  simp only [S, sum_range_add, add_assoc]

lemma S_bounds {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 1) (M H : ℕ) :
    0 ≤ S f M H ∧ S f M H ≤ H := by
  refine ⟨sum_nonneg fun n _ => (hf _).1, ?_⟩
  have := sum_le_sum fun n (_ : n ∈ range H) => (hf (M + n)).2
  simpa [S] using this

lemma S_blocks {f : ℕ → ℝ} {c e : ℝ} {L m₀ : ℕ}
    (hblock : ∀ m, m₀ ≤ m → |S f m L - c * L| ≤ e * L) (k : ℕ) :
    ∀ m, m₀ ≤ m → |S f m (k * L) - c * (k * L)| ≤ k * (e * L) := by
  induction k with
  | zero => intro m _; simp [S]
  | succ k ih =>
    intro m hm
    rw [show (k + 1) * L = k * L + L by ring, S_add]
    have h1 := ih m hm
    have h2 := hblock (m + k * L) (by omega)
    rw [show S f m (k * L) + S f (m + k * L) L - c * (((k + 1 : ℕ) : ℝ) * L) =
        (S f m (k * L) - c * (k * L)) + (S f (m + k * L) L - c * L) by push_cast; ring]
    calc _ ≤ |S f m (k * L) - c * (k * L)| + |S f (m + k * L) L - c * L| :=
          abs_add_le _ _
      _ ≤ k * (e * L) + e * L := add_le_add h1 h2
      _ = ((k + 1 : ℕ) : ℝ) * (e * L) := by push_cast; ring

/-- Uniformity on blocks of a fixed length `L` (from a point `m₀` on) gives uniformity on all
long windows: if `0 ≤ f ≤ 1`, `0 ≤ c ≤ 1` and `|S f m L - c L| ≤ e L` for all `m ≥ m₀`, then
`|S f M H - c H| ≤ e H + L + m₀` for all `M` and all `H ≥ m₀`. -/
lemma S_window {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 1) {c e : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (he : 0 ≤ e) {L m₀ : ℕ} (hL : 0 < L)
    (hblock : ∀ m, m₀ ≤ m → |S f m L - c * L| ≤ e * L) (M H : ℕ) (hH : m₀ ≤ H) :
    |S f M H - c * H| ≤ e * H + L + m₀ := by
  obtain ⟨H', rfl⟩ : ∃ H', H = m₀ + H' := ⟨H - m₀, by omega⟩
  have hdm := Nat.div_add_mod H' L
  set k := H' / L
  set r := H' % L
  have hr : r < L := Nat.mod_lt _ hL
  rw [← hdm, S_add, S_add]
  have h1 := S_bounds hf M m₀
  have h3 := S_bounds hf (M + m₀ + L * k) r
  have h2 := S_blocks hblock k (M + m₀) (by omega)
  rw [show k * L = L * k by ring] at h2
  have hrL : (r : ℝ) ≤ L := by exact_mod_cast hr.le
  have hkL : ((L * k : ℕ) : ℝ) ≤ ((m₀ + (L * k + r) : ℕ) : ℝ) := by
    exact_mod_cast (show L * k ≤ m₀ + (L * k + r) by omega)
  have hkL' : (k : ℝ) * (e * L) = e * ((L * k : ℕ) : ℝ) := by push_cast; ring
  rw [hkL'] at h2
  have h4 : e * ((L * k : ℕ) : ℝ) ≤ e * ((m₀ + (L * k + r) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hkL he
  have hab := abs_le.1 h2
  have hc' : c * (m₀ : ℝ) ≤ m₀ := by nlinarith [(Nat.cast_nonneg m₀ : (0 : ℝ) ≤ m₀)]
  have hcr : c * (r : ℝ) ≤ r := by nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hc'' : 0 ≤ c * (m₀ : ℝ) := by positivity
  have hcr' : 0 ≤ c * (r : ℝ) := by positivity
  rw [abs_le]
  push_cast at hab h1 h3 h4 ⊢
  constructor <;> nlinarith

/-- Splitting `[0, qK)` into the `q` residue classes modulo `q`. -/
lemma sum_range_mul (g : ℕ → ℝ) (q K : ℕ) :
    ∑ j ∈ range (q * K), g j = ∑ r ∈ range q, ∑ i ∈ range K, g (r + i * q) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show q * (K + 1) = q * K + q by ring, sum_range_add, ih]
    simp only [sum_range_succ, sum_add_distrib]
    congr 1
    refine sum_congr rfl fun r _ => ?_
    rw [add_comm (q * K) r, mul_comm q K]

/-- A super-block `[0, qK)` of the rotation by `α`, where `s = qα - p` and
`K |s| ≤ 1 < (K + 1) |s|`, meets each interval `[a, b) ⊆ [0, 1]` modulo `1` in
`(b - a) q K + O(q)` points, uniformly in the phase `γ`. -/
lemma rot_superblock {α : ℝ} {q : ℕ} {p : ℤ} {s : ℝ} (hs : s = q * α - p) (hs0 : s ≠ 0)
    {K : ℕ} (hK : K * |s| ≤ 1) (hK' : 1 < (K + 1) * |s|) (γ : ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    |∑ j ∈ range (q * K), ind a b (j * α + γ) - (b - a) * (q * K)| ≤ 2 * q := by
  rw [sum_range_mul]
  have hinner : ∀ r ∈ range q, ∑ i ∈ range K, ind a b (((r + i * q : ℕ) : ℝ) * α + γ) =
      ∑ i ∈ range K, ind a b ((r * α + γ) + i * s) := by
    intro r _
    refine sum_congr rfl fun i _ => ?_
    rw [← ind_add_int a b (r * α + γ + i * s) (i * p)]
    congr 1
    rw [hs]
    push_cast
    ring
  rw [sum_congr rfl hinner]
  have e : (b - a) * ((q : ℝ) * K) = ∑ r ∈ range q, (b - a) * K := by
    rw [sum_const, card_range, nsmul_eq_mul]; ring
  rw [e, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ r ∈ range q, (2 : ℝ) :=
        sum_le_sum fun r _ => count_AP hs0 hK hK' _ ha hab hb
    _ = 2 * q := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-! ## Lemma \ref{KR:lem:rot}: uniform distribution of an irrational rotation -/

/-- Paper, Lemma \ref{KR:lem:rot}, in `ε`-form: for irrational `α`, the number of
`0 ≤ j < L` with `{jα + γ} ∈ [a, b)` is `(b - a) L + o(L)`, uniformly in `γ ∈ ℝ` and
`0 ≤ a ≤ b ≤ 1`. -/
theorem rot_uniform {α : ℝ} (hα : Irrational α) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → ∀ γ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      |∑ j ∈ range L, ind a b (j * α + γ) - (b - a) * L| ≤ ε * L := by
  set n : ℕ := ⌈4 / ε⌉₊ + 1 with hn
  have hn0 : 0 < n := by omega
  have hn4 : 4 / ε < n := by
    rw [hn]; push_cast; linarith [Nat.le_ceil (4 / ε)]
  obtain ⟨q, hq, -, hqs⟩ := Real.exists_nat_abs_mul_sub_round_le α hn0
  set s : ℝ := q * α - round ((q : ℝ) * α) with hs
  have hs0 : s ≠ 0 := by
    intro h
    exact (hα.natCast_mul hq.ne').ne_int (round ((q : ℝ) * α)) (by linarith)
  have hsabs : 0 < |s| := abs_pos.2 hs0
  set K : ℕ := ⌊1 / |s|⌋₊ with hKdef
  have hK1 : (K : ℝ) ≤ 1 / |s| := Nat.floor_le (by positivity)
  have hK2 : 1 / |s| < K + 1 := Nat.lt_floor_add_one _
  have hK : K * |s| ≤ 1 := by rwa [le_div_iff₀ hsabs] at hK1
  have hK' : 1 < (K + 1) * |s| := by rwa [div_lt_iff₀ hsabs] at hK2
  have hKn : (n : ℝ) + 1 ≤ 1 / |s| := by
    rw [le_div_iff₀ hsabs]
    rw [le_div_iff₀ (by positivity)] at hqs
    linarith
  have hKn' : (n : ℝ) ≤ K := by
    have : n + 1 ≤ ⌊1 / |s|⌋₊ + 1 := by
      have := Nat.le_floor (show ((n + 1 : ℕ) : ℝ) ≤ 1 / |s| by push_cast; exact hKn)
      omega
    have : n ≤ K := by omega
    exact_mod_cast this
  have hεK : 4 ≤ ε * K := by
    have := (div_lt_iff₀ hε).1 hn4
    nlinarith
  have hKpos : 0 < K := by
    have : (0 : ℝ) < K := by nlinarith
    exact_mod_cast this
  set Lb := q * K with hLb
  have hLb0 : 0 < Lb := Nat.mul_pos hq hKpos
  refine ⟨⌈2 * Lb / ε⌉₊, fun L hL γ a b ha hab hb => ?_⟩
  set f : ℕ → ℝ := fun j => ind a b (j * α + γ) with hf
  have hf01 : ∀ j, 0 ≤ f j ∧ f j ≤ 1 := fun j => ⟨ind_nonneg _ _ _, ind_le_one _ _ _⟩
  have hblock : ∀ m, 0 ≤ m → |S f m Lb - (b - a) * Lb| ≤ ε / 2 * Lb := by
    intro m _
    have h := rot_superblock (α := α) (q := q) (p := round ((q : ℝ) * α)) hs hs0 hK hK'
      (γ + m * α) ha hab hb
    have e : S f m Lb = ∑ j ∈ range (q * K), ind a b (j * α + (γ + m * α)) := by
      simp only [S, hf]
      refine sum_congr rfl fun j _ => ?_
      push_cast; ring_nf
    rw [e, hLb]
    push_cast
    refine h.trans ?_
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    nlinarith
  have hw := S_window hf01 (sub_nonneg.2 hab) (by linarith) (by positivity) hLb0 hblock 0 L
    (Nat.zero_le _)
  have e : ∑ j ∈ range L, ind a b (j * α + γ) = S f 0 L := by simp [S, hf]
  rw [e]
  refine hw.trans ?_
  have hL' : 2 * Lb / ε ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast hL)
  rw [div_le_iff₀ hε] at hL'
  push_cast
  linarith

/-- The discrepancy
`D_L = sup_{γ ∈ ℝ} sup_{0 ≤ a ≤ b ≤ 1} (1/L) |#{0 ≤ j < L : {jα + γ} ∈ [a, b)} - (b - a) L|`. -/
def discrepancy (α : ℝ) (L : ℕ) : ℝ := by
  classical
  exact ⨆ (γ : ℝ) (a : ℝ) (b : ℝ) (_ : 0 ≤ a ∧ a ≤ b ∧ b ≤ 1),
    |((((range L).filter fun j : ℕ => Int.fract ((j : ℝ) * α + γ) ∈ Set.Ico a b).card : ℕ) : ℝ) -
      (b - a) * L| / L

/-- Paper, Lemma \ref{KR:lem:rot}: for irrational `α`, `D_L → 0` as `L → ∞`. -/
theorem lem_rot {α : ℝ} (hα : Irrational α) : Tendsto (discrepancy α) atTop (𝓝 0) := by
  have key : ∀ ε > 0, ∀ᶠ L in atTop, discrepancy α L ≤ ε := by
    intro ε hε
    obtain ⟨L₀, hL₀⟩ := rot_uniform hα hε
    filter_upwards [eventually_ge_atTop (max L₀ 1)] with L hL
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    unfold discrepancy
    refine Real.iSup_le (fun γ => Real.iSup_le (fun a => Real.iSup_le (fun b =>
      Real.iSup_le (fun h => ?_) hε.le) hε.le) hε.le) hε.le
    rw [div_le_iff₀ hLpos]
    have hc := hL₀ L (le_of_max_le_left hL) γ a b h.1 h.2.1 h.2.2
    have e : ((((range L).filter fun j : ℕ => Int.fract ((j : ℝ) * α + γ) ∈ Set.Ico a b).card : ℕ) : ℝ) =
        ∑ j ∈ range L, ind a b (j * α + γ) := by
      rw [card_filter]; push_cast; rfl
    rw [e]
    exact hc
  have hnn : ∀ L, 0 ≤ discrepancy α L := fun L => by
    unfold discrepancy
    exact Real.iSup_nonneg fun γ => Real.iSup_nonneg fun a => Real.iSup_nonneg fun b =>
      Real.iSup_nonneg fun _ => by positivity
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun L => lt_of_lt_of_le ha (hnn L), fun a ha => ?_⟩
  filter_upwards [key (a / 2) (by positivity)] with L hL
  linarith

/-! ## The sets `E` and `A'` -/

/-- `φ(n) = n α - κ log n`. -/
def φ (α κ : ℝ) (n : ℕ) : ℝ := n * α - κ * Real.log n

/-- `E = {n ∈ ℕ : {φ(n)} ∈ [0, c)}`, where `c = 1/2 - 2δ` and `ℕ = {1, 2, …}`. -/
def E (α κ δ : ℝ) : Set ℕ := {n | 0 < n ∧ Int.fract (φ α κ n) ∈ Set.Ico 0 (1 / 2 - 2 * δ)}

/-- `A' = (2ℕ - 1) ∪ 2E`: the odd positive integers together with the numbers `2m`, `m ∈ E`. -/
def A' (α κ δ : ℝ) : Set ℕ := {n | Odd n} ∪ {n | ∃ m ∈ E α κ δ, n = 2 * m}

lemma pos_of_mem_E {α κ δ : ℝ} {n : ℕ} (h : n ∈ E α κ δ) : 0 < n := h.1

lemma pos_of_mem_A' {α κ δ : ℝ} {n : ℕ} (h : n ∈ A' α κ δ) : 0 < n := by
  rcases h with ⟨k, rfl⟩ | ⟨m, hm, rfl⟩
  · omega
  · have := hm.1; omega

/-- The indicator function of `A ⊆ ℕ`, as a real function. -/
def indN (A : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ A then 1 else 0

lemma indN_bounds (A : Set ℕ) (n : ℕ) : 0 ≤ indN A n ∧ indN A n ≤ 1 := by
  unfold indN; split_ifs <;> norm_num

/-- `|A ∩ [M, M + H)| = Σ_{M ≤ n < M + H} 1_A(n)`. -/
lemma ncard_Ico_eq_S (A : Set ℕ) (M H : ℕ) :
    ((A ∩ Set.Ico M (M + H)).ncard : ℝ) = S (indN A) M H := by
  classical
  have e : A ∩ Set.Ico M (M + H) = ↑((Finset.Ico M (M + H)).filter (· ∈ A)) := by
    ext n; simp [and_comm]
  rw [e, Set.ncard_coe_finset, card_filter, Finset.sum_Ico_eq_sum_range,
    show M + H - M = H by omega]
  push_cast
  rfl

/-- `fract (w + e) = fract w + e` when `0 ≤ fract w + e < 1`. -/
lemma fract_add_eq {w e : ℝ} (h0 : 0 ≤ Int.fract w + e) (h1 : Int.fract w + e < 1) :
    Int.fract (w + e) = Int.fract w + e :=
  Int.fract_eq_iff.2 ⟨h0, h1, ⌊w⌋, by rw [← Int.self_sub_fract]; ring⟩

/-- For `0 ≤ η < e` and `c + e ≤ 1`:
`{y} ∈ [e, c) ⟹ {y - η} ∈ [0, c) ⟹ {y} ∈ [0, c + e)`. -/
lemma fract_sandwich {y η e c : ℝ} (hη0 : 0 ≤ η) (hηe : η < e) (hce : c + e ≤ 1) :
    (Int.fract y ∈ Set.Ico e c → Int.fract (y - η) ∈ Set.Ico 0 c) ∧
      (Int.fract (y - η) ∈ Set.Ico 0 c → Int.fract y ∈ Set.Ico 0 (c + e)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have := Int.fract_lt_one y
    rw [sub_eq_add_neg, fract_add_eq (by linarith) (by linarith)]
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have e1 : y = (y - η) + η := by ring
    rw [e1, fract_add_eq (by linarith) (by linarith)]
    constructor <;> linarith

lemma ite_le_ite_of_imp {P Q : Prop} [Decidable P] [Decidable Q] (h : P → Q) :
    (if P then (1 : ℝ) else 0) ≤ if Q then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos hP, if_pos (h hP)]
  · rw [if_neg hP]; split_ifs <;> norm_num

/-! ## Theorem \ref{KR:thm:main}(a): uniform density -/

/-- Uniform density of `E` (window-sum form). -/
lemma E_uniform_S {α κ δ : ℝ} (hα : Irrational α) (hκ : 0 < κ) (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℕ, ∀ M H : ℕ, H₀ ≤ H →
      |S (indN (E α κ δ)) M H - (1 / 2 - 2 * δ) * H| ≤ ε * H := by
  classical
  set c := 1 / 2 - 2 * δ with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hc1 : c < 1 / 2 := by rw [hc]; linarith
  set e := min ε c / 4 with he
  have he0 : 0 < e := by rw [he]; exact div_pos (lt_min hε hc0) (by norm_num)
  have hec : e ≤ c := by rw [he]; linarith [min_le_right ε c]
  have heε : e ≤ ε / 4 := by rw [he]; linarith [min_le_left ε c]
  have hce : c + e ≤ 1 := by linarith
  obtain ⟨L₀, hL₀⟩ := rot_uniform hα he0
  set L := max L₀ 1 with hLdef
  have hL : 0 < L := by omega
  set m₀ := ⌈κ * L / e⌉₊ + 1 with hm₀
  set f := indN (E α κ δ) with hf
  have hblock : ∀ m, m₀ ≤ m → |S f m L - c * L| ≤ (2 * e) * L := by
    intro m hm
    set γ := m * α - κ * Real.log m with hγ
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmκ : κ * L < e * m := by
      have h1 : κ * L / e < m := by
        have := Nat.le_ceil (κ * L / e)
        have h2 : ((⌈κ * L / e⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
        push_cast at h2
        linarith
      rwa [div_lt_iff₀ he0, mul_comm (m : ℝ) e] at h1
    have hpt : ∀ j ∈ range L, ind e c (j * α + γ) ≤ f (m + j) ∧
        f (m + j) ≤ ind 0 (c + e) (j * α + γ) := by
      intro j hj
      have hjL : (j : ℝ) ≤ L := by exact_mod_cast (mem_range.1 hj).le
      set η := κ * (Real.log ((m : ℝ) + j) - Real.log m) with hη
      have hmj : (0 : ℝ) < m + j := by positivity
      have hlog : Real.log ((m : ℝ) + j) - Real.log m ≤ j / m := by
        rw [← Real.log_div hmj.ne' hm0.ne']
        have := Real.log_le_sub_one_of_pos (div_pos hmj hm0)
        have e1 : ((m : ℝ) + j) / m - 1 = j / m := by field_simp; ring
        linarith
      have hη0 : 0 ≤ η :=
        mul_nonneg hκ.le (sub_nonneg.2 (Real.log_le_log hm0 (by linarith)))
      have hηe : η < e := by
        have h1 : η ≤ κ * (j / m) := mul_le_mul_of_nonneg_left hlog hκ.le
        have h2 : κ * (j / m) ≤ κ * L / m := by
          rw [mul_div_assoc']
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hjL hκ.le) hm0.le
        have h3 : κ * L / m < e := by rw [div_lt_iff₀ hm0]; linarith
        linarith
      have hφ : φ α κ (m + j) = (j * α + γ) - η := by
        simp only [φ, hγ, hη]; push_cast; ring
      have hmemE : (m + j) ∈ E α κ δ ↔ Int.fract (φ α κ (m + j)) ∈ Set.Ico 0 c :=
        ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      obtain ⟨s1, s2⟩ := fract_sandwich (y := j * α + γ) hη0 hηe hce
      rw [hφ] at hmemE
      constructor
      · simp only [ind, hf, indN]
        exact ite_le_ite_of_imp fun h => hmemE.2 (s1 h)
      · simp only [ind, hf, indN]
        exact ite_le_ite_of_imp fun h => s2 (hmemE.1 h)
    have hlo := hL₀ L (le_max_left _ _) γ e c he0.le hec (by linarith)
    have hhi := hL₀ L (le_max_left _ _) γ 0 (c + e) le_rfl (by linarith) hce
    have hS : S f m L = ∑ j ∈ range L, f (m + j) := rfl
    have hsum1 : ∑ j ∈ range L, ind e c (j * α + γ) ≤ S f m L := by
      rw [hS]; exact sum_le_sum fun j hj => (hpt j hj).1
    have hsum2 : S f m L ≤ ∑ j ∈ range L, ind 0 (c + e) (j * α + γ) := by
      rw [hS]; exact sum_le_sum fun j hj => (hpt j hj).2
    rw [abs_le] at hlo hhi ⊢
    constructor <;> linarith [hlo.1, hlo.2, hhi.1, hhi.2]
  refine ⟨max m₀ ⌈2 * (L + m₀) / ε⌉₊, fun M H hH => ?_⟩
  have hw := S_window (indN_bounds _) hc0.le (by linarith) (by positivity : (0 : ℝ) ≤ 2 * e) hL
    hblock M H (le_of_max_le_left hH)
  have hH2 : 2 * ((L : ℝ) + m₀) / ε ≤ H :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hH)
  rw [div_le_iff₀ hε] at hH2
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have : 2 * e * H ≤ ε / 2 * H := by nlinarith
  linarith

lemma indA'_odd (α κ δ : ℝ) (k : ℕ) : indN (A' α κ δ) (2 * k + 1) = 1 := by
  unfold indN
  rw [if_pos (show 2 * k + 1 ∈ A' α κ δ from Or.inl (odd_two_mul_add_one k))]

lemma indA'_even (α κ δ : ℝ) (k : ℕ) : indN (A' α κ δ) (2 * k) = indN (E α κ δ) k := by
  have h : 2 * k ∈ A' α κ δ ↔ k ∈ E α κ δ := by
    constructor
    · rintro (⟨r, hr⟩ | ⟨m, hm, hm2⟩)
      · omega
      · have : m = k := by omega
        rwa [← this]
    · intro hk
      exact Or.inr ⟨k, hk, rfl⟩
  unfold indN
  by_cases hk : k ∈ E α κ δ
  · rw [if_pos hk, if_pos (h.2 hk)]
  · rw [if_neg hk, if_neg (fun h' => hk (h.1 h'))]

lemma S_two (f : ℕ → ℝ) (x : ℕ) : S f x 2 = f x + f (x + 1) := by
  simp [S, sum_range_succ]

lemma S_one (f : ℕ → ℝ) (x : ℕ) : S f x 1 = f x := by
  simp [S]

lemma S_A'_even (α κ δ : ℝ) (m L : ℕ) :
    S (indN (A' α κ δ)) (2 * m) (2 * L) = L + S (indN (E α κ δ)) m L := by
  induction L with
  | zero => simp [S]
  | succ L ih =>
    rw [show 2 * (L + 1) = 2 * L + 2 by ring, S_add, ih, S_two, S_add, S_one,
      show 2 * m + 2 * L = 2 * (m + L) by ring, indA'_even, indA'_odd]
    push_cast
    ring

lemma S_A'_any (α κ δ : ℝ) (M L : ℕ) :
    |S (indN (A' α κ δ)) M (2 * L) - (L + S (indN (E α κ δ)) (M / 2) L)| ≤ 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' M
  · rw [show 2 * m / 2 = m by omega, S_A'_even]
    simp
  · rw [show (2 * m + 1) / 2 = m by omega, ← S_A'_even]
    have h1 := S_add (indN (A' α κ δ)) (2 * m) 1 (2 * L)
    have h2 := S_add (indN (A' α κ δ)) (2 * m) (2 * L) 1
    rw [show 1 + 2 * L = 2 * L + 1 by ring, S_one] at h1
    rw [S_one] at h2
    have b1 := indN_bounds (A' α κ δ) (2 * m)
    have b2 := indN_bounds (A' α κ δ) (2 * m + 2 * L)
    rw [abs_le]
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]

/-- Uniform density of `A'` (window-sum form). -/
lemma A'_uniform_S {α κ δ : ℝ} (hα : Irrational α) (hκ : 0 < κ) (hδ : 0 < δ)
    (hδ' : δ < 1 / 4) {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℕ, ∀ M H : ℕ, H₀ ≤ H → |S (indN (A' α κ δ)) M H - (3 / 4 - δ) * H| ≤ ε * H := by
  obtain ⟨H₀, hH₀⟩ := E_uniform_S hα hκ hδ hδ' (ε := ε / 8) (by positivity)
  set L := max H₀ (⌈8 / ε⌉₊ + 1) with hLdef
  have hL : 0 < L := by omega
  have hL8 : 8 / ε ≤ L := by
    have := Nat.le_ceil (8 / ε)
    have h2 : ((⌈8 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast le_max_right H₀ _
    push_cast at h2
    linarith
  rw [div_le_iff₀ hε] at hL8
  have hblock : ∀ m, 0 ≤ m → |S (indN (A' α κ δ)) m (2 * L) - (3 / 4 - δ) * ((2 * L : ℕ) : ℝ)|
      ≤ ε / 8 * ((2 * L : ℕ) : ℝ) := by
    intro m _
    have h1 := S_A'_any α κ δ m L
    have h2 := hH₀ (m / 2) L (le_max_left _ _)
    rw [abs_le] at h1 h2 ⊢
    push_cast
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  refine ⟨⌈4 * (2 * L) / ε⌉₊, fun M H hH => ?_⟩
  have hw := S_window (indN_bounds _) (c := 3 / 4 - δ) (by linarith) (by linarith)
    (by positivity : (0 : ℝ) ≤ ε / 8) (by omega : 0 < 2 * L) hblock M H (Nat.zero_le _)
  have hH2 : 4 * (2 * (L : ℝ)) / ε ≤ H :=
    (Nat.le_ceil _).trans (by exact_mod_cast hH)
  rw [div_le_iff₀ hε] at hH2
  push_cast at hw
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have : ε / 8 * H ≤ ε / 2 * H := by nlinarith
  linarith

/-! ## Banach densities -/

/-- The filter on pairs `(M, N) ∈ ℕ × ℕ` with `M ≥ 1` along which `N - M → ∞`. -/
def banachFilter : Filter (ℕ × ℕ) :=
  comap (fun p : ℕ × ℕ => p.2 - p.1) atTop ⊓ 𝓟 {p | 1 ≤ p.1}

instance banachFilter_neBot : banachFilter.NeBot := by
  rw [banachFilter, inf_principal_neBot_iff]
  intro U hU
  obtain ⟨t, ht, hsub⟩ := mem_comap.1 hU
  obtain ⟨a, ha⟩ := mem_atTop_sets.1 ht
  exact ⟨(1, a + 1), hsub (ha _ (by simp)), by simp⟩

/-- The ratio `|A ∩ [M, N]| / (N - M)`, with the normalisation of Kousek and Radić. -/
def banachRatio (A : Set ℕ) (p : ℕ × ℕ) : ℝ :=
  ((A ∩ Set.Icc p.1 p.2).ncard : ℝ) / ((p.2 : ℝ) - p.1)

/-- The lower Banach density `d_*(A) = liminf_{N - M → ∞} |A ∩ [M, N]| / (N - M)`. -/
def lowerBanachDensity (A : Set ℕ) : ℝ := liminf (banachRatio A) banachFilter

/-- The upper Banach density `d^*(A) = limsup_{N - M → ∞} |A ∩ [M, N]| / (N - M)`. -/
def upperBanachDensity (A : Set ℕ) : ℝ := limsup (banachRatio A) banachFilter

/-- A set of uniform density `c` has `|A ∩ [M, N]| / (N - M) → c` as `N - M → ∞`. -/
lemma tendsto_banachRatio {A : Set ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu : ∀ ε > 0, ∃ H₀ : ℕ, ∀ M H : ℕ, H₀ ≤ H → |S (indN A) M H - c * H| ≤ ε * H) :
    Tendsto (banachRatio A) banachFilter (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨H₀, hH₀⟩ := hu (ε / 4) (by positivity)
  set T := max H₀ (⌈4 / ε⌉₊ + 1) with hT
  have hev : ∀ᶠ p in banachFilter, T ≤ p.2 - p.1 :=
    ((eventually_ge_atTop T).comap _).filter_mono inf_le_left
  filter_upwards [hev] with p hp
  obtain ⟨M, N⟩ := p
  simp only at hp
  have hT1 : 1 ≤ T := by omega
  obtain ⟨h, rfl⟩ : ∃ h, N = M + h := ⟨N - M, by omega⟩
  rw [Nat.add_sub_cancel_left] at hp
  have hNM : ((M + h : ℕ) : ℝ) - M = (h : ℝ) := by push_cast; ring
  have hcount : A ∩ Set.Icc M (M + h) = A ∩ Set.Ico M (M + (h + 1)) := by
    ext n; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, h2, by omega⟩
  rw [banachRatio]
  simp only
  rw [hNM, hcount, ncard_Ico_eq_S]
  have hb := hH₀ M (h + 1) (by omega)
  have hh4 : 4 / ε < h := by
    have := Nat.le_ceil (4 / ε)
    have h2 : ((⌈4 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast (le_max_right H₀ _).trans hp
    push_cast at h2
    linarith
  rw [div_lt_iff₀ hε] at hh4
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hpos : (0 : ℝ) < h := by linarith
  rw [Real.dist_eq, show S (indN A) M (h + 1) / h - c = (S (indN A) M (h + 1) - c * h) / h by
    field_simp, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
  push_cast at hb
  rw [abs_le] at hb
  rw [abs_lt]
  constructor <;> nlinarith [hb.1, hb.2]

/-- Paper, Theorem \ref{KR:thm:main}(a), uniform density of `E`: for every `ε > 0` there is
`H₀` with `| |E ∩ [M, M + H)| - c H | ≤ ε H` for all `M` and all `H ≥ H₀`, where
`c = 1/2 - 2δ`. -/
theorem E_uniform {α κ δ : ℝ} (hα : Irrational α) (hκ : 0 < κ) (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ∀ ε > 0, ∃ H₀ : ℕ, ∀ M H : ℕ, H₀ ≤ H →
      |((E α κ δ ∩ Set.Ico M (M + H)).ncard : ℝ) - (1 / 2 - 2 * δ) * H| ≤ ε * H := by
  intro ε hε
  obtain ⟨H₀, h⟩ := E_uniform_S hα hκ hδ hδ' hε
  exact ⟨H₀, fun M H hH => by rw [ncard_Ico_eq_S]; exact h M H hH⟩

/-- Paper, Theorem \ref{KR:thm:main}(a), uniform density of `A'`: for every `ε > 0` there is
`H₀` with `| |A' ∩ [M, M + H)| - (3/4 - δ) H | ≤ ε H` for all `M` and all `H ≥ H₀`. -/
theorem A'_uniform {α κ δ : ℝ} (hα : Irrational α) (hκ : 0 < κ) (hδ : 0 < δ)
    (hδ' : δ < 1 / 4) :
    ∀ ε > 0, ∃ H₀ : ℕ, ∀ M H : ℕ, H₀ ≤ H →
      |((A' α κ δ ∩ Set.Ico M (M + H)).ncard : ℝ) - (3 / 4 - δ) * H| ≤ ε * H := by
  intro ε hε
  obtain ⟨H₀, h⟩ := A'_uniform_S hα hκ hδ hδ' hε
  exact ⟨H₀, fun M H hH => by rw [ncard_Ico_eq_S]; exact h M H hH⟩

lemma tendsto_banachRatio_E {α κ δ : ℝ} (hα : Irrational α) (hκ : 0 < κ) (hδ : 0 < δ)
    (hδ' : δ < 1 / 4) :
    Tendsto (banachRatio (E α κ δ)) banachFilter (𝓝 (1 / 2 - 2 * δ)) :=
  tendsto_banachRatio (by linarith) (by linarith) fun _ hε => E_uniform_S hα hκ hδ hδ' hε

lemma tendsto_banachRatio_A' {α κ δ : ℝ} (hα : Irrational α) (hκ : 0 < κ) (hδ : 0 < δ)
    (hδ' : δ < 1 / 4) :
    Tendsto (banachRatio (A' α κ δ)) banachFilter (𝓝 (3 / 4 - δ)) :=
  tendsto_banachRatio (by linarith) (by linarith) fun _ hε => A'_uniform_S hα hκ hδ hδ' hε

/-- Paper, Theorem \ref{KR:thm:main}(a), "in particular": `d_*(E) = d^*(E) = 1/2 - 2δ` and
`d_*(A') = d^*(A') = 3/4 - δ`. -/
theorem banach_densities {α κ δ : ℝ} (hα : Irrational α) (hκ : 0 < κ) (hδ : 0 < δ)
    (hδ' : δ < 1 / 4) :
    lowerBanachDensity (E α κ δ) = 1 / 2 - 2 * δ ∧
      upperBanachDensity (E α κ δ) = 1 / 2 - 2 * δ ∧
      lowerBanachDensity (A' α κ δ) = 3 / 4 - δ ∧
      upperBanachDensity (A' α κ δ) = 3 / 4 - δ :=
  ⟨(tendsto_banachRatio_E hα hκ hδ hδ').liminf_eq,
    (tendsto_banachRatio_E hα hκ hδ hδ').limsup_eq,
    (tendsto_banachRatio_A' hα hκ hδ hδ').liminf_eq,
    (tendsto_banachRatio_A' hα hκ hδ hδ').limsup_eq⟩

/-! ## Theorem \ref{KR:thm:main}(b) and (c) -/

/-- `|log u - log v - log 2| ≤ |u - 2v| / v` for `0 < v ≤ u`. -/
lemma abs_log_sub_log_two_le {u v : ℝ} (hv : 0 < v) (huv : v ≤ u) :
    |Real.log u - Real.log v - Real.log 2| ≤ |u - 2 * v| / v := by
  have hu : 0 < u := lt_of_lt_of_le hv huv
  have hz : 0 < u / (2 * v) := by positivity
  have e : Real.log u - Real.log v - Real.log 2 = Real.log (u / (2 * v)) := by
    rw [Real.log_div hu.ne' (by positivity), Real.log_mul two_ne_zero hv.ne']; ring
  rw [e]
  have h1 := Real.log_le_sub_one_of_pos hz
  have h2 := Real.one_sub_inv_le_log_of_pos hz
  have e1 : u / (2 * v) - 1 = (u - 2 * v) / (2 * v) := by field_simp
  have e2 : 1 - (u / (2 * v))⁻¹ = (u - 2 * v) / u := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  have h3 : (u - 2 * v) / (2 * v) ≤ |u - 2 * v| / v := by
    rw [div_le_div_iff₀ (by positivity) hv]
    nlinarith [le_abs_self (u - 2 * v), abs_nonneg (u - 2 * v)]
  have h4 : -(|u - 2 * v| / v) ≤ (u - 2 * v) / u := by
    rw [neg_le, ← neg_div, div_le_div_iff₀ hu hv]
    nlinarith [neg_abs_le (u - 2 * v), abs_nonneg (u - 2 * v)]
  rw [abs_le]
  constructor <;> linarith

/-- Paper, Theorem \ref{KR:thm:main}(b). Let `κ log 2 ≡ 1/2 (mod 1)` and `δ > 0`. For every
`t ∈ ℤ` and every infinite `B ⊆ ℕ₀`, `B + B + t ⊄ E`: there are `b, b' ∈ B` such that
`b + b' + t` is not (the image in `ℤ` of) an element of `E`. -/
theorem no_BBt {α κ δ : ℝ} (hκ2 : ∃ k : ℤ, κ * Real.log 2 = 1 / 2 + k) (hδ : 0 < δ) (t : ℤ)
    {B : Set ℕ} (hB : B.Infinite) :
    ¬ ∀ b ∈ B, ∀ b' ∈ B, ∃ n ∈ E α κ δ, (n : ℤ) = b + b' + t := by
  intro hBB
  obtain ⟨k, hk⟩ := hκ2
  set η := 2 * δ with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  -- bins of width `1/N < η/2` for the fractional parts `{bα}`
  set N : ℕ := ⌈2 / η⌉₊ + 1 with hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hNη : 1 / (N : ℝ) < η / 2 := by
    rw [div_lt_iff₀ hN0]
    have := Nat.le_ceil (2 / η)
    have h2 : (2 / η) < N := by rw [hN]; push_cast; linarith
    rw [div_lt_iff₀ hη0] at h2
    linarith
  set bin : ℕ → ℕ := fun b => ⌊Int.fract (b * α) * N⌋₊ with hbin
  have hbinlt : ∀ b, bin b < N := by
    intro b
    rw [hbin]
    simp only
    rw [Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) hN0.le)]
    have := Int.fract_lt_one ((b : ℝ) * α)
    nlinarith
  have hbin_close : ∀ b b', bin b = bin b' →
      |Int.fract ((b : ℝ) * α) - Int.fract ((b' : ℝ) * α)| < η / 2 := by
    intro b b' hbb
    have h1 := Nat.floor_le (mul_nonneg (Int.fract_nonneg ((b : ℝ) * α)) hN0.le)
    have h2 := Nat.lt_floor_add_one (Int.fract ((b : ℝ) * α) * N)
    have h3 := Nat.floor_le (mul_nonneg (Int.fract_nonneg ((b' : ℝ) * α)) hN0.le)
    have h4 := Nat.lt_floor_add_one (Int.fract ((b' : ℝ) * α) * N)
    have hbb' : (⌊Int.fract ((b : ℝ) * α) * N⌋₊ : ℝ) = ⌊Int.fract ((b' : ℝ) * α) * N⌋₊ := by
      exact_mod_cast hbb
    have h5 : |Int.fract ((b : ℝ) * α) - Int.fract ((b' : ℝ) * α)| * N < 1 := by
      rw [show |Int.fract ((b : ℝ) * α) - Int.fract ((b' : ℝ) * α)| * N =
          |(Int.fract ((b : ℝ) * α) - Int.fract ((b' : ℝ) * α)) * N| by
        rw [abs_mul, abs_of_pos hN0], abs_lt, sub_mul]
      constructor <;> linarith
    have h6 : |Int.fract ((b : ℝ) * α) - Int.fract ((b' : ℝ) * α)| < 1 / N := by
      rw [lt_div_iff₀ hN0]; exact h5
    linarith
  -- a bin containing infinitely many elements of `B`
  obtain ⟨j, -, hj⟩ : ∃ j < N, {b ∈ B | bin b = j}.Infinite := by
    by_contra hcon
    push Not at hcon
    apply hB
    refine (Set.Finite.biUnion (Set.finite_lt_nat N) fun j hj => hcon j hj).subset ?_
    intro b hb
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨bin b, hbinlt b, hb, rfl⟩
  obtain ⟨b', ⟨hb'B, hb'j⟩⟩ := hj.nonempty
  set D : ℝ := 2 * (b' : ℝ) + t with hD
  set T : ℕ := ⌈2 * |κ| * |D| / η + |(t : ℝ)|⌉₊ + b' with hT
  obtain ⟨b, ⟨hbB, hbj⟩, hbT⟩ := hj.exists_gt T
  have hbT' : 2 * |κ| * |D| / η + |(t : ℝ)| < b - b' := by
    have := Nat.le_ceil (2 * |κ| * |D| / η + |(t : ℝ)|)
    have h2 : ((T : ℕ) : ℝ) < b := by exact_mod_cast hbT
    rw [hT] at h2
    push_cast at h2
    linarith
  have hbb' : (b' : ℝ) ≤ b := by
    have : b' ≤ b := by omega
    exact_mod_cast this
  -- the two elements `2b + t` and `b + b' + t` of `E`
  obtain ⟨n₁, hn₁E, hn₁⟩ := hBB b hbB b hbB
  obtain ⟨n₂, hn₂E, hn₂⟩ := hBB b hbB b' hb'B
  have hn₁R : (n₁ : ℝ) = 2 * b + t := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hn₁; push_cast at this; linarith
  have hn₂R : (n₂ : ℝ) = b + b' + t := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hn₂; push_cast at this; linarith
  have hn₂pos : (0 : ℝ) < n₂ := by exact_mod_cast hn₂E.1
  have hn₁₂ : (n₂ : ℝ) ≤ n₁ := by rw [hn₁R, hn₂R]; linarith
  -- the logarithmic error `r`
  set r := κ * (Real.log n₁ - Real.log n₂ - Real.log 2) with hr
  have hr_lt : |r| < η / 2 := by
    have h1 := abs_log_sub_log_two_le hn₂pos hn₁₂
    have e1 : (n₁ : ℝ) - 2 * n₂ = -D := by rw [hn₁R, hn₂R, hD]; ring
    rw [e1, abs_neg] at h1
    have h2 : |r| ≤ |κ| * (|D| / n₂) := by
      rw [hr, abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg κ)
    have h3 : 2 * |κ| * |D| / η < n₂ := by
      rw [hn₂R]
      have := neg_abs_le (t : ℝ)
      linarith
    rw [div_lt_iff₀ hη0] at h3
    have h4 : |κ| * (|D| / n₂) < η / 2 := by
      rw [← mul_div_assoc, div_lt_iff₀ hn₂pos]; linarith
    linarith
  -- the rotation error `d`
  set d := Int.fract ((b : ℝ) * α) - Int.fract ((b' : ℝ) * α) with hd
  have hd_lt : |d| < η / 2 := hbin_close b b' (by rw [hbj, hb'j])
  -- phases
  set x := Int.fract (φ α κ n₁) with hx
  set y := Int.fract (φ α κ n₂) with hy
  have hxE : x ∈ Set.Ico 0 (1 / 2 - 2 * δ) := hn₁E.2
  have hyE : y ∈ Set.Ico 0 (1 / 2 - 2 * δ) := hn₂E.2
  set J : ℤ := ⌊(b : ℝ) * α⌋ - ⌊(b' : ℝ) * α⌋ - k - ⌊φ α κ n₁⌋ + ⌊φ α κ n₂⌋ with hJ
  have hJeq : x - y + 1 / 2 = d - r + J := by
    have e1 := Int.self_sub_floor (φ α κ n₁)
    have e2 := Int.self_sub_floor (φ α κ n₂)
    have e3 := Int.self_sub_floor ((b : ℝ) * α)
    have e4 := Int.self_sub_floor ((b' : ℝ) * α)
    have hφ : φ α κ n₁ - φ α κ n₂ = (b - b') * α - κ * (Real.log n₁ - Real.log n₂) := by
      simp only [φ]; rw [hn₁R, hn₂R]; ring
    rw [hx, hy, hd, hr, hJ, ← e1, ← e2, ← e3, ← e4]
    push_cast
    linear_combination hφ - hk
  have hJ0 : (0 : ℝ) < J := by
    rw [abs_lt] at hr_lt hd_lt
    linarith [hxE.1, hxE.2, hyE.1, hyE.2]
  have hJ1 : (J : ℝ) < 1 := by
    rw [abs_lt] at hr_lt hd_lt
    linarith [hxE.1, hxE.2, hyE.1, hyE.2]
  have : (0 : ℤ) < J := by exact_mod_cast hJ0
  have : J < (1 : ℤ) := by exact_mod_cast hJ1
  omega

/-- Paper, Theorem \ref{KR:thm:main}(c). For every infinite `B ⊆ ℕ` (here `0` is allowed in
`B`), `B + B ⊄ A'`. -/
theorem no_BB {α κ δ : ℝ} (hκ2 : ∃ k : ℤ, κ * Real.log 2 = 1 / 2 + k) (hδ : 0 < δ)
    {B : Set ℕ} (hB : B.Infinite) : ¬ sumset B B ⊆ A' α κ δ := by
  intro hsub
  have key : ∀ σ : ℕ, {b ∈ B | b % 2 = σ}.Infinite → False := by
    intro σ hinf
    set C : Set ℕ := {k | 2 * k + σ ∈ B} with hC
    have hCinf : C.Infinite := by
      intro hfin
      apply hinf
      refine (hfin.image (fun k => 2 * k + σ)).subset ?_
      rintro b ⟨hb, hbσ⟩
      refine ⟨b / 2, ?_, ?_⟩
      · show 2 * (b / 2) + σ ∈ B
        rwa [show 2 * (b / 2) + σ = b by omega]
      · show 2 * (b / 2) + σ = b
        omega
    apply no_BBt hκ2 hδ σ hCinf
    intro c₁ hc₁ c₂ hc₂
    have hmem := hsub ⟨2 * c₁ + σ, hc₁, 2 * c₂ + σ, hc₂, rfl⟩
    rcases hmem with ⟨r, hr⟩ | ⟨m, hm, hm2⟩
    · omega
    · refine ⟨m, hm, ?_⟩
      have : m = c₁ + c₂ + σ := by omega
      rw [this]
      push_cast
      ring
  have hu : B = {b ∈ B | b % 2 = 0} ∪ {b ∈ B | b % 2 = 1} := by
    ext b
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hb; rcases Nat.mod_two_eq_zero_or_one b with h | h
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, h⟩
    · rintro (⟨hb, -⟩ | ⟨hb, -⟩) <;> exact hb
  rw [hu] at hB
  rcases Set.infinite_union.1 hB with h | h
  · exact key 0 h
  · exact key 1 h

/-- Paper, Theorem \ref{KR:thm:main}. Let `α` be irrational, `κ > 0` with
`κ log 2 ≡ 1/2 (mod 1)`, `0 < δ < 1/4`, `c = 1/2 - 2δ`, `φ(n) = n α - κ log n`,
`E = {n ∈ ℕ : {φ(n)} ∈ [0, c)}` and `A' = (2ℕ - 1) ∪ 2E`. Then
(a) `E` has uniform density `c`, `d_*(E) = d^*(E) = c`, `A'` has uniform density `3/4 - δ` and
`d_*(A') = d^*(A') = 3/4 - δ`;
(b) for every `t ∈ ℤ` and every infinite `B ⊆ ℕ₀`, `B + B + t ⊄ E`;
(c) for every infinite `B ⊆ ℕ`, `B + B ⊄ A'`. -/
theorem main {α κ δ : ℝ} (hα : Irrational α) (hκ : 0 < κ)
    (hκ2 : ∃ k : ℤ, κ * Real.log 2 = 1 / 2 + k) (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    ((∀ ε > 0, ∃ H₀ : ℕ, ∀ M H : ℕ, 1 ≤ M → H₀ ≤ H →
        |((E α κ δ ∩ Set.Ico M (M + H)).ncard : ℝ) - (1 / 2 - 2 * δ) * H| ≤ ε * H) ∧
      lowerBanachDensity (E α κ δ) = 1 / 2 - 2 * δ ∧
      upperBanachDensity (E α κ δ) = 1 / 2 - 2 * δ ∧
      (∀ ε > 0, ∃ H₀ : ℕ, ∀ M H : ℕ, 1 ≤ M → H₀ ≤ H →
        |((A' α κ δ ∩ Set.Ico M (M + H)).ncard : ℝ) - (3 / 4 - δ) * H| ≤ ε * H) ∧
      lowerBanachDensity (A' α κ δ) = 3 / 4 - δ ∧
      upperBanachDensity (A' α κ δ) = 3 / 4 - δ) ∧
    (∀ t : ℤ, ∀ B : Set ℕ, B.Infinite → ¬ ∀ b ∈ B, ∀ b' ∈ B, ∃ n ∈ E α κ δ, (n : ℤ) = b + b' + t) ∧
    (∀ B : Set ℕ, B.Infinite → ¬ sumset B B ⊆ A' α κ δ) := by
  obtain ⟨d1, d2, d3, d4⟩ := banach_densities hα hκ hδ hδ'
  refine ⟨⟨fun ε hε => ?_, d1, d2, fun ε hε => ?_, d3, d4⟩,
    fun t B hB => no_BBt hκ2 hδ t hB, fun B hB => no_BB hκ2 hδ hB⟩
  · obtain ⟨H₀, h⟩ := E_uniform hα hκ hδ hδ' ε hε
    exact ⟨H₀, fun M H _ hH => h M H hH⟩
  · obtain ⟨H₀, h⟩ := A'_uniform hα hκ hδ hδ' ε hε
    exact ⟨H₀, fun M H _ hH => h M H hH⟩

/-! ## Corollary \ref{KR:cor:main} -/

lemma kappa_spec : (1 / (2 * Real.log 2)) * Real.log 2 = 1 / 2 + ((0 : ℤ) : ℝ) := by
  have : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp
  simp

lemma kappa_pos : 0 < 1 / (2 * Real.log 2) := by
  have := Real.log_pos one_lt_two
  positivity

/-- Paper, Corollary \ref{KR:cor:main}: negative answers to both parts of Question 5.2 of
Kousek and Radić. There is a set `A` of positive integers with `d_*(A) > 1/3` such that
`B + B + t ⊄ A` for every infinite `B ⊆ ℕ` and every `t ∈ ℕ`; and there is a set `A` of
positive integers with `d_*(A) > 2/3` such that `B + B ⊄ A` for every infinite `B ⊆ ℕ`.
(Take `α = √2`, `κ = 1/(2 log 2)`, `δ = 1/24`.) -/
theorem q52_negative :
    (∃ A : Set ℕ, (∀ n ∈ A, 0 < n) ∧ 1 / 3 < lowerBanachDensity A ∧
      ∀ B : Set ℕ, B.Infinite → ∀ t : ℕ, ¬ ∀ b ∈ B, ∀ b' ∈ B, b + b' + t ∈ A) ∧
    (∃ A : Set ℕ, (∀ n ∈ A, 0 < n) ∧ 2 / 3 < lowerBanachDensity A ∧
      ∀ B : Set ℕ, B.Infinite → ¬ sumset B B ⊆ A) := by
  have hα := irrational_sqrt_two
  have hκ2 : ∃ k : ℤ, (1 / (2 * Real.log 2)) * Real.log 2 = 1 / 2 + k := ⟨0, kappa_spec⟩
  have hδ : (0 : ℝ) < 1 / 24 := by norm_num
  have hδ' : (1 : ℝ) / 24 < 1 / 4 := by norm_num
  obtain ⟨d1, -, d3, -⟩ := banach_densities hα kappa_pos hδ hδ'
  refine ⟨⟨E (Real.sqrt 2) (1 / (2 * Real.log 2)) (1 / 24), fun n hn => hn.1, ?_, ?_⟩,
    ⟨A' (Real.sqrt 2) (1 / (2 * Real.log 2)) (1 / 24), fun n hn => pos_of_mem_A' hn, ?_, ?_⟩⟩
  · rw [d1]; norm_num
  · intro B hB t h
    exact no_BBt hκ2 hδ t hB fun b hb b' hb' => ⟨b + b' + t, h b hb b' hb', by push_cast; ring⟩
  · rw [d3]; norm_num
  · exact fun B hB => no_BB hκ2 hδ hB

/-- Paper, Corollary \ref{KR:cor:main}, lower bounds for the two suprema (the upper bounds are
Theorems 1.3 and 1.2 of Kousek and Radić and are not formalized here): for every `ε > 0` there
is a set `A` of positive integers with `d_*(A) > 1/2 - ε` containing no `B + B + t`
(`B ⊆ ℕ` infinite, `t ∈ ℤ`), and a set `A` of positive integers with `d_*(A) > 3/4 - ε`
containing no `B + B` (`B ⊆ ℕ` infinite). -/
theorem sup_lower_bounds :
    (∀ ε > 0, ∃ A : Set ℕ, (∀ n ∈ A, 0 < n) ∧ 1 / 2 - ε < lowerBanachDensity A ∧
      ∀ B : Set ℕ, B.Infinite → ∀ t : ℤ, ¬ ∀ b ∈ B, ∀ b' ∈ B, ∃ n ∈ A, (n : ℤ) = b + b' + t) ∧
    (∀ ε > 0, ∃ A : Set ℕ, (∀ n ∈ A, 0 < n) ∧ 3 / 4 - ε < lowerBanachDensity A ∧
      ∀ B : Set ℕ, B.Infinite → ¬ sumset B B ⊆ A) := by
  have hα := irrational_sqrt_two
  have hκ2 : ∃ k : ℤ, (1 / (2 * Real.log 2)) * Real.log 2 = 1 / 2 + k := ⟨0, kappa_spec⟩
  have hδ : ∀ ε > (0 : ℝ), 0 < min ε (1 / 8) / 4 := fun ε hε => by positivity
  have hδ' : ∀ ε : ℝ, min ε (1 / 8) / 4 < 1 / 4 := fun ε => by
    linarith [min_le_right ε (1 / 8)]
  refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
  · obtain ⟨d1, -, -, -⟩ := banach_densities hα kappa_pos (hδ ε hε) (hδ' ε)
    refine ⟨E (Real.sqrt 2) (1 / (2 * Real.log 2)) (min ε (1 / 8) / 4), fun n hn => hn.1, ?_,
      fun B hB t => no_BBt hκ2 (hδ ε hε) t hB⟩
    rw [d1]
    linarith [min_le_left ε (1 / 8)]
  · obtain ⟨-, -, d3, -⟩ := banach_densities hα kappa_pos (hδ ε hε) (hδ' ε)
    refine ⟨A' (Real.sqrt 2) (1 / (2 * Real.log 2)) (min ε (1 / 8) / 4),
      fun n hn => pos_of_mem_A' hn, ?_, fun B hB => no_BB hκ2 (hδ ε hε) hB⟩
    rw [d3]
    linarith [min_le_left ε (1 / 8)]

end Kmrr25.KR52

end
