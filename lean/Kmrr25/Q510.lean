import Kmrr25.Basic

/-!
# Question 5.10: sets with dense fibres and no translate of `{(b₁, b₂) : b₁ < b₂ ∈ B}`

This file formalizes Section \ref{G:sec:q510} of the paper: Lemma \ref{G:lem:criterion},
Examples \ref{G:ex:4k} and \ref{G:ex:blocks}, Proposition \ref{G:prop:examples} and
Theorem \ref{G:thm:q510}.

The paper's `ℕ = {1, 2, …}`; all sets below are subsets of Lean's `ℕ` not containing `0`
(`mem_G₀_or_G₁`, `mem_sqBlocks` show that `G₀ ⊔ G₁` and `G'₀ ⊔ G'₁` cover `{1, 2, …}`). The
infinite sets `B` in the non-existence statements are arbitrary subsets of Lean's `ℕ` (so `0`
is even allowed), and translations `t` range over `ℤ²`.

* `criterion`: Lemma \ref{G:lem:criterion}; `fibre_eq_left`, `fibre_eq_right`: `A_n = S_c` for
  `n ∈ G_c`.
* `q510_example_4k`: Proposition \ref{G:prop:examples}(i) and Theorem \ref{G:thm:q510} for
  `A = (G₀ × S₀) ∪ (G₁ × S₁)`: the bound `S_c ∩ (G_c + s) < 15|s|`, the Følner property of
  `[1, 4^N]`, fibre densities `1/2` and `1/6` along it, and the absence of the configuration.
  The densities come from the exact count `card_block4`.
* `q510_example_blocks`: Proposition \ref{G:prop:examples}(ii) and Theorem \ref{G:thm:q510} for
  `A' = (G'₀ × S'₀) ∪ (G'₁ × S'₁)`: the bound `(2|s| + 1)²`, natural density `1/4` of every
  fibre, and the absence of the configuration.
* `q510_negative`: the resulting negative answer to Question 5.10.

Densities along a sequence of finite sets `Φ_N` are defined directly as limits of
`|S ∩ Φ_N| / |Φ_N|` (`HasDensityAlong`), and a Følner sequence in `ℕ` is a sequence of finite
sets with `|(Φ_N + t) ∩ Φ_N| / |Φ_N| → 1` for all `t ∈ ℕ` (`IsFolnerNat`).
-/

open Filter Topology Finset
open scoped Classical

noncomputable section

namespace Kmrr25.Q510

/-! ### The configuration and the criterion -/

/-- The fibre `A_n = {m | (n, m) ∈ A}` of `A ⊆ ℕ²` over `n`. -/
def fibre (A : Set (ℕ × ℕ)) (n : ℕ) : Set ℕ := {m | (n, m) ∈ A}

/-- `A ⊆ ℕ²` contains the translate by `t ∈ ℤ²` of the configuration
`{(b₁, b₂) | b₁, b₂ ∈ B, b₁ < b₂}`: `(b₁ + t₁, b₂ + t₂) ∈ A` for all `b₁ < b₂` in `B`
(points computed in `ℤ²`). -/
def ContainsConfig (A : Set (ℕ × ℕ)) (B : Set ℕ) (t : ℤ × ℤ) : Prop :=
  ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ < b₂ → ∃ p ∈ A, (p.1 : ℤ) = b₁ + t.1 ∧ (p.2 : ℤ) = b₂ + t.2

/-- `S ∩ (G + s)` for `S, G ⊆ ℕ` and `s ∈ ℤ`. -/
def shiftInter (S G : Set ℕ) (s : ℤ) : Set ℕ := {m | m ∈ S ∧ ∃ g ∈ G, (m : ℤ) = g + s}

/-- The core of the criterion: if all rows of `A` indexed by `G` lie in `S` and an infinite
`B'` satisfies the configuration with every `b + t₁` (`b ∈ B'`) in `G`, then
`S ∩ (G + (t₂ - t₁))` is infinite. -/
theorem shiftInter_infinite {A : Set (ℕ × ℕ)} {G S : Set ℕ}
    (hA : ∀ n ∈ G, ∀ m, (n, m) ∈ A → m ∈ S) {B : Set ℕ} (hB : B.Infinite) {t : ℤ × ℤ}
    (hBG : ∀ b ∈ B, ∃ g ∈ G, (g : ℤ) = b + t.1) (hc : ContainsConfig A B t) :
    (shiftInter S G (t.2 - t.1)).Infinite := by
  obtain ⟨b₀, hb₀⟩ := hB.nonempty
  have hB' : (B \ Set.Iic b₀).Infinite := hB.sdiff (Set.finite_Iic b₀)
  let φ : ℕ → ℕ := fun b => ((b : ℤ) + t.2).toNat
  have key : ∀ b ∈ B \ Set.Iic b₀, 0 ≤ (b : ℤ) + t.2 ∧ φ b ∈ shiftInter S G (t.2 - t.1) := by
    rintro b ⟨hb, hb'⟩
    simp only [Set.mem_Iic, not_le] at hb'
    obtain ⟨p, hpA, hp1, hp2⟩ := hc b₀ hb₀ b hb hb'
    obtain ⟨g₀, hg₀, hg₀'⟩ := hBG b₀ hb₀
    obtain ⟨g, hg, hg'⟩ := hBG b hb
    have hp1' : p.1 = g₀ := by omega
    have hpS : p.2 ∈ S := hA g₀ hg₀ p.2 (by rw [← hp1']; exact hpA)
    have hφ : φ b = p.2 := by simp only [φ]; omega
    refine ⟨by omega, ?_⟩
    rw [hφ]
    exact ⟨hpS, g, hg, by omega⟩
  have hinj : Set.InjOn φ (B \ Set.Iic b₀) := by
    intro b hb b' hb' h
    have h1 := (key b hb).1
    have h2 := (key b' hb').1
    simp only [φ] at h
    omega
  exact (hB'.image hinj).mono (by rintro _ ⟨b, hb, rfl⟩; exact (key b hb).2)

/-- Paper, Lemma \ref{G:lem:criterion} (fibres). If `G₀, G₁` are disjoint then the fibre of
`A = (G₀ × S₀) ∪ (G₁ × S₁)` over `n ∈ G₀` is `S₀`. -/
theorem fibre_eq_left {G₀ G₁ S₀ S₁ : Set ℕ} (hd : Disjoint G₀ G₁) {n : ℕ} (hn : n ∈ G₀) :
    fibre (G₀ ×ˢ S₀ ∪ G₁ ×ˢ S₁) n = S₀ := by
  ext m
  simp only [fibre, Set.mem_union, Set.mem_prod, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd h (Set.disjoint_left.mp hd hn)
  · intro h; exact Or.inl ⟨hn, h⟩

/-- Paper, Lemma \ref{G:lem:criterion} (fibres). If `G₀, G₁` are disjoint then the fibre of
`A = (G₀ × S₀) ∪ (G₁ × S₁)` over `n ∈ G₁` is `S₁`. -/
theorem fibre_eq_right {G₀ G₁ S₀ S₁ : Set ℕ} (hd : Disjoint G₀ G₁) {n : ℕ} (hn : n ∈ G₁) :
    fibre (G₀ ×ˢ S₀ ∪ G₁ ×ˢ S₁) n = S₁ := by
  rw [Set.union_comm]
  exact fibre_eq_left hd.symm hn

/-- **Paper, Lemma \ref{G:lem:criterion}.** Let `G₀, G₁ ⊆ ℕ` be disjoint and let `S₀, S₁ ⊆ ℕ`
be such that `S_c ∩ (G_c + s)` is finite for every `s ∈ ℤ` and `c ∈ {0, 1}`. Then for
`A = (G₀ × S₀) ∪ (G₁ × S₁)` there are no infinite `B ⊆ ℕ` and `t ∈ ℤ²` with
`(b₁ + t₁, b₂ + t₂) ∈ A` for all `b₁ < b₂` in `B`. -/
theorem criterion {G₀ G₁ S₀ S₁ : Set ℕ} (hd : Disjoint G₀ G₁)
    (h₀ : ∀ s : ℤ, (shiftInter S₀ G₀ s).Finite) (h₁ : ∀ s : ℤ, (shiftInter S₁ G₁ s).Finite) :
    ¬ ∃ (B : Set ℕ) (t : ℤ × ℤ), B.Infinite ∧ ContainsConfig (G₀ ×ˢ S₀ ∪ G₁ ×ˢ S₁) B t := by
  rintro ⟨B, t, hB, hc⟩
  set A := G₀ ×ˢ S₀ ∪ G₁ ×ˢ S₁
  let B₀ := {b ∈ B | ∃ g ∈ G₀, (g : ℤ) = b + t.1}
  let B₁ := {b ∈ B | ∃ g ∈ G₁, (g : ℤ) = b + t.1}
  have hcover : B ⊆ B₀ ∪ B₁ := by
    intro b hb
    obtain ⟨b', hb', hbb'⟩ := hB.exists_gt b
    obtain ⟨p, hpA, hp1, -⟩ := hc b hb b' hb' hbb'
    rcases hpA with ⟨hp, -⟩ | ⟨hp, -⟩
    · exact Or.inl ⟨hb, p.1, hp, hp1⟩
    · exact Or.inr ⟨hb, p.1, hp, hp1⟩
  have hsub : ∀ B' ⊆ B, ContainsConfig A B' t := fun B' hB' b₁ hb₁ b₂ hb₂ h =>
    hc b₁ (hB' hb₁) b₂ (hB' hb₂) h
  rcases Set.infinite_union.mp (hB.mono hcover) with hB₀ | hB₁
  · refine shiftInter_infinite (A := A) (G := G₀) (S := S₀) ?_ hB₀ (fun b hb => hb.2)
      (hsub _ (fun b hb => hb.1)) (h₀ _)
    intro n hn m hm
    rw [← fibre_eq_left (S₀ := S₀) (S₁ := S₁) hd hn]
    exact hm
  · refine shiftInter_infinite (A := A) (G := G₁) (S := S₁) ?_ hB₁ (fun b hb => hb.2)
      (hsub _ (fun b hb => hb.1)) (h₁ _)
    intro n hn m hm
    rw [← fibre_eq_right (S₀ := S₀) (S₁ := S₁) hd hn]
    exact hm


/-! ### Densities along a sequence of finite sets -/

/-- A Følner sequence in `ℕ` in the sense of the paper: finite sets `Φ N` with
`|(Φ_N + t) ∩ Φ_N| / |Φ_N| → 1` for every `t ∈ ℕ`. -/
def IsFolnerNat (Φ : ℕ → Finset ℕ) : Prop :=
  ∀ t : ℕ, Tendsto (fun N => (#((Φ N).image (· + t) ∩ Φ N) : ℝ) / #(Φ N)) atTop (𝓝 1)

/-- The relative density `|F ∩ S| / |F|`. -/
def relDens (F : Finset ℕ) (S : Set ℕ) : ℝ := (#{m ∈ F | m ∈ S} : ℝ) / #F

/-- `S` has density `δ` along `Φ`: `|S ∩ Φ_N| / |Φ_N| → δ`. For `Φ_N = [1, N]` this is natural
density. -/
def HasDensityAlong (Φ : ℕ → Finset ℕ) (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun N => relDens (Φ N) S) atTop (𝓝 δ)

/-- Computing `relDens` with an arbitrary decidable predicate describing `S`. -/
theorem relDens_eq (F : Finset ℕ) (S : Set ℕ) (P : ℕ → Prop) [DecidablePred P]
    (h : ∀ x, x ∈ S ↔ P x) : relDens F S = (#{x ∈ F | P x} : ℝ) / #F := by
  unfold relDens
  congr 3
  exact Finset.filter_congr (fun x _ => h x)

/-- `[1, M_N]` is a Følner sequence whenever `M_N → ∞`. -/
theorem isFolnerNat_Icc {M : ℕ → ℕ} (hM : Tendsto M atTop atTop) :
    IsFolnerNat (fun N => Finset.Icc 1 (M N)) := by
  have hM' : Tendsto (fun N => ((M N : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hM
  intro t
  have hlim : Tendsto (fun N => (1 : ℝ) - t / (M N : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (t : ℝ))).div_atTop hM')
  refine hlim.congr' ?_
  filter_upwards [tendsto_atTop.mp hM (t + 1)] with N hN
  have himg : (Finset.Icc 1 (M N)).image (· + t) ∩ Finset.Icc 1 (M N) =
      Finset.Icc (1 + t) (M N) := by
    rw [Finset.image_add_right_Icc]
    ext x
    simp only [Finset.mem_inter, Finset.mem_Icc]
    omega
  rw [himg, Nat.card_Icc, Nat.card_Icc]
  have hp : (0 : ℝ) < (M N : ℝ) := by exact_mod_cast (show 0 < M N by omega)
  rw [show M N + 1 - (1 + t) = M N - t by omega, show M N + 1 - 1 = M N by omega,
    Nat.cast_sub (by omega)]
  field_simp


/-! ### Example \ref{G:ex:4k} (scale `4^k`) -/

/-- `G₀ = ⋃_{k ≥ 0} [4^k, 2·4^k)`. -/
def G₀ : Set ℕ := {n | ∃ k : ℕ, 4 ^ k ≤ n ∧ n < 2 * 4 ^ k}

/-- `G₁ = ⋃_{k ≥ 0} [2·4^k, 4^{k+1})`. -/
def G₁ : Set ℕ := {n | ∃ k : ℕ, 2 * 4 ^ k ≤ n ∧ n < 4 ^ (k + 1)}

/-- `S₀ = ⋃_{k ≥ 1} [9·4^{k-1}, 15·4^{k-1})` (written with `j = k - 1`). -/
def S₀ : Set ℕ := {m | ∃ j : ℕ, 9 * 4 ^ j ≤ m ∧ m < 15 * 4 ^ j}

/-- `S₁ = ⋃_{k ≥ 1} [5·4^{k-1}, 7·4^{k-1})` (written with `j = k - 1`). -/
def S₁ : Set ℕ := {m | ∃ j : ℕ, 5 * 4 ^ j ≤ m ∧ m < 7 * 4 ^ j}

/-- The set `A = (G₀ × S₀) ∪ (G₁ × S₁) ⊆ ℕ²` of Example \ref{G:ex:4k}. -/
def A : Set (ℕ × ℕ) := G₀ ×ˢ S₀ ∪ G₁ ×ˢ S₁

theorem pow4_cases (j k : ℕ) : 4 ^ k ≤ 4 ^ j ∨ 4 * 4 ^ j ≤ 4 ^ k := by
  rcases le_or_gt k j with h | h
  · exact Or.inl (Nat.pow_le_pow_right (by norm_num) h)
  · right
    calc 4 * 4 ^ j = 4 ^ (j + 1) := by ring
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) h

theorem G₀_disjoint_G₁ : Disjoint G₀ G₁ := by
  rw [Set.disjoint_left]
  rintro n ⟨k, hk1, hk2⟩ ⟨k', hk1', hk2'⟩
  have h4 : 4 ^ (k' + 1) = 4 * 4 ^ k' := by ring
  rcases pow4_cases k' k with h | h <;> omega

/-- `ℕ = G₀ ⊔ G₁` (here `ℕ = {1, 2, …}`). -/
theorem mem_G₀_or_G₁ {n : ℕ} (hn : 1 ≤ n) : n ∈ G₀ ∨ n ∈ G₁ := by
  have h1 := Nat.pow_log_le_self 4 (show n ≠ 0 by omega)
  have h2 := Nat.lt_pow_succ_log_self (show 1 < 4 by norm_num) n
  rcases lt_or_ge n (2 * 4 ^ Nat.log 4 n) with h | h
  · exact Or.inl ⟨_, h1, h⟩
  · exact Or.inr ⟨_, h, h2⟩

/-- Paper, Proposition \ref{G:prop:examples}(i), `c = 0`: every element of `S₀ ∩ (G₀ + s)` is
smaller than `15|s|`. -/
theorem shiftInter_S₀_lt {s : ℤ} {m : ℕ} (hm : m ∈ shiftInter S₀ G₀ s) : (m : ℤ) < 15 * |s| := by
  obtain ⟨⟨j, hj1, hj2⟩, g, ⟨k, hk1, hk2⟩, hmg⟩ := hm
  have h16 : 4 ^ (j + 1) = 4 * 4 ^ j := by ring
  have hc : 4 ^ k ≤ 4 * 4 ^ j ∨ 16 * 4 ^ j ≤ 4 ^ k := by
    rcases pow4_cases (j + 1) k with h | h
    · exact Or.inl (h16 ▸ h)
    · right; rw [h16] at h; omega
  generalize 4 ^ j = X at *
  generalize 4 ^ k = Y at *
  rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

/-- Paper, Proposition \ref{G:prop:examples}(i), `c = 1`: every element of `S₁ ∩ (G₁ + s)` is
smaller than `15|s|`. -/
theorem shiftInter_S₁_lt {s : ℤ} {m : ℕ} (hm : m ∈ shiftInter S₁ G₁ s) : (m : ℤ) < 15 * |s| := by
  obtain ⟨⟨j, hj1, hj2⟩, g, ⟨k, hk1, hk2⟩, hmg⟩ := hm
  have h4 : 4 ^ (k + 1) = 4 * 4 ^ k := by ring
  have hc := pow4_cases j k
  generalize 4 ^ j = X at *
  generalize 4 ^ (k + 1) = Z at *
  generalize 4 ^ k = Y at *
  rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

theorem finite_of_lt {T : Set ℕ} (c : ℤ) (h : ∀ m ∈ T, (m : ℤ) < c) : T.Finite :=
  (Set.finite_lt_nat c.toNat).subset fun m hm => by
    have := h m hm
    simp only [Set.mem_ofPred_eq]
    omega


/-- A union of blocks `⋃_{j ≥ 0} [a·4^j, b·4^j)`. -/
def block4 (a b : ℕ) : Set ℕ := {m | ∃ j : ℕ, a * 4 ^ j ≤ m ∧ m < b * 4 ^ j}

theorem block4_Ioc {a b : ℕ} (ha : 4 < a) (hb : b ≤ 16) (N : ℕ) :
    {m ∈ Finset.Ioc (4 ^ (N + 1)) (4 ^ (N + 2)) | m ∈ block4 a b} =
      Finset.Ico (a * 4 ^ N) (b * 4 ^ N) := by
  have e1 : 4 ^ (N + 1) = 4 * 4 ^ N := by ring
  have e2 : 4 ^ (N + 2) = 16 * 4 ^ N := by ring
  have haN := Nat.mul_le_mul_right (4 ^ N) (show 5 ≤ a by omega)
  have hbN := Nat.mul_le_mul_right (4 ^ N) hb
  ext m
  rw [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
  simp only [block4, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, j, hj1, hj2⟩
    rcases lt_trichotomy j N with h | rfl | h
    · have hp : 4 * 4 ^ j ≤ 4 ^ N := by
        calc 4 * 4 ^ j = 4 ^ (j + 1) := by ring
          _ ≤ 4 ^ N := Nat.pow_le_pow_right (by norm_num) h
      have := Nat.mul_le_mul_right (4 ^ j) hb
      omega
    · exact ⟨hj1, hj2⟩
    · have hp : 4 * 4 ^ N ≤ 4 ^ j := by
        calc 4 * 4 ^ N = 4 ^ (N + 1) := by ring
          _ ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) h
      have := Nat.mul_le_mul_right (4 ^ j) (show 5 ≤ a by omega)
      omega
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by omega, by omega⟩, N, h1, h2⟩

theorem block4_small {a b : ℕ} (ha : 4 < a) {m : ℕ} (hm : m ≤ 4) : m ∉ block4 a b := by
  rintro ⟨j, hj, -⟩
  have h1 : 1 ≤ 4 ^ j := Nat.one_le_pow _ _ (by norm_num)
  have := Nat.mul_le_mul_left a h1
  omega

/-- Exact count: `3 |block4 a b ∩ [1, 4^{N+1}]| + (b - a) = (b - a) 4^N`. -/
theorem card_block4 {a b : ℕ} (ha : 4 < a) (hb : b ≤ 16) (N : ℕ) :
    3 * #{m ∈ Finset.Icc 1 (4 ^ (N + 1)) | m ∈ block4 a b} + (b - a) = (b - a) * 4 ^ N := by
  induction N with
  | zero =>
    have : #{m ∈ Finset.Icc 1 (4 ^ (0 + 1)) | m ∈ block4 a b} = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m hm
      simp only [Finset.mem_Icc] at hm
      exact block4_small ha (by simpa using hm.2)
    rw [this]; simp
  | succ N ih =>
    have hsplit : Finset.Icc 1 (4 ^ (N + 1 + 1)) =
        Finset.Icc 1 (4 ^ (N + 1)) ∪ Finset.Ioc (4 ^ (N + 1)) (4 ^ (N + 2)) := by
      have h1 : 1 ≤ 4 ^ (N + 1) := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 4 ^ (N + 1) ≤ 4 ^ (N + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 4 ^ (N + 1 + 1) = 4 ^ (N + 2) := rfl
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint, block4_Ioc ha hb,
      Nat.card_Ico]
    · have e1 : 4 ^ (N + 1) = 4 * 4 ^ N := by ring
      rw [e1, ← Nat.sub_mul]
      rw [e1] at ih
      nlinarith
    · apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx hx'
      omega

/-- The density of `block4 a b` along `Φ_N = [1, 4^N]` is `(b - a) / 12`. -/
theorem hasDensityAlong_block4 {a b : ℕ} (ha : 4 < a) (hb : b ≤ 16) :
    HasDensityAlong (fun N => Finset.Icc 1 (4 ^ N)) (block4 a b) (((b - a : ℕ) : ℝ) / 12) := by
  unfold HasDensityAlong
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  have hlim : Tendsto (fun N : ℕ => ((b - a : ℕ) : ℝ) / 12 * (1 - (1 / 4 : ℝ) ^ N)) atTop
      (𝓝 (((b - a : ℕ) : ℝ) / 12)) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) < 1 by norm_num)
    simpa using (tendsto_const_nhds (x := ((b - a : ℕ) : ℝ) / 12)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub this)
  refine hlim.congr (fun N => ?_)
  have h := card_block4 ha hb N
  unfold relDens
  rw [Nat.card_Icc, Nat.add_sub_cancel]
  set f := #{m ∈ Finset.Icc 1 (4 ^ (N + 1)) | m ∈ block4 a b}
  set d := b - a
  have h' : (3 : ℝ) * f + d = d * 4 ^ N := by exact_mod_cast h
  have hp : (0 : ℝ) < 4 ^ N := by positivity
  push_cast
  rw [div_pow, one_pow, pow_succ]
  field_simp
  linear_combination (-4 : ℝ) * h'


/-- Paper, Proposition \ref{G:prop:examples}(i), density part: `d_Φ(S₀) = 1/2` along
`Φ_N = [1, 4^N]`. -/
theorem hasDensityAlong_S₀ : HasDensityAlong (fun N => Finset.Icc 1 (4 ^ N)) S₀ (1 / 2) := by
  have := hasDensityAlong_block4 (a := 9) (b := 15) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- Paper, Proposition \ref{G:prop:examples}(i), density part: `d_Φ(S₁) = 1/6` along
`Φ_N = [1, 4^N]`. -/
theorem hasDensityAlong_S₁ : HasDensityAlong (fun N => Finset.Icc 1 (4 ^ N)) S₁ (1 / 6) := by
  have := hasDensityAlong_block4 (a := 5) (b := 7) (by norm_num) (by norm_num)
  norm_num at this
  exact this

/-- `Φ_N = [1, 4^N]` is a Følner sequence in `ℕ`. -/
theorem isFolnerNat_pow4 : IsFolnerNat (fun N => Finset.Icc 1 (4 ^ N)) :=
  isFolnerNat_Icc (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- **Paper, Proposition \ref{G:prop:examples}(i) and Theorem \ref{G:thm:q510} for the set `A`
of Example \ref{G:ex:4k}.**
* `Φ_N = [1, 4^N]` is a Følner sequence;
* every element of `S_c ∩ (G_c + s)` is smaller than `15|s|` (`c = 0, 1`, `s ∈ ℤ`);
* every fibre `A_n`, `n ≥ 1`, has density along `Φ`, equal to `1/2` if `n ∈ G₀` and to `1/6`
  if `n ∈ G₁` (so `liminf_n d_Φ(A_n) = 1/6 > 0`, condition (G:eq:22));
* there is no infinite `B ⊆ ℕ` and no `t ∈ ℤ²` with `(b₁ + t₁, b₂ + t₂) ∈ A` for all
  `b₁ < b₂` in `B`. -/
theorem q510_example_4k :
    IsFolnerNat (fun N => Finset.Icc 1 (4 ^ N)) ∧
    (∀ (s : ℤ) (m : ℕ), m ∈ shiftInter S₀ G₀ s → (m : ℤ) < 15 * |s|) ∧
    (∀ (s : ℤ) (m : ℕ), m ∈ shiftInter S₁ G₁ s → (m : ℤ) < 15 * |s|) ∧
    (∀ n : ℕ, 1 ≤ n →
      (n ∈ G₀ ∧ HasDensityAlong (fun N => Finset.Icc 1 (4 ^ N)) (fibre A n) (1 / 2)) ∨
      (n ∈ G₁ ∧ HasDensityAlong (fun N => Finset.Icc 1 (4 ^ N)) (fibre A n) (1 / 6))) ∧
    ¬ ∃ (B : Set ℕ) (t : ℤ × ℤ), B.Infinite ∧ ContainsConfig A B t := by
  refine ⟨isFolnerNat_pow4, fun s m hm => shiftInter_S₀_lt hm, fun s m hm => shiftInter_S₁_lt hm,
    fun n hn => ?_, criterion G₀_disjoint_G₁ (fun s => finite_of_lt _ fun m hm =>
      shiftInter_S₀_lt hm) (fun s => finite_of_lt _ fun m hm => shiftInter_S₁_lt hm)⟩
  rcases mem_G₀_or_G₁ hn with h | h
  · left
    refine ⟨h, ?_⟩
    rw [A, fibre_eq_left G₀_disjoint_G₁ h]
    exact hasDensityAlong_S₀
  · right
    refine ⟨h, ?_⟩
    rw [A, fibre_eq_right G₀_disjoint_G₁ h]
    exact hasDensityAlong_S₁


/-! ### Example \ref{G:ex:blocks} (square blocks) -/

/-- The union of the square blocks `J_k = [k², (k+1)²)`, `k ≥ 1`, with `k ≡ p (mod 2)`.
`G'_c = sqBlocks c`. -/
def sqBlocks (p : ℕ) : Set ℕ := {n | ∃ k : ℕ, 1 ≤ k ∧ k % 2 = p ∧ k ^ 2 ≤ n ∧ n < (k + 1) ^ 2}

/-- The middle parts `{k² + r | k ≤ 2r < 3k}` of the blocks `J_k`, `k ≥ 1`, `k ≡ p (mod 2)`.
The paper's `S'_c` is `sqMid (1 - c)`. (The paper allows `r ∈ ℤ`, but `k ≤ 2r` forces
`r ≥ 0`.) -/
def sqMid (p : ℕ) : Set ℕ :=
  {m | ∃ k : ℕ, 1 ≤ k ∧ k % 2 = p ∧ ∃ r : ℕ, m = k ^ 2 + r ∧ k ≤ 2 * r ∧ 2 * r < 3 * k}

/-- The set `A' = (G'₀ × S'₀) ∪ (G'₁ × S'₁) ⊆ ℕ²` of Example \ref{G:ex:blocks}. -/
def A' : Set (ℕ × ℕ) := sqBlocks 0 ×ˢ sqMid 1 ∪ sqBlocks 1 ×ˢ sqMid 0

theorem zero_not_mem_sqMid (p : ℕ) : 0 ∉ sqMid p := by
  rintro ⟨k, hk, -, r, hr, -⟩
  have := Nat.one_le_pow 2 k hk
  omega

theorem sq_block_unique {k K x : ℕ} (h1 : k ^ 2 ≤ x) (h2 : x < (k + 1) ^ 2) (h3 : K ^ 2 ≤ x)
    (h4 : x < (K + 1) ^ 2) : k = K := by
  rcases lt_trichotomy k K with h | h | h
  · have := Nat.pow_le_pow_left (show k + 1 ≤ K by omega) 2
    omega
  · exact h
  · have := Nat.pow_le_pow_left (show K + 1 ≤ k by omega) 2
    omega

theorem sqBlocks_disjoint : Disjoint (sqBlocks 0) (sqBlocks 1) := by
  rw [Set.disjoint_left]
  rintro n ⟨k, -, hk, h1, h2⟩ ⟨k', -, hk', h1', h2'⟩
  have := sq_block_unique h1 h2 h1' h2'
  omega

/-- `ℕ = G'₀ ⊔ G'₁` (here `ℕ = {1, 2, …}`). -/
theorem mem_sqBlocks {n : ℕ} (hn : 1 ≤ n) : n ∈ sqBlocks 0 ∨ n ∈ sqBlocks 1 := by
  have h1 := Nat.sqrt_le' n
  have h2 := Nat.lt_succ_sqrt' n
  have h3 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn
  rcases Nat.mod_two_eq_zero_or_one (Nat.sqrt n) with h | h
  · exact Or.inl ⟨_, h3, h, h1, h2⟩
  · exact Or.inr ⟨_, h3, h, h1, h2⟩

/-- Paper, Proposition \ref{G:prop:examples}(ii): every element of `S'_c ∩ (G'_c + s)` is
smaller than `(2|s| + 1)²`. Here `S'_c = sqMid q`, `G'_c = sqBlocks p` with `p ≠ q`. -/
theorem shiftInter_sqMid_lt {p q : ℕ} (hpq : p ≠ q) {s : ℤ} {m : ℕ}
    (hm : m ∈ shiftInter (sqMid q) (sqBlocks p) s) : (m : ℤ) < (2 * |s| + 1) ^ 2 := by
  obtain ⟨⟨k, hk1, hkq, r, rfl, hr1, hr2⟩, g, ⟨k', -, hk'p, hg1, hg2⟩, hmg⟩ := hm
  have hsq : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
  by_cases hks : (k : ℤ) ≤ 2 * |s|
  · have h1 : ((k + 1 : ℕ) : ℤ) ^ 2 ≤ (2 * |s| + 1) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast; linarith
    have h2 : k ^ 2 + r < (k + 1) ^ 2 := by omega
    have h3 : ((k ^ 2 + r : ℕ) : ℤ) < ((k + 1 : ℕ) : ℤ) ^ 2 := by exact_mod_cast h2
    linarith
  · exfalso
    have hgk : k ^ 2 ≤ g ∧ g < (k + 1) ^ 2 := by
      generalize k ^ 2 = K2 at *
      generalize (k + 1) ^ 2 = K3 at *
      rcases abs_cases s with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hks <;> omega
    have := sq_block_unique hgk.1 hgk.2 hg1 hg2
    omega

/-- The number of elements of `sqMid p` in the block `J_K = [K², (K+1)²)`. -/
theorem card_sqMid_block (p K : ℕ) :
    #{m ∈ Finset.Ico (K ^ 2) ((K + 1) ^ 2) | m ∈ sqMid p} = if K % 2 = p then K else 0 := by
  have hsq : (K + 1) ^ 2 = K ^ 2 + 2 * K + 1 := by ring
  split_ifs with hK
  · have : {m ∈ Finset.Ico (K ^ 2) ((K + 1) ^ 2) | m ∈ sqMid p} =
        Finset.Ico (K ^ 2 + (K + 1) / 2) (K ^ 2 + (3 * K + 1) / 2) := by
      ext m
      rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, k, hk1, hkp, r, rfl, hr1, hr2⟩
        have hk : k = K := sq_block_unique (Nat.le_add_right _ _)
          (by have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
              omega) h1 h2
        subst hk
        omega
      · rintro ⟨h1, h2⟩
        refine ⟨⟨by omega, by omega⟩, K, by omega, hK, m - K ^ 2, by omega, by omega, by omega⟩
    rw [this, Nat.card_Ico]
    omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro m hm ⟨k, hk1, hkp, r, rfl, hr1, hr2⟩
    simp only [Finset.mem_Ico] at hm
    have hk : k = K := sq_block_unique (Nat.le_add_right _ _)
      (by have : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
          omega) hm.1 hm.2
    exact hK (hk ▸ hkp)

theorem card_range_split (S : Set ℕ) {a b : ℕ} (hab : a ≤ b) :
    #{m ∈ Finset.range b | m ∈ S} = #{m ∈ Finset.range a | m ∈ S} + #{m ∈ Finset.Ico a b | m ∈ S} := by
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico, ← Finset.card_union_of_disjoint,
    ← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hab]
  exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)

/-- Counting `sqMid p` below `K²`: `4C ≤ K² ≤ 4C + 2K + 2` where `C = |sqMid p ∩ [0, K²)|`. -/
theorem card_sqMid_sq {p : ℕ} (hp : p < 2) (K : ℕ) :
    4 * #{m ∈ Finset.range (K ^ 2) | m ∈ sqMid p} ≤ K ^ 2 ∧
      K ^ 2 ≤ 4 * #{m ∈ Finset.range (K ^ 2) | m ∈ sqMid p} + 2 * K + 2 := by
  have step : ∀ K, #{m ∈ Finset.range ((K + 1) ^ 2) | m ∈ sqMid p} =
      #{m ∈ Finset.range (K ^ 2) | m ∈ sqMid p} + if K % 2 = p then K else 0 := by
    intro K
    rw [card_range_split _ (Nat.pow_le_pow_left (Nat.le_succ K) 2), card_sqMid_block]
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    match K, ih with
    | 0, _ => simp
    | 1, _ =>
      simp [Finset.filter_singleton, zero_not_mem_sqMid]
    | K + 2, ih =>
      have h := ih K (by omega)
      have e1 := step K
      have e2 := step (K + 1)
      have hsq1 : (K + 1) ^ 2 = K ^ 2 + 2 * K + 1 := by ring
      have hsq2 : (K + 1 + 1) ^ 2 = K ^ 2 + 4 * K + 4 := by ring
      rw [e1] at e2
      rw [show K + 2 = K + 1 + 1 from rfl, e2, hsq2]
      have hpar : (K % 2 = p ∧ (K + 1) % 2 ≠ p) ∨ (K % 2 ≠ p ∧ (K + 1) % 2 = p) := by omega
      rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos h1, if_neg h2]; omega
      · rw [if_neg h1, if_pos h2]; omega


theorem tendsto_sqrt_atTop : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b ^ 2, fun _ ha => (Nat.sqrt_eq' b) ▸ Nat.sqrt_le_sqrt ha⟩

/-- Paper, Proposition \ref{G:prop:examples}(ii), density part: `sqMid p` (that is, `S'₀` and
`S'₁`) has natural density `1/4`. -/
theorem hasDensityAlong_sqMid {p : ℕ} (hp : p < 2) :
    HasDensityAlong (fun N => Finset.Icc 1 N) (sqMid p) (1 / 4) := by
  have hc : ∀ N, #{m ∈ Finset.Icc 1 N | m ∈ sqMid p} = #{m ∈ Finset.range (N + 1) | m ∈ sqMid p} := by
    intro N
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨?_, by omega⟩, h3⟩
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (h ▸ h3) (zero_not_mem_sqMid p)
      · exact h
  -- the key estimate, for `N ≥ 1` and `K = ⌊√N⌋`
  have key : ∀ N, 1 ≤ N →
      (1 / 4 - 2 / (Nat.sqrt N : ℝ) ≤ relDens (Finset.Icc 1 N) (sqMid p)) ∧
      (relDens (Finset.Icc 1 N) (sqMid p) ≤ 1 / 4 + 2 / (Nat.sqrt N : ℝ)) := by
    intro N hN
    have hK1 : 1 ≤ Nat.sqrt N := Nat.sqrt_pos.mpr hN
    have hK2 : Nat.sqrt N ^ 2 ≤ N := Nat.sqrt_le' N
    have hK3 : N < (Nat.sqrt N + 1) ^ 2 := Nat.lt_succ_sqrt' N
    generalize Nat.sqrt N = K at *
    have hsq : (K + 1) ^ 2 = K ^ 2 + 2 * K + 1 := by ring
    have s1 := card_range_split (sqMid p) (show K ^ 2 ≤ N + 1 by omega)
    have s2 := card_range_split (sqMid p) (show N + 1 ≤ (K + 1) ^ 2 by omega)
    have s3 := card_range_split (sqMid p) (Nat.pow_le_pow_left (show K ≤ K + 1 by omega) 2)
    rw [card_sqMid_block] at s3
    have hb := card_sqMid_sq hp K
    have hite : (if K % 2 = p then K else 0) ≤ K := by split_ifs <;> omega
    unfold relDens
    rw [hc, Nat.card_Icc, Nat.add_sub_cancel]
    set c := #{m ∈ Finset.range (N + 1) | m ∈ sqMid p}
    have e1 : 4 * c ≤ N + 4 * K := by omega
    have e2 : N ≤ 4 * c + 4 * K + 2 := by omega
    have r1 : (4 : ℝ) * c ≤ N + 4 * K := by exact_mod_cast e1
    have r2 : (N : ℝ) ≤ 4 * c + 4 * K + 2 := by exact_mod_cast e2
    have rK : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have rN : (K : ℝ) ^ 2 ≤ N := by exact_mod_cast hK2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hKpos : (0 : ℝ) < K := by linarith
    have h2 : 2 * (K : ℝ) ≤ 2 / K * N := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hKpos]; nlinarith
    constructor
    · rw [le_div_iff₀ hNpos, sub_mul]; linarith
    · rw [div_le_iff₀ hNpos, add_mul]; linarith
  have hs : Tendsto (fun N => 2 / (Nat.sqrt N : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (2 : ℝ))).div_atTop
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_sqrt_atTop)
  have hlo : Tendsto (fun N => 1 / 4 - 2 / (Nat.sqrt N : ℝ)) atTop (𝓝 (1 / 4)) := by
    simpa using (tendsto_const_nhds (x := (1 / 4 : ℝ))).sub hs
  have hhi : Tendsto (fun N => 1 / 4 + 2 / (Nat.sqrt N : ℝ)) atTop (𝓝 (1 / 4)) := by
    simpa using (tendsto_const_nhds (x := (1 / 4 : ℝ))).add hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN using (key N hN).1
  · filter_upwards [eventually_ge_atTop 1] with N hN using (key N hN).2

/-- `Φ_N = [1, N]` is a Følner sequence in `ℕ`. -/
theorem isFolnerNat_Icc_id : IsFolnerNat (fun N => Finset.Icc 1 N) :=
  isFolnerNat_Icc tendsto_id

/-- **Paper, Proposition \ref{G:prop:examples}(ii) and Theorem \ref{G:thm:q510} for the set `A'`
of Example \ref{G:ex:blocks}.**
* `Φ_N = [1, N]` is a Følner sequence;
* every element of `S'_c ∩ (G'_c + s)` is smaller than `(2|s| + 1)²` (`c = 0, 1`, `s ∈ ℤ`);
* every fibre `A'_n`, `n ≥ 1`, has natural density exactly `1/4`;
* there is no infinite `B ⊆ ℕ` and no `t ∈ ℤ²` with `(b₁ + t₁, b₂ + t₂) ∈ A'` for all
  `b₁ < b₂` in `B`. -/
theorem q510_example_blocks :
    IsFolnerNat (fun N => Finset.Icc 1 N) ∧
    (∀ (s : ℤ) (m : ℕ), m ∈ shiftInter (sqMid 1) (sqBlocks 0) s → (m : ℤ) < (2 * |s| + 1) ^ 2) ∧
    (∀ (s : ℤ) (m : ℕ), m ∈ shiftInter (sqMid 0) (sqBlocks 1) s → (m : ℤ) < (2 * |s| + 1) ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → HasDensityAlong (fun N => Finset.Icc 1 N) (fibre A' n) (1 / 4)) ∧
    ¬ ∃ (B : Set ℕ) (t : ℤ × ℤ), B.Infinite ∧ ContainsConfig A' B t := by
  refine ⟨isFolnerNat_Icc_id, fun s m hm => shiftInter_sqMid_lt (by norm_num) hm,
    fun s m hm => shiftInter_sqMid_lt (by norm_num) hm, fun n hn => ?_,
    criterion sqBlocks_disjoint
      (fun s => finite_of_lt _ fun m hm => shiftInter_sqMid_lt (by norm_num) hm)
      (fun s => finite_of_lt _ fun m hm => shiftInter_sqMid_lt (by norm_num) hm)⟩
  rcases mem_sqBlocks hn with h | h
  · rw [A', fibre_eq_left sqBlocks_disjoint h]
    exact hasDensityAlong_sqMid (by norm_num)
  · rw [A', fibre_eq_right sqBlocks_disjoint h]
    exact hasDensityAlong_sqMid (by norm_num)


theorem A'_subset_pos : A' ⊆ {q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2} := by
  have hB : ∀ p n, n ∈ sqBlocks p → 1 ≤ n := by
    rintro p n ⟨k, hk, -, h, -⟩
    have := Nat.one_le_pow 2 k hk
    omega
  have hM : ∀ p m, m ∈ sqMid p → 1 ≤ m := by
    intro p m hm
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (h ▸ hm) (zero_not_mem_sqMid p)
    · exact h
  rintro ⟨n, m⟩ (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact ⟨hB _ _ h1, hM _ _ h2⟩
  · exact ⟨hB _ _ h1, hM _ _ h2⟩

/-- **Paper, Theorem \ref{G:thm:q510}: the answer to Question 5.10 is negative.** There are a
set `A ⊆ {1, 2, …}²` and a Følner sequence `Φ` in `ℕ` such that every fibre `A_n`, `n ≥ 1`,
has density `d_Φ(A_n) = 1/4` along `Φ` (so `liminf_n d_Φ(A_n) = 1/4 > 0`), but there is no
infinite `B ⊆ ℕ` and no `t ∈ ℤ²` (in particular no `t ∈ ℕ²`) with `(b₁ + t₁, b₂ + t₂) ∈ A`
for all `b₁ < b₂` in `B`. (Take `A = A'` of Example \ref{G:ex:blocks} and `Φ_N = [1, N]`;
see also `q510_example_4k` for the set `A` of Example \ref{G:ex:4k}.) -/
theorem q510_negative :
    ∃ (A : Set (ℕ × ℕ)) (Φ : ℕ → Finset ℕ), A ⊆ {q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2} ∧
      IsFolnerNat Φ ∧ (∀ n : ℕ, 1 ≤ n → HasDensityAlong Φ (fibre A n) (1 / 4)) ∧
      ¬ ∃ (B : Set ℕ) (t : ℤ × ℤ), B.Infinite ∧ ContainsConfig A B t := by
  obtain ⟨h1, -, -, h4, h5⟩ := q510_example_blocks
  exact ⟨A', _, A'_subset_pos, h1, h4, h5⟩

end Kmrr25.Q510
