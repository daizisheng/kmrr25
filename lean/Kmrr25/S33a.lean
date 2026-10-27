import Kmrr25.Basic

/-!
# Which ordered polynomial sums are unavoidable (Question §3.3(a))

Paper, Section \ref{IA:sec:u33a}: Theorem \ref{IA:thm:u33a} and Lemmas \ref{IA:lem:P},
\ref{IA:lem:Rk}, \ref{IA:lem:subadd}.

For `f, g ∈ 𝒫 = {f ∈ ℚ[x] : f(ℕ) ⊆ ℕ₀}` and `B ⊆ ℕ` let
`f(B) ⊕_< g(B) = {f(b₁) + g(b₂) : b₁, b₂ ∈ B, b₁ < b₂}`.

## Main results

* `thm_u33a_neg` — Theorem \ref{IA:thm:u33a}\ref{IA:it:u33a-neg}, **unconditional**: for every
  `ε > 0` there is `A ⊆ ℕ` with `d̲(A) > 1 - ε` such that for all `f, g ∈ 𝒫` with
  `max (deg f, deg g) ≥ 2`, all infinite `B` and all `t ∈ ℤ`, `f(B) ⊕_< g(B) + t ⊄ A`
  (one set `A` for all pairs).
* `thm_u33a_pos` — Theorem \ref{IA:thm:u33a}\ref{IA:it:u33a-pos}, **conditional on Kousek's
  Theorem 1.2**: if `deg f, deg g ≤ 1`, every `A ⊆ ℕ` with `d*(A) > 0` contains
  `f(B) ⊕_< g(B) + t` for some infinite `B ⊆ ℕ` and `t ≥ 0`.
* `thm_u33a_classification` — the two parts together (conditional on Kousek's theorem): for
  `f, g ∈ 𝒫`, the configuration is unavoidable in sets of positive upper Banach density iff
  `deg f ≤ 1` and `deg g ≤ 1`.
* Lemma \ref{IA:lem:P}: `ClassP.intValued`, `exists_denom`, `modEq_of_denom` (i);
  `ClassP.leadingCoeff_pos`, `ClassP.natDegree_add` (ii); `ClassP.eq_linear` (iii).
* Lemma \ref{IA:lem:Rk}: `lem_Rk` (for every `ε > 0` some `k` has `|R_k(h)| < ε k`) and
  `lem_Rk_iInf` (`inf_k |R_k(h)| / k = 0`).
* Lemma \ref{IA:lem:subadd}: `lem_subadd` (natural densities, as in the paper) and the more
  general `subadd_core` (upper density bounds).
* `tendsto_ubd`: the limit in the definition of `d*` exists.

## External results

* **Kousek, Theorem 1.2** (*Asymmetric infinite sumsets in large sets of integers*) is not
  formalized. It is the `Prop` `KousekThm12`, transcribed from the paper's quotation in the
  proof of part \ref{IA:it:u33a-pos} (in a form implied by the quotation), and it is an explicit
  hypothesis of `thm_u33a_pos` and `thm_u33a_classification` only.
* **Ackelsberg, Lemma 4.3**, which the paper cites in the proof of Lemma \ref{IA:lem:Rk}, is
  stated in the form used there as the `Prop` `AckelsbergLem43` (for `h ∈ ℚ[x]` with
  `h(ℤ) ⊆ ℤ` and `deg h ≥ 2`, `∑_{p ∉ 𝒫_h} 1/p = ∞`). This `Prop` is **proved** here
  (`ackelsbergLem43`) by an argument different from Ackelsberg's: for `d = deg h` and every large
  prime `p ≡ 1 (mod d)`, `h` does not permute `ℤ/pℤ` (Hermite's criterion,
  `not_surjective_of_natDegree_dvd`), and `∑_{p ≡ 1 (mod d)} 1/p = ∞`
  (`not_summable_one_div_primes_one_mod`, derived from Mathlib's proof of Dirichlet's theorem).
  The rest of the proof of Lemma \ref{IA:lem:Rk} (`lem_Rk_of_ackelsberg`, via the Chinese
  remainder theorem) follows the paper. Hence part \ref{IA:it:u33a-neg} is unconditional.

## Conventions

* The paper's `ℕ` is `{1, 2, …}`; Lean's `ℕ` contains `0`. A set `A ⊆ {1, 2, …}` is a
  `Set ℕ` with `0 ∉ A`; `[N] = {1, …, N}` is `Finset.Icc 1 N`, and `cnt A a b = |A ∩ [a, b]|`.
* `ClassP f` means `f(n) ∈ ℕ₀` for every `n ≥ 1`. Polynomials are evaluated in `ℚ`; the
  configuration `ordSum f g B` is a subset of `ℚ`, and `ShiftSubset X t A` means `X + t ⊆ A`.
* Densities: `ldens A = liminf |A ∩ [N]| / N`, `udens A = limsup |A ∩ [N]| / N`,
  `ubd A = lim_N sup_{M ≥ 0} |A ∩ [M + 1, M + N]| / N` (as in the paper's introduction; the
  limit exists by `tendsto_ubd`).
* In `thm_u33a_neg`, `B` ranges over all infinite subsets of `{0, 1, 2, …}` (which contains the
  paper's statement for `B ⊆ {1, 2, …}`), and the set `A` satisfies `0 ∉ A`. In `thm_u33a_pos` the
  set `A` is an arbitrary `Set ℕ`, and the conclusion provides `B ⊆ {1, 2, …}`, `t ∈ ℕ₀`.
* `lem_subadd` assumes `∑ δ_j < ∞` (`Summable δ`); otherwise the paper's bound is vacuous.
-/

open Polynomial Filter Topology Finset
open scoped Classical

namespace Kmrr25.S33a

/-- The class `𝒫 = {f ∈ ℚ[x] : f(ℕ) ⊆ ℕ₀}`, where `ℕ = {1, 2, …}`. -/
def ClassP (f : ℚ[X]) : Prop := ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, f.eval (n : ℚ) = m

/-- `h ∈ ℚ[x]` is integer-valued on `ℤ`: `h(ℤ) ⊆ ℤ`. -/
def IntValued (h : ℚ[X]) : Prop := ∀ n : ℤ, ∃ m : ℤ, h.eval (n : ℚ) = m

/-! ## Lemma \ref{IA:lem:P} -/

section LemmaP

/-- A polynomial over `ℚ` taking integer values at `y + 1, …, y + deg f + 1` takes an integer
value at `y` (from the vanishing of the `(deg f + 1)`-st forward difference). -/
lemma eval_mem_of_shifts (f : ℚ[X]) (y : ℤ)
    (hy : ∀ k ∈ Finset.range (f.natDegree + 1),
      f.eval ((y + ((k + 1 : ℕ) : ℤ) : ℤ) : ℚ) ∈ (Int.castRingHom ℚ).range) :
    f.eval (y : ℚ) ∈ (Int.castRingHom ℚ).range := by
  set Z := (Int.castRingHom ℚ).range
  have h0 := congr_fun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := f)
    (Nat.lt_succ_self f.natDegree)) (y : ℚ)
  rw [fwdDiff_iter_eq_sum_shift, Finset.sum_range_succ'] at h0
  simp only [Pi.zero_apply, Nat.choose_zero_right, Nat.cast_one, mul_one, zero_smul,
    add_zero, Nat.sub_zero, zsmul_eq_mul, nsmul_eq_mul] at h0
  push_cast at h0
  obtain ⟨S, T, hsum, hT, hST⟩ : ∃ S T : ℚ, S ∈ Z ∧ T = (-1 : ℚ) ^ (f.natDegree + 1) *
      f.eval (y : ℚ) ∧ S + T = 0 := by
    refine ⟨_, _, ?_, ?_, h0⟩
    · refine Subring.sum_mem _ fun k hk => ?_
      refine Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _
        (Subring.one_mem _)) _) (natCast_mem _ _)) ?_
      have e : ((y : ℚ) + ((k : ℚ) + 1)) = (((y + ((k + 1 : ℕ) : ℤ)) : ℤ) : ℚ) := by
        push_cast; ring
      rw [e]
      exact hy k hk
    · rfl
  have h1 : (-1 : ℚ) ^ (f.natDegree + 1) * f.eval (y : ℚ) = -S := by
    rw [← hT]; linarith [hST]
  have h2 : (-1 : ℚ) ^ (f.natDegree + 1) * (-1 : ℚ) ^ (f.natDegree + 1) = 1 := by
    rw [← mul_pow]; simp
  have e : f.eval (y : ℚ) = (-1 : ℚ) ^ (f.natDegree + 1) * -S := by
    rw [← h1, ← mul_assoc, h2, one_mul]
  rw [e]
  exact Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)
    (Subring.neg_mem _ hsum)

/-- Paper, Lemma \ref{IA:lem:P}(i), first part: every `f ∈ 𝒫` satisfies `f(ℤ) ⊆ ℤ`. -/
theorem ClassP.intValued {f : ℚ[X]} (hf : ClassP f) : IntValued f := by
  set Z := (Int.castRingHom ℚ).range
  have key : ∀ m : ℕ, ∀ y : ℤ, 1 - (m : ℤ) ≤ y → f.eval (y : ℚ) ∈ Z := by
    intro m
    induction m with
    | zero =>
      intro y hy
      push_cast at hy
      obtain ⟨n, hn⟩ := hf y.toNat (by omega)
      refine ⟨n, ?_⟩
      have : ((y.toNat : ℕ) : ℚ) = (y : ℚ) := by
        have : ((y.toNat : ℕ) : ℤ) = y := by omega
        exact_mod_cast this
      rw [this] at hn
      simp [hn]
    | succ m ih =>
      intro y hy
      by_cases h : 1 - (m : ℤ) ≤ y
      · exact ih y h
      · refine eval_mem_of_shifts f y fun k _ => ih _ ?_
        push_cast
        omega
  intro n
  have hn : 1 - ((n.natAbs + 1 : ℕ) : ℤ) ≤ n := by
    push_cast
    have := neg_abs_le n
    linarith
  obtain ⟨m, hm⟩ := key (n.natAbs + 1) n hn
  exact ⟨m, by simp at hm; exact hm.symm⟩

/-- Paper, Lemma \ref{IA:lem:P}(i), second part: every `f ∈ ℚ[x]` has a common denominator:
there are `D ∈ ℕ` and `F ∈ ℤ[x]` with `F = D f`. -/
theorem exists_denom (f : ℚ[X]) :
    ∃ D : ℕ, 0 < D ∧ ∃ F : ℤ[X], F.map (Int.castRingHom ℚ) = C (D : ℚ) * f := by
  refine ⟨∏ i ∈ f.support, (f.coeff i).den, Finset.prod_pos fun i _ => Rat.den_pos _, ?_⟩
  set D := ∏ i ∈ f.support, (f.coeff i).den
  have hl : C (D : ℚ) * f ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul]
    by_cases hn : n ∈ f.support
    · have hd : (f.coeff n).den ∣ D := Finset.dvd_prod_of_mem _ hn
      obtain ⟨e, he⟩ := hd
      refine ⟨e * (f.coeff n).num, ?_⟩
      have h1 : (f.coeff n) * (f.coeff n).den = (f.coeff n).num := Rat.mul_den_eq_num _
      simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
      rw [he, ← h1]
      push_cast
      ring
    · rw [Polynomial.notMem_support_iff.mp hn, mul_zero]
      exact ⟨0, by simp⟩
  exact (Polynomial.mem_lifts _).mp hl

/-- If `F = D f` with `F ∈ ℤ[x]` and `f(x) = y`, then `F(x) = D y`. -/
lemma eval_denom {f : ℚ[X]} {D : ℕ} {F : ℤ[X]}
    (hF : F.map (Int.castRingHom ℚ) = C (D : ℚ) * f) {x y : ℤ} (hxy : f.eval (x : ℚ) = y) :
    F.eval x = D * y := by
  have h1 : ((F.map (Int.castRingHom ℚ)).eval (x : ℚ)) = ((F.eval x : ℤ) : ℚ) := by
    simp
  rw [hF, eval_mul, eval_C, hxy] at h1
  exact_mod_cast h1.symm

/-- Paper, Lemma \ref{IA:lem:P}(i), third part: if `F = D f` with `F ∈ ℤ[x]`, then
`n ≡ n' (mod D k)` implies `f(n) ≡ f(n') (mod k)`. -/
theorem modEq_of_denom {f : ℚ[X]} {D : ℕ} (hD : 0 < D) {F : ℤ[X]}
    (hF : F.map (Int.castRingHom ℚ) = C (D : ℚ) * f) (k : ℤ) {n n' m m' : ℤ}
    (hm : f.eval (n : ℚ) = m) (hm' : f.eval (n' : ℚ) = m') (hnn : (D : ℤ) * k ∣ n - n') :
    k ∣ m - m' := by
  have h1 := Polynomial.sub_dvd_eval_sub n n' F
  rw [eval_denom hF hm, eval_denom hF hm'] at h1
  obtain ⟨s, hs⟩ := hnn
  obtain ⟨Q, hQ⟩ := h1
  refine ⟨s * Q, ?_⟩
  have hD' : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  apply mul_left_cancel₀ hD'
  rw [mul_sub, hQ, hs]
  ring

/-- Paper, Lemma \ref{IA:lem:P}(ii): a non-constant `f ∈ 𝒫` has positive leading coefficient. -/
theorem ClassP.leadingCoeff_pos {f : ℚ[X]} (hf : ClassP f) (hdeg : 0 < f.natDegree) :
    0 < f.leadingCoeff := by
  by_contra hneg
  push Not at hneg
  have ht := (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos f
    (natDegree_pos_iff_degree_pos.mp hdeg) hneg).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn1, hn2⟩ := ((eventually_ge_atTop 1).and
    (ht.eventually (eventually_lt_atBot 0))).exists
  obtain ⟨m, hm⟩ := hf n hn1
  have : (0 : ℚ) ≤ f.eval (n : ℚ) := by rw [hm]; positivity
  exact absurd hn2 (not_lt.mpr this)

/-- Paper, Lemma \ref{IA:lem:P}(ii), consequence: `deg (f + g) = max (deg f) (deg g)` for
`f, g ∈ 𝒫`. -/
theorem ClassP.natDegree_add {f g : ℚ[X]} (hf : ClassP f) (hg : ClassP g) :
    (f + g).natDegree = max f.natDegree g.natDegree := by
  rcases lt_trichotomy f.natDegree g.natDegree with h | h | h
  · rw [natDegree_add_eq_right_of_natDegree_lt h, max_eq_right h.le]
  · rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
    · have : (f + g).natDegree ≤ 0 := (natDegree_add_le _ _).trans (by rw [← h, h0]; simp)
      omega
    · have hlf := hf.leadingCoeff_pos h0
      have hlg := hg.leadingCoeff_pos (h ▸ h0)
      have hf0 : f ≠ 0 := by rintro rfl; simp at h0
      have hg0 : g ≠ 0 := by rintro rfl; simp [h] at h0
      have hd := degree_add_eq_of_leadingCoeff_add_ne_zero (add_pos hlf hlg).ne'
      rw [degree_eq_natDegree hf0, degree_eq_natDegree hg0, h, max_self,
        ← degree_eq_natDegree hg0] at hd
      rw [natDegree_eq_of_degree_eq hd, h, max_self]
  · rw [natDegree_add_eq_left_of_natDegree_lt h, max_eq_left h.le]

/-- Paper, Lemma \ref{IA:lem:P}(iii): if `f ∈ 𝒫` and `deg f ≤ 1`, then `f(x) = m x + c` with
`m ∈ ℕ₀` and `c ∈ ℤ`. -/
theorem ClassP.eq_linear {f : ℚ[X]} (hf : ClassP f) (hdeg : f.natDegree ≤ 1) :
    ∃ m : ℕ, ∃ c : ℤ, f = C (m : ℚ) * X + C (c : ℚ) := by
  have e := eq_X_add_C_of_natDegree_le_one hdeg
  set a := f.coeff 1
  set b := f.coeff 0
  have hev : ∀ x : ℚ, f.eval x = a * x + b := by
    intro x; rw [e]; simp
  obtain ⟨m1, hm1⟩ := hf 1 le_rfl
  obtain ⟨m2, hm2⟩ := hf 2 (by norm_num)
  rw [hev] at hm1 hm2
  push_cast at hm1 hm2
  have ha : a = ((m2 : ℤ) - m1 : ℤ) := by push_cast; linarith
  have hb : b = ((2 * m1 : ℤ) - m2 : ℤ) := by push_cast; linarith
  have hnn : 0 ≤ (m2 : ℤ) - m1 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨m3, hm3⟩ := hf (3 * m1 + 1) (by omega)
    rw [hev, ha, hb] at hm3
    push_cast at hm3
    have h1 : ((m2 : ℤ) - m1) * (3 * m1 + 1) + (2 * m1 - m2) = (m3 : ℤ) := by exact_mod_cast hm3
    nlinarith
  refine ⟨((m2 : ℤ) - m1).toNat, (2 * m1 : ℤ) - m2, ?_⟩
  have hcast : (((m2 : ℤ) - m1 : ℤ) : ℚ) = ((((m2 : ℤ) - m1).toNat : ℕ) : ℚ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnn).symm
  rw [e, ha, hb, hcast]

end LemmaP

/-! ## Lemma \ref{IA:lem:Rk} -/

section LemmaRk

/-- `R_k(h) = {h(n) mod k : n ∈ ℤ} ⊆ ℤ/kℤ` for an integer-valued `h ∈ ℚ[x]`. -/
def Rset (h : ℚ[X]) (k : ℕ) : Set (ZMod k) :=
  {r | ∃ n : ℤ, ∃ m : ℤ, h.eval (n : ℚ) = m ∧ (m : ZMod k) = r}

/-- `h(ℤ)` meets every residue class modulo `p`, i.e. `p ∈ 𝒫_h`. -/
def HitsAll (h : ℚ[X]) (p : ℕ) : Prop := Rset h p = Set.univ

lemma Rset_ncard_le (h : ℚ[X]) (k : ℕ) [NeZero k] : (Rset h k).ncard ≤ k := by
  calc (Rset h k).ncard ≤ (Set.univ : Set (ZMod k)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
    _ = k := by rw [Set.ncard_univ, Nat.card_zmod]

/-- Chinese remainder theorem: `|R_{mn}(h)| ≤ |R_m(h)| |R_n(h)|` for coprime `m, n`. -/
lemma Rset_mul_le (h : ℚ[X]) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    (Rset h (m * n)).ncard ≤ (Rset h m).ncard * (Rset h n).ncard := by
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  rw [← Set.ncard_prod]
  refine Set.ncard_le_ncard_of_injOn (ZMod.chineseRemainder hmn) ?_
    (ZMod.chineseRemainder hmn).injective.injOn (Set.toFinite _)
  rintro r ⟨x, z, hz, rfl⟩
  rw [map_intCast]
  exact ⟨⟨x, z, hz, by simp⟩, ⟨x, z, hz, by simp⟩⟩

/-- If `p_1, …, p_s` are distinct primes outside `𝒫_h` and `k = p_1 ⋯ p_s`, then
`|R_k(h)| ≤ ∏ (p_i - 1)`. -/
lemma Rset_prod_le (h : ℚ[X]) (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime ∧ ¬ HitsAll h p) :
    (Rset h (∏ p ∈ F, p)).ncard ≤ ∏ p ∈ F, (p - 1) := by
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Rset_ncard_le h 1
  | insert a F haF ih =>
    rw [Finset.prod_insert haF, Finset.prod_insert haF]
    have ha := hF a (Finset.mem_insert_self a F)
    have hF' : ∀ p ∈ F, p.Prime ∧ ¬ HitsAll h p := fun p hp =>
      hF p (Finset.mem_insert_of_mem hp)
    have hpos : 0 < ∏ p ∈ F, p := Finset.prod_pos fun p hp => (hF' p hp).1.pos
    have hcop : a.Coprime (∏ p ∈ F, p) := Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes ha.1 (hF' p hp).1).mpr (by rintro rfl; exact haF hp)
    refine (Rset_mul_le h ha.1.pos hpos hcop).trans (Nat.mul_le_mul ?_ (ih hF'))
    have : NeZero a := ⟨ha.1.ne_zero⟩
    have := Set.ncard_lt_card ha.2
    rw [Nat.card_zmod] at this
    omega

/-- Ackelsberg, Lemma 4.3 (*Counterexamples to generalizations of the Erdős `B + B + t`
problem*), in the form in which the paper uses it: if `h ∈ ℚ[x]` satisfies `h(ℤ) ⊆ ℤ` and
`deg h ≥ 2`, then `∑_{p ∈ 𝒫 ∖ 𝒫_h} 1/p = ∞`, where `𝒫_h` is the set of primes `p` such that
`h(ℤ)` meets every residue class modulo `p`. -/
def AckelsbergLem43 : Prop :=
  ∀ h : ℚ[X], IntValued h → 2 ≤ h.natDegree →
    ¬ Summable (fun n : ℕ => if n.Prime ∧ ¬ HitsAll h n then (1 / n : ℝ) else 0)

/-- Paper, Lemma \ref{IA:lem:Rk}, derived from `AckelsbergLem43`: if `h(ℤ) ⊆ ℤ` and
`deg h ≥ 2`, then `inf_k |R_k(h)| / k = 0`, i.e. for every `ε > 0` there is `k ∈ ℕ` with
`|R_k(h)| < ε k`. -/
theorem lem_Rk_of_ackelsberg (hA : AckelsbergLem43) {h : ℚ[X]} (hint : IntValued h)
    (hdeg : 2 ≤ h.natDegree) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧ ((Rset h k).ncard : ℝ) < ε * k := by
  set v : ℕ → ℝ := fun n => if n.Prime ∧ ¬ HitsAll h n then (1 / n : ℝ) else 0 with hv
  have hv0 : ∀ n, 0 ≤ v n := fun n => by
    simp only [hv]; split_ifs <;> positivity
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hv0).mp (hA h hint hdeg)
  obtain ⟨N, hN⟩ := (ht.eventually (eventually_gt_atTop (Real.log (1 / ε)))).exists
  set F := (Finset.range N).filter (fun n => n.Prime ∧ ¬ HitsAll h n) with hFdef
  have hFp : ∀ p ∈ F, p.Prime ∧ ¬ HitsAll h p := fun p hp => (Finset.mem_filter.mp hp).2
  have hsum : ∑ i ∈ Finset.range N, v i = ∑ p ∈ F, (1 / p : ℝ) := by
    rw [hFdef, Finset.sum_filter]
  rw [hsum] at hN
  have hpos : 0 < ∏ p ∈ F, p := Finset.prod_pos fun p hp => (hFp p hp).1.pos
  refine ⟨∏ p ∈ F, p, hpos, ?_⟩
  have h1 : ((Rset h (∏ p ∈ F, p)).ncard : ℝ) ≤ ∏ p ∈ F, ((p : ℝ) - 1) := by
    have := Rset_prod_le h F hFp
    have e : ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) = ∏ p ∈ F, ((p : ℝ) - 1) := by
      push_cast
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.cast_sub (hFp p hp).1.one_le, Nat.cast_one]
    rw [← e]
    exact_mod_cast this
  have h2 : ∏ p ∈ F, ((p : ℝ) - 1) = (∏ p ∈ F, (p : ℝ)) * ∏ p ∈ F, (1 - 1 / (p : ℝ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (hFp p hp).1.ne_zero
    field_simp
  have h3 : ∏ p ∈ F, (1 - 1 / (p : ℝ)) ≤ Real.exp (-∑ p ∈ F, (1 / p : ℝ)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
    · have : (1 : ℝ) ≤ p := by exact_mod_cast (hFp p hp).1.one_le
      rw [sub_nonneg]
      exact div_le_one_of_le₀ this (by positivity)
    · have := Real.add_one_le_exp (-(1 / (p : ℝ)))
      linarith
  have h4 : Real.exp (-∑ p ∈ F, (1 / p : ℝ)) < ε := by
    have : Real.exp (-∑ p ∈ F, (1 / p : ℝ)) < Real.exp (-Real.log (1 / ε)) :=
      Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.log_div (by norm_num) hε.ne', Real.log_one, zero_sub, neg_neg,
      Real.exp_log hε] at this
  have hk : (0 : ℝ) < ∏ p ∈ F, (p : ℝ) := by
    rw [← Nat.cast_prod]; exact_mod_cast hpos
  push_cast
  calc ((Rset h (∏ p ∈ F, p)).ncard : ℝ) ≤ (∏ p ∈ F, (p : ℝ)) * ∏ p ∈ F, (1 - 1 / (p : ℝ)) :=
        h1.trans h2.le
    _ ≤ (∏ p ∈ F, (p : ℝ)) * Real.exp (-∑ p ∈ F, (1 / p : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 hk.le
    _ < (∏ p ∈ F, (p : ℝ)) * ε := mul_lt_mul_of_pos_left h4 hk
    _ = ε * ∏ p ∈ F, (p : ℝ) := mul_comm _ _

end LemmaRk

/-! ## Densities on `ℕ` -/

section Densities

/-- `|A ∩ [a, b]|` for `A ⊆ ℕ`. -/
noncomputable def cnt (A : Set ℕ) (a b : ℕ) : ℕ := ((Finset.Icc a b).filter (· ∈ A)).card

/-- Lower density `d̲(A) = liminf_{N → ∞} |A ∩ [N]| / N`, with `[N] = {1, …, N}`. -/
noncomputable def ldens (A : Set ℕ) : ℝ := liminf (fun N : ℕ => (cnt A 1 N : ℝ) / N) atTop

/-- Upper density `d̄(A) = limsup_{N → ∞} |A ∩ [N]| / N`, with `[N] = {1, …, N}`. -/
noncomputable def udens (A : Set ℕ) : ℝ := limsup (fun N : ℕ => (cnt A 1 N : ℝ) / N) atTop

/-- Upper Banach density `d*(A) = lim_{N → ∞} sup_{M ≥ 0} |A ∩ [M + 1, M + N]| / N`. -/
noncomputable def ubd (A : Set ℕ) : ℝ :=
  limUnder atTop (fun N : ℕ => (⨆ M : ℕ, (cnt A (M + 1) (M + N) : ℝ)) / N)

/-- `E` has upper density at most `δ`, in the explicit form
`∀ η > 0, |E ∩ [N]| ≤ (δ + η) N` for all large `N`. -/
def UpperDensLe (E : Set ℕ) (δ : ℝ) : Prop :=
  ∀ η > 0, ∀ᶠ N in atTop, (cnt E 1 N : ℝ) ≤ (δ + η) * N

lemma cnt_le (A : Set ℕ) (N : ℕ) : cnt A 1 N ≤ N := by
  unfold cnt
  calc _ ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
    _ = N := by simp

lemma cnt_window_le (A : Set ℕ) (M N : ℕ) : cnt A (M + 1) (M + N) ≤ N := by
  unfold cnt
  calc _ ≤ (Finset.Icc (M + 1) (M + N)).card := Finset.card_filter_le _ _
    _ = N := by simp

/-- The limit in the definition of `d*` exists (by subadditivity, Fekete's lemma), so that
`ubd A` is the limit `lim_{N → ∞} sup_M |A ∩ [M + 1, M + N]| / N`. -/
theorem tendsto_ubd (A : Set ℕ) :
    Tendsto (fun N : ℕ => (⨆ M : ℕ, (cnt A (M + 1) (M + N) : ℝ)) / N) atTop (𝓝 (ubd A)) := by
  set u : ℕ → ℝ := fun N => ⨆ M : ℕ, (cnt A (M + 1) (M + N) : ℝ) with hu
  have hbdd : ∀ N, BddAbove (Set.range fun M : ℕ => (cnt A (M + 1) (M + N) : ℝ)) := fun N =>
    ⟨N, by rintro _ ⟨M, rfl⟩; exact Nat.cast_le.mpr (cnt_window_le A M N)⟩
  have hsub : Subadditive u := by
    intro m n
    refine ciSup_le fun M => ?_
    have h1 : cnt A (M + 1) (M + (m + n)) ≤ cnt A (M + 1) (M + m) + cnt A (M + m + 1) (M + m + n) := by
      unfold cnt
      refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union] at hx ⊢
      by_cases h : x ≤ M + m
      · exact Or.inl ⟨⟨hx.1.1, h⟩, hx.2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hx.2⟩
    calc (cnt A (M + 1) (M + (m + n)) : ℝ)
        ≤ cnt A (M + 1) (M + m) + cnt A (M + m + 1) (M + m + n) := by exact_mod_cast h1
      _ ≤ u m + u n := add_le_add (le_ciSup (hbdd m) M) (le_ciSup (hbdd n) (M + m))
  have hbb : BddBelow (Set.range fun n => u n / n) :=
    ⟨0, by
      rintro _ ⟨n, rfl⟩
      exact div_nonneg (Real.iSup_nonneg fun M => Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  have ht := hsub.tendsto_lim hbb
  unfold ubd
  rw [ht.limUnder_eq]
  exact ht

/-- `UpperDensLe E δ` gives `d̄(E) ≤ δ`. -/
lemma udens_le_of_upperDensLe {E : Set ℕ} {δ : ℝ} (h : UpperDensLe E δ) : udens E ≤ δ := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  refine Filter.limsup_le_of_le (isCoboundedUnder_le_of_le atTop fun N => by positivity) ?_
  filter_upwards [h η hη, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [div_le_iff₀ hN0]
  linarith

/-- A set with natural density `δ` has upper density at most `δ`. -/
lemma upperDensLe_of_tendsto {E : Set ℕ} {δ : ℝ}
    (h : Tendsto (fun N : ℕ => (cnt E 1 N : ℝ) / N) atTop (𝓝 δ)) : UpperDensLe E δ := by
  intro η hη
  filter_upwards [h.eventually (eventually_lt_nhds (show δ < δ + η by linarith)),
    eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [div_lt_iff₀ hN0] at hN
  exact hN.le

/-- A union of residue classes: if `E = {x : x - t mod k ∈ R}`, then
`|E ∩ [N]| ≤ (N / k + 1) |R|`. -/
lemma cnt_periodic_le (k : ℕ) [NeZero k] (R : Set (ZMod k)) (t : ℤ) (N : ℕ) :
    cnt {x : ℕ | (((x : ℤ) - t : ℤ) : ZMod k) ∈ R} 1 N ≤ (N / k + 1) * R.ncard := by
  unfold cnt
  set φ : ℕ → ZMod k := fun x => (((x : ℤ) - t : ℤ) : ZMod k) with hφ
  set s := (Finset.Icc 1 N).filter (· ∈ {x : ℕ | φ x ∈ R})
  have himg : (s.image φ).card ≤ R.ncard := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro r hr
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, s, Finset.mem_filter,
      Set.mem_ofPred_eq] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact hx.2
  refine (Finset.card_le_mul_card_image s (N / k + 1) ?_).trans (Nat.mul_le_mul_left _ himg)
  intro b _
  calc _ ≤ (Finset.range (N / k + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun x => x / k) ?_ ?_
        · intro x hx
          simp only [Finset.coe_filter, Set.mem_ofPred_eq, s, Finset.mem_filter,
            Finset.mem_Icc] at hx
          simp only [Finset.coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hx.1.1.2)
        · intro x hx y hy hxy
          simp only [Finset.coe_filter, Set.mem_ofPred_eq, s, Finset.mem_filter] at hx hy
          have he : φ x = φ y := hx.2.trans hy.2.symm
          simp only [hφ, ZMod.intCast_eq_intCast_iff_dvd_sub] at he
          have hmod : x % k = y % k := by
            have hd : (k : ℤ) ∣ (y : ℤ) - x := by
              have e2 : (y : ℤ) - t - ((x : ℤ) - t) = (y : ℤ) - x := by ring
              rwa [e2] at he
            have h := Int.modEq_iff_dvd.mpr hd
            unfold Int.ModEq at h
            have : ((x % k : ℕ) : ℤ) = ((y % k : ℕ) : ℤ) := by push_cast; exact h
            exact_mod_cast this
          have hxy' : x / k = y / k := hxy
          calc x = k * (x / k) + x % k := (Nat.div_add_mod x k).symm
            _ = k * (y / k) + y % k := by rw [hxy', hmod]
            _ = y := Nat.div_add_mod y k
    _ = N / k + 1 := Finset.card_range _

/-- A union of `r` residue classes modulo `k` has upper density at most `r / k`. -/
lemma upperDensLe_periodic (k : ℕ) [NeZero k] (R : Set (ZMod k)) (t : ℤ) :
    UpperDensLe {x : ℕ | (((x : ℤ) - t : ℤ) : ZMod k) ∈ R} (R.ncard / k) := by
  intro η hη
  have hk : (0 : ℝ) < k := by exact_mod_cast (NeZero.pos k)
  filter_upwards [eventually_ge_atTop ⌈(R.ncard : ℝ) / η⌉₊] with N hN
  have h1 := cnt_periodic_le k R t N
  have h2 : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
  have h3 : (R.ncard : ℝ) / η ≤ N := (Nat.ceil_le).mp hN
  have h4 : (R.ncard : ℝ) ≤ η * N := by rwa [div_le_iff₀ hη, mul_comm] at h3
  have h5 : (cnt {x : ℕ | (((x : ℤ) - t : ℤ) : ZMod k) ∈ R} 1 N : ℝ) ≤
      ((N / k : ℕ) + 1 : ℝ) * R.ncard := by exact_mod_cast h1
  have h6 : ((N / k : ℕ) + 1 : ℝ) * R.ncard ≤ ((N : ℝ) / k + 1) * R.ncard :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h7 : ((N : ℝ) / k + 1) * R.ncard = (R.ncard / k) * N + R.ncard := by
    field_simp
  nlinarith

end Densities

/-! ## Lemma \ref{IA:lem:subadd} -/

section LemmaSubadd

/-- The core of Lemma \ref{IA:lem:subadd}, for sets `E_j` of upper density at most `δ_j`:
there is `S ⊆ ℕ` with `E_j ∖ S` finite for every `j` and `d̄(S) ≤ ∑ δ_j` (in the explicit
form `UpperDensLe`). -/
theorem subadd_core (E : ℕ → Set ℕ) (δ : ℕ → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ : Summable δ)
    (hE : ∀ j, UpperDensLe (E j) (δ j)) :
    ∃ S : Set ℕ, (∀ j, (E j \ S).Finite) ∧ UpperDensLe S (∑' j, δ j) := by
  -- `ε_J = 1 / (J + 1)^2`
  have hε : ∀ J : ℕ, (0 : ℝ) < 1 / ((J : ℝ) + 1) ^ 2 := fun J => by positivity
  have hM : ∀ i J : ℕ, ∃ M : ℕ, ∀ N ≥ M,
      (cnt (E i) 1 N : ℝ) ≤ (δ i + 1 / ((J : ℝ) + 1) ^ 2) * N := fun i J =>
    eventually_atTop.mp (hE i _ (hε J))
  choose Mf hMf using hM
  set m : ℕ → ℕ := fun J => ∑ i ∈ Finset.range (J + 1), Mf i J with hm
  set M : ℕ → ℕ := fun J => J + ∑ J' ∈ Finset.range (J + 1), m J' with hMdef
  have hMmono : Monotone M := by
    refine monotone_nat_of_le_succ fun J => ?_
    simp only [hMdef, Finset.sum_range_succ _ (J + 1)]
    omega
  have hMge : ∀ J, J ≤ M J := fun J => by simp only [hMdef]; omega
  have hMf_le : ∀ i J, i ≤ J → Mf i J ≤ M J := by
    intro i J hiJ
    calc Mf i J ≤ m J := by
          simp only [hm]
          exact Finset.single_le_sum (f := fun i => Mf i J) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))
      _ ≤ ∑ J' ∈ Finset.range (J + 1), m J' :=
          Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (by omega))
      _ ≤ M J := by simp only [hMdef]; omega
  refine ⟨{x | ∃ j, x ∈ E j ∧ M j < x}, fun j => ?_, fun η hη => ?_⟩
  · refine (Set.finite_Iic (M j)).subset fun x hx => ?_
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hx
    exact hx.2 j hx.1
  · obtain ⟨J0, hJ0⟩ := exists_nat_one_div_lt hη
    filter_upwards [eventually_ge_atTop (M J0)] with N hN
    set J := Nat.findGreatest (fun J => M J ≤ N) N with hJ
    have hJ0N : J0 ≤ N := (hMge J0).trans hN
    have hMJ : M J ≤ N := Nat.findGreatest_spec (P := fun J => M J ≤ N) hJ0N hN
    have hJ0J : J0 ≤ J := Nat.le_findGreatest (P := fun J => M J ≤ N) hJ0N hN
    have hbig : ∀ j, J < j → N < M j := by
      intro j hj
      by_cases hjN : j ≤ N
      · exact not_le.mp (Nat.findGreatest_is_greatest (P := fun J => M J ≤ N) hj hjN)
      · exact lt_of_lt_of_le (not_le.mp hjN) (hMge j)
    -- `S ∩ [N] ⊆ ⋃_{j ≤ J} (E_j ∩ [N])`
    have hsub : (Finset.Icc 1 N).filter (· ∈ {x | ∃ j, x ∈ E j ∧ M j < x}) ⊆
        (Finset.range (J + 1)).biUnion fun j => (Finset.Icc 1 N).filter (· ∈ E j) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hx
      obtain ⟨⟨hx1, hxN⟩, j, hjE, hjx⟩ := hx
      have hjJ : j ≤ J := by
        by_contra hcon
        have := hbig j (not_le.mp hcon)
        omega
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨j, by omega, ⟨hx1, hxN⟩, hjE⟩
    have hcnt : (cnt {x | ∃ j, x ∈ E j ∧ M j < x} 1 N : ℝ) ≤
        ∑ j ∈ Finset.range (J + 1), (cnt (E j) 1 N : ℝ) := by
      unfold cnt
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hterm : ∀ j ∈ Finset.range (J + 1),
        (cnt (E j) 1 N : ℝ) ≤ (δ j + 1 / ((J : ℝ) + 1) ^ 2) * N := by
      intro j hj
      exact hMf j J N ((hMf_le j J (by simpa [Nat.lt_succ_iff] using hj)).trans hMJ)
    have hpart : ∑ j ∈ Finset.range (J + 1), δ j ≤ ∑' j, δ j :=
      hδ.sum_le_tsum _ fun j _ => hδ0 j
    have hJη : 1 / ((J : ℝ) + 1) ≤ η := by
      have : 1 / ((J : ℝ) + 1) ≤ 1 / ((J0 : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.succ_le_succ hJ0J
      linarith
    have hNn : (0 : ℝ) ≤ N := by positivity
    calc (cnt {x | ∃ j, x ∈ E j ∧ M j < x} 1 N : ℝ)
        ≤ ∑ j ∈ Finset.range (J + 1), (δ j + 1 / ((J : ℝ) + 1) ^ 2) * N :=
          hcnt.trans (Finset.sum_le_sum hterm)
      _ = (∑ j ∈ Finset.range (J + 1), δ j + 1 / ((J : ℝ) + 1)) * N := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
          congr 1
          push_cast
          field_simp
      _ ≤ (∑' j, δ j + η) * N := by
          apply mul_le_mul_of_nonneg_right _ hNn
          linarith

/-- Paper, Lemma \ref{IA:lem:subadd}: let `E_1, E_2, … ⊆ ℕ` have natural densities
`δ_1, δ_2, …` with `∑ δ_j < ∞`. Then there is `S ⊆ ℕ` such that `E_j ∖ S` is finite for every
`j` and `d̄(S) ≤ ∑_j δ_j`. -/
theorem lem_subadd (E : ℕ → Set ℕ) (δ : ℕ → ℝ)
    (hE : ∀ j, Tendsto (fun N : ℕ => (cnt (E j) 1 N : ℝ) / N) atTop (𝓝 (δ j)))
    (hδ : Summable δ) :
    ∃ S : Set ℕ, (∀ j, (E j \ S).Finite) ∧ udens S ≤ ∑' j, δ j := by
  have hδ0 : ∀ j, 0 ≤ δ j := fun j =>
    ge_of_tendsto' (hE j) fun N => by positivity
  obtain ⟨S, hS, hd⟩ := subadd_core E δ hδ0 hδ fun j => upperDensLe_of_tendsto (hE j)
  exact ⟨S, hS, udens_le_of_upperDensLe hd⟩

end LemmaSubadd

/-! ## Ordered polynomial sums and Theorem \ref{IA:thm:u33a}\ref{IA:it:u33a-neg} -/

section Negative

/-- The ordered sum set `f(B) ⊕_< g(B) = {f(b₁) + g(b₂) : b₁, b₂ ∈ B, b₁ < b₂}`. -/
def ordSum (f g : ℚ[X]) (B : Set ℕ) : Set ℚ :=
  {x | ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ < b₂ ∧ x = f.eval (b₁ : ℚ) + g.eval (b₂ : ℚ)}

/-- `X + t ⊆ A` for `X ⊆ ℚ`, `t ∈ ℤ` and `A ⊆ ℕ`. -/
def ShiftSubset (X : Set ℚ) (t : ℤ) (A : Set ℕ) : Prop :=
  ∀ x ∈ X, ∃ a ∈ A, (a : ℚ) = x + t

lemma coeffList_getD (p : ℚ[X]) (i : ℕ) :
    ((List.range (p.natDegree + 1)).map p.coeff).getD i 0 = p.coeff i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < p.natDegree + 1
  · rw [List.getElem?_range h]; simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    simp only [Option.map_none, Option.getD_none]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- `ℚ[x]` is countable. -/
lemma countable_polynomial : Countable ℚ[X] := by
  refine Function.Injective.countable
    (f := fun p : ℚ[X] => (List.range (p.natDegree + 1)).map p.coeff) ?_
  intro p q hpq
  ext i
  rw [← coeffList_getD p i, ← coeffList_getD q i]
  exact congrArg (fun L => L.getD i 0) hpq

lemma IntValued.add {f g : ℚ[X]} (hf : IntValued f) (hg : IntValued g) : IntValued (f + g) := by
  intro n
  obtain ⟨a, ha⟩ := hf n
  obtain ⟨b, hb⟩ := hg n
  exact ⟨a + b, by rw [eval_add, ha, hb]; push_cast; ring⟩

lemma classP_X_sq : ClassP (X ^ 2 : ℚ[X]) := fun n _ => ⟨n ^ 2, by simp⟩

lemma classP_zero : ClassP (0 : ℚ[X]) := fun _ _ => ⟨0, by simp⟩

/-- A non-constant `f ∈ 𝒫` tends to `+∞` along `ℕ`. -/
lemma ClassP.tendsto_atTop {f : ℚ[X]} (hf : ClassP f) (hdeg : 0 < f.natDegree) :
    Tendsto (fun b : ℕ => f.eval (b : ℚ)) atTop atTop :=
  (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg f (natDegree_pos_iff_degree_pos.mp hdeg)
    (hf.leadingCoeff_pos hdeg).le).comp tendsto_natCast_atTop_atTop

/-- Pigeonhole: an infinite `B ⊆ ℕ` has infinitely many elements in some residue class
modulo `L`. -/
lemma exists_infinite_residue {B : Set ℕ} (hB : B.Infinite) (L : ℕ) [NeZero L] :
    ∃ r : ZMod L, (B ∩ {b | (b : ZMod L) = r}).Infinite := by
  by_contra hcon
  push Not at hcon
  apply hB
  have : B = ⋃ r : ZMod L, (B ∩ {b | (b : ZMod L) = r}) := by
    ext b; simp
  rw [this]
  exact Set.finite_iUnion fun r => hcon r

/-- Lemma \ref{IA:lem:Rk} in the form used in the proof of
Theorem \ref{IA:thm:u33a}\ref{IA:it:u33a-neg}. -/
def LemmaRkStatement : Prop :=
  ∀ h : ℚ[X], IntValued h → 2 ≤ h.natDegree → ∀ ε : ℝ, 0 < ε →
    ∃ k : ℕ, 0 < k ∧ ((Rset h k).ncard : ℝ) < ε * k

/-- Paper, Theorem \ref{IA:thm:u33a}\ref{IA:it:u33a-neg}, derived from
Lemma \ref{IA:lem:Rk}. -/
theorem u33a_neg_of_lemmaRk (hRk : LemmaRkStatement) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Set ℕ, 0 ∉ A ∧ 1 - ε < ldens A ∧
      ∀ f g : ℚ[X], ClassP f → ClassP g → 2 ≤ max f.natDegree g.natDegree →
        ∀ B : Set ℕ, B.Infinite → ∀ t : ℤ, ¬ ShiftSubset (ordSum f g B) t A := by
  have := countable_polynomial
  -- enumerate the triples `(f, g, t)`
  let T := {q : ℚ[X] × ℚ[X] × ℤ //
    ClassP q.1 ∧ ClassP q.2.1 ∧ 2 ≤ max q.1.natDegree q.2.1.natDegree}
  have hTne : Nonempty T := ⟨⟨(X ^ 2, 0, 0), classP_X_sq, classP_zero, by simp⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat T
  have hhint : ∀ j, IntValued ((e j).1.1 + (e j).1.2.1) := fun j =>
    (e j).2.1.intValued.add (e j).2.2.1.intValued
  have hhdeg : ∀ j, 2 ≤ ((e j).1.1 + (e j).1.2.1).natDegree := fun j => by
    rw [(e j).2.1.natDegree_add (e j).2.2.1]; exact (e j).2.2.2
  have hk : ∀ j : ℕ, ∃ k : ℕ, 0 < k ∧
      ((Rset ((e j).1.1 + (e j).1.2.1) k).ncard : ℝ) < ε / 2 / 2 ^ j * k := fun j =>
    hRk _ (hhint j) (hhdeg j) _ (by positivity)
  choose k hkpos hkR using hk
  let δ : ℕ → ℝ := fun j => (Rset ((e j).1.1 + (e j).1.2.1) (k j)).ncard / k j
  let E : ℕ → Set ℕ := fun j =>
    {x : ℕ | (((x : ℤ) - (e j).1.2.2 : ℤ) : ZMod (k j)) ∈ Rset ((e j).1.1 + (e j).1.2.1) (k j)}
  have hδ0 : ∀ j, 0 ≤ δ j := fun j => by positivity
  have hδlt : ∀ j, δ j < ε / 2 / 2 ^ j := fun j => by
    have : (0 : ℝ) < k j := by exact_mod_cast hkpos j
    exact (div_lt_iff₀ this).mpr (hkR j)
  have hδs : Summable δ :=
    Summable.of_nonneg_of_le hδ0 (fun j => (hδlt j).le) (summable_geometric_two' ε)
  have hδsum : ∑' j, δ j < ε := by
    have := Summable.tsum_lt_tsum_of_nonneg (i := 0) hδ0 (fun j => (hδlt j).le) (hδlt 0)
      (summable_geometric_two' ε)
    rwa [tsum_geometric_two'] at this
  have hE : ∀ j, UpperDensLe (E j) (δ j) := fun j => by
    have : NeZero (k j) := ⟨(hkpos j).ne'⟩
    exact upperDensLe_periodic _ _ _
  obtain ⟨S, hSfin, hSd⟩ := subadd_core E δ hδ0 hδs hE
  refine ⟨{x | 1 ≤ x ∧ x ∉ S}, by simp, ?_, ?_⟩
  · -- the lower density of `A = ℕ ∖ S`
    set σ := ∑' j, δ j
    have hη : 0 < (ε - σ) / 2 := by linarith
    have hcntA : ∀ N, (cnt {x | 1 ≤ x ∧ x ∉ S} 1 N : ℝ) + cnt S 1 N = N := by
      intro N
      have : cnt {x | 1 ≤ x ∧ x ∉ S} 1 N + cnt S 1 N = N := by
        unfold cnt
        rw [← Finset.card_union_of_disjoint]
        · refine (congrArg Finset.card (?_ : _ = Finset.Icc 1 N)).trans (by simp)
          ext x
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
          tauto
        · rw [Finset.disjoint_left]
          intro x hx hx'
          simp only [Finset.mem_filter, Set.mem_ofPred_eq] at hx hx'
          exact hx.2.2 hx'.2
      exact_mod_cast this
    refine lt_of_lt_of_le (b := 1 - σ - (ε - σ) / 2) (by linarith) ?_
    refine Filter.le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (x := 1) fun N => ?_) ?_
    · exact div_le_one_of_le₀ (by exact_mod_cast cnt_le _ N) (by positivity)
    · filter_upwards [hSd _ hη, eventually_ge_atTop 1] with N hN hN1
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
      rw [le_div_iff₀ hN0]
      have := hcntA N
      nlinarith
  · -- no configuration `f(B) ⊕_< g(B) + t` in `A`
    intro f g hf hg hdeg B hB t hsub
    obtain ⟨j, hj⟩ := he ⟨(f, g, t), hf, hg, hdeg⟩
    have hej : (e j).1 = (f, g, t) := by rw [hj]
    set K := k j with hK
    have hKpos : 0 < K := hkpos j
    obtain ⟨Df, hDf, Ff, hFf⟩ := exists_denom f
    obtain ⟨Dg, hDg, Fg, hFg⟩ := exists_denom g
    set L := Df * Dg * K with hL
    have hLpos : 0 < L := by positivity
    have : NeZero L := ⟨hLpos.ne'⟩
    obtain ⟨r, hr⟩ := exists_infinite_residue hB L
    set B' := B ∩ {b | (b : ZMod L) = r}
    obtain ⟨n, hn⟩ := hr.nonempty
    have hcong : ∀ b ∈ B', (L : ℤ) ∣ (b : ℤ) - n := by
      intro b hb
      have h1 : ((b : ℤ) : ZMod L) = ((n : ℤ) : ZMod L) := by
        simp only [Int.cast_natCast]; exact hb.2.trans hn.2.symm
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1.symm
    have hfi := hf.intValued
    have hgi := hg.intValued
    obtain ⟨mf, hmf⟩ := hfi n
    obtain ⟨mg, hmg⟩ := hgi n
    -- every element of the configuration lies in `E j ∖ S`
    have key : ∀ b₁ ∈ B', ∀ b₂ ∈ B', b₁ < b₂ →
        ∃ a : ℕ, a ∈ E j \ S ∧ (a : ℚ) = f.eval (b₁ : ℚ) + g.eval (b₂ : ℚ) + t := by
      intro b₁ hb₁ b₂ hb₂ hlt
      obtain ⟨a, haA, ha⟩ := hsub _ ⟨b₁, hb₁.1, b₂, hb₂.1, hlt, rfl⟩
      refine ⟨a, ⟨?_, haA.2⟩, ha⟩
      obtain ⟨m1, hm1⟩ := hfi b₁
      obtain ⟨m2, hm2⟩ := hgi b₂
      have d1 : (K : ℤ) ∣ m1 - mf := modEq_of_denom hDf hFf K hm1 hmf
        (dvd_trans (⟨(Dg : ℤ), by push_cast [hL]; ring⟩ : (Df : ℤ) * K ∣ (L : ℤ))
          (hcong b₁ hb₁))
      have d2 : (K : ℤ) ∣ m2 - mg := modEq_of_denom hDg hFg K hm2 hmg
        (dvd_trans (⟨(Df : ℤ), by push_cast [hL]; ring⟩ : (Dg : ℤ) * K ∣ (L : ℤ))
          (hcong b₂ hb₂))
      simp only [Int.cast_natCast] at hm1 hm2 hmf hmg
      have haz : (a : ℤ) = m1 + m2 + t := by
        have : (a : ℚ) = ((m1 + m2 + t : ℤ) : ℚ) := by rw [ha, hm1, hm2]; push_cast; ring
        exact_mod_cast this
      show (((a : ℤ) - (e j).1.2.2 : ℤ) : ZMod (k j)) ∈ Rset ((e j).1.1 + (e j).1.2.1) (k j)
      rw [hej]
      refine ⟨n, mf + mg, by simp [eval_add, hmf, hmg], ?_⟩
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      have e3 : (a : ℤ) - t - (mf + mg) = (m1 - mf) + (m2 - mg) := by rw [haz]; ring
      simp only
      rw [e3]
      exact dvd_add d1 d2
    -- the configuration is unbounded
    have unb : ∀ C : ℚ, ∃ b₁ ∈ B', ∃ b₂ ∈ B', b₁ < b₂ ∧ C < f.eval (b₁ : ℚ) + g.eval (b₂ : ℚ) := by
      intro C
      rcases Nat.eq_zero_or_pos g.natDegree with hg0 | hgpos
      · have hfdeg : 0 < f.natDegree := by
          rw [hg0] at hdeg; simp at hdeg; omega
        have hgc : ∀ b : ℚ, g.eval b = g.coeff 0 := fun b => by
          rw [eq_C_of_natDegree_eq_zero hg0]; simp
        obtain ⟨N0, hN0⟩ := eventually_atTop.mp
          ((hf.tendsto_atTop hfdeg).eventually (eventually_gt_atTop (C - g.coeff 0)))
        obtain ⟨b₁, hb₁, hb₁N⟩ := hr.exists_gt N0
        obtain ⟨b₂, hb₂, hb₂N⟩ := hr.exists_gt b₁
        refine ⟨b₁, hb₁, b₂, hb₂, hb₂N, ?_⟩
        have := hN0 b₁ hb₁N.le
        rw [hgc]
        linarith
      · obtain ⟨N0, hN0⟩ := eventually_atTop.mp
          ((hg.tendsto_atTop hgpos).eventually (eventually_gt_atTop (C - f.eval (n : ℚ))))
        obtain ⟨b₂, hb₂, hb₂N⟩ := hr.exists_gt (max n N0)
        refine ⟨n, hn, b₂, hb₂, lt_of_le_of_lt (le_max_left _ _) hb₂N, ?_⟩
        have := hN0 b₂ (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hb₂N))
        linarith
    obtain ⟨U, hU⟩ := (hSfin j).bddAbove
    obtain ⟨b₁, hb₁, b₂, hb₂, hlt, hbig⟩ := unb ((U : ℚ) + 1 - t)
    obtain ⟨a, ha, haeq⟩ := key b₁ hb₁ b₂ hb₂ hlt
    have h1 : a ≤ U := hU ha
    have h2 : (a : ℚ) ≤ U := by exact_mod_cast h1
    linarith

end Negative

/-! ## A proof of the case of Ackelsberg's Lemma 4.3 used here

We prove `AckelsbergLem43` (so that Lemma \ref{IA:lem:Rk} and
Theorem \ref{IA:thm:u33a}\ref{IA:it:u33a-neg} hold unconditionally) by a classical argument which
is different from Ackelsberg's: if `d = deg h ≥ 2`, then for every large prime `p ≡ 1 (mod d)` the
reduction of `h` modulo `p` is not a permutation of `ℤ/pℤ` (Hermite's criterion), and
`∑_{p ≡ 1 (mod d)} 1/p = ∞` (Dirichlet's theorem, from Mathlib's lower bound for the
`L`-series of the von Mangoldt function restricted to a residue class). -/

section AckelsbergProof

lemma sum_pow_card_sub_one_zmod (p : ℕ) [Fact p.Prime] : ∑ x : ZMod p, x ^ (p - 1) = -1 := by
  have hp := (Fact.out : p.Prime)
  have h1 : ∀ x : ZMod p, x ^ (p - 1) = 1 - if x = 0 then 1 else 0 := by
    intro x
    split_ifs with hx
    · rw [hx, zero_pow (by have := hp.two_le; omega)]; ring
    · rw [ZMod.pow_card_sub_one_eq_one hx]; ring
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (0 : ZMod p)]
  simp

/-- For `Q ∈ (ℤ/pℤ)[x]` of degree at most `p - 1`, `∑_x Q(x) = -[x^{p-1}] Q`. -/
lemma sum_eval_eq_neg_coeff (p : ℕ) [Fact p.Prime] (Q : (ZMod p)[X])
    (hQ : Q.natDegree ≤ p - 1) : ∑ x : ZMod p, Q.eval x = -Q.coeff (p - 1) := by
  have hp := (Fact.out : p.Prime)
  have hlt : Q.natDegree < p := by have := hp.two_le; omega
  simp_rw [eval_eq_sum_range' hlt]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single (p - 1)]
  · rw [sum_pow_card_sub_one_zmod]; ring
  · intro i hi hne
    rw [FiniteField.sum_pow_lt_card_sub_one (ZMod p) i (by
      rw [ZMod.card]; have := Finset.mem_range.mp hi; omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by have := hp.two_le; omega)) h

/-- Hermite's criterion (a special case): a polynomial over `ℤ/pℤ` of degree `d ≥ 2` with
`d ∣ p - 1` does not induce a surjection (equivalently, a permutation) of `ℤ/pℤ`. -/
theorem not_surjective_of_natDegree_dvd (p : ℕ) [Fact p.Prime] (P : (ZMod p)[X])
    (hd : 2 ≤ P.natDegree) (hdvd : P.natDegree ∣ p - 1) :
    ¬ Function.Surjective (fun x => P.eval x) := by
  intro hs
  have hp := (Fact.out : p.Prime)
  have hbij : Function.Bijective (fun x => P.eval x) :=
    ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  obtain ⟨t, ht⟩ := hdvd
  have hp2 := hp.two_le
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, mul_zero] at ht; omega
    · exact h0
  have htlt : t < p - 1 := by
    rw [ht]; nlinarith
  have h1 : ∑ x : ZMod p, (P.eval x) ^ t = 0 := by
    rw [Function.Bijective.sum_comp hbij (fun y => y ^ t)]
    exact FiniteField.sum_pow_lt_card_sub_one _ t (by rw [ZMod.card]; exact htlt)
  have hdeg : (P ^ t).natDegree = p - 1 := by rw [natDegree_pow, ht, mul_comm]
  have h2 := sum_eval_eq_neg_coeff p (P ^ t) hdeg.le
  simp_rw [eval_pow] at h2
  rw [h1, ← hdeg, coeff_natDegree, leadingCoeff_pow] at h2
  have hP0 : P ≠ 0 := by rintro rfl; simp at hd
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  exact pow_ne_zero t hlc (neg_eq_zero.mp h2.symm)

open ArithmeticFunction ArithmeticFunction.vonMangoldt in
/-- Dirichlet's theorem in the form `∑_{p ≡ 1 (mod q)} 1/p = ∞`. -/
theorem not_summable_one_div_primes_one_mod (q : ℕ) [NeZero q] :
    ¬ Summable (fun n : ℕ => if n.Prime ∧ (n : ZMod q) = 1 then (1 / n : ℝ) else 0) := by
  intro hu
  set u : ℕ → ℝ := fun n => if n.Prime ∧ (n : ZMod q) = 1 then (1 / n : ℝ) else 0 with hudef
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [hudef]; split_ifs <;> positivity
  obtain ⟨C, hC⟩ := LSeries_residueClass_lower_bound (q := q) (a := 1) isUnit_one
  set c : ℝ := (q.totient : ℝ)⁻¹ with hcdef
  have hc : 0 < c := inv_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q))
  set v : ℕ → ℝ := fun n => (if n.Prime then 0 else residueClass (1 : ZMod q) n) / n with hvdef
  have hv : Summable v := summable_residueClass_non_primes_div 1
  have hv0 : ∀ n, 0 ≤ v n := fun n => by
    simp only [hvdef]; split_ifs
    · simp
    · exact div_nonneg (residueClass_nonneg _ _) (Nat.cast_nonneg _)
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, ∑' k, u (k + Y) < c / 2 :=
    ((tendsto_sum_nat_add u).eventually (gt_mem_nhds (half_pos hc))).exists
  set T : ℕ → ℝ := fun n => if Y ≤ n then u n else 0 with hTdef
  have hT0 : ∀ n, 0 ≤ T n := fun n => by simp only [hTdef]; split_ifs; exacts [hu0 n, le_rfl]
  have hTs : Summable T := Summable.of_nonneg_of_le hT0
    (fun n => by simp only [hTdef]; split_ifs; exacts [le_rfl, hu0 n]) hu
  have hT : ∑' n, T n = ∑' k, u (k + Y) := by
    rw [← hTs.sum_add_tsum_nat_add Y, Finset.sum_eq_zero (fun i hi => by
      simp only [hTdef, if_neg (not_le.mpr (Finset.mem_range.mp hi))]), zero_add]
    exact tsum_congr fun k => by simp [hTdef]
  have hlogY : 0 ≤ Real.log Y := Real.log_natCast_nonneg Y
  -- the termwise bound
  have hterm : ∀ x : ℝ, 1 < x → ∀ n : ℕ, residueClass (1 : ZMod q) n / (n : ℝ) ^ x ≤
      Real.log Y * u n + (1 / (x - 1)) * T n + v n := by
    intro x hx n
    have hx1 : 0 < x - 1 := by linarith
    have hR0 : 0 ≤ Real.log Y * u n + (1 / (x - 1)) * T n := by
      have := hu0 n; have := hT0 n; positivity
    by_cases hn : n.Prime
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.one_le
      have hnpos : (0 : ℝ) < n := by linarith
      have hvn : v n = 0 := by simp [hvdef, hn]
      rw [hvn, add_zero]
      by_cases hcl : (n : ZMod q) = 1
      · have hres : residueClass (1 : ZMod q) n = Real.log n := by
          simp only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq, hcl, if_true]
          exact vonMangoldt_apply_prime hn
        have hun : u n = 1 / n := by simp [hudef, hn, hcl]
        rw [hres]
        have hnx : (n : ℝ) ≤ (n : ℝ) ^ x := Real.self_le_rpow_of_one_le hn1 hx.le
        by_cases hYn : Y ≤ n
        · have hTn : T n = 1 / n := by simp [hTdef, hYn, hun]
          have hlog := Real.log_le_rpow_div hnpos.le hx1
          have hsplit : (n : ℝ) ^ x = (n : ℝ) ^ (x - 1) * n := by
            rw [Real.rpow_sub_one hnpos.ne']; field_simp
          have hpow : 0 < (n : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hnpos _
          have : Real.log n / (n : ℝ) ^ x ≤ (1 / (x - 1)) * T n := by
            rw [hTn, hsplit, div_le_iff₀ (by positivity)]
            calc Real.log n ≤ (n : ℝ) ^ (x - 1) / (x - 1) := hlog
              _ = 1 / (x - 1) * (1 / n) * ((n : ℝ) ^ (x - 1) * n) := by field_simp
          have := hu0 n
          nlinarith
        · have hnY : (n : ℝ) ≤ Y := by exact_mod_cast (not_le.mp hYn).le
          have hlogn : Real.log n ≤ Real.log Y := Real.log_le_log hnpos hnY
          have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
          have : Real.log n / (n : ℝ) ^ x ≤ Real.log Y * u n := by
            rw [hun]
            calc Real.log n / (n : ℝ) ^ x ≤ Real.log n / n :=
                  div_le_div_of_nonneg_left hlog0 hnpos hnx
              _ ≤ Real.log Y / n := div_le_div_of_nonneg_right hlogn hnpos.le
              _ = Real.log Y * (1 / n) := by ring
          have := hT0 n
          have : 0 ≤ 1 / (x - 1) * T n := by positivity
          linarith
      · have hres : residueClass (1 : ZMod q) n = 0 := by
          simp [residueClass, hcl]
        rw [hres, zero_div]
        exact hR0
    · have hvn : v n = residueClass (1 : ZMod q) n / n := by simp [hvdef, hn]
      rw [hvn]
      have h1 : residueClass (1 : ZMod q) n / (n : ℝ) ^ x ≤ residueClass (1 : ZMod q) n / n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; simp
        · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h0
          exact div_le_div_of_nonneg_left (residueClass_nonneg _ _) (by linarith)
            (Real.self_le_rpow_of_one_le hn1 hx.le)
      linarith
  set K' : ℝ := C + Real.log Y * ∑' n, u n + ∑' n, v n with hK'
  set δ0 : ℝ := min 1 (c / (2 * (|K'| + 1))) with hδ0
  have hδpos : 0 < δ0 := lt_min one_pos (by positivity)
  have hδle : δ0 ≤ c / (2 * (|K'| + 1)) := min_le_right _ _
  set x : ℝ := 1 + δ0 with hxdef
  have hx : x ∈ Set.Ioc 1 2 := ⟨by linarith, by linarith [min_le_left 1 (c / (2 * (|K'| + 1)))]⟩
  have hx1 : 1 < x := hx.1
  have hlow := hC hx
  have hRs : Summable fun n => Real.log Y * u n + (1 / (x - 1)) * T n + v n :=
    ((hu.mul_left _).add (hTs.mul_left _)).add hv
  have hLs : Summable fun n => residueClass (1 : ZMod q) n / (n : ℝ) ^ x :=
    Summable.of_nonneg_of_le (fun n => div_nonneg (residueClass_nonneg _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hterm x hx1) hRs
  have hup := hLs.tsum_le_tsum (hterm x hx1) hRs
  rw [Summable.tsum_add ((hu.mul_left _).add (hTs.mul_left _)) hv,
    Summable.tsum_add (hu.mul_left _) (hTs.mul_left _), tsum_mul_left, tsum_mul_left, hT] at hup
  have hxδ : x - 1 = δ0 := by rw [hxdef]; ring
  rw [hxδ] at hlow hup
  have hinv : 0 < 1 / δ0 := by positivity
  have h3 : 1 / δ0 * ∑' k, u (k + Y) ≤ 1 / δ0 * (c / 2) := mul_le_mul_of_nonneg_left hY.le hinv.le
  have h4 : c / δ0 - C ≤ Real.log Y * ∑' n, u n + 1 / δ0 * (c / 2) + ∑' n, v n := by
    have := hlow.trans hup
    rw [div_eq_mul_one_div c δ0] at this ⊢
    linarith
  have h5 : c / (2 * δ0) ≤ K' := by
    have e : c / δ0 = c / (2 * δ0) + 1 / δ0 * (c / 2) := by field_simp; ring
    rw [hK']; linarith
  have h6 : |K'| + 1 ≤ c / (2 * δ0) := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hδle
    nlinarith [abs_nonneg K']
  linarith [le_abs_self K']

/-- Large primes `p ≡ 1 (mod deg h)` lie outside `𝒫_h`. -/
lemma not_hitsAll_of_large {h : ℚ[X]} (hdeg : 2 ≤ h.natDegree) {D : ℕ} (hD : 0 < D)
    {F : ℤ[X]} (hF : F.map (Int.castRingHom ℚ) = C (D : ℚ) * h) {p : ℕ} (hp : p.Prime)
    (hp1 : (p : ZMod h.natDegree) = 1) (hpD : D < p) (hpc : F.leadingCoeff.natAbs < p) :
    ¬ HitsAll h p := by
  intro hall
  have : Fact p.Prime := ⟨hp⟩
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hFdeg : F.natDegree = h.natDegree := by
    have := congrArg natDegree hF
    rwa [natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)),
      natDegree_C_mul hD0] at this
  have hF0 : F ≠ 0 := by rintro rfl; simp at hFdeg; omega
  set P := F.map (Int.castRingHom (ZMod p)) with hP
  have hlc : (Int.castRingHom (ZMod p)) F.leadingCoeff ≠ 0 := by
    intro h0
    rw [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h0 (by simpa using hpc)
    exact leadingCoeff_ne_zero.mpr hF0 this
  have hPdeg : P.natDegree = h.natDegree := by
    rw [hP, natDegree_map_of_leadingCoeff_ne_zero _ hlc, hFdeg]
  have hdvd : h.natDegree ∣ p - 1 := by
    have h1 : p % h.natDegree = 1 := by
      have := (ZMod.natCast_eq_natCast_iff' p 1 h.natDegree).mp (by simpa using hp1)
      rwa [Nat.mod_eq_of_lt (by omega : 1 < h.natDegree)] at this
    have := Nat.dvd_sub_mod (n := h.natDegree) p
    rwa [h1] at this
  have hDp : (D : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => absurd (Nat.le_of_dvd hD hd) (not_le.mpr hpD)
  apply not_surjective_of_natDegree_dvd p P (hPdeg ▸ hdeg) (hPdeg ▸ hdvd)
  intro s
  have hr : s * (D : ZMod p)⁻¹ ∈ Rset h p := by rw [hall]; trivial
  obtain ⟨n, m, hnm, hm⟩ := hr
  refine ⟨n, ?_⟩
  simp only [hP]
  rw [Polynomial.eval_intCast_map, Int.cast_id, eval_denom hF hnm, map_mul, eq_intCast,
    eq_intCast, Int.cast_natCast, hm, mul_comm, mul_assoc, inv_mul_cancel₀ hDp, mul_one]

/-- Ackelsberg's Lemma 4.3, in the form `AckelsbergLem43` used in the paper, proved via
Hermite's criterion and Dirichlet's theorem. -/
theorem ackelsbergLem43 : AckelsbergLem43 := by
  intro h hint hdeg hsum
  obtain ⟨D, hD, F, hF⟩ := exists_denom h
  set d := h.natDegree with hd
  have : NeZero d := ⟨by omega⟩
  set M := D + F.leadingCoeff.natAbs with hM
  apply not_summable_one_div_primes_one_mod d
  have hfin : Summable fun n : ℕ => if n ≤ M then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := Finset.range (M + 1)) fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_le]
      omega
  refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
    (hsum.add hfin)
  by_cases hpn : n.Prime ∧ (n : ZMod d) = 1
  · rw [if_pos hpn]
    by_cases hnM : n ≤ M
    · have h1 : (1 / n : ℝ) ≤ 1 := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · simp [h0]
        · exact div_le_one_of_le₀ (by exact_mod_cast h0) (by positivity)
      have h2 : (0 : ℝ) ≤ if n.Prime ∧ ¬ HitsAll h n then (1 / n : ℝ) else 0 := by
        split_ifs <;> positivity
      rw [if_pos hnM]
      linarith
    · have hnh : ¬ HitsAll h n := not_hitsAll_of_large hdeg hD hF hpn.1 hpn.2 (by omega)
        (by omega)
      rw [if_pos ⟨hpn.1, hnh⟩, if_neg hnM, add_zero]
  · rw [if_neg hpn]
    have h2 : (0 : ℝ) ≤ if n.Prime ∧ ¬ HitsAll h n then (1 / n : ℝ) else 0 := by
      split_ifs <;> positivity
    have h3 : (0 : ℝ) ≤ if n ≤ M then (1 : ℝ) else 0 := by split_ifs <;> positivity
    linarith

end AckelsbergProof

/-! ## Main results -/

/-- Paper, Lemma \ref{IA:lem:Rk}: if `h ∈ ℚ[x]` satisfies `h(ℤ) ⊆ ℤ` and `deg h ≥ 2`, then
`inf_{k ∈ ℕ} |R_k(h)| / k = 0`, in the form: for every `ε > 0` there is `k ≥ 1` with
`|R_k(h)| < ε k`. -/
theorem lem_Rk : LemmaRkStatement := fun _ hint hdeg ε hε =>
  lem_Rk_of_ackelsberg ackelsbergLem43 hint hdeg ε hε

/-- Paper, Lemma \ref{IA:lem:Rk}, literally: `inf_{k ∈ ℕ} |R_k(h)| / k = 0`. -/
theorem lem_Rk_iInf {h : ℚ[X]} (hint : IntValued h) (hdeg : 2 ≤ h.natDegree) :
    ⨅ k : ℕ+, ((Rset h k).ncard : ℝ) / (k : ℕ) = 0 := by
  have hbdd : BddBelow (Set.range fun k : ℕ+ => ((Rset h k).ncard : ℝ) / (k : ℕ)) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_ciInf fun k => by positivity)
  obtain ⟨k, hk, hkR⟩ := lem_Rk h hint hdeg ε hε
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  calc ⨅ k : ℕ+, ((Rset h k).ncard : ℝ) / (k : ℕ) ≤ ((Rset h k).ncard : ℝ) / k :=
        ciInf_le hbdd ⟨k, hk⟩
    _ ≤ ε := by rw [div_le_iff₀ hk']; exact hkR.le
    _ = 0 + ε := by ring

/-- Paper, Theorem \ref{IA:thm:u33a}\ref{IA:it:u33a-neg}: for every `ε > 0` there is a set
`A ⊆ ℕ = {1, 2, …}` with lower density `> 1 - ε` such that for **all** `f, g ∈ 𝒫` with
`max (deg f, deg g) ≥ 2`, every infinite `B ⊆ ℕ` and every `t ∈ ℤ`,
`f(B) ⊕_< g(B) + t ⊄ A`. -/
theorem thm_u33a_neg (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Set ℕ, 0 ∉ A ∧ 1 - ε < ldens A ∧
      ∀ f g : ℚ[X], ClassP f → ClassP g → 2 ≤ max f.natDegree g.natDegree →
        ∀ B : Set ℕ, B.Infinite → ∀ t : ℤ, ¬ ShiftSubset (ordSum f g B) t A :=
  u33a_neg_of_lemmaRk lem_Rk ε hε

/-! ## Theorem \ref{IA:thm:u33a}\ref{IA:it:u33a-pos}: reduction to Kousek's theorem -/

section Positive

/-- Kousek, Theorem 1.2 (*Asymmetric infinite sumsets in large sets of integers*), as quoted in the
paper (proof of Theorem \ref{IA:thm:u33a}\ref{IA:it:u33a-pos}): if `m, ℓ ≥ 1` and `A ⊆ ℕ` has
positive upper Banach density, there are an infinite `B ⊆ ℕ` and `t ∈ ℕ` with
`{m b₁ + ℓ b₂ : b₁, b₂ ∈ B, b₁ < b₂} + t ⊆ A`.

Here `A ⊆ ℕ = {1, 2, …}` is expressed by `0 ∉ A`. The conclusion allows `0 ∈ B` and `t = 0`, so
this hypothesis is implied by the quoted theorem (whose `B` and `t` lie in `{1, 2, …}`). It is a
hypothesis of `thm_u33a_pos`; it is not proved in this file. -/
def KousekThm12 : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ m → 1 ≤ ℓ → ∀ A : Set ℕ, 0 ∉ A → 0 < ubd A →
    ∃ B : Set ℕ, B.Infinite ∧ ∃ t : ℕ, ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ < b₂ → m * b₁ + ℓ * b₂ + t ∈ A

/-- A set of positive upper Banach density is infinite. -/
lemma infinite_of_ubd_pos {A : Set ℕ} (hA : 0 < ubd A) : A.Infinite := by
  intro hfin
  set K := hfin.toFinset.card
  have hcnt : ∀ a b, cnt A a b ≤ K := fun a b => by
    unfold cnt
    refine Finset.card_le_card fun x hx => ?_
    simp only [Finset.mem_filter] at hx
    exact hfin.mem_toFinset.mpr hx.2
  have hlim : Tendsto (fun N : ℕ => (⨆ M : ℕ, (cnt A (M + 1) (M + N) : ℝ)) / N) atTop (𝓝 0) := by
    have hK : Tendsto (fun N : ℕ => (K : ℝ) / N) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hK (fun N => ?_)
      (fun N => ?_)
    · exact div_nonneg (Real.iSup_nonneg fun M => Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact div_le_div_of_nonneg_right (ciSup_le fun M => Nat.cast_le.mpr (hcnt (M + 1) (M + N)))
        (Nat.cast_nonneg _)
  have : ubd A = 0 := hlim.limUnder_eq
  linarith

/-- Removing `0` does not change the upper Banach density. -/
lemma ubd_diff_zero (A : Set ℕ) : ubd (A \ {0}) = ubd A := by
  unfold ubd
  congr 1
  funext N
  congr 1
  refine iSup_congr fun M => ?_
  unfold cnt
  congr 1
  refine congrArg Finset.card (Finset.ext fun x => ?_)
  simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by omega⟩

/-- An infinite `A ⊆ ℕ` contains `n B + c₀ + t` for some infinite `B ⊆ {1, 2, …}` and `t ≥ 0`
(any `n ≥ 1`, `c₀ ∈ ℤ`). -/
lemma exists_progression {A : Set ℕ} (hA : A.Infinite) {n : ℕ} (hn : 1 ≤ n) (c₀ : ℤ) :
    ∃ B : Set ℕ, B.Infinite ∧ (∀ b ∈ B, 1 ≤ b) ∧ ∃ t : ℕ,
      ∀ b ∈ B, ∃ a ∈ A, (a : ℤ) = n * b + c₀ + t := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨r, hr⟩ := exists_infinite_residue hA n
  set q₀ := c₀.toNat
  set A' := {x | x ∈ A ∩ {b | (b : ZMod n) = r} ∧ q₀ < x / n}
  have hmod : ∀ x ∈ A ∩ {b | (b : ZMod n) = r}, x % n = r.val := by
    intro x hx
    rw [← hx.2, ZMod.val_natCast]
  have hA' : A'.Infinite := by
    have hsub : A ∩ {b | (b : ZMod n) = r} ⊆ A' ∪ Set.Iio (n * (q₀ + 1)) := by
      intro x hx
      by_cases hq : q₀ < x / n
      · exact Or.inl ⟨hx, hq⟩
      · right
        simp only [Set.mem_Iio]
        have := Nat.lt_mul_div_succ x (show 0 < n by omega)
        have h2 : x / n + 1 ≤ q₀ + 1 := by omega
        calc x < n * (x / n + 1) := this
          _ ≤ n * (q₀ + 1) := Nat.mul_le_mul_left _ h2
    intro hfin
    exact hr ((hfin.union (Set.finite_Iio _)).subset hsub)
  refine ⟨(fun x => x / n - q₀) '' A', ?_, ?_, (n * q₀ + r.val - c₀).toNat, ?_⟩
  · refine hA'.image fun x hx y hy hxy => ?_
    have hxy' : x / n - q₀ = y / n - q₀ := hxy
    have h1 : x / n = y / n := by have := hx.2; have := hy.2; omega
    have h2 : x % n = y % n := by rw [hmod x hx.1, hmod y hy.1]
    calc x = n * (x / n) + x % n := (Nat.div_add_mod x n).symm
      _ = n * (y / n) + y % n := by rw [h1, h2]
      _ = y := Nat.div_add_mod y n
  · rintro _ ⟨x, hx, rfl⟩
    show 1 ≤ x / n - q₀
    have := hx.2
    omega
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, hx.1.1, ?_⟩
    have hq : (q₀ : ℤ) ≥ c₀ := Int.self_le_toNat c₀
    have hnq : (n : ℤ) * q₀ ≥ q₀ := by
      have : (1 : ℤ) ≤ n := by exact_mod_cast hn
      nlinarith [Int.natCast_nonneg q₀]
    have ht : (((n * q₀ + r.val - c₀ : ℤ)).toNat : ℤ) = n * q₀ + r.val - c₀ :=
      Int.toNat_of_nonneg (by have := Int.natCast_nonneg r.val; omega)
    have hsub : (((x / n - q₀ : ℕ)) : ℤ) = (x / n : ℕ) - q₀ := by
      have := hx.2; push_cast [Nat.cast_sub this.le]; ring
    rw [ht, hsub]
    have h1 := Nat.div_add_mod x n
    rw [hmod x hx.1] at h1
    have h1' : (n : ℤ) * ((x / n : ℕ) : ℤ) + (r.val : ℤ) = x := by exact_mod_cast h1
    linarith

/-- Paper, Theorem \ref{IA:thm:u33a}\ref{IA:it:u33a-pos}, **conditional on Kousek's
Theorem 1.2** (`KousekThm12`): if `f, g ∈ 𝒫` have `deg f ≤ 1` and `deg g ≤ 1`, then every
`A ⊆ ℕ` with `d*(A) > 0` contains `f(B) ⊕_< g(B) + t` for some infinite `B ⊆ {1, 2, …}` and
some `t ≥ 0`. -/
theorem thm_u33a_pos (hK : KousekThm12) {f g : ℚ[X]} (hf : ClassP f) (hg : ClassP g)
    (hdf : f.natDegree ≤ 1) (hdg : g.natDegree ≤ 1) (A : Set ℕ) (hA : 0 < ubd A) :
    ∃ B : Set ℕ, B.Infinite ∧ (∀ b ∈ B, 1 ≤ b) ∧ ∃ t : ℕ, ShiftSubset (ordSum f g B) t A := by
  obtain ⟨m, c, rfl⟩ := hf.eq_linear hdf
  obtain ⟨ℓ, c', rfl⟩ := hg.eq_linear hdg
  have hAinf := infinite_of_ubd_pos hA
  simp only [ShiftSubset, ordSum]
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · rcases Nat.eq_zero_or_pos ℓ with hl0 | hl
    · -- `m = ℓ = 0`: the configuration is the single point `c + c'`
      obtain ⟨a, ha, hac⟩ := hAinf.exists_gt (c + c').toNat
      refine ⟨Set.Ici 1, Set.Ici_infinite 1, fun b hb => hb, (a - (c + c') : ℤ).toNat, ?_⟩
      rintro x ⟨b₁, -, b₂, -, -, rfl⟩
      refine ⟨a, ha, ?_⟩
      have : (((a - (c + c') : ℤ)).toNat : ℤ) = a - (c + c') :=
        Int.toNat_of_nonneg (by have := Int.self_le_toNat (c + c'); omega)
      have h' : ((((a - (c + c') : ℤ)).toNat : ℤ) : ℚ) = (a : ℚ) - (c + c') := by
        rw [this]; push_cast; ring
      simp only [hm0, hl0, Nat.cast_zero, map_zero, zero_mul, zero_add, eval_C]
      rw [h']; ring
    · -- `m = 0 < ℓ`
      obtain ⟨B, hB, hB1, t, hBt⟩ := exists_progression hAinf hl (c + c')
      refine ⟨B, hB, hB1, t, ?_⟩
      rintro x ⟨b₁, -, b₂, hb₂, -, rfl⟩
      obtain ⟨a, ha, hae⟩ := hBt b₂ hb₂
      refine ⟨a, ha, ?_⟩
      have : (a : ℚ) = ((ℓ * b₂ + (c + c') + t : ℤ) : ℚ) := by exact_mod_cast hae
      rw [this]
      simp only [hm0, Nat.cast_zero, map_zero, zero_mul, zero_add, eval_add, eval_mul, eval_C,
        eval_X]
      push_cast; ring
  · rcases Nat.eq_zero_or_pos ℓ with hl0 | hl
    · -- `ℓ = 0 < m`
      obtain ⟨B, hB, hB1, t, hBt⟩ := exists_progression hAinf hm (c + c')
      refine ⟨B, hB, hB1, t, ?_⟩
      rintro x ⟨b₁, hb₁, b₂, -, -, rfl⟩
      obtain ⟨a, ha, hae⟩ := hBt b₁ hb₁
      refine ⟨a, ha, ?_⟩
      have : (a : ℚ) = ((m * b₁ + (c + c') + t : ℤ) : ℚ) := by exact_mod_cast hae
      rw [this]
      simp only [hl0, Nat.cast_zero, map_zero, zero_mul, zero_add, eval_add, eval_mul, eval_C,
        eval_X]
      push_cast; ring
    · -- `m, ℓ ≥ 1`: Kousek's theorem
      obtain ⟨B, hB, t, hBt⟩ := hK m ℓ hm hl (A \ {0}) (by simp) (by rwa [ubd_diff_zero])
      set j := (c + c').toNat
      set B' := {b | b ∈ B ∧ j < b}
      have hB' : B'.Infinite := by
        have : B ⊆ B' ∪ Set.Iic j := fun b hb => by
          by_cases h : j < b
          · exact Or.inl ⟨hb, h⟩
          · exact Or.inr (not_lt.mp h)
        intro hfin
        exact hB ((hfin.union (Set.finite_Iic j)).subset this)
      have hinj : Set.InjOn (fun b => b - j) B' := fun x hx y hy hxy => by
        simp only at hxy; have := hx.2; have := hy.2; omega
      refine ⟨(fun b => b - j) '' B', hB'.image hinj, ?_,
        ((t : ℤ) + (m + ℓ) * j - (c + c')).toNat, ?_⟩
      · rintro _ ⟨b, hb, rfl⟩; show 1 ≤ b - j; have := hb.2; omega
      · rintro x ⟨_, ⟨b₁, hb₁, rfl⟩, _, ⟨b₂, hb₂, rfl⟩, hlt, rfl⟩
        have h12 : b₁ < b₂ := by have := hb₁.2; have := hb₂.2; simp only at hlt; omega
        refine ⟨m * b₁ + ℓ * b₂ + t, (hBt b₁ hb₁.1 b₂ hb₂.1 h12).1, ?_⟩
        have hj : (j : ℤ) ≥ c + c' := Int.self_le_toNat _
        have ht : ((((t : ℤ) + (m + ℓ) * j - (c + c'))).toNat : ℤ) =
            (t : ℤ) + (m + ℓ) * j - (c + c') := Int.toNat_of_nonneg (by
          have : (0 : ℤ) ≤ t := Int.natCast_nonneg t
          have : (j : ℤ) ≤ (m + ℓ) * j := by
            have : (1 : ℤ) ≤ m + ℓ := by omega
            nlinarith [Int.natCast_nonneg j]
          omega)
        have ht' : (((((t : ℤ) + (m + ℓ) * j - (c + c'))).toNat : ℤ) : ℚ) =
            (t : ℚ) + (m + ℓ) * j - (c + c') := by rw [ht]; push_cast; ring
        have e1 : ((b₁ - j : ℕ) : ℚ) = b₁ - j := by
          have := hb₁.2; push_cast [Nat.cast_sub this.le]; ring
        have e2 : ((b₂ - j : ℕ) : ℚ) = b₂ - j := by
          have := hb₂.2; push_cast [Nat.cast_sub this.le]; ring
        simp only [eval_add, eval_mul, eval_C, eval_X]
        rw [ht', e1, e2]
        push_cast
        ring

/-- Lower density bounds upper Banach density from below. -/
lemma ldens_le_ubd (A : Set ℕ) : ldens A ≤ ubd A := by
  have hbdd : ∀ N, BddAbove (Set.range fun M : ℕ => (cnt A (M + 1) (M + N) : ℝ)) := fun N =>
    ⟨N, by rintro _ ⟨M, rfl⟩; exact Nat.cast_le.mpr (cnt_window_le A M N)⟩
  have hle : ∀ N : ℕ, (cnt A 1 N : ℝ) / N ≤ (⨆ M : ℕ, (cnt A (M + 1) (M + N) : ℝ)) / N :=
    fun N => div_le_div_of_nonneg_right (by simpa using le_ciSup (hbdd N) 0) (Nat.cast_nonneg _)
  calc ldens A ≤ liminf (fun N : ℕ => (⨆ M : ℕ, (cnt A (M + 1) (M + N) : ℝ)) / N) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall hle)
          (isBoundedUnder_of_eventually_ge (a := 0) (Eventually.of_forall fun N =>
            div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
          (isCoboundedUnder_ge_of_le atTop (x := 1) fun N =>
            div_le_one_of_le₀ (ciSup_le fun M => Nat.cast_le.mpr (cnt_window_le A M N))
              (Nat.cast_nonneg _))
    _ = ubd A := (tendsto_ubd A).liminf_eq

/-- Paper, Theorem \ref{IA:thm:u33a} (the classification answering Question
\ref{IA:q:u33a}), **conditional on Kousek's Theorem 1.2**: for `f, g ∈ 𝒫`, every `A ⊆ ℕ` of
positive upper Banach density contains `f(B) ⊕_< g(B) + t` for some infinite `B ⊆ {1, 2, …}` and
some `t ≥ 0` if and only if `deg f ≤ 1` and `deg g ≤ 1`. -/
theorem thm_u33a_classification (hK : KousekThm12) {f g : ℚ[X]} (hf : ClassP f)
    (hg : ClassP g) :
    (∀ A : Set ℕ, 0 < ubd A →
        ∃ B : Set ℕ, B.Infinite ∧ (∀ b ∈ B, 1 ≤ b) ∧ ∃ t : ℕ, ShiftSubset (ordSum f g B) t A) ↔
      (f.natDegree ≤ 1 ∧ g.natDegree ≤ 1) := by
  constructor
  · intro h
    by_contra hdeg
    have hmax : 2 ≤ max f.natDegree g.natDegree := by
      rw [not_and_or] at hdeg
      rcases hdeg with h1 | h1 <;> simp only [not_le] at h1 <;> omega
    obtain ⟨A, -, hA, hno⟩ := thm_u33a_neg (1 / 2) (by norm_num)
    have hpos : 0 < ubd A := by linarith [ldens_le_ubd A]
    obtain ⟨B, hB, -, t, ht⟩ := h A hpos
    exact hno f g hf hg hmax B hB t ht
  · rintro ⟨hdf, hdg⟩ A hA
    exact thm_u33a_pos hK hf hg hdf hdg A hA

end Positive

end Kmrr25.S33a
