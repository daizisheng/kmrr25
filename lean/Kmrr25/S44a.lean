import Kmrr25.Basic

/-!
# Sumsets in random sets (paper, Section \ref{IB:sec:u44a})

Let `p = (p_n)` be a sequence in `[0, 1]` and let `A ⊆ ℕ` be the random set in which the events
`{n ∈ A}` are independent with `P(n ∈ A) = p_n`. Question §4.4(a) of the survey asks for which `p`
the set `A` almost surely contains sumsets.

## The model

* `p : ℕ → unitInterval`, and the random set is modelled by the infinite product of Bernoulli
  measures `bernoulliSeq p = Measure.infinitePi (fun n ↦ Ber(true, false, p n))` on `ℕ → Bool`
  (Mathlib's `Measure.infinitePi`), the outcome `ω` corresponding to `randSet ω = {n | ω n = true}`.
  Coordinate `n` is `true` with probability `p n`, independently.
* "Almost surely `E`" is `∀ᵐ ω ∂bernoulliSeq p, E ω`, i.e. the set `{ω | ¬ E ω}` has outer measure
  `0`. No measurability of `E` is needed; for the analytic (hence universally measurable) events of
  the paper this is exactly `P(E) = 1` for the completed product measure, as in the paper. The
  `0`–`1` statements are formalized as `(∀ᵐ ω, E ω) ∨ (∀ᵐ ω, ¬ E ω)`.

## Conventions

* The paper's `ℕ` is `{1, 2, …}`, while here sets live in Lean's `ℕ = {0, 1, 2, …}` and `p_0` is
  an arbitrary value. The paper's setting is the special case `p_0 = 0`, and nothing is lost by
  allowing `0` in the sets `B, C, F`: an infinite `B` stays infinite after removing `0`, and
  `B + F` with `0 ∈ F` is the same set as `(B - 1) + (F + 1)` for `B ⊆ {1, 2, …}`. Accordingly,
  in the monotone theorem the comparison `α q_n ≤ p_n ≤ β q_n` is only required for `n ≥ 1`.
* For `F ⊆ ℤ` the paper sets `p_m = 0` for `m ≤ 0`; in the present indexing this becomes `p_m = 0`
  for `m < 0` (`pz`).
* `S_F = ∑_n ∏_{f ∈ F} p_{n+f} ∈ [0, ∞]` is an extended nonnegative real (`SF`, `SFZ`).
* A set `A ⊆ ℕ` is thick if it contains arbitrarily long intervals (`Thick`).

## Main results

* `thm_monotone` — Theorem \ref{IB:thm:monotone}: for `p` comparable to a non-increasing
  sequence, the five conditions (1) `A` a.s. contains `B + C` with `B, C` infinite; (2) `A` is a.s.
  thick; (3) `∑ p_n^k = ∞` for every `k`; (4) for every `ε > 0`, `p_n n^ε` does not tend to `0`;
  (5) a.s., for every `k`, `A` contains `B + F` with `B` infinite and `|F| = k`; are equivalent.
* `thm_monotone_neg`, `thm_monotone_neg_int` — the negative half: if they fail, there is `k` such
  that a.s. `A` contains no `B + F` with `B` infinite and `|F| = k` (for `F ⊆ ℕ`, resp. `F ⊆ ℤ`).
* `thm_monotone_zero_one` — the events in (1), (2), (5) have probability `0` or `1`.
* `ex_gap` — Example \ref{IB:ex:gap}.
* `thm_finite_int` — Theorem \ref{IB:thm:finite}: for finite nonempty `F ⊆ ℤ`,
  `P(E_F) = 1` if `S_F = ∞` and `P(E_F) = 0` otherwise; `thm_finite` is the case `F ⊆ ℕ`, and
  `thm_finite_card`, `thm_finite_all`, `thm_finite_thick` are its consequences for `E_k`,
  `E_{<ω}` and thickness.
* `lem_thick` — Lemma \ref{IB:lem:thick}: a thick set contains `B + C` with `B, C` infinite.

The probabilistic inputs are the first Borel–Cantelli lemma (`ae_finite_setOfPred_mem`) and the
second Borel–Cantelli lemma for independent events (`ProbabilityTheory.measure_limsup_eq_one`),
both from Mathlib; independence of events depending on disjoint finite sets of coordinates is
proved here from the product formula `Measure.infinitePi_pi`. Lemma \ref{IB:lem:BC} is used only
for translates `K_n = n + F`, where the colouring argument is replaced by splitting `n` into
residue classes modulo `max F + 1`.

## The rest of the section

The strategy criteria (Theorems \ref{IB:thm:strategy} and \ref{IB:thm:strategy2}), the non-Borel
theorem \ref{IB:thm:nonborel}, the hierarchy theorem \ref{IB:thm:hierarchy} and the examples
attached to them are formalized in `Kmrr25.S44b`. (In the paper, (1) ⇒ (5) of the monotone theorem
is quoted from the hierarchy theorem; here it is the elementary observation
`HasSumset.hasAllFinite`, so this file does not depend on `Kmrr25.S44b`.)
-/

open MeasureTheory ProbabilityTheory unitInterval Filter Set
open scoped ENNReal Topology

namespace Kmrr25.S44a

/-! ## The random set -/

/-- The law of the random set: the product over `n ∈ ℕ` of Bernoulli measures on `Bool` giving
mass `p n` to `true` (meaning `n ∈ A`) and `1 - p n` to `false`. -/
noncomputable def bernoulliSeq (p : ℕ → I) : Measure (ℕ → Bool) :=
  Measure.infinitePi fun n => Ber(true, false, p n)

instance (p : ℕ → I) : IsProbabilityMeasure (bernoulliSeq p) := by
  unfold bernoulliSeq; infer_instance

/-- The random set `A = {n | ω n = true}` attached to an outcome `ω`. -/
def randSet (ω : ℕ → Bool) : Set ℕ := {n | ω n = true}

/-- The cylinder event `T ⊆ A`. -/
def cyl (T : Finset ℕ) : Set (ℕ → Bool) := {ω | ∀ j ∈ T, ω j = true}

lemma cyl_eq (T : Finset ℕ) : cyl T = Set.pi (T : Set ℕ) (fun _ => {true}) := by
  ext ω; simp [cyl]

lemma measurableSet_cyl (T : Finset ℕ) : MeasurableSet (cyl T) := by
  rw [cyl_eq]; exact MeasurableSet.pi T.countable_toSet fun _ _ => measurableSet_singleton _

/-- `P(T ⊆ A) = ∏_{j ∈ T} p_j`. -/
lemma measure_cyl (p : ℕ → I) (T : Finset ℕ) :
    bernoulliSeq p (cyl T) = ∏ j ∈ T, ((toNNReal (p j) : NNReal) : ℝ≥0∞) := by
  rw [cyl_eq, bernoulliSeq]
  erw [Measure.infinitePi_pi (μ := fun n => Ber(true, false, p n))
    (fun _ _ => measurableSet_singleton _)]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) rfl (by simp)

lemma cyl_biUnion (G : ℕ → Finset ℕ) (s : Finset ℕ) :
    (⋂ i ∈ s, cyl (G i)) = cyl (s.biUnion G) := by
  ext ω; simp [cyl]; grind

/-- Events `G_i ⊆ A` for pairwise disjoint finite sets `G_i` are independent. -/
lemma iIndepSet_cyl (p : ℕ → I) (G : ℕ → Finset ℕ)
    (hG : Pairwise fun i j => Disjoint (G i) (G j)) :
    iIndepSet (fun i => cyl (G i)) (bernoulliSeq p) := by
  rw [iIndepSet_iff_meas_biInter fun i => measurableSet_cyl _]
  intro s
  rw [cyl_biUnion, measure_cyl, Finset.prod_biUnion (fun i _ j _ hij => hG hij)]
  exact Finset.prod_congr rfl fun i _ => (measure_cyl p (G i)).symm

/-- The second Borel–Cantelli lemma for the events `G_i ⊆ A`, `G_i` pairwise disjoint: if
`∑ P(G_i ⊆ A) = ∞`, then a.s. `G_i ⊆ A` for infinitely many `i`. -/
lemma ae_frequently_cyl (p : ℕ → I) (G : ℕ → Finset ℕ)
    (hG : Pairwise fun i j => Disjoint (G i) (G j))
    (hsum : ∑' i, bernoulliSeq p (cyl (G i)) = ∞) :
    ∀ᵐ ω ∂bernoulliSeq p, ∃ᶠ i in atTop, ω ∈ cyl (G i) := by
  have h1 := measure_limsup_eq_one (fun i => measurableSet_cyl (G i)) (iIndepSet_cyl p G hG) hsum
  have hm : MeasurableSet (limsup (fun i => cyl (G i)) atTop) := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i =>
      MeasurableSet.iUnion fun _ => measurableSet_cyl _
  have h2 : bernoulliSeq p (limsup (fun i => cyl (G i)) atTop)ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff hm]; exact h1
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h2
  simp only [mem_compl_iff, mem_limsup_iff_frequently_mem]
  exact hω

/-! ## Finite configurations (Theorem \ref{IB:thm:finite}) -/

/-- Splitting a series over `ℕ` into residue classes modulo `N`. -/
lemma tsum_residue (f : ℕ → ℝ≥0∞) (N : ℕ) [NeZero N] :
    ∑' n, f n = ∑ r : Fin N, ∑' m, f (m * N + r) := by
  rw [← (Nat.divModEquiv N).symm.tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm, tsum_fintype]
  rfl

lemma exists_residue_tsum_eq_top (f : ℕ → ℝ≥0∞) (N : ℕ) [NeZero N] (h : ∑' n, f n = ∞) :
    ∃ r : Fin N, ∑' m, f (m * N + r) = ∞ := by
  by_contra hc
  push Not at hc
  rw [tsum_residue f N] at h
  exact ENNReal.sum_ne_top.2 (fun r _ => hc r) h

/-- The weight `w_F(n) = ∏_{f ∈ F} p_{n+f} = P(n + F ⊆ A)`. -/
noncomputable def w (p : ℕ → I) (F : Finset ℕ) (n : ℕ) : ℝ≥0∞ :=
  ∏ f ∈ F, ((toNNReal (p (n + f)) : NNReal) : ℝ≥0∞)

/-- `S_F = ∑_n w_F(n) ∈ [0, ∞]` for finite `F ⊆ ℕ`. -/
noncomputable def SF (p : ℕ → I) (F : Finset ℕ) : ℝ≥0∞ := ∑' n, w p F n

lemma measure_cyl_image (p : ℕ → I) (F : Finset ℕ) (n : ℕ) :
    bernoulliSeq p (cyl (F.image (n + ·))) = w p F n := by
  rw [measure_cyl, Finset.prod_image (fun a _ b _ h => Nat.add_left_cancel h)]
  rfl

/-- The event `E_F`: there is an infinite `B ⊆ ℕ` with `B + F ⊆ A`. -/
def EF (F : Finset ℕ) (A : Set ℕ) : Prop := ∃ B : Set ℕ, B.Infinite ∧ sumset B (F : Set ℕ) ⊆ A

lemma mem_cyl_image {ω : ℕ → Bool} {F : Finset ℕ} {n : ℕ} :
    ω ∈ cyl (F.image (n + ·)) ↔ ∀ f ∈ F, n + f ∈ randSet ω := by
  simp [cyl, randSet]

/-- `E_F` holds iff `n + F ⊆ A` for infinitely many `n`. -/
lemma EF_iff (F : Finset ℕ) (ω : ℕ → Bool) :
    EF F (randSet ω) ↔ {n | ω ∈ cyl (F.image (n + ·))}.Infinite := by
  constructor
  · rintro ⟨B, hB, hBF⟩
    refine hB.mono fun b hb => mem_cyl_image.2 fun f hf => hBF ⟨b, hb, f, hf, rfl⟩
  · intro h
    refine ⟨_, h, ?_⟩
    rintro _ ⟨b, hb, f, hf, rfl⟩
    exact mem_cyl_image.1 hb f hf

/-- If `S_F < ∞`, then a.s. `E_F` fails (first Borel–Cantelli lemma). -/
theorem finite_zero (p : ℕ → I) (F : Finset ℕ) (h : SF p F ≠ ∞) :
    ∀ᵐ ω ∂bernoulliSeq p, ¬ EF F (randSet ω) := by
  have h' : ∑' n, bernoulliSeq p (cyl (F.image (n + ·))) ≠ ∞ := by
    simpa only [measure_cyl_image, SF] using h
  filter_upwards [ae_finite_setOfPred_mem h'] with ω hω
  rw [EF_iff]
  exact fun h => h hω

/-- If `S_F = ∞`, then a.s. `E_F` holds (second Borel–Cantelli lemma along a residue class). -/
theorem finite_one (p : ℕ → I) (F : Finset ℕ) (h : SF p F = ∞) :
    ∀ᵐ ω ∂bernoulliSeq p, EF F (randSet ω) := by
  set N := F.sup id + 1
  have : NeZero N := ⟨Nat.succ_ne_zero _⟩
  have hFN : ∀ f ∈ F, f < N := fun f hf => Nat.lt_succ_of_le (Finset.le_sup (f := id) hf)
  obtain ⟨r, hr⟩ := exists_residue_tsum_eq_top (w p F) N h
  set G : ℕ → Finset ℕ := fun m => F.image ((m * N + r) + ·)
  have hG : Pairwise fun i j => Disjoint (G i) (G j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    simp only [G, Finset.mem_image]
    rintro _ ⟨f, hf, rfl⟩ ⟨g, hg, hfg⟩
    have h1 := hFN f hf
    have h2 := hFN g hg
    have e : f + i * N = g + j * N := by omega
    have key : ∀ (a k : ℕ), a < N → (a + k * N) / N = k := fun a k ha => by
      rw [Nat.add_mul_div_right _ _ (Nat.pos_of_neZero N), Nat.div_eq_of_lt ha, zero_add]
    exact hij (by rw [← key f i h1, e, key g j h2])
  have hsum : ∑' m, bernoulliSeq p (cyl (G m)) = ∞ := by
    simpa only [G, measure_cyl_image] using hr
  filter_upwards [ae_frequently_cyl p G hG hsum] with ω hω
  rw [EF_iff]
  have hinf : {m | ω ∈ cyl (G m)}.Infinite := Nat.frequently_atTop_iff_infinite.1 hω
  have hinj : Function.Injective fun m : ℕ => m * N + (r : ℕ) := by
    intro a b hab
    simpa [Nat.pos_of_neZero N] using hab
  refine ((hinf.image hinj.injOn)).mono ?_
  rintro _ ⟨m, hm, rfl⟩
  exact hm

/-! ## Two real-variable lemmas (proof of (3) ⇔ (4) in Theorem \ref{IB:thm:monotone}) -/

/-- If `p_n n^ε → 0` for some `ε > 0` (and `p ≥ 0`), then `∑ p_n^k < ∞` for some `k`. -/
lemma summable_pow_of_tendsto {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n) {ε : ℝ} (hε : 0 < ε)
    (h : Tendsto (fun n : ℕ => p n * (n : ℝ) ^ ε) atTop (𝓝 0)) :
    ∃ k : ℕ, Summable fun n => p n ^ k := by
  refine ⟨⌈2 / ε⌉₊, ?_⟩
  set k := ⌈2 / ε⌉₊
  have hk : 1 < ε * k := by
    have := Nat.le_ceil (2 / ε)
    have h2 : 2 ≤ ε * k := by
      rw [div_le_iff₀ hε] at this; linarith
    linarith
  have hg : Summable fun n : ℕ => ((n : ℝ) ^ (ε * k))⁻¹ := Real.summable_nat_rpow_inv.2 hk
  refine hg.of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [h.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpos : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hnpos ε
  have hle : p n ≤ ((n : ℝ) ^ ε)⁻¹ := by
    rw [← one_div]; exact (le_div_iff₀ hpos).2 hn.le
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hp0 n) k)]
  calc p n ^ k ≤ (((n : ℝ) ^ ε)⁻¹) ^ k := pow_le_pow_left₀ (hp0 n) hle k
    _ = ((n : ℝ) ^ (ε * k))⁻¹ := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]

/-- If `q ≥ 0` is non-increasing and `∑ q_n^k < ∞` with `k ≥ 1`, then `q_n n^ε → 0` for
`ε = 1/(2k)`. -/
lemma tendsto_of_summable_pow {q : ℕ → ℝ} (hq : Antitone q) (hq0 : ∀ n, 0 ≤ q n) {k : ℕ}
    (hk : k ≠ 0) (hs : Summable fun n => q n ^ k) :
    Tendsto (fun n : ℕ => q n * (n : ℝ) ^ ((k : ℝ)⁻¹ / 2)) atTop (𝓝 0) := by
  set S := ∑' n, q n ^ k
  set ε : ℝ := (k : ℝ)⁻¹ / 2
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hε : 0 < ε := by positivity
  have hS0 : 0 ≤ S := tsum_nonneg fun n => pow_nonneg (hq0 n) k
  -- `n q_n^k ≤ S`
  have h1 : ∀ n : ℕ, (n : ℝ) * q n ^ k ≤ S := by
    intro n
    have := Finset.card_nsmul_le_sum (Finset.range n) (fun m => q m ^ k) (q n ^ k)
      (fun m hm => pow_le_pow_left₀ (hq0 n) (hq (Finset.mem_range.1 hm).le) k)
    rw [Finset.card_range, nsmul_eq_mul] at this
    exact this.trans (hs.sum_le_tsum _ fun m _ => pow_nonneg (hq0 m) k)
  -- the bound `q_n n^ε ≤ S^(1/k) n^(-ε)` for `n ≥ 1`
  have h2 : ∀ n : ℕ, 1 ≤ n →
      q n * (n : ℝ) ^ ε ≤ S ^ (k : ℝ)⁻¹ * (n : ℝ) ^ (-ε) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hqk : q n ^ k ≤ S / n := by
      rw [le_div_iff₀ hnpos, mul_comm]; exact h1 n
    have hq' : q n ≤ (S / n) ^ (k : ℝ)⁻¹ := by
      calc q n = (q n ^ k) ^ (k : ℝ)⁻¹ := (Real.pow_rpow_inv_natCast (hq0 n) hk).symm
        _ ≤ (S / n) ^ (k : ℝ)⁻¹ :=
          Real.rpow_le_rpow (pow_nonneg (hq0 n) k) hqk (by positivity)
    have hsplit : (n : ℝ) ^ (k : ℝ)⁻¹ = (n : ℝ) ^ ε * (n : ℝ) ^ ε := by
      rw [← Real.rpow_add hnpos]; congr 1; ring
    have hpos : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hnpos ε
    calc q n * (n : ℝ) ^ ε ≤ (S / n) ^ (k : ℝ)⁻¹ * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_right hq' hpos.le
      _ = S ^ (k : ℝ)⁻¹ * (n : ℝ) ^ (-ε) := by
          rw [Real.div_rpow hS0 hnpos.le, hsplit, Real.rpow_neg hnpos.le]
          field_simp
  have hg : Tendsto (fun n : ℕ => S ^ (k : ℝ)⁻¹ * (n : ℝ) ^ (-ε)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop).const_mul
      (S ^ (k : ℝ)⁻¹)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · exact Eventually.of_forall fun n => mul_nonneg (hq0 n) (Real.rpow_nonneg (Nat.cast_nonneg n) ε)
  · filter_upwards [eventually_ge_atTop 1] with n hn using h2 n hn

/-- `S_F < ∞` iff the real series `∑_n ∏_{f ∈ F} p_{n+f}` converges. -/
lemma SF_ne_top_iff (p : ℕ → I) (F : Finset ℕ) :
    SF p F ≠ ∞ ↔ Summable fun n => ∏ f ∈ F, (p (n + f) : ℝ) := by
  have : ∀ n, w p F n = ((∏ f ∈ F, toNNReal (p (n + f)) : NNReal) : ℝ≥0∞) := fun n => by
    simp [w]
  simp only [SF, this, ENNReal.tsum_coe_ne_top_iff_summable_coe, NNReal.coe_prod, coe_toNNReal]

/-- `A ⊆ ℕ` is thick if it contains arbitrarily long intervals of consecutive integers. -/
def Thick (A : Set ℕ) : Prop := ∀ L : ℕ, ∃ n, ∀ h ≤ L, n + h ∈ A

lemma Thick.exists_gt {A : Set ℕ} (hA : Thick A) (M L : ℕ) : ∃ n, M < n ∧ ∀ h ≤ L, n + h ∈ A := by
  obtain ⟨n, hn⟩ := hA (M + 1 + L)
  exact ⟨n + (M + 1), by omega, fun h hh => by rw [add_assoc]; exact hn _ (by omega)⟩

/-- `A` is thick iff `E_{\{0, …, L-1\}}` holds for every `L`. -/
lemma thick_iff (ω : ℕ → Bool) : Thick (randSet ω) ↔ ∀ L, EF (Finset.range L) (randSet ω) := by
  constructor
  · intro h L
    rw [EF_iff]
    refine Set.infinite_of_forall_exists_gt fun M => ?_
    obtain ⟨n, hMn, hn⟩ := h.exists_gt M L
    exact ⟨n, mem_cyl_image.2 fun f hf => hn f (Finset.mem_range.1 hf).le, hMn⟩
  · intro h L
    obtain ⟨B, hB, hBF⟩ := h (L + 1)
    obtain ⟨b, hb⟩ := hB.nonempty
    exact ⟨b, fun i hi => hBF ⟨b, hb, i, by simp; omega, rfl⟩⟩

/-! ## The monotone theorem (Theorem \ref{IB:thm:monotone}) -/

/-- The hypothesis of Theorem \ref{IB:thm:monotone}: there are a non-increasing sequence `q` and
constants `0 < α ≤ β` with `α q_n ≤ p_n ≤ β q_n` for all `n ≥ 1` (see the conventions above for
the index `0`). -/
def ComparableToAntitone (p : ℕ → I) : Prop :=
  ∃ (q : ℕ → ℝ) (α β : ℝ), Antitone q ∧ 0 < α ∧ α ≤ β ∧
    ∀ n, 1 ≤ n → α * q n ≤ p n ∧ (p n : ℝ) ≤ β * q n

lemma ComparableToAntitone.q_nonneg {p : ℕ → I} {q : ℕ → ℝ} {α β : ℝ} (hq : Antitone q)
    (hα : 0 < α) (hαβ : α ≤ β) (hc : ∀ n, 1 ≤ n → α * q n ≤ p n ∧ (p n : ℝ) ≤ β * q n) (n : ℕ) :
    0 ≤ q n := by
  have h1 : 0 ≤ q (n + 1) := by
    have := (hc (n + 1) (by omega)).2
    have hp := (p (n + 1)).2.1
    by_contra h
    push Not at h
    nlinarith
  exact h1.trans (hq (Nat.le_succ n))

/-- `∑ p_n^0 = ∞`. -/
lemma not_summable_pow_zero (p : ℕ → I) : ¬ Summable fun n => (p n : ℝ) ^ 0 := by
  intro h
  have := h.tendsto_atTop_zero
  simp only [pow_zero] at this
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)

/-- Paper, proof of Theorem \ref{IB:thm:monotone}, (3) ⇔ (4). -/
theorem cond3_iff_cond4 {p : ℕ → I} (hp : ComparableToAntitone p) :
    (∀ k : ℕ, ¬ Summable fun n => (p n : ℝ) ^ k) ↔
      ∀ ε : ℝ, 0 < ε → ¬ Tendsto (fun n : ℕ => (p n : ℝ) * (n : ℝ) ^ ε) atTop (𝓝 0) := by
  obtain ⟨q, α, β, hq, hα, hαβ, hc⟩ := hp
  have hq0 := ComparableToAntitone.q_nonneg hq hα hαβ hc
  have hβ : 0 < β := hα.trans_le hαβ
  constructor
  · intro h3 ε hε h
    obtain ⟨k, hk⟩ := summable_pow_of_tendsto (fun n => (p n).2.1) hε h
    exact h3 k hk
  · intro h4 k hk
    have hk0 : k ≠ 0 := by rintro rfl; exact not_summable_pow_zero p hk
    have hqs : Summable fun n => q n ^ k := by
      refine (hk.mul_left ((α⁻¹) ^ k)).of_norm_bounded_eventually ?_
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hq0 n) k), ← mul_pow]
      refine pow_le_pow_left₀ (hq0 n) ?_ k
      rw [← div_eq_inv_mul, le_div_iff₀ hα, mul_comm]
      exact (hc n hn).1
    have ht := tendsto_of_summable_pow hq hq0 hk0 hqs
    refine h4 ((k : ℝ)⁻¹ / 2) (by positivity) (squeeze_zero' ?_ ?_ (by simpa using ht.const_mul β))
    · exact Eventually.of_forall fun n =>
        mul_nonneg (p n).2.1 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hc n hn).2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- If `∑ p_n^k < ∞`, then `S_F < ∞` for every `F ⊆ ℕ` with `|F| = k`. -/
-- paper, proof of Theorem \ref{IB:thm:monotone}, (5) ⇒ (3)
lemma SF_ne_top_of_summable {p : ℕ → I} (hp : ComparableToAntitone p) {k : ℕ}
    (hk : Summable fun n => (p n : ℝ) ^ k) (F : Finset ℕ) (hF : F.card = k) : SF p F ≠ ∞ := by
  obtain ⟨q, α, β, hq, hα, hαβ, hc⟩ := hp
  have hq0 := ComparableToAntitone.q_nonneg hq hα hαβ hc
  rw [SF_ne_top_iff]
  refine (hk.mul_left ((β / α) ^ k)).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun f _ => (p (n + f)).2.1)]
  calc ∏ f ∈ F, (p (n + f) : ℝ) ≤ ∏ _f ∈ F, β * q n := by
        refine Finset.prod_le_prod (fun f _ => (p (n + f)).2.1) fun f _ => ?_
        exact (hc (n + f) (by omega)).2.trans
          (mul_le_mul_of_nonneg_left (hq (Nat.le_add_right n f)) (hα.trans_le hαβ).le)
    _ = (β * q n) ^ k := by rw [Finset.prod_const, hF]
    _ ≤ ((β / α) * p n) ^ k := by
        refine pow_le_pow_left₀ (mul_nonneg (hα.trans_le hαβ).le (hq0 n)) ?_ k
        rw [div_mul_eq_mul_div, le_div_iff₀ hα, mul_assoc, mul_comm (q n)]
        exact mul_le_mul_of_nonneg_left (hc n hn).1 (hα.trans_le hαβ).le
    _ = (β / α) ^ k * (p n : ℝ) ^ k := mul_pow _ _ _

/-- If `∑ p_n^L = ∞`, then `S_{\{0, …, L-1\}} = ∞`. -/
-- paper, proof of Theorem \ref{IB:thm:monotone}, (3) ⇒ (2)
lemma SF_range_eq_top {p : ℕ → I} (hp : ComparableToAntitone p) {L : ℕ}
    (hL : ¬ Summable fun n => (p n : ℝ) ^ L) : SF p (Finset.range L) = ∞ := by
  obtain ⟨q, α, β, hq, hα, hαβ, hc⟩ := hp
  have hq0 := ComparableToAntitone.q_nonneg hq hα hαβ hc
  have hβ : 0 < β := hα.trans_le hαβ
  by_contra hne
  rw [← ne_eq, SF_ne_top_iff] at hne
  apply hL
  rw [← summable_nat_add_iff L]
  refine (hne.mul_left ((β / α) ^ L)).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (p (m + L)).2.1 L)]
  calc (p (m + L) : ℝ) ^ L ≤ (β * q (m + L)) ^ L :=
        pow_le_pow_left₀ (p (m + L)).2.1 (hc (m + L) (by omega)).2 L
    _ = ∏ _i ∈ Finset.range L, β * q (m + L) := by rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range L, (β / α) * p (m + i) := by
        refine Finset.prod_le_prod (fun i _ => mul_nonneg hβ.le (hq0 _)) fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        rw [div_mul_eq_mul_div, le_div_iff₀ hα, mul_assoc, mul_comm (q _)]
        refine mul_le_mul_of_nonneg_left ?_ hβ.le
        exact (mul_le_mul_of_nonneg_left (hq (by omega)) hα.le).trans (hc (m + i) (by omega)).1
    _ = (β / α) ^ L * ∏ i ∈ Finset.range L, (p (m + i) : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-- Paper, Theorem \ref{IB:thm:finite}, for `F ⊆ ℕ`: `P(E_F) = 1` if `S_F = ∞` and `P(E_F) = 0`
otherwise. -/
theorem thm_finite (p : ℕ → I) (F : Finset ℕ) :
    (SF p F = ∞ → ∀ᵐ ω ∂bernoulliSeq p, EF F (randSet ω)) ∧
    (SF p F ≠ ∞ → ∀ᵐ ω ∂bernoulliSeq p, ¬ EF F (randSet ω)) :=
  ⟨finite_one p F, finite_zero p F⟩

/-- Paper, Theorem \ref{IB:thm:finite}, the event `E_k` (some `F ⊆ ℕ` with `|F| = k` has `E_F`):
`P(E_k) = 1` if `S_F = ∞` for some `F ⊆ ℕ` with `|F| = k`, and `P(E_k) = 0` otherwise. -/
theorem thm_finite_card (p : ℕ → I) (k : ℕ) :
    ((∃ F : Finset ℕ, F.card = k ∧ SF p F = ∞) →
      ∀ᵐ ω ∂bernoulliSeq p, ∃ F : Finset ℕ, F.card = k ∧ EF F (randSet ω)) ∧
    ((∀ F : Finset ℕ, F.card = k → SF p F ≠ ∞) →
      ∀ᵐ ω ∂bernoulliSeq p, ¬ ∃ F : Finset ℕ, F.card = k ∧ EF F (randSet ω)) := by
  constructor
  · rintro ⟨F, hF, hS⟩
    exact (finite_one p F hS).mono fun ω h => ⟨F, hF, h⟩
  · intro h
    have : ∀ F : Finset ℕ, ∀ᵐ ω ∂bernoulliSeq p, F.card = k → ¬ EF F (randSet ω) := by
      intro F
      by_cases hF : F.card = k
      · exact (finite_zero p F (h F hF)).mono fun ω h _ => h
      · exact ae_of_all _ fun ω h => absurd h hF
    filter_upwards [ae_all_iff.2 this] with ω hω
    rintro ⟨F, hF, hE⟩
    exact hω F hF hE

/-- Paper, Theorem \ref{IB:thm:finite}, the event `E_{<ω} = ⋂_k E_k`: it has probability `1` if
for every `k` some `F ⊆ ℕ` with `|F| = k` has `S_F = ∞`, and probability `0` otherwise. -/
theorem thm_finite_all (p : ℕ → I) :
    ((∀ k : ℕ, ∃ F : Finset ℕ, F.card = k ∧ SF p F = ∞) →
      ∀ᵐ ω ∂bernoulliSeq p, ∀ k : ℕ, ∃ F : Finset ℕ, F.card = k ∧ EF F (randSet ω)) ∧
    (¬ (∀ k : ℕ, ∃ F : Finset ℕ, F.card = k ∧ SF p F = ∞) →
      ∀ᵐ ω ∂bernoulliSeq p, ¬ ∀ k : ℕ, ∃ F : Finset ℕ, F.card = k ∧ EF F (randSet ω)) := by
  constructor
  · intro h
    exact ae_all_iff.2 fun k => (thm_finite_card p k).1 (h k)
  · intro h
    push Not at h
    obtain ⟨k, hk⟩ := h
    filter_upwards [(thm_finite_card p k).2 hk] with ω hω h
    exact hω (h k)

/-- Paper, Theorem \ref{IB:thm:finite}, thickness: `A` is a.s. thick if
`S_{\{0, …, L-1\}} = ∞` for all `L`, and a.s. not thick otherwise. -/
theorem thm_finite_thick (p : ℕ → I) :
    ((∀ L : ℕ, SF p (Finset.range L) = ∞) → ∀ᵐ ω ∂bernoulliSeq p, Thick (randSet ω)) ∧
    ((∃ L : ℕ, SF p (Finset.range L) ≠ ∞) → ∀ᵐ ω ∂bernoulliSeq p, ¬ Thick (randSet ω)) := by
  constructor
  · intro h
    filter_upwards [ae_all_iff.2 fun L => finite_one p _ (h L)] with ω hω
    exact (thick_iff ω).2 hω
  · rintro ⟨L, hL⟩
    filter_upwards [finite_zero p _ hL] with ω hω h
    exact hω ((thick_iff ω).1 h L)

/-- Paper, Lemma \ref{IB:lem:thick}: a thick set `A ⊆ ℕ` contains `B + C` for some infinite
`B, C ⊆ ℕ`. -/
theorem lem_thick {A : Set ℕ} (hA : Thick A) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ A := by
  choose nb hnb using fun c : ℕ => hA.exists_gt c c
  let seq : ℕ → ℕ × ℕ := fun j => Nat.rec (nb 0, nb (nb 0))
    (fun _ x => (nb x.2, nb (nb x.2))) j
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

/-- `A` contains `B + C` for some infinite `B, C ⊆ ℕ` (the event `E_{BC}`). -/
def HasSumset (A : Set ℕ) : Prop := ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ A

/-- For every `k`, `A` contains `B + F` with `B ⊆ ℕ` infinite and `F ⊆ ℕ`, `|F| = k` (the event
`E_{<ω}`, condition (5) of Theorem \ref{IB:thm:monotone}). -/
def HasAllFinite (A : Set ℕ) : Prop := ∀ k : ℕ, ∃ F : Finset ℕ, F.card = k ∧ EF F A

/-- `B + C ⊆ A` with `C` infinite gives `B + F ⊆ A` for finite `F ⊆ C` of every size. -/
lemma HasSumset.hasAllFinite {A : Set ℕ} (h : HasSumset A) : HasAllFinite A := by
  obtain ⟨B, C, hB, hC, hBC⟩ := h
  intro k
  obtain ⟨F, hFC, hFk⟩ := hC.exists_subset_card_eq k
  refine ⟨F, hFk, B, hB, ?_⟩
  rintro _ ⟨b, hb, c, hc, rfl⟩
  exact hBC ⟨b, hb, c, hFC hc, rfl⟩

/-- Paper, Theorem \ref{IB:thm:monotone}, negative half: if the conditions fail (i.e.
`∑ p_n^k < ∞` for some `k`), there is `k` such that almost surely `A` contains no `B + F` with
`B` infinite and `F ⊆ ℕ`, `|F| = k`. -/
theorem thm_monotone_neg {p : ℕ → I} (hp : ComparableToAntitone p)
    (h : ¬ ∀ k : ℕ, ¬ Summable fun n => (p n : ℝ) ^ k) :
    ∃ k : ℕ, ∀ᵐ ω ∂bernoulliSeq p, ∀ (B : Set ℕ) (F : Finset ℕ),
      B.Infinite → F.card = k → ¬ sumset B (F : Set ℕ) ⊆ randSet ω := by
  push Not at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  filter_upwards [(thm_finite_card p k).2 (SF_ne_top_of_summable hp hk)] with ω hω B F hB hF hBF
  exact hω ⟨F, hF, B, hB, hBF⟩

/-- Paper, Theorem \ref{IB:thm:monotone}. If `p` is comparable to a non-increasing sequence, the
following are equivalent:
(1) `A` almost surely contains `B + C` for some infinite `B, C`;
(2) `A` is almost surely thick;
(3) `∑_n p_n^k = ∞` for every `k`;
(4) for every `ε > 0`, `p_n n^ε` does not tend to `0`;
(5) almost surely, for every `k` there are an infinite `B` and `F ⊆ ℕ` with `|F| = k` and
`B + F ⊆ A`. -/
theorem thm_monotone {p : ℕ → I} (hp : ComparableToAntitone p) :
    List.TFAE [
      ∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω),
      ∀ᵐ ω ∂bernoulliSeq p, Thick (randSet ω),
      ∀ k : ℕ, ¬ Summable fun n => (p n : ℝ) ^ k,
      ∀ ε : ℝ, 0 < ε → ¬ Tendsto (fun n : ℕ => (p n : ℝ) * (n : ℝ) ^ ε) atTop (𝓝 0),
      ∀ᵐ ω ∂bernoulliSeq p, HasAllFinite (randSet ω)] := by
  tfae_have 1 → 5 := fun h => h.mono fun ω hω => hω.hasAllFinite
  tfae_have 5 → 3 := by
    intro h5
    by_contra h3
    obtain ⟨k, hk⟩ := thm_monotone_neg hp h3
    obtain ⟨ω, h5ω, hkω⟩ := (h5.and hk).exists
    obtain ⟨F, hF, B, hB, hBF⟩ := h5ω k
    exact hkω B F hB hF hBF
  tfae_have 3 → 2 := fun h3 => (thm_finite_thick p).1 fun L => SF_range_eq_top hp (h3 L)
  tfae_have 2 → 1 := fun h => h.mono fun ω hω => lem_thick hω
  tfae_have 3 ↔ 4 := cond3_iff_cond4 hp
  tfae_finish

/-- Paper, Theorem \ref{IB:thm:monotone}, last sentence: the events in (1), (2), (5) have
probability `0` or `1`. -/
theorem thm_monotone_zero_one {p : ℕ → I} (hp : ComparableToAntitone p) :
    ((∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω)) ∨
        ∀ᵐ ω ∂bernoulliSeq p, ¬ HasSumset (randSet ω)) ∧
      ((∀ᵐ ω ∂bernoulliSeq p, Thick (randSet ω)) ∨
        ∀ᵐ ω ∂bernoulliSeq p, ¬ Thick (randSet ω)) ∧
      ((∀ᵐ ω ∂bernoulliSeq p, HasAllFinite (randSet ω)) ∨
        ∀ᵐ ω ∂bernoulliSeq p, ¬ HasAllFinite (randSet ω)) := by
  have h := thm_monotone hp
  by_cases h3 : ∀ k : ℕ, ¬ Summable fun n => (p n : ℝ) ^ k
  · exact ⟨.inl ((h.out 2 0).1 h3), .inl ((h.out 2 1).1 h3), .inl ((h.out 2 4).1 h3)⟩
  · obtain ⟨k, hk⟩ := thm_monotone_neg hp h3
    have h5 : ∀ᵐ ω ∂bernoulliSeq p, ¬ HasAllFinite (randSet ω) := by
      filter_upwards [hk] with ω hω h
      obtain ⟨F, hF, B, hB, hBF⟩ := h k
      exact hω B F hB hF hBF
    have h1 : ∀ᵐ ω ∂bernoulliSeq p, ¬ HasSumset (randSet ω) :=
      h5.mono fun ω hω h => hω h.hasAllFinite
    exact ⟨.inr h1, .inr (h1.mono fun ω hω h => hω (lem_thick h)), .inr h5⟩

/-! ## Finite configurations `F ⊆ ℤ` -/

/-- `p` extended to `ℤ` by `p_m = 0` for `m < 0`, as an extended real. -/
noncomputable def pz (p : ℕ → I) (m : ℤ) : ℝ≥0∞ :=
  if 0 ≤ m then ((toNNReal (p m.toNat) : NNReal) : ℝ≥0∞) else 0

/-- `S_F = ∑_{n ∈ ℤ} ∏_{f ∈ F} p_{n+f} ∈ [0, ∞]` for finite `F ⊆ ℤ`. -/
noncomputable def SFZ (p : ℕ → I) (F : Finset ℤ) : ℝ≥0∞ := ∑' n : ℤ, ∏ f ∈ F, pz p (n + f)

/-- The event `E_F` for finite `F ⊆ ℤ`: there is an infinite `B ⊆ ℕ` with `B + F ⊆ A` in `ℤ`. -/
def EFZ (F : Finset ℤ) (A : Set ℕ) : Prop :=
  ∃ B : Set ℕ, B.Infinite ∧ sumset (((↑) : ℕ → ℤ) '' B) (F : Set ℤ) ⊆ ((↑) : ℕ → ℤ) '' A

/-- The translate `F - min F ⊆ ℕ` of a nonempty finite `F ⊆ ℤ`. -/
def shiftF (F : Finset ℤ) (c : ℤ) : Finset ℕ := F.image fun f => (f - c).toNat

lemma shiftF_injOn {F : Finset ℤ} {c : ℤ} (hc : ∀ f ∈ F, c ≤ f) :
    Set.InjOn (fun f : ℤ => (f - c).toNat) (F : Set ℤ) := by
  intro a ha b hb h
  have := hc a ha; have := hc b hb
  simp only at h
  omega

/-- `S_F = S_{F - min F}`. -/
lemma SFZ_eq (p : ℕ → I) {F : Finset ℤ} (hF : F.Nonempty) :
    SFZ p F = SF p (shiftF F (F.min' hF)) := by
  set c := F.min' hF
  have hc : ∀ f ∈ F, c ≤ f := fun f hf => F.min'_le f hf
  have hinj : Function.Injective fun m : ℕ => (m : ℤ) - c := fun a b h => by
    simp only [sub_left_inj, Nat.cast_inj] at h; exact h
  rw [SFZ, ← hinj.tsum_eq]
  · refine tsum_congr fun m => ?_
    rw [w, shiftF, Finset.prod_image (shiftF_injOn hc)]
    refine Finset.prod_congr rfl fun f hf => ?_
    have := hc f hf
    rw [pz, if_pos (by omega)]
    congr 3
    omega
  · intro n hn
    by_cases h : 0 ≤ n + c
    · exact ⟨(n + c).toNat, by simp only; omega⟩
    · exfalso
      apply hn
      exact Finset.prod_eq_zero (F.min'_mem hF) (by rw [pz, if_neg h])

/-- `E_F ⇔ E_{F - min F}`. -/
lemma EFZ_iff {F : Finset ℤ} (hF : F.Nonempty) (A : Set ℕ) :
    EFZ F A ↔ EF (shiftF F (F.min' hF)) A := by
  set c := F.min' hF
  have hc : ∀ f ∈ F, c ≤ f := fun f hf => F.min'_le f hf
  constructor
  · rintro ⟨B, hB, hBF⟩
    refine ⟨{m : ℕ | ∃ b ∈ B, (m : ℤ) = b + c}, ?_, ?_⟩
    · refine Set.infinite_of_forall_exists_gt fun M => ?_
      obtain ⟨b, hb, hbM⟩ := hB.exists_gt (M + c.natAbs)
      exact ⟨(b + c).toNat, ⟨b, hb, by omega⟩, by omega⟩
    · rintro _ ⟨m, ⟨b, hb, hm⟩, g, hg, rfl⟩
      simp only [shiftF, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hg
      obtain ⟨f, hf, rfl⟩ := hg
      obtain ⟨a, ha, hab⟩ := hBF ⟨(b : ℤ), ⟨b, hb, rfl⟩, f, hf, rfl⟩
      have := hc f hf
      have : a = m + (f - c).toNat := by omega
      rw [← this]; exact ha
  · rintro ⟨B, hB, hBF⟩
    refine ⟨{b : ℕ | ∃ m ∈ B, (b : ℤ) = m - c}, ?_, ?_⟩
    · refine Set.infinite_of_forall_exists_gt fun M => ?_
      obtain ⟨m, hm, hmM⟩ := hB.exists_gt (M + c.natAbs)
      exact ⟨(m - c).toNat, ⟨m, hm, by omega⟩, by omega⟩
    · rintro _ ⟨_, ⟨b, ⟨m, hm, hbm⟩, rfl⟩, f, hf, rfl⟩
      have := hc f hf
      have hmem := hBF ⟨m, hm, (f - c).toNat, by
        simp only [shiftF, Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨f, hf, rfl⟩, rfl⟩
      refine ⟨m + (f - c).toNat, hmem, ?_⟩
      push_cast
      omega

/-- Paper, Theorem \ref{IB:thm:finite}: for finite nonempty `F ⊆ ℤ`, `P(E_F) = 1` if `S_F = ∞`
and `P(E_F) = 0` otherwise. -/
theorem thm_finite_int (p : ℕ → I) {F : Finset ℤ} (hF : F.Nonempty) :
    (SFZ p F = ∞ → ∀ᵐ ω ∂bernoulliSeq p, EFZ F (randSet ω)) ∧
    (SFZ p F ≠ ∞ → ∀ᵐ ω ∂bernoulliSeq p, ¬ EFZ F (randSet ω)) := by
  simp only [SFZ_eq p hF, EFZ_iff hF]
  exact thm_finite p _

lemma card_shiftF {F : Finset ℤ} (hF : F.Nonempty) : (shiftF F (F.min' hF)).card = F.card :=
  Finset.card_image_of_injOn (shiftF_injOn fun f hf => F.min'_le f hf)

/-- Paper, Theorem \ref{IB:thm:monotone}, negative half, for `F ⊆ ℤ`: if `∑ p_n^k < ∞` for some
`k`, there is `k` such that almost surely `A` contains no `B + F` with `B ⊆ ℕ` infinite and
`F ⊆ ℤ`, `|F| = k`. -/
theorem thm_monotone_neg_int {p : ℕ → I} (hp : ComparableToAntitone p)
    (h : ¬ ∀ k : ℕ, ¬ Summable fun n => (p n : ℝ) ^ k) :
    ∃ k : ℕ, ∀ᵐ ω ∂bernoulliSeq p, ∀ (B : Set ℕ) (F : Finset ℤ), B.Infinite → F.card = k →
      ¬ sumset (((↑) : ℕ → ℤ) '' B) (F : Set ℤ) ⊆ ((↑) : ℕ → ℤ) '' randSet ω := by
  obtain ⟨k, hk⟩ := thm_monotone_neg hp h
  refine ⟨k, hk.mono fun ω hω B F hB hF hBF => ?_⟩
  rcases F.eq_empty_or_nonempty with rfl | hne
  · -- `k = 0`: then `∅ + B = ∅ ⊆ A` contradicts `hω` for `F = ∅`
    exact hω B ∅ hB hF (by simp [sumset])
  · obtain ⟨B', hB', hB'F⟩ := (EFZ_iff hne _).1 ⟨B, hB, hBF⟩
    exact hω B' _ hB' ((card_shiftF hne).trans hF) hB'F

/-! ## Example \ref{IB:ex:gap} -/

/-- The sequence `N_1 = 10`, `N_{j+1} = N_j^{j+1}` (`gapN 0 = 10` is an unused value). -/
def gapN : ℕ → ℕ
  | 0 => 10
  | 1 => 10
  | (j + 2) => gapN (j + 1) ^ (j + 2)

lemma gapN_succ {j : ℕ} (hj : 1 ≤ j) : gapN (j + 1) = gapN j ^ (j + 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rfl

lemma ten_le_gapN : ∀ j, 10 ≤ gapN j
  | 0 => le_rfl
  | 1 => le_rfl
  | (j + 2) => by
    rw [gapN]
    exact (ten_le_gapN (j + 1)).trans (Nat.le_self_pow (by omega) _)

lemma gapN_lt_succ {j : ℕ} (hj : 1 ≤ j) : gapN j < gapN (j + 1) := by
  rw [gapN_succ hj]
  have h := ten_le_gapN j
  calc gapN j < gapN j ^ 2 := by nlinarith
    _ ≤ gapN j ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)

lemma gapN_strictMono : StrictMono fun j => gapN (j + 1) :=
  strictMono_nat_of_lt_succ fun j => gapN_lt_succ (by omega)

lemma gapN_lt {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : gapN i < gapN j := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact gapN_strictMono (by omega)

lemma gapN_le {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : gapN i ≤ gapN j := by
  rcases hij.lt_or_eq with h | rfl
  · exact (gapN_lt hi h).le
  · exact le_rfl

lemma add_nine_le_gapN : ∀ j, j + 9 ≤ gapN j
  | 0 => by decide
  | 1 => le_rfl
  | (j + 2) => by
    have h1 := add_nine_le_gapN (j + 1)
    have h2 : gapN (j + 1) < gapN (j + 2) := gapN_lt_succ (j := j + 1) (by omega)
    omega

lemma lt_gapN (j : ℕ) : j < gapN j := by
  have := add_nine_le_gapN j; omega

/-- `gapJ n` is the index `j ≥ 1` with `N_j ≤ n < N_{j+1}`, or `0` if `n < N_1 = 10`. -/
def gapJ (n : ℕ) : ℕ := Nat.findGreatest (fun j => 1 ≤ j ∧ gapN j ≤ n) n

lemma gapJ_eq {j n : ℕ} (hj : 1 ≤ j) (h1 : gapN j ≤ n) (h2 : n < gapN (j + 1)) : gapJ n = j := by
  rw [gapJ, Nat.findGreatest_eq_iff]
  refine ⟨((lt_gapN j).trans_le h1).le, fun _ => ⟨hj, h1⟩, fun m hjm _ hm => ?_⟩
  exact absurd (hm.2.trans_lt h2) (not_lt.2 (gapN_le (by omega) hjm))

lemma gapJ_eq_zero {n : ℕ} (hn : n < 10) : gapJ n = 0 := by
  rw [gapJ, Nat.findGreatest_eq_zero_iff]
  intro j _ _ h
  have := ten_le_gapN j
  omega

lemma gapJ_spec {n : ℕ} (hn : 10 ≤ n) : 1 ≤ gapJ n ∧ gapN (gapJ n) ≤ n :=
  Nat.findGreatest_spec (P := fun j => 1 ≤ j ∧ gapN j ≤ n) (m := 1) (by omega) ⟨le_rfl, hn⟩

lemma gapJ_mono : Monotone gapJ := fun _ _ h =>
  Nat.findGreatest_mono (fun _ hj => ⟨hj.1, hj.2.trans h⟩) h

/-- `p_n = 1` for `n < N_1` and `p_n = N_j^{-1/2}` for `N_j ≤ n < N_{j+1}`
(see `gapPr_of_lt`, `gapPr_of_mem`). -/
noncomputable def gapPr (n : ℕ) : ℝ :=
  if gapJ n = 0 then 1 else (gapN (gapJ n) : ℝ) ^ (-(1 / 2 : ℝ))

lemma gapPr_of_lt {n : ℕ} (hn : n < 10) : gapPr n = 1 := by
  simp [gapPr, gapJ_eq_zero hn]

lemma gapPr_of_mem {j n : ℕ} (hj : 1 ≤ j) (h1 : gapN j ≤ n) (h2 : n < gapN (j + 1)) :
    gapPr n = (gapN j : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [gapPr, gapJ_eq hj h1 h2, if_neg (by omega)]

lemma one_le_gapN_real (j : ℕ) : (1 : ℝ) ≤ gapN j := by
  have := ten_le_gapN j
  exact_mod_cast (by omega : 1 ≤ gapN j)

lemma gapPr_mem (n : ℕ) : gapPr n ∈ unitInterval := by
  unfold gapPr
  split_ifs
  · exact unitInterval.one_mem
  · exact ⟨Real.rpow_nonneg (by positivity) _,
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_gapN_real _) (by norm_num)⟩

lemma gapPr_antitone : Antitone gapPr := by
  intro n n' h
  by_cases hn : gapJ n = 0
  · rw [show gapPr n = 1 by simp [gapPr, hn]]
    exact (gapPr_mem n').2
  · have hn' : gapJ n' ≠ 0 := by have := gapJ_mono h; omega
    simp only [gapPr, if_neg hn, if_neg hn']
    refine Real.rpow_le_rpow_of_nonpos (by linarith [one_le_gapN_real (gapJ n)]) ?_ (by norm_num)
    exact_mod_cast gapN_le (by omega) (gapJ_mono h)

lemma tendsto_gapN : Tendsto gapN atTop atTop :=
  tendsto_atTop_mono (fun j => (lt_gapN j).le) tendsto_id

lemma gap_along_N {ε : ℝ} (hε : ε < 1 / 2) :
    Tendsto (fun j => gapPr (gapN j) * (gapN j : ℝ) ^ ε) atTop (𝓝 0) := by
  have hpos : 0 < 1 / 2 - ε := by linarith
  have h := (tendsto_rpow_neg_atTop hpos).comp
    (tendsto_natCast_atTop_atTop.comp tendsto_gapN)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hNpos : (0 : ℝ) < gapN j := by linarith [one_le_gapN_real j]
  simp only [Function.comp_apply]
  rw [gapPr_of_mem hj le_rfl (gapN_lt_succ hj), ← Real.rpow_add hNpos]
  congr 1; ring

lemma gap_not_tendsto_atTop {ε : ℝ} (hε : ε < 1 / 2) :
    ¬ Tendsto (fun n : ℕ => gapPr n * (n : ℝ) ^ ε) atTop atTop := fun h =>
  not_tendsto_atTop_of_tendsto_nhds (gap_along_N hε) (h.comp tendsto_gapN)

lemma gap_not_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    ¬ Tendsto (fun n : ℕ => gapPr n * (n : ℝ) ^ ε) atTop (𝓝 0) := by
  intro h
  -- along `n_j = N_j^j` the values are `N_j^{jε - 1/2} ≥ 1` once `jε ≥ 1/2`
  have hn : Tendsto (fun j => gapN j ^ j) atTop atTop :=
    tendsto_atTop_mono' atTop (by
      filter_upwards [eventually_ge_atTop 1] with j hj
      exact Nat.le_self_pow (by omega) _) tendsto_gapN
  have h1 := h.comp hn
  have h2 : ∀ᶠ j in atTop, (1 : ℝ) ≤ (fun n : ℕ => gapPr n * (n : ℝ) ^ ε) (gapN j ^ j) := by
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈1 / (2 * ε)⌉₊] with j hj hjε
    have hN1 := one_le_gapN_real j
    have hNpos : (0 : ℝ) < gapN j := by linarith
    have hmem1 : gapN j ≤ gapN j ^ j := Nat.le_self_pow (by omega) _
    have hmem2 : gapN j ^ j < gapN (j + 1) := by
      rw [gapN_succ hj]
      exact Nat.pow_lt_pow_right (by have := ten_le_gapN j; omega) (by omega)
    have hjε' : 1 / 2 ≤ (j : ℝ) * ε := by
      have := (Nat.ceil_le.1 hjε)
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    show (1 : ℝ) ≤ gapPr (gapN j ^ j) * (((gapN j ^ j : ℕ) : ℝ)) ^ ε
    rw [gapPr_of_mem hj hmem1 hmem2, Nat.cast_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    exact Real.one_le_rpow hN1 (by linarith)
  have := ge_of_tendsto h1 h2
  norm_num at this

/-- The sequence of Example \ref{IB:ex:gap} as a sequence in `[0, 1]`. -/
noncomputable def gapP (n : ℕ) : I := ⟨gapPr n, gapPr_mem n⟩

/-- Paper, Example \ref{IB:ex:gap}. The sequence `p_n = N_j^{-1/2}` (`N_j ≤ n < N_{j+1}`) is
non-increasing; along `n = N_j`, `p_n n^ε → 0` for `ε < 1/2`, so `p_n n^ε → ∞` fails; for every
`ε > 0`, `p_n n^ε` does not tend to `0`; and `A` is almost surely thick. -/
theorem ex_gap :
    Antitone (fun n => (gapP n : ℝ)) ∧
    (∀ ε : ℝ, ε < 1 / 2 →
      Tendsto (fun j => (gapP (gapN j) : ℝ) * (gapN j : ℝ) ^ ε) atTop (𝓝 0)) ∧
    (∀ ε : ℝ, ε < 1 / 2 → ¬ Tendsto (fun n : ℕ => (gapP n : ℝ) * (n : ℝ) ^ ε) atTop atTop) ∧
    (∀ ε : ℝ, 0 < ε → ¬ Tendsto (fun n : ℕ => (gapP n : ℝ) * (n : ℝ) ^ ε) atTop (𝓝 0)) ∧
    ∀ᵐ ω ∂bernoulliSeq gapP, Thick (randSet ω) := by
  have h4 : ∀ ε : ℝ, 0 < ε → ¬ Tendsto (fun n : ℕ => (gapP n : ℝ) * (n : ℝ) ^ ε) atTop (𝓝 0) :=
    fun ε hε => gap_not_tendsto_zero hε
  have hc : ComparableToAntitone gapP :=
    ⟨gapPr, 1, 1, gapPr_antitone, one_pos, le_rfl, fun n _ => by simp [gapP]⟩
  exact ⟨gapPr_antitone, fun ε hε => gap_along_N hε, fun ε hε => gap_not_tendsto_atTop hε, h4,
    ((thm_monotone hc).out 3 1).1 h4⟩

end Kmrr25.S44a
