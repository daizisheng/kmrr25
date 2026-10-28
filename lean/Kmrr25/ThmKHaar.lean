import Kmrr25.ThmKL2

/-!
# Theorem K: harmonic analysis on the Kronecker group `K = closure (α Γ)`

For a homomorphism `α : Γ →+ Torus` the group `K = KG α` is a closed subgroup of the torus
`(ℝ/ℤ)^ℕ`. Its characters are the restrictions of the characters
`z ↦ e(∑ n_j z_j)` of the torus (`charC α n`); they separate points, so by the Stone–Weierstrass
theorem their linear combinations ("trigonometric polynomials") are uniformly dense in `C(K)`
and hence dense in `L²(m_K)`. We prove:

* orthonormality of distinct characters in `L²(m_K)` and a Parseval identity;
* density of trigonometric polynomials (`exists_trig_l2_approx`);
* continuity of translation in `L¹(m_K)` (`eventually_integral_norm_translate_sub_lt`);
* the mean ergodic theorem for the dense rotation `z ↦ z + α γ`
  (`tendsto_rotation_avg_l2`), via Lemma \ref{K:lem:wiener}(a).

No Pontryagin duality is needed: we only use the characters coming from the torus.
-/

open Filter Topology Finset MeasureTheory
open scoped Classical ComplexConjugate

noncomputable section

namespace Kmrr25.ThmK

open Q516

/-! ## Characters of the torus -/

/-- The character `z ↦ e(∑_j n_j z_j)` of the torus `(ℝ/ℤ)^ℕ`, for `n : ℕ →₀ ℤ`. -/
def tchr (n : ℕ →₀ ℤ) (z : Torus) : ℂ := (AddCircle.toCircle (n.sum fun j k => k • z j) : ℂ)

lemma continuous_tchr (n : ℕ →₀ ℤ) : Continuous (tchr n) := by
  unfold tchr
  refine continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp ?_)
  simp only [Finsupp.sum]
  exact continuous_finsetSum _ fun j _ => (continuous_zsmul _).comp (continuous_apply j)

lemma tchr_add (n : ℕ →₀ ℤ) (z w : Torus) : tchr n (z + w) = tchr n z * tchr n w := by
  simp only [tchr, Pi.add_apply, smul_add, Finsupp.sum_add, AddCircle.toCircle_add,
    Circle.coe_mul]

lemma tchr_zero_arg (n : ℕ →₀ ℤ) : tchr n 0 = 1 := by
  simp [tchr]

lemma tchr_add_index (n n' : ℕ →₀ ℤ) (z : Torus) : tchr (n + n') z = tchr n z * tchr n' z := by
  have : ((n + n').sum fun j k => k • z j) = (n.sum fun j k => k • z j) + n'.sum fun j k => k • z j :=
    Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
  simp only [tchr, this, AddCircle.toCircle_add, Circle.coe_mul]

lemma tchr_zero_index (z : Torus) : tchr 0 z = 1 := by simp [tchr]

lemma tchr_neg_index (n : ℕ →₀ ℤ) (z : Torus) : tchr (-n) z = conj (tchr n z) := by
  have : ((-n).sum fun j k => k • z j) = -(n.sum fun j k => k • z j) := by
    rw [Finsupp.sum_neg_index (h := fun j k => k • z j) (fun _ => zero_smul _ _)]
    simp only [neg_smul, Finsupp.sum_neg]
  simp only [tchr, this, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

lemma norm_tchr (n : ℕ →₀ ℤ) (z : Torus) : ‖tchr n z‖ = 1 := Circle.norm_coe _

lemma tchr_single (j : ℕ) (z : Torus) :
    tchr (Finsupp.single j 1) z = (AddCircle.toCircle (z j) : ℂ) := by
  simp [tchr, Finsupp.sum_single_index]

/-! ## Characters of `K` -/

section Chars

variable {Γ : Type*} [AddCommGroup Γ] (α : Γ →+ Torus)

/-- The character `charC α n = tchr n |_K` of `K = KG α`. -/
def charC (n : ℕ →₀ ℤ) : C(KG α, ℂ) := ⟨fun z => tchr n z, (continuous_tchr n).comp continuous_subtype_val⟩

@[simp] lemma charC_apply (n : ℕ →₀ ℤ) (z : KG α) : charC α n z = tchr n z := rfl

/-- The set of characters of `K` coming from the torus. -/
def Chars : Set C(KG α, ℂ) := Set.range (charC α)

variable {α}

lemma Chars.map_add {χ : C(KG α, ℂ)} (hχ : χ ∈ Chars α) (z w : KG α) : χ (z + w) = χ z * χ w := by
  obtain ⟨n, rfl⟩ := hχ
  simp [tchr_add]

lemma Chars.map_zero {χ : C(KG α, ℂ)} (hχ : χ ∈ Chars α) : χ 0 = 1 := by
  obtain ⟨n, rfl⟩ := hχ
  simp [tchr_zero_arg]

lemma Chars.norm_eq {χ : C(KG α, ℂ)} (hχ : χ ∈ Chars α) (z : KG α) : ‖χ z‖ = 1 := by
  obtain ⟨n, rfl⟩ := hχ
  exact norm_tchr _ _

lemma Chars.mul_mem {χ χ' : C(KG α, ℂ)} (hχ : χ ∈ Chars α) (hχ' : χ' ∈ Chars α) :
    χ * χ' ∈ Chars α := by
  obtain ⟨n, rfl⟩ := hχ
  obtain ⟨n', rfl⟩ := hχ'
  exact ⟨n + n', by ext z; simp [tchr_add_index]⟩

lemma Chars.star_mem {χ : C(KG α, ℂ)} (hχ : χ ∈ Chars α) : star χ ∈ Chars α := by
  obtain ⟨n, rfl⟩ := hχ
  exact ⟨-n, by ext z; simp [tchr_neg_index]⟩

lemma Chars.one_mem : (1 : C(KG α, ℂ)) ∈ Chars α := ⟨0, by ext z; simp [tchr_zero_index]⟩

lemma Chars.mul_conj_self {χ : C(KG α, ℂ)} (hχ : χ ∈ Chars α) (z : KG α) :
    χ z * conj (χ z) = 1 := by
  rw [Complex.mul_conj', (Chars.norm_eq (hχ))]; simp

lemma Chars.mul_star_mem {χ χ' : C(KG α, ℂ)} (hχ : χ ∈ Chars α) (hχ' : χ' ∈ Chars α) :
    χ * star χ' ∈ Chars α := (Chars.mul_mem (hχ)) (Chars.star_mem (hχ'))

lemma Chars.conj_eq_inv {χ : C(KG α, ℂ)} (hχ : χ ∈ Chars α) (z : KG α) :
    conj (χ z) = χ (-z) := by
  have h1 := (Chars.map_add (hχ)) z (-z)
  rw [add_neg_cancel, (Chars.map_zero (hχ))] at h1
  have h2 := (Chars.mul_conj_self (hχ)) z
  have hz : χ z ≠ 0 := by
    intro h; rw [h, zero_mul] at h1; exact one_ne_zero h1
  exact mul_left_cancel₀ hz (h2.trans h1)

variable (α)

/-- The trigonometric polynomials on `K`: the linear span of the characters, a star subalgebra
of `C(K, ℂ)`. -/
def trigAlg : StarSubalgebra ℂ C(KG α, ℂ) where
  carrier := Submodule.span ℂ (Chars α)
  mul_mem' {a b} ha hb := by
    have : a * b ∈ Submodule.span ℂ (Chars α) * Submodule.span ℂ (Chars α) :=
      Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact Chars.mul_mem hx hy
  one_mem' := Submodule.subset_span Chars.one_mem
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span Chars.one_mem)
  star_mem' {a} ha := by
    induction ha using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Chars.star_mem hx)
    | zero => simp
    | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

lemma trigAlg_separatesPoints : (trigAlg α).SeparatesPoints := by
  intro z w hzw
  have : (z : Torus) ≠ w := fun h => hzw (Subtype.ext h)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 this
  refine ⟨_, ⟨charC α (Finsupp.single j 1), Submodule.subset_span ⟨_, rfl⟩, rfl⟩, ?_⟩
  simp only [charC_apply, tchr_single]
  intro h
  exact hj (AddCircle.injective_toCircle one_ne_zero (Subtype.ext h))

/-- A *trigonometric polynomial* on `K`: a finite linear combination of distinct characters. -/
def IsTrig (P : KG α → ℂ) : Prop :=
  ∃ (t : Finset C(KG α, ℂ)) (c : C(KG α, ℂ) → ℂ), (↑t ⊆ Chars α) ∧
    P = fun z => ∑ χ ∈ t, c χ * χ z

/-- Stone–Weierstrass: trigonometric polynomials are uniformly dense in `C(K, ℂ)`. -/
lemma exists_trig_uniform_approx (f : C(KG α, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P, IsTrig α P ∧ ∀ z, ‖f z - P z‖ < ε := by
  have hdense := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (trigAlg α) (trigAlg_separatesPoints α)
  have hf : f ∈ (trigAlg α).topologicalClosure := by rw [hdense]; trivial
  obtain ⟨P, hP, hdist⟩ := Metric.mem_closure_iff.1 hf ε hε
  obtain ⟨c, t, ht, -, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.1 hP
  refine ⟨fun z => ∑ χ ∈ t, c χ * χ z, ⟨t, c, ht, rfl⟩, fun z => ?_⟩
  have := (ContinuousMap.dist_apply_le_dist (f := f) (g := ∑ a ∈ t, c a • a) z).trans_lt hdist
  rw [dist_eq_norm] at this
  simpa [ContinuousMap.coe_sum, Finset.sum_apply] using this

lemma IsTrig.continuous {P : KG α → ℂ} (hP : IsTrig α P) : Continuous P := by
  obtain ⟨t, c, -, rfl⟩ := hP
  exact continuous_finsetSum _ fun χ _ => continuous_const.mul χ.continuous

lemma IsTrig.bdd {P : KG α → ℂ} (hP : IsTrig α P) : Bdd P :=
  ⟨hP.continuous.measurable, by
    obtain ⟨C, hC⟩ := (isCompact_range hP.continuous).isBounded.exists_norm_le
    exact ⟨C, fun z => hC _ ⟨z, rfl⟩⟩⟩

end Chars

/-! ## Haar measure on `K` -/

section Haar

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}

instance (α : Γ →+ Torus) : IsProbabilityMeasure (haarK α) :=
  ⟨by rw [haarK, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.addHaarMeasure_self⟩

instance (α : Γ →+ Torus) : (haarK α).IsAddHaarMeasure := by
  unfold haarK; infer_instance

lemma integral_haarK_add (G : KG α → ℂ) (k : KG α) :
    ∫ z, G (z + k) ∂haarK α = ∫ z, G z ∂haarK α :=
  integral_add_right_eq_self G k

lemma integral_haarK_add_real (G : KG α → ℝ) (k : KG α) :
    ∫ z, G (z + k) ∂haarK α = ∫ z, G z ∂haarK α :=
  integral_add_right_eq_self G k

lemma map_haarK_add (k : KG α) : (haarK α).map (· + k) = haarK α :=
  map_add_right_eq_self _ k

/-- The integral of a nontrivial character vanishes. -/
lemma Chars.integral_eq {χ : C(KG α, ℂ)} (hχ : χ ∈ Chars α) :
    ∫ z, χ z ∂haarK α = if χ = 1 then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨k, hk⟩ : ∃ k, χ k ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact h (ContinuousMap.ext hc)
    have h1 := integral_haarK_add (α := α) (fun z => χ z) k
    simp only [(Chars.map_add (hχ))] at h1
    rw [integral_mul_const] at h1
    have : (∫ z, χ z ∂haarK α) * (χ k - 1) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
    rcases mul_eq_zero.1 this with h2 | h2
    · exact h2
    · exact absurd (sub_eq_zero.1 h2) hk

/-- Orthonormality of characters in `L²(m_K)`. -/
lemma Chars.integral_mul_conj {χ χ' : C(KG α, ℂ)} (hχ : χ ∈ Chars α) (hχ' : χ' ∈ Chars α) :
    ∫ z, χ z * conj (χ' z) ∂haarK α = if χ = χ' then 1 else 0 := by
  have h := Chars.integral_eq (Chars.mul_star_mem hχ hχ')
  simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, RCLike.star_def] at h
  rw [h]
  congr 1
  apply propext
  constructor
  · intro h1
    ext z
    have := congrArg (fun f : C(KG α, ℂ) => f z * χ' z) h1
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, RCLike.star_def,
      ContinuousMap.one_apply, one_mul, mul_assoc] at this
    rw [mul_comm (conj _), (Chars.mul_conj_self (hχ')), mul_one] at this
    exact this
  · rintro rfl
    ext z
    simp [(Chars.mul_conj_self (hχ))]

/-- Parseval identity with multipliers: for distinct characters `χ ∈ t`,
`∫ |∑ c_χ w_χ χ|² dm = ∑ |c_χ|² |w_χ|²`. -/
lemma integral_norm_sum_chars_sq {t : Finset C(KG α, ℂ)} (ht : ↑t ⊆ Chars α)
    (c : C(KG α, ℂ) → ℂ) :
    ∫ z, ‖∑ χ ∈ t, c χ * χ z‖ ^ 2 ∂haarK α = ∑ χ ∈ t, ‖c χ‖ ^ 2 := by
  have hb : ∀ χ ∈ t, Bdd fun z : KG α => χ z := fun χ hχ =>
    ⟨χ.continuous.measurable, 1, fun z => ((Chars.norm_eq (ht hχ)) z).le⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have : (fun z => ((‖∑ χ ∈ t, c χ * χ z‖ ^ 2 : ℝ) : ℂ)) =
      fun z => ∑ χ ∈ t, ∑ χ' ∈ t, c χ * conj (c χ') * (χ z * conj (χ' z)) := by
    funext z
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => ?_
    simp only [map_mul]; ring
  rw [this, integral_finsetSum _ fun χ hχ => integrable_finsetSum _ fun χ' hχ' =>
    (((hb χ hχ).mul (hb χ' hχ').conj').integrable).const_mul _]
  push_cast
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [integral_finsetSum _ fun χ' hχ' => (((hb χ hχ).mul (hb χ' hχ').conj').integrable).const_mul _]
  have : ∀ χ' ∈ t, ∫ z, c χ * conj (c χ') * (χ z * conj (χ' z)) ∂haarK α =
      if χ = χ' then c χ * conj (c χ) else 0 := by
    intro χ' hχ'
    rw [integral_const_mul, Chars.integral_mul_conj (ht hχ) (ht hχ')]
    split_ifs with h
    · subst h; ring
    · ring
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq t χ, if_pos hχ, Complex.mul_conj']

end Haar

/-! ## Approximation and the rotation -/

section Approx

variable {Γ : Type*} [AddCommGroup Γ] {α : Γ →+ Torus}

lemma tendsto_zero_of_forall_eventually_le {a : ℕ → ℝ} (h0 : ∀ N, 0 ≤ a N)
    (h : ∀ ε > 0, ∀ᶠ N in atTop, a N ≤ ε) : Tendsto a atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun b hb => Eventually.of_forall fun N => hb.trans_le (h0 N),
    fun b hb => (h (b / 2) (half_pos hb)).mono fun N hN => hN.trans_lt (half_lt_self hb)⟩

lemma norm_avg_sq_le {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Finset ι)
    (x : ι → E) : ‖avg F x‖ ^ 2 ≤ avg F fun i => ‖x i‖ ^ 2 := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp [avg]
  have hc : (0 : ℝ) < #F := by exact_mod_cast hF.card_pos
  have h1 := norm_avg_le_avg_norm F x
  have h2 : (avg F fun i => ‖x i‖) ^ 2 ≤ avg F fun i => ‖x i‖ ^ 2 := by
    simp only [avg, smul_eq_mul]
    have := sq_sum_le_card_mul_sum_sq (s := F) (f := fun i => ‖x i‖)
    rw [mul_pow, inv_pow]
    calc ((#F : ℝ) ^ 2)⁻¹ * (∑ i ∈ F, ‖x i‖) ^ 2 ≤ ((#F : ℝ) ^ 2)⁻¹ * (#F * ∑ i ∈ F, ‖x i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- The image of `Γ` is dense in `K`. -/
lemma denseRange_kα (α : Γ →+ Torus) : DenseRange (kα α) := by
  intro z
  have hz : (z : Torus) ∈ closure (Set.range α) := z.2
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  have : Subtype.val '' Set.range (kα α) = Set.range α := by
    ext x; simp [kα]
  rw [Set.mem_preimage]
  convert hz using 2 <;> first | exact this | rfl

/-- A character of `K` which is trivial on `α Γ` is trivial. -/
lemma Chars.eq_one_of_forall {χ : C(KG α, ℂ)} (h : ∀ γ, χ (kα α γ) = 1) : χ = 1 := by
  have : (χ : KG α → ℂ) = fun _ => 1 :=
    (denseRange_kα α).equalizer χ.continuous continuous_const (funext h)
  ext z; simpa using congrFun this z

/-- Følner averages of `γ ↦ χ(α γ)` tend to `[χ = 1]`. -/
lemma Chars.tendsto_avg {χ : C(KG α, ℂ)} (hχ : χ ∈ Chars α) {Φ : ℕ → Finset Γ} (hΦ : IsFolner Φ) :
    Tendsto (fun N => avg (Φ N) fun γ => χ (kα α γ)) atTop (𝓝 (if χ = 1 then 1 else 0)) := by
  split_ifs with h
  · subst h
    simp only [ContinuousMap.one_apply]
    exact tendsto_const_nhds.congr fun N => (avg_const (hΦ.1 N) _).symm
  · obtain ⟨γ, hγ⟩ : ∃ γ, χ (kα α γ) ≠ 1 := by
      by_contra hc; push_neg at hc; exact h (Chars.eq_one_of_forall hc)
    exact hΦ.tendsto_avg_character (fun γ => χ (kα α γ))
      (fun a b => by rw [(kα α).map_add, Chars.map_add hχ]) (fun a => Chars.norm_eq hχ _) hγ

/-- Trigonometric polynomials are dense in `L²(m_K)`. -/
lemma exists_trig_l2_approx {G : KG α → ℂ} (hG : Bdd G) {ε : ℝ} (hε : 0 < ε) :
    ∃ P, IsTrig α P ∧ ∫ z, ‖G z - P z‖ ^ 2 ∂haarK α < ε := by
  obtain ⟨g, hg, -⟩ := (hG.memLp (μ := haarK α) (ENNReal.ofReal 2)).exists_boundedContinuous_integral_rpow_sub_le
    two_pos (ε := ε / 8) (by positivity)
  simp only [Real.rpow_two] at hg
  have hδ : 0 < Real.sqrt (ε / 8) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨P, hP, hgP⟩ := exists_trig_uniform_approx α g.toContinuousMap hδ
  refine ⟨P, hP, ?_⟩
  have hgb : Bdd fun z => g z := ⟨g.continuous.measurable, ‖g‖, fun z => g.norm_coe_le_norm z⟩
  have h1 : ∫ z, ‖g z - P z‖ ^ 2 ∂haarK α ≤ ε / 8 := by
    calc ∫ z, ‖g z - P z‖ ^ 2 ∂haarK α ≤ ∫ _z, Real.sqrt (ε / 8) ^ 2 ∂haarK α :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
            (integrable_const _) (Eventually.of_forall fun z =>
              pow_le_pow_left₀ (norm_nonneg _) (hgP z).le 2)
      _ = ε / 8 := by rw [Real.sq_sqrt (by positivity)]; simp
  have h2 := integral_norm_add_sq_le (μ := haarK α) ((hG.sub hgb).memLp 2) ((hgb.sub hP.bdd).memLp 2)
  simp only [sub_add_sub_cancel] at h2
  linarith

/-- Continuity of translation in `L¹(m_K)`. -/
lemma eventually_integral_norm_translate_sub_lt {G : KG α → ℂ} (hG : Bdd G) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ k in 𝓝 (0 : KG α), ∫ z, ‖G (z + k) - G z‖ ∂haarK α < ε := by
  obtain ⟨g, hg, -⟩ := (hG.integrable (μ := haarK α)).exists_boundedContinuous_integral_sub_le
    (ε := ε / 4) (by positivity)
  have hgb : Bdd fun z => g z := ⟨g.continuous.measurable, ‖g‖, fun z => g.norm_coe_le_norm z⟩
  have htube : ∀ᶠ k in 𝓝 (0 : KG α), ∀ z ∈ (Set.univ : Set (KG α)), ‖g (z + k) - g z‖ < ε / 4 := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun z _ => ?_
    have hc : Continuous fun p : KG α × KG α => ‖g (p.2 + p.1) - g p.2‖ :=
      (g.continuous.comp (continuous_snd.add continuous_fst)).sub (g.continuous.comp continuous_snd)
        |>.norm
    have := hc.continuousAt (x := ((0 : KG α), z))
    have h0 : ‖g (z + 0) - g z‖ = 0 := by simp
    rw [ContinuousAt, h0] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [htube] with k hk
  have hGk : Bdd fun z => G (z + k) := hG.comp (measurable_add_const k)
  have hgk : Bdd fun z => g (z + k) := hgb.comp (measurable_add_const k)
  have e1 : ∫ z, ‖G (z + k) - g (z + k)‖ ∂haarK α = ∫ z, ‖G z - g z‖ ∂haarK α :=
    integral_haarK_add_real (fun z => ‖G z - g z‖) k
  have e2 : ∫ z, ‖g (z + k) - g z‖ ∂haarK α ≤ ε / 4 := by
    calc ∫ z, ‖g (z + k) - g z‖ ∂haarK α ≤ ∫ _z, ε / 4 ∂haarK α :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (integrable_const _) (Eventually.of_forall fun z => (hk z trivial).le)
      _ = ε / 4 := by simp
  have e3 : ∫ z, ‖g z - G z‖ ∂haarK α = ∫ z, ‖G z - g z‖ ∂haarK α := by
    congr 1; funext z; rw [norm_sub_rev]
  have i1 : Integrable (fun z => ‖G (z + k) - g (z + k)‖) (haarK α) := (hGk.sub hgk).integrable.norm
  have i2 : Integrable (fun z => ‖g (z + k) - g z‖) (haarK α) := (hgk.sub hgb).integrable.norm
  have i3 : Integrable (fun z => ‖g z - G z‖) (haarK α) := (hgb.sub hG).integrable.norm
  have i12 : Integrable (fun z => ‖G (z + k) - g (z + k)‖ + ‖g (z + k) - g z‖) (haarK α) :=
    i1.add i2
  have hle : ∫ z, ‖G (z + k) - G z‖ ∂haarK α ≤
      ∫ z, (‖G (z + k) - g (z + k)‖ + ‖g (z + k) - g z‖ + ‖g z - G z‖) ∂haarK α := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (i12.add i3)
      (Eventually.of_forall fun z => ?_)
    calc ‖G (z + k) - G z‖ = ‖(G (z + k) - g (z + k)) + (g (z + k) - g z) + (g z - G z)‖ := by
          congr 1; ring
      _ ≤ _ := norm_add₃_le
  rw [integral_add i12 i3, integral_add i1 i2, e1, e3] at hle
  linarith

/-- The mean ergodic theorem for the dense rotation `z ↦ z + α γ` on `K`. -/
theorem tendsto_rotation_avg_l2 {G : KG α → ℂ} (hG : Bdd G) {Φ : ℕ → Finset Γ}
    (hΦ : IsFolner Φ) :
    Tendsto (fun N => ∫ z, ‖avg (Φ N) (fun γ => G (z + kα α γ)) - ∫ u, G u ∂haarK α‖ ^ 2
      ∂haarK α) atTop (𝓝 0) := by
  refine tendsto_zero_of_forall_eventually_le (fun N => integral_nonneg fun z => by positivity)
    fun ε hε => ?_
  obtain ⟨P, hP, hGP⟩ := exists_trig_l2_approx hG (ε := ε / 16) (by positivity)
  obtain ⟨t, c, ht, rfl⟩ := hP
  set P : KG α → ℂ := fun z => ∑ χ ∈ t, c χ * χ z with hPdef
  have hPb : Bdd P := IsTrig.bdd α ⟨t, c, ht, rfl⟩
  set H : KG α → ℂ := fun z => G z - P z with hHdef
  have hHb : Bdd H := hG.sub hPb
  -- the trigonometric part converges uniformly
  set e : ℕ → ℝ := fun N => ∑ χ ∈ t, ‖c χ‖ *
    ‖(avg (Φ N) fun γ => χ (kα α γ)) - if χ = 1 then 1 else 0‖ with hedef
  have he : Tendsto e atTop (𝓝 0) := by
    have : Tendsto e atTop (𝓝 (∑ χ ∈ t, ‖c χ‖ * ‖(if χ = 1 then (1 : ℂ) else 0) -
        if χ = 1 then 1 else 0‖)) :=
      tendsto_finsetSum _ fun χ hχ => tendsto_const_nhds.mul
        ((Chars.tendsto_avg (ht hχ) hΦ).sub tendsto_const_nhds).norm
    simpa using this
  have hPint : ∫ u, P u ∂haarK α = ∑ χ ∈ t, c χ * if χ = 1 then 1 else 0 := by
    rw [hPdef, integral_finsetSum _ fun χ hχ =>
      (Integrable.const_mul (⟨χ.continuous.measurable, 1,
        fun z => (Chars.norm_eq (ht hχ) z).le⟩ : Bdd fun z => χ z).integrable _)]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [integral_const_mul, Chars.integral_eq (ht hχ)]
  have hbN : ∀ N z, ‖avg (Φ N) (fun γ => P (z + kα α γ)) - ∫ u, P u ∂haarK α‖ ≤ e N := by
    intro N z
    have : avg (Φ N) (fun γ => P (z + kα α γ)) - ∫ u, P u ∂haarK α =
        ∑ χ ∈ t, c χ * χ z * ((avg (Φ N) fun γ => χ (kα α γ)) - if χ = 1 then 1 else 0) := by
      rw [hPint]
      simp only [hPdef, avg, Finset.smul_sum, mul_sub, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun χ hχ => ?_
        simp only [Chars.map_add (ht hχ), Finset.smul_sum, Finset.mul_sum, Complex.real_smul]
        refine Finset.sum_congr rfl fun γ _ => ?_
        ring
      · refine Finset.sum_congr rfl fun χ hχ => ?_
        split_ifs with h
        · subst h; simp
        · simp
    rw [this]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ hχ => ?_)
    rw [norm_mul, norm_mul, Chars.norm_eq (ht hχ), mul_one]
  -- the error part
  have hHint : ∫ u, ‖H u‖ ^ 2 ∂haarK α < ε / 16 := hGP
  have hHN : ∀ N, ∫ z, ‖avg (Φ N) (fun γ => H (z + kα α γ)) - ∫ u, H u ∂haarK α‖ ^ 2 ∂haarK α
      ≤ 4 * ∫ u, ‖H u‖ ^ 2 ∂haarK α := by
    intro N
    have hHk : ∀ γ, Bdd fun z => H (z + kα α γ) := fun γ => hHb.comp (measurable_add_const _)
    have hint1 : ‖∫ u, H u ∂haarK α‖ ^ 2 ≤ ∫ u, ‖H u‖ ^ 2 ∂haarK α := by
      have := norm_integral_mul_conj_sq_le (μ := haarK α) (hHb.memLp 2) ((Bdd.const 1).memLp 2)
      simpa using this
    have hpt : ∀ z, ‖avg (Φ N) (fun γ => H (z + kα α γ)) - ∫ u, H u ∂haarK α‖ ^ 2 ≤
        2 * (avg (Φ N) fun γ => ‖H (z + kα α γ)‖ ^ 2) + 2 * ∫ u, ‖H u‖ ^ 2 ∂haarK α := by
      intro z
      have h1 := norm_avg_sq_le (Φ N) fun γ => H (z + kα α γ)
      have h2 := norm_sub_le (avg (Φ N) fun γ => H (z + kα α γ)) (∫ u, H u ∂haarK α)
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      nlinarith [sq_nonneg (‖avg (Φ N) fun γ => H (z + kα α γ)‖ - ‖∫ u, H u ∂haarK α‖)]
    have hb1 : Bdd fun z => avg (Φ N) fun γ => ((‖H (z + kα α γ)‖ ^ 2 : ℝ) : ℂ) :=
      Bdd.avg _ fun γ _ => ⟨Complex.continuous_ofReal.measurable.comp
        (((hHk γ).meas.norm).pow_const 2), by
          obtain ⟨C, hC0, hC⟩ := hHb.exists_bound_nonneg
          exact ⟨C ^ 2, fun z => by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2⟩⟩
    have hint2 : ∫ z, (avg (Φ N) fun γ => ‖H (z + kα α γ)‖ ^ 2) ∂haarK α =
        ∫ u, ‖H u‖ ^ 2 ∂haarK α := by
      simp only [avg, smul_eq_mul]
      rw [integral_const_mul, integral_finsetSum _ fun γ _ =>
        ((memLp_two_iff_integrable_sq_norm (hHk γ).meas.aestronglyMeasurable).1 ((hHk γ).memLp 2))]
      simp only [integral_haarK_add_real (fun z => ‖H z‖ ^ 2)]
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (hΦ.card_pos N).ne', one_mul]
    have hint3 : Integrable (fun z => avg (Φ N) fun γ => ‖H (z + kα α γ)‖ ^ 2) (haarK α) := by
      have := hb1.integrable (μ := haarK α)
      have h' := this.re
      refine h'.congr (Eventually.of_forall fun z => ?_)
      simp only [avg, Complex.real_smul, RCLike.re_to_complex, ← Complex.ofReal_sum,
        ← Complex.ofReal_mul, Complex.ofReal_re, smul_eq_mul]
    calc _ ≤ ∫ z, (2 * (avg (Φ N) fun γ => ‖H (z + kα α γ)‖ ^ 2) + 2 * ∫ u, ‖H u‖ ^ 2 ∂haarK α)
          ∂haarK α :=
          integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
            ((hint3.const_mul 2).add (integrable_const _)) (Eventually.of_forall hpt)
      _ = 4 * ∫ u, ‖H u‖ ^ 2 ∂haarK α := by
          rw [integral_add (hint3.const_mul 2) (integrable_const _), integral_const_mul, hint2]
          simp; ring
  have hevent : ∀ᶠ N in atTop, 2 * e N ^ 2 ≤ ε / 2 := by
    have h2 : Tendsto (fun N => 2 * e N ^ 2) atTop (𝓝 0) := by simpa using (he.pow 2).const_mul 2
    exact h2.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hevent] with N hN
  have hsplit : ∀ z, avg (Φ N) (fun γ => G (z + kα α γ)) - ∫ u, G u ∂haarK α =
      (avg (Φ N) (fun γ => H (z + kα α γ)) - ∫ u, H u ∂haarK α) +
        (avg (Φ N) (fun γ => P (z + kα α γ)) - ∫ u, P u ∂haarK α) := by
    intro z
    have hGint : ∫ u, G u ∂haarK α = ∫ u, H u ∂haarK α + ∫ u, P u ∂haarK α := by
      rw [← integral_add hHb.integrable hPb.integrable]
      congr 1; funext u; simp [hHdef]
    rw [hGint]
    have : (fun γ => G (z + kα α γ)) = fun γ => H (z + kα α γ) + P (z + kα α γ) := by
      funext γ; simp [hHdef]
    rw [this, avg_add']
    ring
  have hmeasH : ∀ N, Bdd fun z => avg (Φ N) (fun γ => H (z + kα α γ)) - ∫ u, H u ∂haarK α :=
    fun N => (Bdd.avg _ fun γ _ => hHb.comp (measurable_add_const _)).sub (Bdd.const _)
  have hmeasP : ∀ N, Bdd fun z => avg (Φ N) (fun γ => P (z + kα α γ)) - ∫ u, P u ∂haarK α :=
    fun N => (Bdd.avg _ fun γ _ => hPb.comp (measurable_add_const _)).sub (Bdd.const _)
  have := integral_norm_add_sq_le (μ := haarK α) ((hmeasH N).memLp 2) ((hmeasP N).memLp 2)
  simp only [← hsplit] at this
  have hP2 : ∫ z, ‖avg (Φ N) (fun γ => P (z + kα α γ)) - ∫ u, P u ∂haarK α‖ ^ 2 ∂haarK α ≤
      e N ^ 2 := by
    calc _ ≤ ∫ _z, e N ^ 2 ∂haarK α :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
            (integrable_const _) (Eventually.of_forall fun z =>
              pow_le_pow_left₀ (norm_nonneg _) (hbN N z) 2)
      _ = e N ^ 2 := by simp
  have := hHN N
  linarith

end Approx

end Kmrr25.ThmK
