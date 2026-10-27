import Kmrr25.Q56

/-!
# A double Følner sequence in `ℚ`, and the negative answer to Question 5.6

Paper, Section \ref{SP:sec:q56}. The paper quotes the existence of a double Følner sequence in
`ℚ` (in the sense of `Kmrr25.Q56.IsDoubleFolner`) from the literature. Here we construct one
explicitly and combine it with `Kmrr25.Q56.theoremN` to obtain the negative answer to
Question \ref{SP:q:56}, as stated in the paper.

## The construction

Let `n_N = (N!)^N` and `L_N = (N + 1) N! n_N`, and let
`F_N = {σ (1 + N! k) / ((N!)^2 d) : σ ∈ {1, -1}, d ∣ n_N, 0 ≤ k < L_N}`.

* The parametrisation `(σ, d, k) ↦ σ (1 + N! k) / ((N!)^2 d)` is injective, because
  `1 + N! k` is coprime to every divisor of `n_N` (`elt_injOn`).
* *Additive invariance.* Let `x = a / b` in lowest terms and `N ≥ b`. Then
  `x + σ (1 + N! k) / ((N!)^2 d) = σ (1 + N! (k + σ s)) / ((N!)^2 d)` with
  `s = a (N! / b) d ∈ ℤ`, `|s| ≤ |a| N! n_N`. So all indices with `k` at distance at least
  `|a| N! n_N` from the ends of `[0, L_N)` are good, and the ratio is at least
  `1 - 2 |a| / (N + 1)` (`add_ratio_ge`).
* *Multiplicative invariance.* Multiplication by `-1` permutes `F_N`. For a prime `p ≤ N`,
  multiplication by `p` maps the element with index `(σ, d, k)` to the one with index
  `(σ, d / p, k)` whenever `p ∣ d`; since `p^N ∣ n_N`, at most a fraction `1 / (N + 1)` of the
  divisors of `n_N` are prime to `p` (`card_divisors_not_dvd_mul_le`). The set of `x ≠ 0` for
  which the multiplicative ratio tends to `1` is closed under products and inverses
  (`MulGood.mul`, `MulGood.inv`), hence it is all of `ℚ^*`.

## Main results

* `isDoubleFolner_folner`, `exists_isDoubleFolner` : a double Følner sequence in `ℚ` exists.
* `q56_negative` : Question \ref{SP:q:56} has a negative answer: not every `A ⊆ ℚ` with
  `d_Φ(A) > 0` (the limit exists and is positive) for some double Følner sequence `Φ` contains
  `B + C` and `BC` for some infinite `B, C ⊆ ℚ`.
-/

open Filter Topology Finset
open scoped Classical

noncomputable section

namespace Kmrr25.DoubleFolnerQ

open Kmrr25.Q56

/-! ## Generic counting lemmas -/

/-- `#(F ∩ f F) + #(F ∩ g F) ≤ #(F ∩ (f ∘ g) F) + #F` for injective `f`. -/
lemma card_inter_image_comp (F : Finset ℚ) {f : ℚ → ℚ} (g : ℚ → ℚ) (hf : Function.Injective f) :
    #(F ∩ F.image f) + #(F ∩ F.image g) ≤ #(F ∩ F.image (f ∘ g)) + #F := by
  set U := F ∩ F.image f
  set V := (F ∩ F.image g).image f
  have hV : #V = #(F ∩ F.image g) := card_image_of_injective _ hf
  have h1 : U ∩ V ⊆ F ∩ F.image (f ∘ g) := by
    intro y hy
    obtain ⟨hyU, hyV⟩ := mem_inter.1 hy
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hyV
    obtain ⟨-, hz⟩ := mem_inter.1 hz
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hz
    exact mem_inter.2 ⟨(mem_inter.1 hyU).1, mem_image.2 ⟨w, hw, rfl⟩⟩
  have h2 : U ∪ V ⊆ F.image f := by
    intro y hy
    rcases mem_union.1 hy with hy | hy
    · exact (mem_inter.1 hy).2
    · obtain ⟨z, hz, rfl⟩ := mem_image.1 hy
      exact mem_image.2 ⟨z, (mem_inter.1 hz).1, rfl⟩
  have h3 := card_union_add_card_inter U V
  have h4 := card_le_card h1
  have h5 := (card_le_card h2).trans (card_image_le (s := F) (f := f))
  omega

/-- If `g` is a two-sided inverse of `f`, then `#(F ∩ g F) = #(F ∩ f F)`. -/
lemma card_inter_image_inv (F : Finset ℚ) {f g : ℚ → ℚ} (hfg : ∀ x, f (g x) = x)
    (hgf : ∀ x, g (f x) = x) : #(F ∩ F.image g) = #(F ∩ F.image f) := by
  have hf : Function.Injective f := Function.LeftInverse.injective hgf
  rw [← card_image_of_injective (F ∩ F.image g) hf, image_inter _ _ hf, image_image]
  have : f ∘ g = id := funext hfg
  rw [this, image_id, inter_comm]

/-- If `f` is injective and `f y ∈ F` for all `y ∈ F'`, where `F' ⊆ F`, then
`#F' ≤ #(F ∩ f F)`. -/
lemma card_le_card_inter_image {F F' : Finset ℚ} {f : ℚ → ℚ} (hf : Function.Injective f)
    (hF' : F' ⊆ F) (hmap : ∀ y ∈ F', f y ∈ F) : #F' ≤ #(F ∩ F.image f) := by
  rw [← card_image_of_injective F' hf]
  apply card_le_card
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_image.1 hy
  exact mem_inter.2 ⟨hmap z hz, mem_image.2 ⟨z, hF' hz, rfl⟩⟩

/-- The ratio `|F ∩ f F| / |F|` is at most `1`. -/
lemma ratio_le_one (F : Finset ℚ) (f : ℚ → ℚ) :
    (#(F ∩ F.image f) : ℝ) / #F ≤ 1 := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  · rw [div_le_one (by exact_mod_cast hF.card_pos)]
    exact_mod_cast card_le_card inter_subset_left

/-- A ratio bounded above by `1` and below by a function tending to `1` tends to `1`. -/
lemma tendsto_ratio_of_lower {F : ℕ → Finset ℚ} {f : ℚ → ℚ} {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 1))
    (hle : ∀ᶠ N in atTop, g N ≤ (#(F N ∩ (F N).image f) : ℝ) / #(F N)) :
    Tendsto (fun N => (#(F N ∩ (F N).image f) : ℝ) / #(F N)) atTop (𝓝 1) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds hle
    (Eventually.of_forall fun N => ratio_le_one (F N) f)

/-! ## Divisors not divisible by a prime -/

/-- If `p^K ∣ n`, then at most a fraction `1/(K+1)` of the divisors of `n` are coprime to `p`. -/
lemma card_divisors_not_dvd_mul_le {p n K : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hK : p ^ K ∣ n) :
    #{d ∈ n.divisors | ¬ p ∣ d} * (K + 1) ≤ #n.divisors := by
  rw [← card_range (K + 1), ← card_product]
  apply card_le_card_of_injOn (fun x => x.1 * p ^ x.2)
  · intro x hx
    simp only [mem_coe, mem_product, mem_filter, mem_range, Nat.mem_divisors] at hx
    obtain ⟨⟨⟨hd, -⟩, hpd⟩, hi⟩ := hx
    simp only [mem_coe, Nat.mem_divisors]
    refine ⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ hd ((pow_dvd_pow p (by omega)).trans hK), hn⟩
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).symm
  · rintro ⟨d, i⟩ hx ⟨d', j⟩ hy hxy
    simp only [mem_coe, mem_product, mem_filter, mem_range, Nat.mem_divisors] at hx hy
    simp only at hxy
    have hd0 : d ≠ 0 := fun h => hx.1.2 (h ▸ dvd_zero p)
    have hd0' : d' ≠ 0 := fun h => hy.1.2 (h ▸ dvd_zero p)
    have hp0 : p ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hp0' : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
    have e := congrArg (fun m => m.factorization p) hxy
    simp only [Nat.factorization_mul hd0 hp0, Nat.factorization_mul hd0' hp0',
      Finsupp.add_apply, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hx.1.2,
      Nat.factorization_eq_zero_of_not_dvd hy.1.2, zero_add] at e
    subst e
    have := Nat.eq_of_mul_eq_mul_right (pos_of_ne_zero hp0) hxy
    rw [this]

/-! ## The construction -/

/-- `n_N = (N!)^N`. -/
def nN (N : ℕ) : ℕ := N.factorial ^ N

/-- `L_N = (N + 1) N! n_N`. -/
def lN (N : ℕ) : ℤ := (N + 1) * N.factorial * nN N

/-- The index set `{±1} × {d : d ∣ n_N} × [0, L_N)`. -/
def idx (N : ℕ) : Finset (ℤ × ℕ × ℤ) :=
  ({1, -1} : Finset ℤ) ×ˢ (nN N).divisors ×ˢ Ico 0 (lN N)

/-- The rational number `σ (1 + N! k) / ((N!)^2 d)` attached to the index `(σ, d, k)`. -/
def elt (N : ℕ) (i : ℤ × ℕ × ℤ) : ℚ :=
  i.1 * (1 + N.factorial * i.2.2) / ((N.factorial : ℚ) ^ 2 * i.2.1)

/-- The double Følner sequence:
`F_N = {σ (1 + N! k) / ((N!)^2 d) : σ = ±1, d ∣ (N!)^N, 0 ≤ k < L_N}`. -/
def folner (N : ℕ) : Finset ℚ := (idx N).image (elt N)

lemma mem_idx {N : ℕ} {i : ℤ × ℕ × ℤ} :
    i ∈ idx N ↔ (i.1 = 1 ∨ i.1 = -1) ∧ i.2.1 ∣ nN N ∧ 0 ≤ i.2.2 ∧ i.2.2 < lN N := by
  have : nN N ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero N)
  simp [idx, mem_product, this]

lemma nN_pos (N : ℕ) : 0 < nN N := pow_pos (Nat.factorial_pos N) _

lemma lN_pos (N : ℕ) : 0 < lN N := by
  have := nN_pos N
  have := Nat.factorial_pos N
  unfold lN
  positivity

lemma isCoprime_of_dvd {N d : ℕ} (hd : d ∣ nN N) (k : ℤ) :
    IsCoprime (d : ℤ) (1 + N.factorial * k) := by
  have h1 : IsCoprime (N.factorial : ℤ) (1 + N.factorial * k) := ⟨-k, 1, by ring⟩
  refine (h1.pow_left (m := N)).of_isCoprime_of_dvd_left ?_
  have := Int.natCast_dvd_natCast.2 hd
  simpa [nN] using this

lemma elt_injOn (N : ℕ) : Set.InjOn (elt N) (idx N) := by
  rintro ⟨σ, d, k⟩ hi ⟨σ', d', k'⟩ hi' h
  rw [mem_coe, mem_idx] at hi hi'
  simp only at hi hi'
  obtain ⟨hσ, hd, hk0, -⟩ := hi
  obtain ⟨hσ', hd', hk0', -⟩ := hi'
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (nN_pos N)
  have hdpos' : 0 < d' := Nat.pos_of_dvd_of_pos hd' (nN_pos N)
  have hf : (0 : ℚ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  simp only [elt] at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have h' : σ * (1 + N.factorial * k) * d' = σ' * (1 + N.factorial * k') * d := by
    have h2 : ((σ * (1 + N.factorial * k) * d' : ℤ) : ℚ) * (N.factorial : ℚ) ^ 2 =
        ((σ' * (1 + N.factorial * k') * d : ℤ) : ℚ) * (N.factorial : ℚ) ^ 2 := by
      push_cast
      linear_combination h
    exact_mod_cast mul_right_cancel₀ (by positivity) h2
  have hf' : (0 : ℤ) ≤ N.factorial := by positivity
  have hp : 0 < (1 + N.factorial * k) * (d' : ℤ) := by positivity
  have hp' : 0 < (1 + N.factorial * k') * (d : ℤ) := by positivity
  have hσσ : σ = σ' := by
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;> first | rfl | nlinarith
  subst hσσ
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have h3 : (1 + N.factorial * k) * (d' : ℤ) = (1 + N.factorial * k') * d := by
    have := h'
    rw [mul_assoc, mul_assoc] at this
    exact mul_left_cancel₀ hσ0 this
  have hdd' : (d : ℤ) ∣ d' :=
    (isCoprime_of_dvd hd k).dvd_of_dvd_mul_left ⟨1 + N.factorial * k', by linear_combination h3⟩
  have hd'd : (d' : ℤ) ∣ d :=
    (isCoprime_of_dvd hd' k').dvd_of_dvd_mul_left ⟨1 + N.factorial * k, by linear_combination -h3⟩
  have hdeq : (d : ℤ) = d' := Int.dvd_antisymm (by positivity) (by positivity) hdd' hd'd
  have hdeq' : d = d' := by exact_mod_cast hdeq
  subst hdeq'
  have hk : (N.factorial : ℤ) * k = N.factorial * k' := by
    have := mul_right_cancel₀ (by positivity : (d : ℤ) ≠ 0) h3
    linarith
  have := mul_left_cancel₀ (by positivity : (N.factorial : ℤ) ≠ 0) hk
  rw [this]

lemma card_folner (N : ℕ) :
    #(folner N) = 2 * #(nN N).divisors * (lN N).toNat := by
  rw [folner, card_image_of_injOn (elt_injOn N), idx, card_product, card_product,
    Int.card_Ico, sub_zero]
  have : #({1, -1} : Finset ℤ) = 2 := by decide
  rw [this, mul_assoc]

lemma folner_nonempty (N : ℕ) : (folner N).Nonempty := by
  rw [← card_pos, card_folner]
  have h1 : 0 < #(nN N).divisors := card_pos.2 ⟨1, by simp [(nN_pos N).ne']⟩
  have h2 : 0 < (lN N).toNat := by have := lN_pos N; omega
  positivity

lemma card_folner_real (N : ℕ) :
    (#(folner N) : ℝ) = 2 * #(nN N).divisors * (lN N : ℝ) := by
  rw [card_folner]
  have h : (((lN N).toNat : ℕ) : ℝ) = (lN N : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (lN_pos N).le]
  push_cast
  rw [h]

/-! ## Additive invariance -/

/-- Lower bound for the additive invariance ratio, for `N ≥ den x`. -/
lemma add_ratio_ge (x : ℚ) {N : ℕ} (hN : x.den ≤ N) :
    1 - 2 * |(x.num : ℝ)| / (N + 1) ≤
      (#(folner N ∩ (folner N).image (x + ·)) : ℝ) / #(folner N) := by
  set f := N.factorial with hfdef
  set M : ℤ := |x.num| * f * nN N with hM
  set G : Finset (ℤ × ℕ × ℤ) :=
    ({1, -1} : Finset ℤ) ×ˢ (nN N).divisors ×ˢ Ico M (lN N - M) with hG
  have hM0 : 0 ≤ M := by positivity
  have hGsub : G ⊆ idx N := by
    refine product_subset_product_right (product_subset_product_right ?_)
    intro k hk
    rw [mem_Ico] at hk ⊢
    constructor <;> linarith
  obtain ⟨c, hc⟩ : x.den ∣ f := Nat.dvd_factorial x.pos hN
  have hmap : ∀ y ∈ G.image (elt N), x + y ∈ folner N := by
    intro y hy
    obtain ⟨⟨σ, d, k⟩, hi, rfl⟩ := mem_image.1 hy
    have hi' := mem_idx.1 (hGsub hi)
    simp only at hi'
    obtain ⟨hσ, hd, -, -⟩ := hi'
    simp only [hG, mem_product, mem_Ico] at hi
    obtain ⟨-, -, hk1, hk2⟩ := hi
    set s : ℤ := x.num * c * d with hs
    have hdle : d ≤ nN N := Nat.le_of_dvd (nN_pos N) hd
    have hfd : c ≤ f := by
      rw [hc]
      exact Nat.le_mul_of_pos_left c x.pos
    have hsM : |σ * s| ≤ M := by
      have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
      rw [abs_mul, hσ1, one_mul, hs, abs_mul, abs_mul, hM, Nat.abs_cast, Nat.abs_cast]
      have h1 : (c : ℤ) ≤ f := by exact_mod_cast hfd
      have h2 : (d : ℤ) ≤ nN N := by exact_mod_cast hdle
      have h3 : (0 : ℤ) ≤ |x.num| := abs_nonneg _
      calc |x.num| * (c : ℤ) * d ≤ |x.num| * f * d := by gcongr
        _ ≤ |x.num| * f * nN N := by gcongr
    refine mem_image.2 ⟨(σ, d, k + σ * s), mem_idx.2 ⟨hσ, hd, ?_, ?_⟩, ?_⟩
    · have := neg_abs_le (σ * s)
      simp only
      linarith
    · have := le_abs_self (σ * s)
      simp only
      linarith
    · have hσ2 : (σ : ℚ) * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
      have hdpos : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_dvd_of_pos hd (nN_pos N)
      have hfpos : (0 : ℚ) < f := by exact_mod_cast Nat.factorial_pos N
      have hcq : (f : ℚ) = x.den * c := by exact_mod_cast hc
      have hx : x = x.num / x.den := (Rat.num_div_den x).symm
      simp only [elt, hs]
      push_cast
      rw [← hfdef]
      conv_rhs => rw [hx]
      have hden0 : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.pos.ne'
      field_simp
      rw [hcq]
      linear_combination (↑x.num * ↑x.den * ↑c * ↑d * ↑x.den * ↑c) * hσ2
  have hcard : #G ≤ #(folner N ∩ (folner N).image (x + ·)) := by
    rw [← card_image_of_injOn ((elt_injOn N).mono (by exact_mod_cast hGsub))]
    exact card_le_card_inter_image (add_right_injective x)
      (image_subset_image hGsub) hmap
  have hcardG : (#G : ℝ) ≥ 2 * #(nN N).divisors * ((lN N : ℝ) - 2 * M) := by
    rw [hG, card_product, card_product, Int.card_Ico]
    have : #({1, -1} : Finset ℤ) = 2 := by decide
    rw [this]
    push_cast
    have h := Int.self_le_toNat (lN N - M - M)
    have h' : ((lN N - M - M : ℤ) : ℝ) ≤ ((lN N - M - M).toNat : ℝ) := by exact_mod_cast h
    push_cast at h'
    have : (0 : ℝ) ≤ 2 * #(nN N).divisors := by positivity
    nlinarith
  have hFpos : (0 : ℝ) < #(folner N) := by exact_mod_cast (folner_nonempty N).card_pos
  refine le_trans ?_ (div_le_div_of_nonneg_right (a := (#G : ℝ)) (by exact_mod_cast hcard)
    hFpos.le)
  rw [le_div_iff₀ hFpos, card_folner_real]
  have hL : (lN N : ℝ) = (N + 1) * f * nN N := by simp [lN, hfdef]
  have hMr : (M : ℝ) = |(x.num : ℝ)| * f * nN N := by simp [hM]
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have e : (1 - 2 * |(x.num : ℝ)| / (N + 1)) * (2 * #(nN N).divisors * (lN N : ℝ)) =
      2 * #(nN N).divisors * ((lN N : ℝ) - 2 * M) := by
    rw [hL, hMr]
    field_simp
  rw [e]
  linarith

theorem add_invariant (x : ℚ) :
    Tendsto (fun N => (#(folner N ∩ (folner N).image (x + ·)) : ℝ) / #(folner N))
      atTop (𝓝 1) := by
  refine tendsto_ratio_of_lower (g := fun N : ℕ => 1 - 2 * |(x.num : ℝ)| / (N + 1)) ?_ ?_
  · have h : Tendsto (fun N : ℕ => 2 * |(x.num : ℝ)| / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  · filter_upwards [eventually_ge_atTop x.den] with N hN
    exact add_ratio_ge x hN

/-! ## Multiplicative invariance -/

/-- The multiplicative invariance property of `F` for a single `x`. -/
def MulGood (F : ℕ → Finset ℚ) (x : ℚ) : Prop :=
  Tendsto (fun N => (#(F N ∩ (F N).image (x * ·)) : ℝ) / #(F N)) atTop (𝓝 1)

lemma MulGood.mul {F : ℕ → Finset ℚ} (hF : ∀ N, (F N).Nonempty) {x y : ℚ} (hx0 : x ≠ 0)
    (hx : MulGood F x) (hy : MulGood F y) : MulGood F (x * y) := by
  refine tendsto_ratio_of_lower (g := fun N =>
    (#(F N ∩ (F N).image (x * ·)) : ℝ) / #(F N) + (#(F N ∩ (F N).image (y * ·)) : ℝ) / #(F N) - 1)
    ?_ (Eventually.of_forall fun N => ?_)
  · simpa using (hx.add hy).sub_const 1
  · have hc : (0 : ℝ) < #(F N) := by exact_mod_cast (hF N).card_pos
    have h := card_inter_image_comp (F N) (y * ·) (mul_right_injective₀ hx0) (f := (x * ·))
    have e : ((x * ·) ∘ (y * ·)) = ((x * y) * ·) := funext fun z => (mul_assoc x y z).symm
    rw [e] at h
    have h' := (Nat.cast_le (α := ℝ)).2 h
    push_cast at h'
    rw [← add_div, div_sub_one hc.ne', div_le_div_iff_of_pos_right hc]
    linarith

lemma MulGood.inv {F : ℕ → Finset ℚ} {x : ℚ} (hx0 : x ≠ 0) (hx : MulGood F x) :
    MulGood F x⁻¹ := by
  unfold MulGood at hx ⊢
  refine hx.congr fun N => ?_
  rw [card_inter_image_inv (F N) (f := (x * ·)) (g := (x⁻¹ * ·))
    (fun z => by simp [hx0]) (fun z => by simp [hx0])]

lemma mulGood_neg_one : MulGood folner (-1) := by
  refine tendsto_ratio_of_lower (g := fun _ => 1) tendsto_const_nhds
    (Eventually.of_forall fun N => ?_)
  have hFpos : (0 : ℝ) < #(folner N) := by exact_mod_cast (folner_nonempty N).card_pos
  rw [le_div_iff₀ hFpos, one_mul]
  refine Nat.cast_le.2 (card_le_card_inter_image (mul_right_injective₀ (by norm_num))
    subset_rfl fun y hy => ?_)
  obtain ⟨⟨σ, d, k⟩, hi, rfl⟩ := mem_image.1 hy
  obtain ⟨hσ, hd, hk⟩ := mem_idx.1 hi
  refine mem_image.2 ⟨(-σ, d, k), mem_idx.2 ⟨?_, hd, hk⟩, ?_⟩
  · simp only at hσ ⊢
    omega
  · simp only [elt]
    push_cast
    ring

/-- Lower bound for the multiplicative invariance ratio under a prime `p ≤ N`. -/
lemma mul_prime_ratio_ge {p N : ℕ} (hp : p.Prime) (hpN : p ≤ N) :
    1 - 1 / ((N : ℝ) + 1) ≤
      (#(folner N ∩ (folner N).image ((p : ℚ) * ·)) : ℝ) / #(folner N) := by
  set D := (nN N).divisors with hD
  set G : Finset (ℤ × ℕ × ℤ) :=
    ({1, -1} : Finset ℤ) ×ˢ {d ∈ D | p ∣ d} ×ˢ Ico 0 (lN N) with hG
  have hGsub : G ⊆ idx N :=
    product_subset_product_right (product_subset_product_left (filter_subset _ _))
  have hmap : ∀ y ∈ G.image (elt N), (p : ℚ) * y ∈ folner N := by
    intro y hy
    obtain ⟨⟨σ, d, k⟩, hi, rfl⟩ := mem_image.1 hy
    obtain ⟨hσ, hd, hk⟩ := mem_idx.1 (hGsub hi)
    simp only [hG, mem_product, mem_filter] at hi
    obtain ⟨-, ⟨-, e, rfl⟩, -⟩ := hi
    refine mem_image.2 ⟨(σ, e, k), mem_idx.2 ⟨hσ, (dvd_mul_left e p).trans hd, hk⟩, ?_⟩
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    simp only [elt]
    push_cast
    field_simp
  have hcard : #G ≤ #(folner N ∩ (folner N).image ((p : ℚ) * ·)) := by
    rw [← card_image_of_injOn ((elt_injOn N).mono (by exact_mod_cast hGsub))]
    exact card_le_card_inter_image (mul_right_injective₀ (by exact_mod_cast hp.ne_zero))
      (image_subset_image hGsub) hmap
  have hcnt := card_divisors_not_dvd_mul_le hp (nN_pos N).ne'
    (pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hpN) N : p ^ N ∣ nN N)
  have hsplit := card_filter_add_card_filter_not (s := D) (fun d => p ∣ d)
  have hcntR : (#D : ℝ) - #D / ((N : ℝ) + 1) ≤ #{d ∈ D | p ∣ d} := by
    have h1 : (#{d ∈ D | ¬ p ∣ d} : ℝ) * ((N : ℝ) + 1) ≤ #D := by exact_mod_cast hcnt
    have h2 : (#{d ∈ D | p ∣ d} : ℝ) + #{d ∈ D | ¬ p ∣ d} = #D := by exact_mod_cast hsplit
    have h3 : (#{d ∈ D | ¬ p ∣ d} : ℝ) ≤ #D / ((N : ℝ) + 1) := by
      rw [le_div_iff₀ (by positivity)]
      exact h1
    linarith
  have hcardG : (#G : ℝ) = 2 * #{d ∈ D | p ∣ d} * (lN N : ℝ) := by
    rw [hG, card_product, card_product, Int.card_Ico, sub_zero]
    have : #({1, -1} : Finset ℤ) = 2 := by decide
    rw [this]
    have h : (((lN N).toNat : ℕ) : ℝ) = (lN N : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (lN_pos N).le]
    push_cast
    rw [h]
    ring
  have hFpos : (0 : ℝ) < #(folner N) := by exact_mod_cast (folner_nonempty N).card_pos
  refine le_trans ?_ (div_le_div_of_nonneg_right (a := (#G : ℝ)) (by exact_mod_cast hcard)
    hFpos.le)
  rw [le_div_iff₀ hFpos, card_folner_real, hcardG]
  have hL : (0 : ℝ) < lN N := by exact_mod_cast lN_pos N
  have e : (1 - 1 / ((N : ℝ) + 1)) * (2 * #D * (lN N : ℝ)) =
      2 * (#D - #D / ((N : ℝ) + 1)) * lN N := by ring
  rw [e]
  gcongr

lemma mulGood_prime {p : ℕ} (hp : p.Prime) : MulGood folner p := by
  refine tendsto_ratio_of_lower (g := fun N : ℕ => 1 - 1 / ((N : ℝ) + 1)) ?_ ?_
  · have h : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  · filter_upwards [eventually_ge_atTop p] with N hN
    exact mul_prime_ratio_ge hp hN

lemma mulGood_natCast (n : ℕ) (hn : n ≠ 0) : MulGood folner n := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    refine tendsto_ratio_of_lower (g := fun _ => 1) tendsto_const_nhds
      (Eventually.of_forall fun N => ?_)
    have hFpos : (0 : ℝ) < #(folner N) := by exact_mod_cast (folner_nonempty N).card_pos
    simp [hFpos.ne']
  | prime p hp => exact mulGood_prime hp
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := fun h => hn (by simp [h])
    have hb0 : b ≠ 0 := fun h => hn (by simp [h])
    push_cast
    exact (ha ha0).mul folner_nonempty (by exact_mod_cast ha0) (hb hb0)

theorem mul_invariant (x : ℚ) (hx : x ≠ 0) : MulGood folner x := by
  have hden : MulGood folner (x.den : ℚ)⁻¹ :=
    (mulGood_natCast x.den x.pos.ne').inv (by exact_mod_cast x.pos.ne')
  have hnum : MulGood folner (x.num.natAbs : ℚ) :=
    mulGood_natCast _ (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hx))
  have hx' : x = x.num * (x.den : ℚ)⁻¹ := by
    rw [← div_eq_mul_inv, Rat.num_div_den]
  rcases Int.natAbs_eq x.num with h | h
  · rw [hx', h, Int.cast_natCast]
    exact hnum.mul folner_nonempty (by
      exact_mod_cast Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hx)) hden
  · rw [hx', h, Int.cast_neg, Int.cast_natCast, neg_eq_neg_one_mul, mul_assoc]
    exact mulGood_neg_one.mul folner_nonempty (by norm_num) (hnum.mul folner_nonempty (by
      exact_mod_cast Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hx)) hden)

/-! ## Main results -/

/-- The sequence `folner` is a double Følner sequence in `ℚ`. -/
theorem isDoubleFolner_folner : IsDoubleFolner folner where
  nonempty := folner_nonempty
  add_invariant := add_invariant
  mul_invariant := mul_invariant

/-- A double Følner sequence in `ℚ` exists. -/
theorem exists_isDoubleFolner : ∃ F : ℕ → Finset ℚ, IsDoubleFolner F :=
  ⟨folner, isDoubleFolner_folner⟩

/-- Paper, Theorem \ref{SP:thm:q56}, final statement: Question \ref{SP:q:56} has a negative
answer. It is *not* true that every `A ⊆ ℚ` whose density `d_Φ(A) = lim_N |A ∩ F_N| / |F_N|`
exists and is positive for some double Følner sequence `Φ = (F N)` contains `B + C` and `BC` for
some infinite `B, C ⊆ ℚ`. -/
theorem q56_negative :
    ¬ ∀ A : Set ℚ,
      (∃ F : ℕ → Finset ℚ, IsDoubleFolner F ∧
        ∃ d : ℝ, 0 < d ∧ Tendsto (fun N => relDens (F N) A) atTop (𝓝 d)) →
      ∃ B C : Set ℚ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ A ∧ prodset B C ⊆ A := by
  intro h
  obtain ⟨A, -, hA, hno⟩ := theoremN isDoubleFolner_folner
  exact hno (h A ⟨folner, isDoubleFolner_folner, 1 / 2, by norm_num, hA⟩)

end Kmrr25.DoubleFolnerQ

end
