import Kmrr25.S44a

/-!
# Sumsets in random sets, II: strategies, the hierarchy, rigid sets, non-Borel families

Paper, Section \ref{IB:sec:u44a}, continued from `Kmrr25.S44a` (whose model and conventions are
used throughout: `bernoulliSeq p` on `ℕ → Bool`, `randSet ω`, weights `w p U x`, `S_F = SF p F`,
"almost surely" as `∀ᵐ`).

## Main results

* `lem_BC` — Lemma \ref{IB:lem:BC} (second Borel–Cantelli lemma for a countable family of finite
  sets with bounded overlaps, via a greedy colouring).
* `thm_strategy` — Theorem \ref{IB:thm:strategy}: `P(E_{BC}) ∈ {0, 1}`, and `P(E_{BC}) = 1` iff
  `p` has a `BC`-strategy (`IsBCStrategy`, Definition \ref{IB:def:strategy}).
* `thm_strategy2_oplus`, `thm_strategy2_plus` — Theorem \ref{IB:thm:strategy2} for `B ⊕ B` and
  `B + B` (`IsOplusStrategy`, `IsPlusStrategy`).
* `strategy_deterministic`, `strategy_deterministic_oplus`, `strategy_deterministic_plus` — the
  deterministic case `p = 1_D`.
* `thm_hierarchy` — Theorem \ref{IB:thm:hierarchy}: `(F) ⇒ P(E_{BC}) = 1 ⇒ (N) ⇒ P(E_{<ω}) = 1`;
  `thm_hierarchy_strict` — none of the implications can be reversed, by `ex_tree`
  (Example \ref{IB:ex:tree}), `ex_half` (Example \ref{IB:ex:half}) and `ex_rigid`
  (Example \ref{IB:ex:rigid}); `condF_of_levelSet` — the level-set remark.
* `qInd_iff` — the remark that for `p = q 1_D` (`0 < q ≤ 1`), `P(E_{BC}) = 1` iff `D ∈ 𝔇_{BC}`.
* `ex_oplus` — Example \ref{IB:ex:oplus}.
* `lem_rigid`, `lem_rigid_pair`, `lem_rigid_sidon` — Lemma \ref{IB:lem:rigid}; `lem_R`,
  `lem_R_mono` — Lemma \ref{IB:lem:R}; `cor_R` — Corollary \ref{IB:cor:R}.
* Theorem \ref{IB:thm:nonborel}:
  - `thm_nonborel_a_BC`, `thm_nonborel_a_1` — part \ref{IB:nb1}: `𝔇_{BC}`, `𝔇_⊕`, `𝔇_+ ⊆ 2^ℕ`
    are analytic, `T ↦ D_T` (resp. `D^⊕_T`, `D^+_T`) is a continuous map
    `2^{ℕ^{<ℕ}} → 2^ℕ` with `D_T ∈ 𝔇 ⇔ T ∈ IF` for every tree `T`, and hence they are
    `Σ¹₁`-complete and not Borel, given the classical facts below;
  - `thm_nonborel_b_BC`, `thm_nonborel_b_1` (in `[0,1]^ℕ`) and `thm_nonborel_b_BC_open`,
    `thm_nonborel_b_1_open` (in `(0,1)^ℕ`) — part \ref{IB:nb2}, likewise for `𝔄_*`;
  - `thm_nonborel_c` — part \ref{IB:nb3}: a continuous `g : 2^{ℕ^{<ℕ}} → 𝔆` with
    `g(T) ∈ 𝔄_{BC} ⇔ T ∈ IF` for trees `T`, and no Borel `W ⊆ [0,1]^ℕ` has
    `W ∩ 𝔆 = 𝔄_{BC} ∩ 𝔆` (given that `IF` is not Borel).

## Classical inputs taken as hypotheses (not axioms)

* `KechrisIFComplete`: `IF` is a `Σ¹₁`-complete subset of `Tr` (Kechris, *Classical Descriptive
  Set Theory*, Theorem 27.1).
* `KechrisIFNotBorel`: `IF` is not a Borel subset of `2^{ℕ^{<ℕ}}` (Kechris, Theorem 27.1 with
  the existence of analytic non-Borel sets, Theorem 14.2).

Only the `Σ¹₁`-completeness and non-Borel conclusions of Theorem \ref{IB:thm:nonborel} use them;
the analyticity (upper bounds), the continuity of the reductions and the reduction properties
are proved unconditionally. `Σ¹₁`-completeness (`Sigma11Complete`) is the paper's definition, with
"zero-dimensional" meaning "has a basis of clopen sets" and the test spaces `W'` ranging over
Polish spaces in `Type`. "Borel" is `MeasurableSet[borel _]`.

## Conventions

* As in `Kmrr25.S44a`, sets live in Lean's `ℕ = {0, 1, …}`, `p_0` is arbitrary, and "almost
  surely `E`" is `∀ᵐ ω ∂bernoulliSeq p, E (randSet ω)`, i.e. the complement of `E` has outer
  measure `0`. This is `P(E) = 1` for the completed product measure, as in the paper, and needs no
  measurability of `E`; "`P(E) > 0`" in the proof of the strategy criteria is "outer measure
  `≠ 0`", and the `0`–`1` laws are `(∀ᵐ ω, E) ∨ (∀ᵐ ω, ¬ E)`. In particular the analyticity
  (universal measurability) of the events is not needed for these statements.
* Strategies are sets of (pairs of) finite subsets of Lean's `ℕ`; weights are
  `w p U x = ∏_{u ∈ U} p_{x+u}` (`Kmrr25.S44a.w`). The rigid set `Λ` is the range of a sequence
  `lam` with `lam j > 8 (lam 0 + ⋯ + lam (j-1))` (`IsRigidSeq`, the paper's condition indexed
  from `0`); the examples are proved for every such `lam` and instantiated with `λ_j = 9^j`.
  The labellings `s ↦ β_s, γ_s` by elements of `Λ` with disjoint images are
  `β_s = λ_{2⌜s⌝}`, `γ_s = λ_{2⌜s⌝+1}` for an injective coding `⌜·⌝`.

## Not covered

* The two classical facts above (Σ¹₁-completeness and non-Borelness of `IF`).
* Measurability: no universal measurability of the events is used or proved (see Conventions);
  for the families `𝔇_*` the analyticity is proved (`analyticSet_frakD_BC`,
  `analyticSet_frakD1`), which covers the analyticity of the events `E_{BC}`, `E_⊕`, `E_+` as
  subsets of `2^ℕ`. The analyticity of `E_F`, `E_k` and of the auxiliary events `E(U, V)` is not
  formalized (it is not needed).
-/

open MeasureTheory ProbabilityTheory unitInterval Filter Set
open scoped ENNReal Topology

namespace Kmrr25.S44b

open Kmrr25.S44a

/-! ## Generalities -/

/-- `p_n` as an extended nonnegative real; `w p U x = ∏_{u ∈ U} pe p (x + u)`. -/
noncomputable def pe (p : ℕ → I) (n : ℕ) : ℝ≥0∞ := ((toNNReal (p n) : NNReal) : ℝ≥0∞)

lemma pe_le_one (p : ℕ → I) (n : ℕ) : pe p n ≤ 1 := by
  unfold pe
  exact_mod_cast (show toNNReal (p n) ≤ 1 from by
    rw [← NNReal.coe_le_coe]; simpa using (p n).2.2)

lemma w_eq (p : ℕ → I) (U : Finset ℕ) (x : ℕ) : w p U x = ∏ u ∈ U, pe p (x + u) := rfl

lemma w_le_one (p : ℕ → I) (U : Finset ℕ) (x : ℕ) : w p U x ≤ 1 :=
  Finset.prod_le_one' fun _ _ => pe_le_one p _

/-- A series of terms `≥ c > 0` over an infinite set diverges. -/
lemma tsum_indicator_eq_top {s : Set ℕ} (hs : s.Infinite) {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c ≠ 0) (hf : ∀ x ∈ s, c ≤ f x) : ∑' x, s.indicator f x = ∞ := by
  rw [← tsum_subtype]
  have : Infinite s := hs.to_subtype
  refine top_le_iff.1 ?_
  rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := s) hc]
  exact ENNReal.tsum_le_tsum fun x => hf x x.2

lemma tsum_indicator_mono {s t : Set ℕ} (h : s ⊆ t) (f : ℕ → ℝ≥0∞) :
    ∑' x, s.indicator f x ≤ ∑' x, t.indicator f x :=
  ENNReal.tsum_le_tsum fun _ => indicator_le_indicator_of_subset h (fun _ => zero_le) _

/-- Removing finitely many terms in `[0, 1]` from a divergent series keeps it divergent. -/
lemma tsum_indicator_diff_eq_top {s : Set ℕ} {f : ℕ → ℝ≥0∞} (hf : ∀ x, f x ≤ 1)
    (h : ∑' x, s.indicator f x = ∞) (V : Finset ℕ) :
    ∑' x, (s \ V).indicator f x = ∞ := by
  by_contra hc
  have h1 : ∀ x, s.indicator f x ≤ (s \ V).indicator f x + (V : Set ℕ).indicator 1 x := by
    intro x
    by_cases hx : x ∈ s <;> by_cases hv : x ∈ (V : Set ℕ) <;> simp [hx, hv, hf x]
  have h2 : ∑' x, (V : Set ℕ).indicator (1 : ℕ → ℝ≥0∞) x ≠ ∞ := by
    rw [← tsum_subtype]; simp
  have := (ENNReal.tsum_le_tsum h1).trans_eq (ENNReal.tsum_add)
  rw [h] at this
  exact (ENNReal.add_ne_top.2 ⟨hc, h2⟩) (top_le_iff.1 this)

/-! ## Lemma \ref{IB:lem:BC} -/

/-- Greedy colouring of `ℕ` with `M + 1` colours, when each `n` has at most `M` earlier
neighbours. -/
lemma exists_greedy_coloring (R : ℕ → ℕ → Prop) (M : ℕ)
    (hR : ∀ n, ∃ T : Finset ℕ, T.card ≤ M ∧ ∀ m < n, R m n → m ∈ T) :
    ∃ col : ℕ → Fin (M + 1), ∀ m n, m < n → R m n → col m ≠ col n := by
  classical
  choose T hTc hT using hR
  have key : ∀ n (g : ℕ → Fin (M + 1)), ∃ c : Fin (M + 1), ∀ m < n, R m n → g m ≠ c := by
    intro n g
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin (M + 1))) ⊆ (T n).image g := by
      intro c _
      obtain ⟨m, hm, hRm, rfl⟩ := h c
      exact Finset.mem_image_of_mem _ (hT n m hm hRm)
    have := (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (hTc n))
    simp at this
  let col : ℕ → Fin (M + 1) := (wellFounded_lt (α := ℕ)).fix fun n ih =>
    Classical.choose (key n fun m => if h : m < n then ih m h else 0)
  refine ⟨col, fun m n hmn hRmn => ?_⟩
  have e : col n = Classical.choose (key n fun m => if h : m < n then col m else 0) :=
    (wellFounded_lt (α := ℕ)).fix_eq _ n
  have := Classical.choose_spec (key n fun m => if h : m < n then col m else 0) m hmn hRmn
  rw [e]
  simpa [hmn] using this

/-- Second Borel–Cantelli lemma for a pairwise-disjoint family of cylinders indexed by an
infinite countable set. -/
lemma ae_infinite_of_disjoint {ι : Type*} (p : ℕ → I) (s : Set ι) [Countable s]
    (K : ι → Finset ℕ) (hdisj : ∀ x ∈ s, ∀ x' ∈ s, x ≠ x' → Disjoint (K x) (K x'))
    (hsum : ∑' x : s, bernoulliSeq p (cyl (K x)) = ∞) :
    ∀ᵐ ω ∂bernoulliSeq p, {x | ω ∈ cyl (K x)}.Infinite := by
  classical
  have hs : s.Infinite := by
    intro hfin
    have : Finite s := hfin.to_subtype
    have : Fintype s := Fintype.ofFinite s
    rw [tsum_fintype] at hsum
    exact ENNReal.sum_ne_top.2 (fun x _ => measure_ne_top _ _) hsum
  have : Infinite s := hs.to_subtype
  let _ : Encodable s := Encodable.ofCountable s
  let _ : Denumerable s := Denumerable.ofEncodableOfInfinite s
  let e : ℕ ≃ s := (Denumerable.eqv s).symm
  set G : ℕ → Finset ℕ := fun n => K (e n)
  have hG : Pairwise fun i j => Disjoint (G i) (G j) := by
    intro i j hij
    exact hdisj _ (e i).2 _ (e j).2 fun h => hij (e.injective (Subtype.ext h))
  have hsumG : ∑' n, bernoulliSeq p (cyl (G n)) = ∞ := by
    rw [← hsum, ← e.tsum_eq]
  filter_upwards [ae_frequently_cyl p G hG hsumG] with ω hω
  have hinf : {n | ω ∈ cyl (G n)}.Infinite := Nat.frequently_atTop_iff_infinite.1 hω
  have hinj : Function.Injective fun n => (e n : ι) := fun a b h => e.injective (Subtype.ext h)
  refine (hinf.image hinj.injOn).mono ?_
  rintro _ ⟨n, hn, rfl⟩
  exact hn

/-- Paper, Lemma \ref{IB:lem:BC}: let `(K_x)_{x ∈ ι}` be a countable family of finite subsets
of `ℕ` such that each `K_x` meets `K_{x'}` for at most `M` indices `x' ≠ x`. If
`∑_x P(K_x ⊆ A) = ∞`, then almost surely `K_x ⊆ A` for infinitely many `x`.

(The paper allows `K_x ⊆ ℤ` with `p_m = 0` for `m ≤ 0`; sets not contained in `ℕ` contribute
probability `0`, so it suffices to treat `K_x ⊆ ℕ`.) -/
theorem lem_BC (p : ℕ → I) {ι : Type*} [Countable ι] (K : ι → Finset ℕ) (M : ℕ)
    (hM : ∀ x, ∃ T : Finset ι, T.card ≤ M ∧ ∀ x', x' ≠ x → ¬ Disjoint (K x) (K x') → x' ∈ T)
    (hsum : ∑' x, bernoulliSeq p (cyl (K x)) = ∞) :
    ∀ᵐ ω ∂bernoulliSeq p, {x | ω ∈ cyl (K x)}.Infinite := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  -- the conflict relation transported to `ℕ`
  let R : ℕ → ℕ → Prop := fun m n => ∃ x x', e x = m ∧ e x' = n ∧ ¬ Disjoint (K x) (K x')
  have hR : ∀ n, ∃ T : Finset ℕ, T.card ≤ M ∧ ∀ m < n, R m n → m ∈ T := by
    intro n
    by_cases hn : ∃ x', e x' = n
    · obtain ⟨x', rfl⟩ := hn
      obtain ⟨T, hTc, hT⟩ := hM x'
      refine ⟨T.image e, Finset.card_image_le.trans hTc, ?_⟩
      rintro m hm ⟨x, y, rfl, hy, hxy⟩
      have hy' : y = x' := he hy
      subst hy'
      have hne : x ≠ y := fun h => by subst h; exact lt_irrefl _ hm
      exact Finset.mem_image_of_mem _ (hT x hne fun h => hxy h.symm)
    · refine ⟨∅, by simp, ?_⟩
      rintro m _ ⟨x, x', _, rfl, _⟩
      exact absurd ⟨x', rfl⟩ hn
  obtain ⟨col, hcol⟩ := exists_greedy_coloring R M hR
  have hdisj : ∀ x x', x ≠ x' → col (e x) = col (e x') → Disjoint (K x) (K x') := by
    intro x x' hne hc
    by_contra hK
    rcases lt_or_gt_of_ne (he.ne hne) with h | h
    · exact hcol _ _ h ⟨x, x', rfl, rfl, hK⟩ hc
    · exact hcol _ _ h ⟨x', x, rfl, rfl, fun h' => hK h'.symm⟩ hc.symm
  -- some colour class has divergent sum
  set f : ι → ℝ≥0∞ := fun x => bernoulliSeq p (cyl (K x))
  have hsplit : ∑' x, f x = ∑ c : Fin (M + 1), ∑' x, {x | col (e x) = c}.indicator f x := by
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine tsum_congr fun x => ?_
    rw [Finset.sum_eq_single (col (e x))]
    · simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  obtain ⟨c, hc⟩ : ∃ c : Fin (M + 1), ∑' x, {x | col (e x) = c}.indicator f x = ∞ := by
    by_contra h
    push Not at h
    rw [hsum] at hsplit
    exact ENNReal.sum_ne_top.2 (fun c _ => h c) hsplit.symm
  rw [← tsum_subtype] at hc
  exact ae_infinite_of_disjoint p {x | col (e x) = c} K
    (fun x hx x' hx' hne => hdisj x x' hne (hx.trans hx'.symm)) hc

/-! ## Strategies (Definition \ref{IB:def:strategy}) -/

/-- `∑_{x ∈ X} w_U(x)`. -/
noncomputable def wsum (p : ℕ → I) (U : Finset ℕ) (X : Set ℕ) : ℝ≥0∞ :=
  ∑' x, X.indicator (w p U) x

/-- `X_S(U, V) = {x ∈ ℕ \ V : (U, V ∪ {x}) ∈ S}`. -/
def Xs (S : Set (Finset ℕ × Finset ℕ)) (U V : Finset ℕ) : Set ℕ :=
  {x | x ∉ V ∧ (U, insert x V) ∈ S}

/-- `Y_S(U, V) = {y ∈ ℕ \ U : (U ∪ {y}, V) ∈ S}`. -/
def Ys (S : Set (Finset ℕ × Finset ℕ)) (U V : Finset ℕ) : Set ℕ :=
  {y | y ∉ U ∧ (insert y U, V) ∈ S}

/-- Paper, Definition \ref{IB:def:strategy}: a `BC`-strategy for `p` is a set `S` of pairs of
finite subsets of `ℕ` with `(∅, ∅) ∈ S` such that for every `(U, V) ∈ S`,
(a) `∑_{x ∈ X_S(U,V)} w_U(x) = ∞` and (b) `∑_{y ∈ Y_S(U,V)} w_V(y) = ∞`. -/
def IsBCStrategy (p : ℕ → I) (S : Set (Finset ℕ × Finset ℕ)) : Prop :=
  (∅, ∅) ∈ S ∧ ∀ U V, (U, V) ∈ S → wsum p U (Xs S U V) = ∞ ∧ wsum p V (Ys S U V) = ∞

/-- The weight `w*_U(x)`: `w_U(x)` for `⊕`-strategies (`plus = false`) and `p_{2x} w_U(x)` for
`+`-strategies (`plus = true`). -/
noncomputable def wstar (p : ℕ → I) (plus : Bool) (U : Finset ℕ) (x : ℕ) : ℝ≥0∞ :=
  if plus then pe p (2 * x) * w p U x else w p U x

/-- `X_S(U) = {x ∈ ℕ \ U : U ∪ {x} ∈ S}`. -/
def X1 (S : Set (Finset ℕ)) (U : Finset ℕ) : Set ℕ := {x | x ∉ U ∧ insert x U ∈ S}

/-- A `⊕`-strategy (`plus = false`) or `+`-strategy (`plus = true`): a set `S` of finite subsets
of `ℕ` with `∅ ∈ S` such that `∑_{x ∈ X_S(U)} w*_U(x) = ∞` for every `U ∈ S`. -/
def IsStrategy1 (p : ℕ → I) (plus : Bool) (S : Set (Finset ℕ)) : Prop :=
  ∅ ∈ S ∧ ∀ U ∈ S, ∑' x, (X1 S U).indicator (wstar p plus U) x = ∞

/-- Paper, Definition \ref{IB:def:strategy}: an `⊕`-strategy. -/
abbrev IsOplusStrategy (p : ℕ → I) (S : Set (Finset ℕ)) : Prop := IsStrategy1 p false S

/-- Paper, Definition \ref{IB:def:strategy}: a `+`-strategy. -/
abbrev IsPlusStrategy (p : ℕ → I) (S : Set (Finset ℕ)) : Prop := IsStrategy1 p true S

/-- `B ⊕ B = {b + b' : b, b' ∈ B, b ≠ b'}`. -/
def oplus (B : Set ℕ) : Set ℕ := {n | ∃ b ∈ B, ∃ b' ∈ B, b ≠ b' ∧ n = b + b'}

/-- The event `E_⊕`: there is an infinite `B ⊆ ℕ` with `B ⊕ B ⊆ A`. -/
def HasOplus (A : Set ℕ) : Prop := ∃ B : Set ℕ, B.Infinite ∧ oplus B ⊆ A

/-- The event `E_+`: there is an infinite `B ⊆ ℕ` with `B + B ⊆ A`. -/
def HasPlus (A : Set ℕ) : Prop := ∃ B : Set ℕ, B.Infinite ∧ sumset B B ⊆ A

/-- `E_⊕` (`plus = false`) or `E_+` (`plus = true`), in the form `B ⊕ B ⊆ A` and, in the `+`
case, `2b ∈ A` for `b ∈ B`. -/
def Has1 (plus : Bool) (A : Set ℕ) : Prop :=
  ∃ B : Set ℕ, B.Infinite ∧ oplus B ⊆ A ∧ (plus → ∀ b ∈ B, 2 * b ∈ A)

lemma has1_false (A : Set ℕ) : Has1 false A ↔ HasOplus A := by
  simp [Has1, HasOplus]

lemma sumset_self_subset_iff (B A : Set ℕ) :
    sumset B B ⊆ A ↔ oplus B ⊆ A ∧ ∀ b ∈ B, 2 * b ∈ A := by
  constructor
  · intro h
    refine ⟨?_, fun b hb => h ⟨b, hb, b, hb, by ring⟩⟩
    rintro _ ⟨b, hb, b', hb', -, rfl⟩
    exact h ⟨b, hb, b', hb', rfl⟩
  · rintro ⟨h1, h2⟩ _ ⟨b, hb, b', hb', rfl⟩
    by_cases hbb : b = b'
    · subst hbb; rw [← two_mul]; exact h2 b hb
    · exact h1 ⟨b, hb, b', hb', hbb, rfl⟩

lemma has1_true (A : Set ℕ) : Has1 true A ↔ HasPlus A := by
  simp only [Has1, HasPlus, sumset_self_subset_iff, forall_const]

/-! ### Cylinder computations -/

/-- The set `x + U`. -/
def tr (U : Finset ℕ) (x : ℕ) : Finset ℕ := U.image (x + ·)

lemma measure_cyl_tr (p : ℕ → I) (U : Finset ℕ) (x : ℕ) :
    bernoulliSeq p (cyl (tr U x)) = w p U x := measure_cyl_image p U x

lemma mem_cyl_tr {ω : ℕ → Bool} {U : Finset ℕ} {x : ℕ} :
    ω ∈ cyl (tr U x) ↔ ∀ u ∈ U, x + u ∈ randSet ω := mem_cyl_image

/-- `K_x = x + U`, resp. `K_x = {2x} ∪ (x + U)`. -/
def Kstar (plus : Bool) (U : Finset ℕ) (x : ℕ) : Finset ℕ :=
  if plus then insert (2 * x) (tr U x) else tr U x

lemma mem_cyl_Kstar {ω : ℕ → Bool} {plus : Bool} {U : Finset ℕ} {x : ℕ} :
    ω ∈ cyl (Kstar plus U x) ↔
      (∀ u ∈ U, x + u ∈ randSet ω) ∧ (plus → 2 * x ∈ randSet ω) := by
  cases plus
  · simp [Kstar, mem_cyl_tr]
  · simp only [Kstar, if_true, cyl, Finset.mem_insert, forall_eq_or_imp, tr, Finset.mem_image,
      randSet, Set.mem_ofPred_eq, forall_const]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun u hu => h2 _ ⟨u, hu, rfl⟩, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, by rintro _ ⟨u, hu, rfl⟩; exact h1 u hu⟩

lemma measure_cyl_Kstar (p : ℕ → I) (plus : Bool) (U : Finset ℕ) {x : ℕ} (hx : plus → x ∉ U) :
    bernoulliSeq p (cyl (Kstar plus U x)) = wstar p plus U x := by
  cases plus
  · simp [Kstar, wstar, measure_cyl_tr]
  · have hnot : 2 * x ∉ tr U x := by
      simp only [tr, Finset.mem_image, not_exists, not_and]
      intro u hu h
      have : u = x := by omega
      exact hx rfl (this ▸ hu)
    simp only [Kstar, if_true, wstar]
    rw [measure_cyl, Finset.prod_insert hnot, ← measure_cyl, measure_cyl_tr]
    rfl

/-- `x + U` meets `x' + U` for at most `|U|²` indices `x' ≠ x`. -/
lemma tr_bound (U : Finset ℕ) (x : ℕ) :
    ∃ T : Finset ℕ, T.card ≤ U.card ^ 2 ∧
      ∀ x', x' ≠ x → ¬ Disjoint (tr U x) (tr U x') → x' ∈ T := by
  refine ⟨(U ×ˢ U).image fun q => x + q.1 - q.2, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by rw [Finset.card_product, sq])
  · intro x' _ h
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨z, hz, hz'⟩ := h
    simp only [tr, Finset.mem_image] at hz hz'
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨u', hu', e⟩ := hz'
    exact Finset.mem_image.2 ⟨(u, u'), Finset.mem_product.2 ⟨hu, hu'⟩, by simp; omega⟩

/-- `{2x} ∪ (x + U)` meets `{2x'} ∪ (x' + U)` for at most `|U|² + 2|U|` indices `x' ≠ x`. -/
lemma Kstar_bound (plus : Bool) (U : Finset ℕ) (x : ℕ) :
    ∃ T : Finset ℕ, T.card ≤ U.card ^ 2 + 2 * U.card ∧
      ∀ x', x' ≠ x → ¬ Disjoint (Kstar plus U x) (Kstar plus U x') → x' ∈ T := by
  refine ⟨((U ×ˢ U).image fun q => x + q.1 - q.2) ∪ (U.image fun u => (x + u) / 2) ∪
    (U.image fun u => 2 * x - u), ?_, ?_⟩
  · refine (Finset.card_union_le _ _).trans ?_
    refine (add_le_add (Finset.card_union_le _ _) Finset.card_image_le).trans ?_
    have h1 := (Finset.card_image_le (s := U ×ˢ U) (f := fun q => x + q.1 - q.2)).trans
      (Finset.card_product U U).le
    rw [sq]
    have h2 := Finset.card_image_le (s := U) (f := fun u => (x + u) / 2)
    omega
  · intro x' hne h
    rw [Finset.not_disjoint_iff] at h
    obtain ⟨z, hz, hz'⟩ := h
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product]
    cases plus
    · simp only [Kstar, tr, Bool.false_eq_true, if_false, Finset.mem_image] at hz hz'
      obtain ⟨u, hu, rfl⟩ := hz
      obtain ⟨u', hu', e⟩ := hz'
      exact Or.inl (Or.inl ⟨(u, u'), ⟨hu, hu'⟩, by simp; omega⟩)
    · simp only [Kstar, if_true, tr, Finset.mem_insert, Finset.mem_image] at hz hz'
      rcases hz with rfl | ⟨u, hu, rfl⟩ <;> rcases hz' with e | ⟨u', hu', e⟩
      · exact absurd (by omega) hne
      · exact Or.inr ⟨u', hu', by omega⟩
      · exact Or.inl (Or.inr ⟨u, hu, by omega⟩)
      · exact Or.inl (Or.inl ⟨(u, u'), ⟨hu, hu'⟩, by simp; omega⟩)

/-- Restricting a family indexed by `ℕ` to a subset preserves the bounded-overlap property. -/
lemma bound_subtype {K : ℕ → Finset ℕ} {M : ℕ}
    (h : ∀ x, ∃ T : Finset ℕ, T.card ≤ M ∧ ∀ x', x' ≠ x → ¬ Disjoint (K x) (K x') → x' ∈ T)
    (s : Set ℕ) :
    ∀ x : s, ∃ T : Finset s, T.card ≤ M ∧
      ∀ x' : s, x' ≠ x → ¬ Disjoint (K x) (K x') → x' ∈ T := by
  classical
  intro x
  obtain ⟨T, hTc, hT⟩ := h x
  refine ⟨T.subtype (· ∈ s), (Finset.card_subtype _ _).le.trans
    ((Finset.card_filter_le _ _).trans hTc), fun x' hne hK => ?_⟩
  rw [Finset.mem_subtype]
  exact hT x' (fun e => hne (Subtype.ext e)) hK

/-- Lemma \ref{IB:lem:BC} applied to `K_x = x + U` (resp. `{2x} ∪ (x + U)`), `x ∈ X`, `X ∩ U = ∅`:
if `∑_{x ∈ X} w*_U(x) = ∞`, then a.s. infinitely many `x ∈ X` have `K_x ⊆ A`. -/
lemma ae_infinite_Kstar (p : ℕ → I) (plus : Bool) (U : Finset ℕ) (X : Set ℕ)
    (hXU : plus → ∀ x ∈ X, x ∉ U) (h : ∑' x, X.indicator (wstar p plus U) x = ∞) :
    ∀ᵐ ω ∂bernoulliSeq p, {x | x ∈ X ∧ ω ∈ cyl (Kstar plus U x)}.Infinite := by
  have hb := bound_subtype (fun x => Kstar_bound plus U x) X
  have hsum : ∑' x : X, bernoulliSeq p (cyl (Kstar plus U x)) = ∞ := by
    rw [← h, ← tsum_subtype]
    exact tsum_congr fun x => measure_cyl_Kstar p plus U (fun h => hXU h x x.2)
  filter_upwards [lem_BC p (fun x : X => Kstar plus U x) _ hb hsum] with ω hω
  refine (hω.image Subtype.val_injective.injOn).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x.2, hx⟩

lemma Kstar_false (U : Finset ℕ) (x : ℕ) : Kstar false U x = tr U x := rfl

lemma wstar_false (p : ℕ → I) (U : Finset ℕ) (x : ℕ) : wstar p false U x = w p U x := rfl

/-! ## Proof of Theorem \ref{IB:thm:strategy} -/

/-- An increasing sequence of finite sets whose cardinalities are unbounded has infinite union. -/
lemma iUnion_infinite {F : ℕ → Finset ℕ} (h : ∀ r, r ≤ (F r).card) :
    (⋃ r, (F r : Set ℕ)).Infinite := by
  intro hfin
  have hsub : (F (hfin.toFinset.card + 1) : Set ℕ) ⊆ hfin.toFinset := by
    intro x hx
    rw [Set.Finite.coe_toFinset]
    exact Set.mem_iUnion.2 ⟨_, hx⟩
  have := Finset.card_le_card (Finset.coe_subset.1 hsub)
  have := h (hfin.toFinset.card + 1)
  omega

/-- The greedy construction: if from every `(U, V) ∈ S` one can always add a new `x` to `V` with
`x + U ⊆ A` staying in `S`, and then a new `y` to `U` with `y + V ⊆ A` staying in `S`, then `A`
contains `B + C` with `B, C` infinite. -/
lemma greedy_BC (S : Set (Finset ℕ × Finset ℕ)) (A : Set ℕ) (h0 : (∅, ∅) ∈ S)
    (hX : ∀ U V, (U, V) ∈ S → ∃ x ∈ Xs S U V, ∀ u ∈ U, x + u ∈ A)
    (hY : ∀ U V, (U, V) ∈ S → ∃ y ∈ Ys S U V, ∀ v ∈ V, y + v ∈ A) : HasSumset A := by
  classical
  let St := {q : Finset ℕ × Finset ℕ // q ∈ S ∧ ∀ u ∈ q.1, ∀ v ∈ q.2, u + v ∈ A}
  have step : ∀ q : St, ∃ q' : St, q.1.1 ⊆ q'.1.1 ∧ q.1.2 ⊆ q'.1.2 ∧
      q.1.1.card + 1 = q'.1.1.card ∧ q.1.2.card + 1 = q'.1.2.card := by
    rintro ⟨⟨U, V⟩, hS, hA⟩
    obtain ⟨x, ⟨hxV, hxS⟩, hxA⟩ := hX U V hS
    obtain ⟨y, ⟨hyU, hyS⟩, hyA⟩ := hY U (insert x V) hxS
    refine ⟨⟨(insert y U, insert x V), hyS, ?_⟩, Finset.subset_insert _ _,
      Finset.subset_insert _ _, (Finset.card_insert_of_notMem hyU).symm,
      (Finset.card_insert_of_notMem hxV).symm⟩
    simp only [Finset.mem_insert]
    rintro u (rfl | hu) v hv
    · exact hyA v (Finset.mem_insert.2 hv)
    · rcases hv with rfl | hv
      · rw [add_comm]; exact hxA u hu
      · exact hA u hu v hv
  choose nx hnx using step
  let q0 : St := ⟨(∅, ∅), h0, by simp⟩
  let seq : ℕ → St := fun r => nx^[r] q0
  have hsucc : ∀ r, seq (r + 1) = nx (seq r) := fun r => Function.iterate_succ_apply' _ _ _
  have hmono1 : Monotone fun r => (seq r).1.1 :=
    monotone_nat_of_le_succ fun r => by rw [hsucc]; exact (hnx _).1
  have hmono2 : Monotone fun r => (seq r).1.2 :=
    monotone_nat_of_le_succ fun r => by rw [hsucc]; exact (hnx _).2.1
  have hcard : ∀ r, (seq r).1.1.card = r ∧ (seq r).1.2.card = r := by
    intro r
    induction r with
    | zero => simp [seq, q0]
    | succ r ih => rw [hsucc]; exact ⟨by rw [← (hnx _).2.2.1, ih.1], by rw [← (hnx _).2.2.2, ih.2]⟩
  refine ⟨⋃ r, ((seq r).1.1 : Set ℕ), ⋃ r, ((seq r).1.2 : Set ℕ),
    iUnion_infinite fun r => (hcard r).1.ge, iUnion_infinite fun r => (hcard r).2.ge, ?_⟩
  rintro _ ⟨b, hb, c, hc, rfl⟩
  obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hb
  obtain ⟨r', hr'⟩ := Set.mem_iUnion.1 hc
  exact (seq (max r r')).2.2 b (hmono1 (le_max_left r r') hr) c (hmono2 (le_max_right r r') hr')

/-- If `p` has a `BC`-strategy, then a.s. `E_{BC}` holds. -/
theorem ae_hasSumset_of_strategy {p : ℕ → I} {S : Set (Finset ℕ × Finset ℕ)}
    (hS : IsBCStrategy p S) : ∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω) := by
  have hX : ∀ q : Finset ℕ × Finset ℕ, ∀ᵐ ω ∂bernoulliSeq p, q ∈ S →
      {x | x ∈ Xs S q.1 q.2 ∧ ω ∈ cyl (Kstar false q.1 x)}.Infinite := by
    intro q
    by_cases hq : q ∈ S
    · exact (ae_infinite_Kstar p false q.1 _ (fun h => absurd h Bool.false_ne_true)
        (hS.2 q.1 q.2 hq).1).mono fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hq
  have hY : ∀ q : Finset ℕ × Finset ℕ, ∀ᵐ ω ∂bernoulliSeq p, q ∈ S →
      {y | y ∈ Ys S q.1 q.2 ∧ ω ∈ cyl (Kstar false q.2 y)}.Infinite := by
    intro q
    by_cases hq : q ∈ S
    · exact (ae_infinite_Kstar p false q.2 _ (fun h => absurd h Bool.false_ne_true)
        (hS.2 q.1 q.2 hq).2).mono fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hq
  filter_upwards [ae_all_iff.2 hX, ae_all_iff.2 hY] with ω h1 h2
  refine greedy_BC S (randSet ω) hS.1 (fun U V h => ?_) (fun U V h => ?_)
  · obtain ⟨x, hx, hc⟩ := (h1 (U, V) h).nonempty
    exact ⟨x, hx, mem_cyl_tr.1 hc⟩
  · obtain ⟨y, hy, hc⟩ := (h2 (U, V) h).nonempty
    exact ⟨y, hy, mem_cyl_tr.1 hc⟩

/-- The event `E(U, V)`: there are infinite `B', C'` with `U + C' ⊆ A`, `B' + V ⊆ A` and
`B' + C' ⊆ A`. -/
def Eev (U V : Finset ℕ) (A : Set ℕ) : Prop :=
  ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (∀ u ∈ U, ∀ c ∈ C, u + c ∈ A) ∧
    (∀ b ∈ B, ∀ v ∈ V, b + v ∈ A) ∧ sumset B C ⊆ A

lemma Eev.swap {U V : Finset ℕ} {A : Set ℕ} (h : Eev U V A) : Eev V U A := by
  obtain ⟨B, C, hB, hC, h1, h2, h3⟩ := h
  refine ⟨C, B, hC, hB, fun v hv b hb => ?_, fun c hc u hu => ?_, ?_⟩
  · rw [add_comm]; exact h2 b hb v hv
  · rw [add_comm]; exact h1 u hu c hc
  · rintro _ ⟨c, hc, b, hb, rfl⟩
    rw [add_comm]; exact h3 ⟨b, hb, c, hc, rfl⟩

lemma Eev_empty (A : Set ℕ) : Eev ∅ ∅ A ↔ HasSumset A := by
  simp [Eev, HasSumset]

/-- On `E(U, V)` with witnesses `B', C'`, every `x ∈ C' \ V` has `x + U ⊆ A` and `E(U, V ∪ {x})`
holds. -/
lemma Eev.insert {U V : Finset ℕ} {A : Set ℕ} {B C : Set ℕ} (hB : B.Infinite) (hC : C.Infinite)
    (h1 : ∀ u ∈ U, ∀ c ∈ C, u + c ∈ A) (h2 : ∀ b ∈ B, ∀ v ∈ V, b + v ∈ A)
    (h3 : sumset B C ⊆ A) {x : ℕ} (hx : x ∈ C) :
    Eev U (insert x V) A := by
  refine ⟨B, C \ {x}, hB, hC.sdiff (Set.finite_singleton x), fun u hu c hc => h1 u hu c hc.1,
    fun b hb v hv => ?_, fun n ⟨b, hb, c, hc, e⟩ => h3 ⟨b, hb, c, hc.1, e⟩⟩
  rcases Finset.mem_insert.1 hv with rfl | hv
  · exact h3 ⟨b, hb, v, hx, rfl⟩
  · exact h2 b hb v hv

/-- `S* = {(U, V) : P(E(U, V)) > 0}` (outer measure). -/
def Sstar (p : ℕ → I) : Set (Finset ℕ × Finset ℕ) :=
  {q | bernoulliSeq p {ω | Eev q.1 q.2 (randSet ω)} ≠ 0}

lemma mem_Sstar_swap {p : ℕ → I} {U V : Finset ℕ} : (U, V) ∈ Sstar p ↔ (V, U) ∈ Sstar p := by
  have e : ∀ U V : Finset ℕ, {ω : ℕ → Bool | Eev U V (randSet ω)} = {ω | Eev V U (randSet ω)} :=
    fun U V => Set.ext fun ω => ⟨Eev.swap, Eev.swap⟩
  simp only [Sstar, Set.mem_ofPred_eq, e U V]

lemma Ys_Sstar (p : ℕ → I) (U V : Finset ℕ) : Ys (Sstar p) U V = Xs (Sstar p) V U := by
  ext y; simp only [Ys, Xs, Set.mem_ofPred_eq, mem_Sstar_swap (U := insert y U)]

/-- `S*` satisfies condition (a). -/
lemma Sstar_a (p : ℕ → I) {U V : Finset ℕ} (hq : (U, V) ∈ Sstar p) :
    wsum p U (Xs (Sstar p) U V) = ∞ := by
  classical
  by_contra hfin
  apply hq
  set X := Xs (Sstar p) U V
  let s : ℕ → Set (ℕ → Bool) := fun x => if x ∈ X then cyl (tr U x) else ∅
  have hs : ∑' x, bernoulliSeq p (s x) ≠ ∞ := by
    have e : ∀ x, bernoulliSeq p (s x) = X.indicator (w p U) x := by
      intro x
      by_cases hx : x ∈ X <;> simp [s, hx, measure_cyl_tr]
    simp only [e]
    exact hfin
  have h1 : ∀ᵐ ω ∂bernoulliSeq p, ∀ x, x ∉ V → (U, insert x V) ∉ Sstar p →
      ¬ Eev U (insert x V) (randSet ω) := by
    rw [ae_all_iff]
    intro x
    by_cases hx : x ∉ V ∧ (U, insert x V) ∉ Sstar p
    · have h0 : bernoulliSeq p {ω | Eev U (insert x V) (randSet ω)} = 0 := by
        have := hx.2
        simpa [Sstar] using this
      exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun ω h _ _ => h
    · exact ae_of_all _ fun ω h1 h2 => absurd ⟨h1, h2⟩ hx
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [h1, ae_finite_setOfPred_mem hs] with ω hω hfin' hE
  obtain ⟨B, C, hB, hC, hU, hV, hBC⟩ := hE
  refine ((hC.sdiff V.finite_toSet).mono fun x hx => ?_) hfin'
  have hxX : x ∈ X := by
    refine ⟨hx.2, ?_⟩
    by_contra hn
    exact hω x hx.2 hn (Eev.insert hB hC hU hV hBC hx.1)
  simp only [s, Set.mem_ofPred_eq, if_pos hxX]
  exact mem_cyl_tr.2 fun u hu => by rw [add_comm]; exact hU u hu x hx.1

/-- If `P(E_{BC}) > 0` (outer measure), then `S*` is a `BC`-strategy. -/
lemma Sstar_strategy (p : ℕ → I)
    (h : bernoulliSeq p {ω | HasSumset (randSet ω)} ≠ 0) : IsBCStrategy p (Sstar p) := by
  refine ⟨?_, fun U V hq => ⟨Sstar_a p hq, ?_⟩⟩
  · simpa [Sstar, Eev_empty] using h
  · rw [Ys_Sstar]; exact Sstar_a p (mem_Sstar_swap.1 hq)

/-- Paper, Theorem \ref{IB:thm:strategy}: `P(E_{BC}) ∈ {0, 1}`, and `P(E_{BC}) = 1` if and only
if `p` has a `BC`-strategy. -/
theorem thm_strategy (p : ℕ → I) :
    ((∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω)) ∨
      (∀ᵐ ω ∂bernoulliSeq p, ¬ HasSumset (randSet ω))) ∧
    ((∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω)) ↔ ∃ S, IsBCStrategy p S) := by
  have key : (∃ S, IsBCStrategy p S) ∨ ∀ᵐ ω ∂bernoulliSeq p, ¬ HasSumset (randSet ω) := by
    by_cases h : bernoulliSeq p {ω | HasSumset (randSet ω)} = 0
    · exact Or.inr (measure_eq_zero_iff_ae_notMem.1 h)
    · exact Or.inl ⟨_, Sstar_strategy p h⟩
  refine ⟨key.imp (fun ⟨S, hS⟩ => ae_hasSumset_of_strategy hS) id,
    ⟨fun h => key.resolve_right fun h' => ?_, fun ⟨S, hS⟩ => ae_hasSumset_of_strategy hS⟩⟩
  obtain ⟨ω, h1, h2⟩ := (h.and h').exists
  exact h2 h1

/-! ## Proof of Theorem \ref{IB:thm:strategy2} -/

/-- The greedy construction for single sets. -/
lemma greedy_1 (plus : Bool) (S : Set (Finset ℕ)) (A : Set ℕ) (h0 : ∅ ∈ S)
    (hX : ∀ U ∈ S, ∃ x ∈ X1 S U, (∀ u ∈ U, x + u ∈ A) ∧ (plus → 2 * x ∈ A)) :
    Has1 plus A := by
  classical
  let St := {U : Finset ℕ // U ∈ S ∧ (∀ u ∈ U, ∀ u' ∈ U, u ≠ u' → u + u' ∈ A) ∧
    (plus → ∀ u ∈ U, 2 * u ∈ A)}
  have step : ∀ U : St, ∃ U' : St, U.1 ⊆ U'.1 ∧ U.1.card + 1 = U'.1.card := by
    rintro ⟨U, hS, hA, h2⟩
    obtain ⟨x, ⟨hxU, hxS⟩, hxA, hx2⟩ := hX U hS
    refine ⟨⟨insert x U, hxS, ?_, ?_⟩, Finset.subset_insert _ _,
      (Finset.card_insert_of_notMem hxU).symm⟩
    · simp only [Finset.mem_insert]
      rintro u (rfl | hu) u' (rfl | hu') hne
      · exact absurd rfl hne
      · exact hxA u' hu'
      · rw [add_comm]; exact hxA u hu
      · exact hA u hu u' hu' hne
    · intro hp u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact hx2 hp
      · exact h2 hp u hu
  choose nx hnx using step
  let q0 : St := ⟨∅, h0, by simp, by simp⟩
  let seq : ℕ → St := fun r => nx^[r] q0
  have hsucc : ∀ r, seq (r + 1) = nx (seq r) := fun r => Function.iterate_succ_apply' _ _ _
  have hmono : Monotone fun r => (seq r).1 :=
    monotone_nat_of_le_succ fun r => by rw [hsucc]; exact (hnx _).1
  have hcard : ∀ r, (seq r).1.card = r := by
    intro r
    induction r with
    | zero => simp [seq, q0]
    | succ r ih => rw [hsucc, ← (hnx _).2, ih]
  refine ⟨⋃ r, ((seq r).1 : Set ℕ), iUnion_infinite fun r => (hcard r).ge, ?_, ?_⟩
  · rintro _ ⟨b, hb, b', hb', hne, rfl⟩
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hb
    obtain ⟨r', hr'⟩ := Set.mem_iUnion.1 hb'
    exact (seq (max r r')).2.2.1 b (hmono (le_max_left r r') hr) b'
      (hmono (le_max_right r r') hr') hne
  · intro hp b hb
    obtain ⟨r, hr⟩ := Set.mem_iUnion.1 hb
    exact (seq r).2.2.2 hp b hr

/-- If `p` has a `⊕`- (resp. `+`-) strategy, then a.s. `E_⊕` (resp. `E_+`) holds. -/
theorem ae_has1_of_strategy {p : ℕ → I} {plus : Bool} {S : Set (Finset ℕ)}
    (hS : IsStrategy1 p plus S) : ∀ᵐ ω ∂bernoulliSeq p, Has1 plus (randSet ω) := by
  have hX : ∀ U : Finset ℕ, ∀ᵐ ω ∂bernoulliSeq p, U ∈ S →
      {x | x ∈ X1 S U ∧ ω ∈ cyl (Kstar plus U x)}.Infinite := by
    intro U
    by_cases hU : U ∈ S
    · exact (ae_infinite_Kstar p plus U _ (fun _ x hx => hx.1) (hS.2 U hU)).mono
        fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hU
  filter_upwards [ae_all_iff.2 hX] with ω h1
  refine greedy_1 plus S (randSet ω) hS.1 fun U hU => ?_
  obtain ⟨x, hx, hc⟩ := (h1 U hU).nonempty
  exact ⟨x, hx, mem_cyl_Kstar.1 hc⟩

/-- The event `E*(U)`: there is an infinite `B'` with `U + B' ⊆ A`, `B' ⊕ B' ⊆ A` (and `2b ∈ A`
for `b ∈ B'` in the `+` case). -/
def Estar (plus : Bool) (U : Finset ℕ) (A : Set ℕ) : Prop :=
  ∃ B : Set ℕ, B.Infinite ∧ (∀ u ∈ U, ∀ b ∈ B, u + b ∈ A) ∧ oplus B ⊆ A ∧
    (plus → ∀ b ∈ B, 2 * b ∈ A)

lemma Estar_empty (plus : Bool) (A : Set ℕ) : Estar plus ∅ A ↔ Has1 plus A := by
  simp [Estar, Has1]

/-- `S* = {U : P(E*(U)) > 0}` (outer measure). -/
def S1star (p : ℕ → I) (plus : Bool) : Set (Finset ℕ) :=
  {U | bernoulliSeq p {ω | Estar plus U (randSet ω)} ≠ 0}

lemma S1star_a (p : ℕ → I) (plus : Bool) {U : Finset ℕ} (hU : U ∈ S1star p plus) :
    ∑' x, (X1 (S1star p plus) U).indicator (wstar p plus U) x = ∞ := by
  classical
  by_contra hfin
  apply hU
  set X := X1 (S1star p plus) U
  let s : ℕ → Set (ℕ → Bool) := fun x => if x ∈ X then cyl (Kstar plus U x) else ∅
  have hs : ∑' x, bernoulliSeq p (s x) ≠ ∞ := by
    have e : ∀ x, bernoulliSeq p (s x) = X.indicator (wstar p plus U) x := by
      intro x
      by_cases hx : x ∈ X
      · simp [s, hx, measure_cyl_Kstar p plus U (fun _ => hx.1)]
      · simp [s, hx]
    simp only [e]
    exact hfin
  have h1 : ∀ᵐ ω ∂bernoulliSeq p, ∀ x, x ∉ U → insert x U ∉ S1star p plus →
      ¬ Estar plus (insert x U) (randSet ω) := by
    rw [ae_all_iff]
    intro x
    by_cases hx : x ∉ U ∧ insert x U ∉ S1star p plus
    · have h0 : bernoulliSeq p {ω | Estar plus (insert x U) (randSet ω)} = 0 := by
        have := hx.2
        simpa [S1star] using this
      exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun ω h _ _ => h
    · exact ae_of_all _ fun ω h1 h2 => absurd ⟨h1, h2⟩ hx
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [h1, ae_finite_setOfPred_mem hs] with ω hω hfin' hE
  obtain ⟨B, hB, hU', hB2, hpl⟩ := hE
  refine ((hB.sdiff U.finite_toSet).mono fun x hx => ?_) hfin'
  have hxX : x ∈ X := by
    refine ⟨hx.2, ?_⟩
    by_contra hn
    refine hω x hx.2 hn ⟨B \ {x}, hB.sdiff (Set.finite_singleton x), ?_, ?_, ?_⟩
    · intro u hu b hb
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact hB2 ⟨u, hx.1, b, hb.1, fun h => hb.2 h.symm, rfl⟩
      · exact hU' u hu b hb.1
    · rintro _ ⟨b, hb, b', hb', hne, rfl⟩
      exact hB2 ⟨b, hb.1, b', hb'.1, hne, rfl⟩
    · exact fun hp b hb => hpl hp b hb.1
  simp only [s, Set.mem_ofPred_eq, if_pos hxX]
  exact mem_cyl_Kstar.2 ⟨fun u hu => by rw [add_comm]; exact hU' u hu x hx.1,
    fun hp => hpl hp x hx.1⟩

/-- The common form of the two statements of Theorem \ref{IB:thm:strategy2}. -/
theorem thm_strategy1 (p : ℕ → I) (plus : Bool) :
    ((∀ᵐ ω ∂bernoulliSeq p, Has1 plus (randSet ω)) ∨
      (∀ᵐ ω ∂bernoulliSeq p, ¬ Has1 plus (randSet ω))) ∧
    ((∀ᵐ ω ∂bernoulliSeq p, Has1 plus (randSet ω)) ↔ ∃ S, IsStrategy1 p plus S) := by
  have key : (∃ S, IsStrategy1 p plus S) ∨ ∀ᵐ ω ∂bernoulliSeq p, ¬ Has1 plus (randSet ω) := by
    by_cases h : bernoulliSeq p {ω | Has1 plus (randSet ω)} = 0
    · exact Or.inr (measure_eq_zero_iff_ae_notMem.1 h)
    · refine Or.inl ⟨S1star p plus, ?_, fun U hU => S1star_a p plus hU⟩
      simpa [S1star, Estar_empty] using h
  refine ⟨key.imp (fun ⟨S, hS⟩ => ae_has1_of_strategy hS) id,
    ⟨fun h => key.resolve_right fun h' => ?_, fun ⟨S, hS⟩ => ae_has1_of_strategy hS⟩⟩
  obtain ⟨ω, h1, h2⟩ := (h.and h').exists
  exact h2 h1

/-- Paper, Theorem \ref{IB:thm:strategy2}, for `B ⊕ B`: `P(E_⊕) ∈ {0, 1}`, and `P(E_⊕) = 1` if
and only if `p` has an `⊕`-strategy. -/
theorem thm_strategy2_oplus (p : ℕ → I) :
    ((∀ᵐ ω ∂bernoulliSeq p, HasOplus (randSet ω)) ∨
      (∀ᵐ ω ∂bernoulliSeq p, ¬ HasOplus (randSet ω))) ∧
    ((∀ᵐ ω ∂bernoulliSeq p, HasOplus (randSet ω)) ↔ ∃ S, IsOplusStrategy p S) := by
  simpa only [has1_false] using thm_strategy1 p false

/-- Paper, Theorem \ref{IB:thm:strategy2}, for `B + B`: `P(E_+) ∈ {0, 1}`, and `P(E_+) = 1` if
and only if `p` has a `+`-strategy. -/
theorem thm_strategy2_plus (p : ℕ → I) :
    ((∀ᵐ ω ∂bernoulliSeq p, HasPlus (randSet ω)) ∨
      (∀ᵐ ω ∂bernoulliSeq p, ¬ HasPlus (randSet ω))) ∧
    ((∀ᵐ ω ∂bernoulliSeq p, HasPlus (randSet ω)) ↔ ∃ S, IsPlusStrategy p S) := by
  simpa only [has1_true] using thm_strategy1 p true

/-! ## The deterministic case -/

/-- The deterministic sequence `p = 1_D`. -/
noncomputable def indP (D : Set ℕ) : ℕ → I := fun n => by classical exact if n ∈ D then 1 else 0

lemma pe_indP_of_mem {D : Set ℕ} {n : ℕ} (h : n ∈ D) : pe (indP D) n = 1 := by
  simp [pe, indP, h]

lemma pe_indP_of_notMem {D : Set ℕ} {n : ℕ} (h : n ∉ D) : pe (indP D) n = 0 := by
  simp [pe, indP, h]

/-- For `p = 1_D`, almost surely `A = D`. -/
lemma ae_randSet_indP (D : Set ℕ) : ∀ᵐ ω ∂bernoulliSeq (indP D), randSet ω = D := by
  classical
  have h : ∀ n, ∀ᵐ ω ∂bernoulliSeq (indP D), (n ∈ randSet ω ↔ n ∈ D) := by
    intro n
    have hm : ∀ n, bernoulliSeq (indP D) (cyl {n}) = pe (indP D) n := by
      intro n; rw [measure_cyl, Finset.prod_singleton]; rfl
    by_cases hn : n ∈ D
    · have hm := (hm n).trans (pe_indP_of_mem hn)
      have : bernoulliSeq (indP D) (cyl {n})ᶜ = 0 := by
        rw [prob_compl_eq_zero_iff (measurableSet_cyl _)]; exact hm
      refine (measure_eq_zero_iff_ae_notMem.1 this).mono fun ω hω => ?_
      simp only [Set.mem_compl_iff, not_not, cyl, Finset.mem_singleton, forall_eq,
        Set.mem_ofPred_eq] at hω
      simp [randSet, hω, hn]
    · have hm := (hm n).trans (pe_indP_of_notMem hn)
      refine (measure_eq_zero_iff_ae_notMem.1 hm).mono fun ω hω => ?_
      simp only [cyl, Finset.mem_singleton, forall_eq, Set.mem_ofPred_eq] at hω
      simp [randSet, hω, hn]
  filter_upwards [ae_all_iff.2 h] with ω hω
  exact Set.ext hω

/-- For `p = 1_D`, an event holds a.s. iff it holds for `D`. -/
lemma ae_indP_iff (D : Set ℕ) (P : Set ℕ → Prop) :
    (∀ᵐ ω ∂bernoulliSeq (indP D), P (randSet ω)) ↔ P D := by
  constructor
  · intro h
    obtain ⟨ω, h1, h2⟩ := (h.and (ae_randSet_indP D)).exists
    rwa [h2] at h1
  · intro h
    filter_upwards [ae_randSet_indP D] with ω hω
    rwa [hω]

lemma w_indP_eq_one {D : Set ℕ} {U : Finset ℕ} {x : ℕ} (h : ∀ u ∈ U, x + u ∈ D) :
    w (indP D) U x = 1 := by
  rw [w_eq]
  exact Finset.prod_eq_one fun u hu => pe_indP_of_mem (h u hu)

/-- The pairs of finite subsets of `B₀` and of `C₀`. -/
def pairsOf (B0 C0 : Set ℕ) : Set (Finset ℕ × Finset ℕ) := {q | ↑q.1 ⊆ B0 ∧ ↑q.2 ⊆ C0}

lemma Xs_pairsOf {B0 C0 : Set ℕ} {U V : Finset ℕ} (hU : ↑U ⊆ B0) (hV : ↑V ⊆ C0) :
    Xs (pairsOf B0 C0) U V = C0 \ V := by
  ext x
  simp only [Xs, pairsOf, Set.mem_ofPred_eq, Finset.coe_insert, Set.insert_subset_iff,
    Set.mem_sdiff, Finset.mem_coe]
  tauto

lemma Ys_pairsOf {B0 C0 : Set ℕ} {U V : Finset ℕ} (hU : ↑U ⊆ B0) (hV : ↑V ⊆ C0) :
    Ys (pairsOf B0 C0) U V = B0 \ U := by
  ext x
  simp only [Ys, pairsOf, Set.mem_ofPred_eq, Finset.coe_insert, Set.insert_subset_iff,
    Set.mem_sdiff, Finset.mem_coe]
  tauto

/-- The pairs of finite subsets of `B₀` and `C₀` form a `BC`-strategy as soon as the sums
`∑_{x ∈ C₀ \ V} w_U(x)` and `∑_{y ∈ B₀ \ U} w_V(y)` diverge for all finite `U ⊆ B₀`, `V ⊆ C₀`. -/
lemma pairsOf_strategy {p : ℕ → I} {B0 C0 : Set ℕ}
    (h : ∀ U V : Finset ℕ, ↑U ⊆ B0 → ↑V ⊆ C0 → wsum p U (C0 \ V) = ∞ ∧ wsum p V (B0 \ U) = ∞) :
    IsBCStrategy p (pairsOf B0 C0) := by
  refine ⟨⟨by simp, by simp⟩, fun U V ⟨hU, hV⟩ => ?_⟩
  rw [Xs_pairsOf hU hV, Ys_pairsOf hU hV]
  exact h U V hU hV

/-- The finite subsets of `B₀`. -/
def setsOf (B0 : Set ℕ) : Set (Finset ℕ) := {U | ↑U ⊆ B0}

lemma X1_setsOf {B0 : Set ℕ} {U : Finset ℕ} (hU : ↑U ⊆ B0) : X1 (setsOf B0) U = B0 \ U := by
  ext x
  simp only [X1, setsOf, Set.mem_ofPred_eq, Finset.coe_insert, Set.insert_subset_iff,
    Set.mem_sdiff, Finset.mem_coe]
  tauto

lemma setsOf_strategy {p : ℕ → I} {plus : Bool} {B0 : Set ℕ}
    (h : ∀ U : Finset ℕ, ↑U ⊆ B0 → ∑' x, (B0 \ U).indicator (wstar p plus U) x = ∞) :
    IsStrategy1 p plus (setsOf B0) := by
  refine ⟨by simp [setsOf], fun U hU => ?_⟩
  rw [X1_setsOf hU]
  exact h U hU

/-- Paper, the deterministic case (end of \S\ref{IB:ss:proofsAB}): for `p = 1_D`, a
`BC`-strategy exists iff `D` contains `B + C` with `B, C` infinite. -/
theorem strategy_deterministic (D : Set ℕ) :
    (∃ S, IsBCStrategy (indP D) S) ↔ HasSumset D := by
  constructor
  · intro h
    exact (ae_indP_iff D HasSumset).1 ((thm_strategy _).2.2 h)
  · rintro ⟨B, C, hB, hC, hBC⟩
    refine ⟨_, pairsOf_strategy (B0 := B) (C0 := C) fun U V hU hV => ⟨?_, ?_⟩⟩
    · refine tsum_indicator_eq_top (hC.sdiff V.finite_toSet) one_ne_zero fun x hx => ?_
      rw [w_indP_eq_one fun u hu => ?_]
      rw [add_comm]; exact hBC ⟨u, hU hu, x, hx.1, rfl⟩
    · refine tsum_indicator_eq_top (hB.sdiff U.finite_toSet) one_ne_zero fun x hx => ?_
      rw [w_indP_eq_one fun v hv => hBC ⟨x, hx.1, v, hV hv, rfl⟩]

/-- The deterministic case for single sets: for `p = 1_D`, a `⊕`- (resp. `+`-) strategy exists
iff `D ⊇ B ⊕ B` (resp. `D ⊇ B + B`) for some infinite `B`. -/
theorem strategy1_deterministic (plus : Bool) (D : Set ℕ) :
    (∃ S, IsStrategy1 (indP D) plus S) ↔ Has1 plus D := by
  constructor
  · intro h
    exact (ae_indP_iff D (Has1 plus)).1 ((thm_strategy1 _ plus).2.2 h)
  · rintro ⟨B, hB, hBB, h2⟩
    refine ⟨_, setsOf_strategy (B0 := B) fun U hU => ?_⟩
    refine tsum_indicator_eq_top (hB.sdiff U.finite_toSet) one_ne_zero fun x hx => ?_
    have hw : w (indP D) U x = 1 := w_indP_eq_one fun u hu =>
      hBB ⟨x, hx.1, u, hU hu, fun e => hx.2 (e ▸ hu), rfl⟩
    cases plus
    · simp [wstar, hw]
    · simp [wstar, hw, pe_indP_of_mem (h2 rfl x hx.1)]

/-- Paper, the deterministic case for `B ⊕ B`. -/
theorem strategy_deterministic_oplus (D : Set ℕ) :
    (∃ S, IsOplusStrategy (indP D) S) ↔ HasOplus D := by
  rw [← has1_false]; exact strategy1_deterministic false D

/-- Paper, the deterministic case for `B + B`. -/
theorem strategy_deterministic_plus (D : Set ℕ) :
    (∃ S, IsPlusStrategy (indP D) S) ↔ HasPlus D := by
  rw [← has1_true]; exact strategy1_deterministic true D

/-! ## The hierarchy (Theorem \ref{IB:thm:hierarchy}) -/

/-- Condition (F): there are infinite `B₀, C₀ ⊆ ℕ` such that `∑_{c ∈ C₀} w_U(c) = ∞` for every
finite `U ⊆ B₀` and `∑_{b ∈ B₀} w_V(b) = ∞` for every finite `V ⊆ C₀`. -/
def CondF (p : ℕ → I) : Prop :=
  ∃ B0 C0 : Set ℕ, B0.Infinite ∧ C0.Infinite ∧
    (∀ U : Finset ℕ, ↑U ⊆ B0 → wsum p U C0 = ∞) ∧ (∀ V : Finset ℕ, ↑V ⊆ C0 → wsum p V B0 = ∞)

/-- Condition (N): there are infinite `B₀, C₀ ⊆ ℕ` such that `S_G = ∞` for every finite nonempty
`G ⊆ B₀` and for every finite nonempty `G ⊆ C₀`.

(Here `S_G = ∑_{n ∈ ℕ} w_G(n)`; the paper's sum over `n ∈ ℤ` differs from it by finitely many
terms in `[0, 1]`, so the condition `S_G = ∞` is the same.) -/
def CondN (p : ℕ → I) : Prop :=
  ∃ B0 C0 : Set ℕ, B0.Infinite ∧ C0.Infinite ∧
    (∀ G : Finset ℕ, G.Nonempty → ↑G ⊆ B0 → SF p G = ∞) ∧
    (∀ G : Finset ℕ, G.Nonempty → ↑G ⊆ C0 → SF p G = ∞)

lemma SF_empty (p : ℕ → I) : SF p ∅ = ∞ := by
  simp [SF, w]

/-- (F) implies `P(E_{BC}) = 1`. -/
theorem condF_imp (p : ℕ → I) (h : CondF p) : ∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω) := by
  obtain ⟨B0, C0, -, -, hU, hV⟩ := h
  exact ae_hasSumset_of_strategy (pairsOf_strategy fun U V hU' hV' =>
    ⟨tsum_indicator_diff_eq_top (w_le_one p U) (hU U hU') V,
      tsum_indicator_diff_eq_top (w_le_one p V) (hV V hV') U⟩)

/-- `P(E_{BC}) = 1` implies (N). -/
theorem imp_condN (p : ℕ → I) (h : ∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω)) : CondN p := by
  have h0 : ∀ᵐ ω ∂bernoulliSeq p, ∀ G : Finset ℕ, SF p G ≠ ∞ → ¬ EF G (randSet ω) := by
    rw [ae_all_iff]
    intro G
    by_cases hG : SF p G = ∞
    · exact ae_of_all _ fun ω h => absurd hG h
    · exact (finite_zero p G hG).mono fun ω h _ => h
  obtain ⟨ω, ⟨B, C, hB, hC, hBC⟩, hω⟩ := (h.and h0).exists
  refine ⟨B, C, hB, hC, fun G _ hG => ?_, fun G _ hG => ?_⟩
  · by_contra hne
    refine hω G hne ⟨C, hC, ?_⟩
    rintro _ ⟨c, hc, g, hg, rfl⟩
    rw [add_comm]; exact hBC ⟨g, hG hg, c, hc, rfl⟩
  · by_contra hne
    refine hω G hne ⟨B, hB, ?_⟩
    rintro _ ⟨b, hb, g, hg, rfl⟩
    exact hBC ⟨b, hb, g, hG hg, rfl⟩

/-- (N) implies `P(E_{<ω}) = 1`. -/
theorem condN_imp (p : ℕ → I) (h : CondN p) :
    ∀ᵐ ω ∂bernoulliSeq p, HasAllFinite (randSet ω) := by
  obtain ⟨B0, C0, -, hC, -, hG⟩ := h
  refine (thm_finite_all p).1 fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨∅, rfl, SF_empty p⟩
  · obtain ⟨F, hFC, hFk⟩ := hC.exists_subset_card_eq k
    exact ⟨F, hFk, hG F (Finset.card_pos.1 (hFk ▸ hk)) hFC⟩

/-- Paper, Theorem \ref{IB:thm:hierarchy} (the implications):
`(F) ⇒ P(E_{BC}) = 1 ⇒ (N) ⇒ P(E_{<ω}) = 1`. -/
theorem thm_hierarchy (p : ℕ → I) :
    (CondF p → ∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω)) ∧
    ((∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω)) → CondN p) ∧
    (CondN p → ∀ᵐ ω ∂bernoulliSeq p, HasAllFinite (randSet ω)) :=
  ⟨condF_imp p, imp_condN p, condN_imp p⟩

/-- The remark after Theorem \ref{IB:thm:hierarchy}: (F) holds if some level set
`{n : p_n ≥ δ}`, `δ > 0`, contains `B₀ + C₀` with `B₀, C₀` infinite. -/
theorem condF_of_levelSet (p : ℕ → I) {δ : ℝ≥0∞} (hδ : δ ≠ 0) {B0 C0 : Set ℕ}
    (hB : B0.Infinite) (hC : C0.Infinite) (h : ∀ b ∈ B0, ∀ c ∈ C0, δ ≤ pe p (b + c)) :
    CondF p := by
  refine ⟨B0, C0, hB, hC, fun U hU => ?_, fun V hV => ?_⟩
  · refine tsum_indicator_eq_top hC (pow_ne_zero U.card hδ) fun x hx => ?_
    rw [w_eq, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun u hu => by rw [add_comm]; exact h u (hU hu) x hx
  · refine tsum_indicator_eq_top hB (pow_ne_zero V.card hδ) fun x hx => ?_
    rw [w_eq, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun v hv => h x hx v (hV hv)

/-- The sequence `p = q 1_D`. -/
noncomputable def qInd (q : I) (D : Set ℕ) : ℕ → I := fun n => by
  classical exact if n ∈ D then q else 0

/-- The remark after Theorem \ref{IB:thm:hierarchy}: for `p = q 1_D` with `0 < q ≤ 1`,
`P(E_{BC}) = 1` iff `D` contains `B + C` with `B, C` infinite. -/
theorem qInd_iff {q : I} (hq : 0 < (q : ℝ)) (D : Set ℕ) :
    (∀ᵐ ω ∂bernoulliSeq (qInd q D), HasSumset (randSet ω)) ↔ HasSumset D := by
  classical
  constructor
  · intro h
    have hsub : ∀ n, ∀ᵐ ω ∂bernoulliSeq (qInd q D), n ∈ randSet ω → n ∈ D := by
      intro n
      by_cases hn : n ∈ D
      · exact ae_of_all _ fun _ _ => hn
      · have h0 : bernoulliSeq (qInd q D) (cyl {n}) = 0 := by
          rw [measure_cyl, Finset.prod_singleton]
          simp [qInd, hn]
        refine (measure_eq_zero_iff_ae_notMem.1 h0).mono fun ω hω hmem => absurd ?_ hω
        intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact hmem
    obtain ⟨ω, ⟨B, C, hB, hC, hBC⟩, hω⟩ := (h.and (ae_all_iff.2 hsub)).exists
    exact ⟨B, C, hB, hC, fun n hn => hω n (hBC hn)⟩
  · rintro ⟨B0, C0, hB0, hC0, hBC⟩
    refine condF_imp _ (condF_of_levelSet _ (δ := ((toNNReal q : NNReal) : ℝ≥0∞)) ?_ hB0 hC0
      fun b hb c hc => ?_)
    · exact ne_of_gt (ENNReal.coe_pos.2 (by rw [← NNReal.coe_pos]; exact hq))
    · have hD : b + c ∈ D := hBC ⟨b, hb, c, hc, rfl⟩
      simp [pe, qInd, hD]

/-! ## Example \ref{IB:ex:oplus} -/

/-- `D = {2^i + 2^j : 0 ≤ i < j}`. -/
def Dbin : Set ℕ := {n | ∃ i j, i < j ∧ n = 2 ^ i + 2 ^ j}

lemma powsum_inj {s t : Finset ℕ} (h : ∑ i ∈ s, 2 ^ i = ∑ i ∈ t, 2 ^ i) : s = t := by
  rw [← Finset.toFinset_bitIndices_sum_two_pow s, h, Finset.toFinset_bitIndices_sum_two_pow]

/-- An element of `D` is not a sum of `2^i` over a set of `≠ 2` exponents. -/
lemma not_mem_Dbin {s : Finset ℕ} (hs : s.card ≠ 2) : ∑ i ∈ s, 2 ^ i ∉ Dbin := by
  rintro ⟨i, j, hij, e⟩
  have : s = {i, j} := powsum_inj (by rw [e, Finset.sum_pair hij.ne])
  rw [this, Finset.card_pair hij.ne] at hs
  exact hs rfl

lemma half_of_mem_Dbin {b : ℕ} (h : 2 * b ∈ Dbin) : ∃ a c, a < c ∧ b = 2 ^ a + 2 ^ c := by
  obtain ⟨i, j, hij, e⟩ := h
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [pow_succ] at e; omega
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    refine ⟨i', j', by omega, ?_⟩
    rw [pow_succ, pow_succ] at e; omega

/-- Paper, Example \ref{IB:ex:oplus}: for `D = {2^i + 2^j : i < j}`, `B = {2^i}` satisfies
`B ⊕ B ⊆ D`, but no infinite `B` satisfies `B + B ⊆ D`. Hence for `p = 1_D` there is an
`⊕`-strategy but no `+`-strategy. -/
theorem ex_oplus :
    HasOplus Dbin ∧ ¬ HasPlus Dbin ∧ (∃ S, IsOplusStrategy (indP Dbin) S) ∧
      ¬ ∃ S, IsPlusStrategy (indP Dbin) S := by
  have h1 : HasOplus Dbin := by
    refine ⟨Set.range (2 ^ ·), Set.infinite_range_of_injective
      (Nat.pow_right_injective le_rfl), ?_⟩
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, hne, rfl⟩
    rcases lt_or_gt_of_ne (fun h : i = j => hne (by rw [h])) with h | h
    · exact ⟨i, j, h, rfl⟩
    · exact ⟨j, i, h, add_comm _ _⟩
  have h2 : ¬ HasPlus Dbin := by
    rintro ⟨B, hB, hBB⟩
    have hform : ∀ b ∈ B, ∃ a c, a < c ∧ b = 2 ^ a + 2 ^ c := fun b hb =>
      half_of_mem_Dbin (hBB ⟨b, hb, b, hb, by ring⟩)
    choose! lo hi hlh hb using hform
    obtain ⟨b0, hb0⟩ := hB.nonempty
    set c := hi b0
    -- every `b ∈ B` has lowest digit `≤ c`
    have hlo : ∀ b ∈ B, lo b ≤ c := by
      intro b hbB
      by_contra hgt
      push Not at hgt
      have hmem := hBB ⟨b0, hb0, b, hbB, rfl⟩
      have e : b0 + b = ∑ i ∈ {lo b0, c, lo b, hi b}, 2 ^ i := by
        have h1 := hlh b0 hb0
        have h2 := hlh b hbB
        rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
          Finset.sum_pair (by omega)]
        conv_lhs => rw [hb b0 hb0, hb b hbB]
        ring
      have hcard : ({lo b0, c, lo b, hi b} : Finset ℕ).card = 4 := by
        have h1 := hlh b0 hb0
        have h2 := hlh b hbB
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem
          (by simp; omega), Finset.card_pair (by omega)]
      rw [e] at hmem
      exact not_mem_Dbin (by rw [hcard]; decide) hmem
    -- elements `≥ 2^(c+2)` have highest digit `≥ c + 2`
    set B' := {b ∈ B | 2 ^ (c + 2) ≤ b}
    have hB' : B'.Infinite := by
      have : B' = B \ {b | b < 2 ^ (c + 2)} := by ext b; simp [B']
      rw [this]
      exact hB.sdiff (Set.finite_lt_nat _)
    have hhi : ∀ b ∈ B', c + 2 ≤ hi b := by
      rintro b ⟨hbB, hbig⟩
      by_contra hlt
      push Not at hlt
      have h1 : 2 ^ lo b ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (hlo b hbB)
      have h2 : 2 ^ hi b ≤ 2 ^ (c + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hb b hbB] at hbig
      rw [pow_succ] at h2
      rw [pow_succ, pow_succ] at hbig
      have := Nat.two_pow_pos c
      omega
    obtain ⟨b1, hb1, b2, hb2, hne, he⟩ := hB'.exists_ne_map_eq_of_mapsTo
      (f := lo) (t := Set.Iic c) (fun b hb => hlo b hb.1) (Set.finite_Iic c)
    have hh : hi b1 ≠ hi b2 := by
      intro h
      exact hne (by rw [hb b1 hb1.1, hb b2 hb2.1, he, h])
    have hmem := hBB ⟨b1, hb1.1, b2, hb2.1, rfl⟩
    have hl1 := hhi b1 hb1
    have hl2 := hhi b2 hb2
    have hlo1 := hlo b1 hb1.1
    have e : b1 + b2 = ∑ i ∈ {lo b1 + 1, hi b1, hi b2}, 2 ^ i := by
      rw [Finset.sum_insert (by simp; omega), Finset.sum_pair hh]
      conv_lhs => rw [hb b1 hb1.1, hb b2 hb2.1]
      rw [he]; ring
    have hcard : ({lo b1 + 1, hi b1, hi b2} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair hh]
    rw [e] at hmem
    exact not_mem_Dbin (by rw [hcard]; decide) hmem
  refine ⟨h1, h2, (strategy_deterministic_oplus Dbin).2 h1, fun h => h2 ?_⟩
  exact (strategy_deterministic_plus Dbin).1 h

/-! ## Rigid sets (Lemmas \ref{IB:lem:rigid}, \ref{IB:lem:R}, Corollary \ref{IB:cor:R}) -/

/-- `Λ = {λ_0 < λ_1 < ⋯} ⊆ ℕ` with `λ_j > 8 (λ_0 + ⋯ + λ_{j-1})` for all `j`: the paper's condition
`λ_{j+1} > 8(λ_1 + ⋯ + λ_j)`, indexed from `0` (for `j = 0` it says `λ_0 ≥ 1`). -/
def IsRigidSeq (lam : ℕ → ℕ) : Prop := ∀ j, 8 * ∑ i ∈ Finset.range j, lam i < lam j

/-- The paper's example `λ_j = 9^j` (`j ≥ 1`). -/
lemma isRigidSeq_nine : IsRigidSeq fun j => 9 ^ (j + 1) := by
  have h : ∀ j, 8 * ∑ i ∈ Finset.range j, 9 ^ (i + 1) + 9 = 9 ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, mul_add, pow_succ 9 (j + 1)]; omega
  intro j
  have := h j
  simp only
  omega

/-- Membership in `Λ`, for integers. -/
def InL (lam : ℕ → ℕ) (z : ℤ) : Prop := ∃ j, z = lam j

/-- Membership in `Λ + Λ`, for integers. -/
def InLL (lam : ℕ → ℕ) (z : ℤ) : Prop := ∃ a b, z = (lam a : ℤ) + lam b

section Rigid

variable {lam : ℕ → ℕ}

lemma le_sum_range {i j : ℕ} (hij : i < j) :
    lam i ≤ ∑ k ∈ Finset.range j, lam k :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hij)

lemma IsRigidSeq.strictMono (h : IsRigidSeq lam) : StrictMono lam := by
  intro i j hij
  have := le_sum_range (lam := lam) hij
  have := h j
  omega

lemma IsRigidSeq.injective (h : IsRigidSeq lam) : Function.Injective lam :=
  h.strictMono.injective

/-- Paper, Lemma \ref{IB:lem:rigid}: if `∑_j e_j λ_j = 0` with `e_j ∈ ℤ` and `∑_j |e_j| ≤ 8`,
then all `e_j = 0`. (The finitely many possibly nonzero `e_j` are those with `j ∈ s`.) -/
theorem lem_rigid (h : IsRigidSeq lam) (s : Finset ℕ) (e : ℕ → ℤ)
    (he : ∑ j ∈ s, |e j| ≤ 8) (hz : ∑ j ∈ s, e j * lam j = 0) : ∀ j ∈ s, e j = 0 := by
  classical
  by_contra hne
  push Not at hne
  set T := s.filter fun j => e j ≠ 0
  have hT : T.Nonempty := by
    obtain ⟨j, hj, hj'⟩ := hne
    exact ⟨j, Finset.mem_filter.2 ⟨hj, hj'⟩⟩
  set J := T.max' hT
  have hJ : J ∈ T := T.max'_mem hT
  have hsT : ∑ j ∈ T, e j * lam j = ∑ j ∈ s, e j * lam j :=
    Finset.sum_filter_of_ne fun j _ hj h0 => hj (by rw [h0, zero_mul])
  rw [← hsT, ← Finset.add_sum_erase T _ hJ] at hz
  have hle8 : ∀ j ∈ s, |e j| ≤ 8 := fun j hj =>
    (Finset.single_le_sum (fun i _ => abs_nonneg (e i)) hj).trans he
  have hsub : T.erase J ⊆ Finset.range J := by
    intro j hj
    rw [Finset.mem_erase] at hj
    exact Finset.mem_range.2 (lt_of_le_of_ne (T.le_max' j hj.2) hj.1)
  have hbound : |∑ j ∈ T.erase J, e j * (lam j : ℤ)| < lam J := by
    calc |∑ j ∈ T.erase J, e j * (lam j : ℤ)| ≤ ∑ j ∈ T.erase J, |e j * (lam j : ℤ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ T.erase J, 8 * (lam j : ℤ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [abs_mul, Nat.abs_cast]
          have := hle8 j (Finset.mem_filter.1 (Finset.mem_of_mem_erase hj)).1
          exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
      _ ≤ ∑ j ∈ Finset.range J, 8 * (lam j : ℤ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity
      _ = ((8 * ∑ j ∈ Finset.range J, lam j : ℕ) : ℤ) := by push_cast; rw [Finset.mul_sum]
      _ < lam J := by exact_mod_cast h J
  have heJ : 1 ≤ |e J| := Int.one_le_abs (Finset.mem_filter.1 hJ).2
  have h1 : |e J * (lam J : ℤ)| = |∑ j ∈ T.erase J, e j * (lam j : ℤ)| := by
    rw [eq_neg_of_add_eq_zero_left hz, abs_neg]
  rw [abs_mul, Nat.abs_cast] at h1
  have : (lam J : ℤ) ≤ |e J| * lam J := le_mul_of_one_le_left (Nat.cast_nonneg _) heJ
  linarith

lemma sum_map_eq_sum_count (M : Multiset ℕ) (f : ℕ → ℤ) {s : Finset ℕ} (hs : M.toFinset ⊆ s) :
    (M.map f).sum = ∑ j ∈ s, (M.count j : ℤ) * f j := by
  classical
  rw [Finset.sum_multiset_map_count]
  simp only [nsmul_eq_mul]
  exact Finset.sum_subset hs fun j _ hj => by
    rw [Multiset.count_eq_zero.2 (by simpa using hj)]; simp

/-- Lemma \ref{IB:lem:rigid} for multisets of indices: if `∑_{i ∈ M} λ_i = ∑_{i ∈ N} λ_i` and
`|M| + |N| ≤ 8`, then `M = N`. -/
theorem rigid_ms (h : IsRigidSeq lam) {M N : Multiset ℕ} (hc : Multiset.card M + Multiset.card N ≤ 8)
    (hs : (M.map lam).sum = (N.map lam).sum) : M = N := by
  classical
  set s := (M + N).toFinset
  set e : ℕ → ℤ := fun j => (M.count j : ℤ) - N.count j
  have hMs : M.toFinset ⊆ s := fun j hj => by simp [s] at hj ⊢; exact Or.inl hj
  have hNs : N.toFinset ⊆ s := fun j hj => by simp [s] at hj ⊢; exact Or.inr hj
  have key := lem_rigid h s e ?_ ?_
  · ext j
    by_cases hj : j ∈ s
    · have := key j hj
      simp only [e] at this
      omega
    · simp only [s, Multiset.mem_toFinset, Multiset.mem_add, not_or] at hj
      rw [Multiset.count_eq_zero.2 hj.1, Multiset.count_eq_zero.2 hj.2]
  · calc ∑ j ∈ s, |e j| ≤ ∑ j ∈ s, (((M + N).count j : ℕ) : ℤ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          simp only [e, Multiset.count_add]
          push_cast
          rw [abs_le]
          constructor <;> linarith [(Nat.cast_nonneg (M.count j) : (0 : ℤ) ≤ _),
            (Nat.cast_nonneg (N.count j) : (0 : ℤ) ≤ _)]
      _ = ((Multiset.card (M + N) : ℕ) : ℤ) := by
          rw [← Multiset.toFinset_sum_count_eq]; push_cast; rfl
      _ ≤ 8 := by rw [Multiset.card_add]; exact_mod_cast hc
  · have h1 := sum_map_eq_sum_count M (fun j => (lam j : ℤ)) hMs
    have h2 := sum_map_eq_sum_count N (fun j => (lam j : ℤ)) hNs
    have h3 : (M.map fun j => (lam j : ℤ)).sum = (N.map fun j => (lam j : ℤ)).sum := by
      have := congrArg (fun n : ℕ => (n : ℤ)) hs
      simpa [Multiset.map_map] using this
    simp only [e, sub_mul, Finset.sum_sub_distrib, ← h1, ← h2, h3, sub_self]

lemma pair_eq_pair_iff' {a b c d : ℕ} :
    ({a, b} : Multiset ℕ) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a ∈ ({c, d} : Multiset ℕ) := h ▸ by simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      simpa using h
    · right
      refine ⟨rfl, ?_⟩
      rw [Multiset.pair_comm c a] at h
      simpa using h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Multiset.pair_comm _ _

/-- Paper, Lemma \ref{IB:lem:rigid}, unique representation: every element of `Λ + Λ` has a unique
representation `λ_a + λ_b` as an unordered pair. -/
theorem lem_rigid_pair (h : IsRigidSeq lam) {a b c d : ℕ} (e : lam a + lam b = lam c + lam d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [← pair_eq_pair_iff']
  exact rigid_ms h (by simp) (by simpa using e)

/-- Integer version of `lem_rigid_pair`. -/
lemma rigid_pair_int (h : IsRigidSeq lam) {a b c d : ℕ}
    (e : (lam a : ℤ) + lam b = lam c + lam d) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) :=
  lem_rigid_pair h (by exact_mod_cast e)

/-- Paper, Lemma \ref{IB:lem:rigid}, the Sidon property: if `λ_a - λ_b = λ_c - λ_d ≠ 0`, then
`λ_a = λ_c` and `λ_b = λ_d`. -/
theorem lem_rigid_sidon (h : IsRigidSeq lam) {a b c d : ℕ}
    (e : (lam a : ℤ) - lam b = lam c - lam d) (hne : (lam a : ℤ) - lam b ≠ 0) :
    lam a = lam c ∧ lam b = lam d := by
  rcases rigid_pair_int h (a := a) (b := d) (c := c) (d := b) (by linarith) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd (sub_self _) hne

end Rigid

section LemR

variable {lam : ℕ → ℕ}

/-- The conclusion of Lemma \ref{IB:lem:R} for a given `t`: `x - t ∈ Λ` for `x ∈ X`, `c + t ∈ Λ`
for `c ∈ Γ`, and `P(x + c) = {x - t, c + t}` (as multisets) for `x ∈ X`, `c ∈ Γ`, where `P(n)` is
the unordered pair `{λ, λ'}` with `n = λ + λ'`. -/
def IsShift (lam : ℕ → ℕ) (X Γ : Set ℤ) (t : ℤ) : Prop :=
  (∀ x ∈ X, InL lam (x - t)) ∧ (∀ c ∈ Γ, InL lam (c + t)) ∧
    ∀ x ∈ X, ∀ c ∈ Γ, ∀ a b : ℕ, x + c = (lam a : ℤ) + lam b →
      ({(lam a : ℤ), (lam b : ℤ)} : Multiset ℤ) = {x - t, c + t}

lemma isShift_of (h : IsRigidSeq lam) {X Γ : Set ℤ} {t : ℤ} (h1 : ∀ x ∈ X, InL lam (x - t))
    (h2 : ∀ c ∈ Γ, InL lam (c + t)) : IsShift lam X Γ t := by
  refine ⟨h1, h2, fun x hx c hc a b e => ?_⟩
  obtain ⟨i, hi⟩ := h1 x hx
  obtain ⟨j, hj⟩ := h2 c hc
  rw [hi, hj]
  rcases rigid_pair_int h (a := a) (b := b) (c := i) (d := j)
    (by rw [← e, ← hi, ← hj]; ring) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Multiset.pair_comm _ _

/-- Uniqueness of the shift, from one row and two columns. -/
lemma shift_unique (h : IsRigidSeq lam) {x c1 c2 t t' : ℤ} (hc : c1 ≠ c2)
    (hx : InL lam (x - t)) (hx' : InL lam (x - t')) (h1 : InL lam (c1 + t))
    (h1' : InL lam (c1 + t')) (h2 : InL lam (c2 + t)) (h2' : InL lam (c2 + t')) : t = t' := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨a', ha'⟩ := hx'
  have key : ∀ c, InL lam (c + t) → InL lam (c + t') → t = t' ∨ x - t = c + t' := by
    rintro c ⟨b, hb⟩ ⟨b', hb'⟩
    rcases rigid_pair_int h (a := a) (b := b) (c := a') (d := b')
      (by rw [← ha, ← hb, ← ha', ← hb']; ring) with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · left; linarith
    · right; rw [ha, hb']
  rcases key c1 h1 h1' with e | e1
  · exact e
  rcases key c2 h2 h2' with e | e2
  · exact e
  exact absurd (by linarith) hc

lemma ms_cancel {P Q P' R : Multiset ℕ} (h : P + Q = P' + R) (hd : ∀ z ∈ P, z ∉ R)
    (hc : Multiset.card P' ≤ Multiset.card P) : P = P' := by
  classical
  refine Multiset.eq_of_le_of_card_le (Multiset.le_iff_count.2 fun z => ?_) hc
  by_cases hz : z ∈ P
  · have := congrArg (Multiset.count z) h
    simp only [Multiset.count_add, Multiset.count_eq_zero.2 (hd z hz)] at this
    omega
  · rw [Multiset.count_eq_zero.2 hz]; exact Nat.zero_le _

lemma map_sum_four (a b c d : ℕ) :
    (({a, b, c, d} : Multiset ℕ).map lam).sum = lam a + lam b + lam c + lam d := by
  simp; ring

/-- Lemma \ref{IB:lem:R} for two rows. -/
lemma two_rows (h : IsRigidSeq lam) {x1 x2 : ℤ} (hx : x1 ≠ x2) {Γ : Set ℤ} {c1 c2 : ℤ}
    (hc1 : c1 ∈ Γ) (hc2 : c2 ∈ Γ) (hc : c1 ≠ c2)
    (hΓ : ∀ c ∈ Γ, InLL lam (x1 + c) ∧ InLL lam (x2 + c)) :
    ∃ t, InL lam (x1 - t) ∧ InL lam (x2 - t) ∧ ∀ c ∈ Γ, InL lam (c + t) := by
  -- a column in which the two representations share an element
  have good : ∃ u u' v : ℕ, ∃ c0 ∈ Γ, x1 + c0 = (lam u : ℤ) + lam v ∧
      x2 + c0 = (lam u' : ℤ) + lam v := by
    by_contra hng
    push Not at hng
    have disj : ∀ c ∈ Γ, ∀ a1 b1 a2 b2 : ℕ, x1 + c = (lam a1 : ℤ) + lam b1 →
        x2 + c = (lam a2 : ℤ) + lam b2 → ∀ z ∈ ({a1, b1} : Multiset ℕ),
          z ∉ ({a2, b2} : Multiset ℕ) := by
      intro c hc a1 b1 a2 b2 e1 e2 z hz hz'
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz hz'
      rcases hz with rfl | rfl <;> rcases hz' with hq | hq
      · exact hng b1 b2 z c hc (by rw [e1]; ring) (by rw [e2, hq]; ring)
      · exact hng b1 a2 z c hc (by rw [e1]; ring) (by rw [e2, hq])
      · exact hng a1 b2 z c hc e1 (by rw [e2, hq]; ring)
      · exact hng a1 a2 z c hc e1 (by rw [e2, hq])
    obtain ⟨⟨a1, b1, e1⟩, ⟨a2, b2, e2⟩⟩ := hΓ c1 hc1
    obtain ⟨⟨a1', b1', e1'⟩, ⟨a2', b2', e2'⟩⟩ := hΓ c2 hc2
    have hrel : (({a1, b1} + {a2', b2'} : Multiset ℕ).map lam).sum =
        (({a1', b1'} + {a2, b2} : Multiset ℕ).map lam).sum := by
      simp only [Multiset.map_add, Multiset.sum_add, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton]
      have : (x1 + c1) + (x2 + c2) = (x1 + c2) + (x2 + c1) := by ring
      rw [e1, e2, e1', e2'] at this
      have h' : ((lam a1 + (lam b1) + (lam a2' + lam b2') : ℕ) : ℤ) =
          ((lam a1' + lam b1' + (lam a2 + lam b2) : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast h'
    have hms := rigid_ms h (by simp) hrel
    have hP := ms_cancel hms (disj c1 hc1 a1 b1 a2 b2 e1 e2) (by simp)
    have : (lam a1 : ℤ) + lam b1 = lam a1' + lam b1' := by
      have := congrArg (fun M : Multiset ℕ => (M.map lam).sum) hP
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton] at this
      exact_mod_cast this
    exact hc (by linarith)
  obtain ⟨u, u', v, c0, hc0, f1, f2⟩ := good
  have huu : u ≠ u' := by
    rintro rfl
    exact hx (by linarith)
  refine ⟨x1 - lam u, by rw [sub_sub_cancel]; exact ⟨u, rfl⟩, ⟨u', by linarith⟩, fun c hc => ?_⟩
  obtain ⟨⟨a1, b1, e1⟩, ⟨a2, b2, e2⟩⟩ := hΓ c hc
  have hrel : (({a1, b1, u'} : Multiset ℕ).map lam).sum = (({a2, b2, u} : Multiset ℕ).map lam).sum := by
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton]
    have : (x1 + c) - (x2 + c) = (x1 + c0) - (x2 + c0) := by ring
    rw [e1, e2, f1, f2] at this
    have h' : ((lam a1 + (lam b1 + lam u') : ℕ) : ℤ) =
        ((lam a2 + (lam b2 + lam u) : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast h'
  have hms := rigid_ms h (by simp) hrel
  have hu : u ∈ ({a1, b1, u'} : Multiset ℕ) := hms ▸ by simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · exact ⟨b1, by linarith⟩
  · exact ⟨a1, by linarith⟩
  · exact absurd rfl huu

/-- Paper, Lemma \ref{IB:lem:R}: let `X, Γ ⊆ ℤ` with `|X| ≥ 2`, `|Γ| ≥ 2` and
`X + Γ ⊆ Λ + Λ`. Then there is a unique `t ∈ ℤ` such that `x - t ∈ Λ` for `x ∈ X`, `c + t ∈ Λ`
for `c ∈ Γ`, and `P(x + c) = {x - t, c + t}` for `x ∈ X`, `c ∈ Γ`. -/
theorem lem_R (h : IsRigidSeq lam) {X Γ : Set ℤ} (hX : ∃ x1 ∈ X, ∃ x2 ∈ X, x1 ≠ x2)
    (hΓ : Γ.Nontrivial) (hXΓ : ∀ x ∈ X, ∀ c ∈ Γ, InLL lam (x + c)) :
    ∃! t, IsShift lam X Γ t := by
  obtain ⟨x1, hx1, x2, hx2, hx⟩ := hX
  obtain ⟨c1, hc1, c2, hc2, hc⟩ := hΓ
  obtain ⟨t, ht1, -, htc⟩ := two_rows h hx hc1 hc2 hc fun c hc => ⟨hXΓ x1 hx1 c hc, hXΓ x2 hx2 c hc⟩
  refine ⟨t, isShift_of h (fun x hx => ?_) htc, fun t' ht' => ?_⟩
  · by_cases hxx : x = x1
    · rw [hxx]; exact ht1
    obtain ⟨t', ht1', htx', htc'⟩ := two_rows h (Ne.symm hxx) hc1 hc2 hc
      fun c hc => ⟨hXΓ x1 hx1 c hc, hXΓ x hx c hc⟩
    have := shift_unique h hc ht1 ht1' (htc c1 hc1) (htc' c1 hc1) (htc c2 hc2) (htc' c2 hc2)
    rw [this]; exact htx'
  · exact (shift_unique h hc ht1 (ht'.1 x1 hx1) (htc c1 hc1) (ht'.2.1 c1 hc1) (htc c2 hc2)
      (ht'.2.1 c2 hc2)).symm

/-- Paper, Lemma \ref{IB:lem:R}, last assertion: if `X' ⊆ X` and `Γ' ⊆ Γ` with `|X'| ≥ 2` and
`|Γ'| ≥ 2`, then `t(X', Γ') = t(X, Γ)`. -/
theorem lem_R_mono (h : IsRigidSeq lam) {X Γ X' Γ' : Set ℤ} (hX' : ∃ x1 ∈ X', ∃ x2 ∈ X', x1 ≠ x2)
    (hΓ' : Γ'.Nontrivial) (hXX : X' ⊆ X) (hΓΓ : Γ' ⊆ Γ) {t t' : ℤ} (ht : IsShift lam X Γ t)
    (ht' : IsShift lam X' Γ' t') : t' = t := by
  obtain ⟨x1, hx1, -, -, -⟩ := hX'
  obtain ⟨c1, hc1, c2, hc2, hc⟩ := hΓ'
  exact shift_unique h hc (ht'.1 x1 hx1) (ht.1 x1 (hXX hx1)) (ht'.2.1 c1 hc1)
    (ht.2.1 c1 (hΓΓ hc1)) (ht'.2.1 c2 hc2) (ht.2.1 c2 (hΓΓ hc2))

/-- Paper, Corollary \ref{IB:cor:R}: if `B, C ⊆ ℤ` are infinite and `B + C ⊆ Λ + Λ`, there is
`t ∈ ℤ` with `B - t ⊆ Λ`, `C + t ⊆ Λ` and `P(b + c) = {b - t, c + t}` for `b ∈ B`, `c ∈ C`. -/
theorem cor_R (h : IsRigidSeq lam) {B C : Set ℤ} (hB : B.Infinite) (hC : C.Infinite)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, InLL lam (b + c)) : ∃ t, IsShift lam B C t :=
  (lem_R h hB.nontrivial hC.nontrivial hBC).exists

end LemR

/-! ## Examples \ref{IB:ex:half} and \ref{IB:ex:rigid} -/

lemma EF_iff_infinite (G : Finset ℕ) (A : Set ℕ) :
    EF G A ↔ {n | ∀ g ∈ G, n + g ∈ A}.Infinite := by
  constructor
  · rintro ⟨B, hB, hBG⟩
    exact hB.mono fun b hb g hg => hBG ⟨b, hb, g, hg, rfl⟩
  · intro h
    refine ⟨_, h, ?_⟩
    rintro _ ⟨n, hn, g, hg, rfl⟩
    exact hn g hg

/-- For `p = 1_D`, `S_G = ∞` iff `G` has infinitely many translates in `D`. -/
lemma SF_indP_eq_top_iff (D : Set ℕ) (G : Finset ℕ) : SF (indP D) G = ∞ ↔ EF G D := by
  constructor
  · intro h
    exact (ae_indP_iff D (EF G)).1 (finite_one _ G h)
  · intro h
    by_contra hne
    exact (ae_indP_iff D (fun A => ¬ EF G A)).1 (finite_zero _ G hne) h

lemma infinite_image_cast {s : Set ℕ} (hs : s.Infinite) : ((fun n : ℕ => (n : ℤ)) '' s).Infinite :=
  hs.image Nat.cast_injective.injOn

lemma finite_of_cast_subset {s : Set ℕ} {T : Set ℤ} (hT : T.Finite)
    (h : ∀ n ∈ s, (n : ℤ) ∈ T) : s.Finite :=
  (hT.preimage Nat.cast_injective.injOn).subset fun n hn => h n hn

section Examples

variable {lam : ℕ → ℕ}

/-- Corollary \ref{IB:cor:R} for subsets of `ℕ`, with explicit indices. -/
lemma cor_R_nat (h : IsRigidSeq lam) {B C : Set ℕ} (hB : B.Infinite) (hC : C.Infinite)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, InLL lam ((b : ℤ) + c)) :
    ∃ t : ℤ, ∃ jb jc : ℕ → ℕ, (∀ b ∈ B, (b : ℤ) - t = lam (jb b)) ∧
      ∀ c ∈ C, (c : ℤ) + t = lam (jc c) := by
  obtain ⟨t, ht1, ht2, -⟩ := cor_R h (infinite_image_cast hB) (infinite_image_cast hC)
    (by rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩; exact hBC b hb c hc)
  have h1 : ∀ b : ℕ, ∃ j, b ∈ B → (b : ℤ) - t = lam j := fun b => by
    by_cases hb : b ∈ B
    · obtain ⟨j, hj⟩ := ht1 _ ⟨b, hb, rfl⟩; exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => absurd h hb⟩
  have h2 : ∀ c : ℕ, ∃ j, c ∈ C → (c : ℤ) + t = lam j := fun c => by
    by_cases hc : c ∈ C
    · obtain ⟨j, hj⟩ := ht2 _ ⟨c, hc, rfl⟩; exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose jb hjb using h1
  choose jc hjc using h2
  exact ⟨t, jb, jc, fun b hb => hjb b hb, fun c hc => hjc c hc⟩

lemma rigid_pair_shift (h : IsRigidSeq lam) {b c : ℕ} {t : ℤ} {j j' x y : ℕ}
    (hb : (b : ℤ) - t = lam j) (hc : (c : ℤ) + t = lam j') (e : b + c = lam x + lam y) :
    (j = x ∧ j' = y) ∨ (j = y ∧ j' = x) := by
  have e' : (b : ℤ) + c = lam x + lam y := by exact_mod_cast e
  exact rigid_pair_int h (by rw [← hb, ← hc]; linarith)

lemma two_mul_ne_two_mul_add_one {a b : ℕ} : 2 * a ≠ 2 * b + 1 := by omega

/-- The set `D = {β_{k,m} + γ_i : i ≤ k}` of Example \ref{IB:ex:half}, with the labels
`β_{k,m} = λ_{2⟨k,m⟩}` and `γ_i = λ_{2i+1}` (`⟨·,·⟩` the Cantor pairing). -/
def halfD (lam : ℕ → ℕ) : Set ℕ :=
  {n | ∃ k m i, i ≤ k ∧ n = lam (2 * Nat.pair k m) + lam (2 * i + 1)}

/-- Paper, Example \ref{IB:ex:half}: for `p = 1_D` with `D = {β_{k,m} + γ_i : i ≤ k}`, condition
(N) holds but `P(E_{BC}) = 0`; in particular `D` has all finite configurations (`E_{<ω}`) but
contains no `B + C` with `B, C` infinite. -/
theorem ex_half (h : IsRigidSeq lam) :
    CondN (indP (halfD lam)) ∧
    (∀ᵐ ω ∂bernoulliSeq (indP (halfD lam)), ¬ HasSumset (randSet ω)) ∧
    HasAllFinite (halfD lam) ∧ ¬ HasSumset (halfD lam) := by
  have hmono := h.strictMono
  have hγinj : Function.Injective fun i => lam (2 * i + 1) :=
    h.injective.comp fun a b e => by simp at e; omega
  have hN : CondN (indP (halfD lam)) := by
    have hC0 : (Set.range fun i => lam (2 * i + 1)).Infinite :=
      Set.infinite_range_of_injective hγinj
    have key : ∀ G : Finset ℕ, ↑G ⊆ Set.range (fun i => lam (2 * i + 1)) →
        SF (indP (halfD lam)) G = ∞ := by
      intro G hG
      rw [SF_indP_eq_top_iff]
      set K := G.sup id
      refine ⟨Set.range fun m => lam (2 * Nat.pair K m),
        Set.infinite_range_of_injective (h.injective.comp fun a b e => by
          simpa [Nat.pair_eq_pair] using e), ?_⟩
      rintro _ ⟨_, ⟨m, rfl⟩, g, hg, rfl⟩
      obtain ⟨i, rfl⟩ := hG hg
      refine ⟨K, m, i, ?_, rfl⟩
      have h1 : 2 * i + 1 ≤ lam (2 * i + 1) := hmono.id_le _
      have h2 : lam (2 * i + 1) ≤ K := Finset.le_sup (f := id) hg
      omega
    exact ⟨_, _, hC0, hC0, fun G _ hG => key G hG, fun G _ hG => key G hG⟩
  have hBC : ¬ HasSumset (halfD lam) := by
    rintro ⟨B, C, hB, hC, hBCD⟩
    have hmem : ∀ b ∈ B, ∀ c ∈ C, ∃ k m i, i ≤ k ∧
        b + c = lam (2 * Nat.pair k m) + lam (2 * i + 1) := fun b hb c hc =>
      hBCD ⟨b, hb, c, hc, rfl⟩
    obtain ⟨t, jb, jc, hjb, hjc⟩ := cor_R_nat h hB hC fun b hb c hc => by
      obtain ⟨k, m, i, -, e⟩ := hmem b hb c hc
      exact ⟨_, _, by rw [← Nat.cast_add, e]; push_cast; rfl⟩
    obtain ⟨b1, hb1⟩ := hB.nonempty
    obtain ⟨c1, hc1⟩ := hC.nonempty
    rcases Nat.even_or_odd (jb b1) with ⟨r, hr⟩ | ⟨r, hr⟩
    · -- `b₁ - t` is a `β`-label: then `C + t` lies in `{γ_i : i ≤ k₁}`
      apply hC
      refine finite_of_cast_subset (T := (fun i : ℕ => (lam (2 * i + 1) : ℤ) - t) ''
        Set.Iic (Nat.unpair r).1) ((Set.finite_Iic _).image _) fun c hc => ?_
      obtain ⟨k, m, i, hik, e⟩ := hmem b1 hb1 c hc
      rcases rigid_pair_shift h (hjb b1 hb1) (hjc c hc) e with ⟨e1, e2⟩ | ⟨e1, -⟩
      · have : Nat.pair k m = r := by omega
        refine ⟨i, ?_, ?_⟩
        · rw [← this, Nat.unpair_pair]; exact hik
        · simp only; rw [← e2, ← hjc c hc]; ring
      · omega
    · -- `b₁ - t` is a `γ`-label: then `B - t` lies in `{γ_i : i ≤ k₁}`
      obtain ⟨k1, m1, i1, -, e1⟩ := hmem b1 hb1 c1 hc1
      have hc1β : jc c1 = 2 * Nat.pair k1 m1 := by
        rcases rigid_pair_shift h (hjb b1 hb1) (hjc c1 hc1) e1 with ⟨e, -⟩ | ⟨-, e⟩
        · omega
        · exact e
      apply hB
      refine finite_of_cast_subset (T := (fun i : ℕ => (lam (2 * i + 1) : ℤ) + t) ''
        Set.Iic k1) ((Set.finite_Iic _).image _) fun b hb => ?_
      obtain ⟨k, m, i, hik, e⟩ := hmem b hb c1 hc1
      rcases rigid_pair_shift h (hjb b hb) (hjc c1 hc1) e with ⟨-, e2⟩ | ⟨e1', e2⟩
      · omega
      · have : Nat.pair k m = Nat.pair k1 m1 := by omega
        rw [Nat.pair_eq_pair] at this
        refine ⟨i, by rw [Set.mem_Iic, ← this.1]; exact hik, ?_⟩
        simp only; rw [← e1', ← hjb b hb]; ring
  exact ⟨hN, (ae_indP_iff _ (fun A => ¬ HasSumset A)).2 hBC,
    (ae_indP_iff _ HasAllFinite).1 (condN_imp _ hN), hBC⟩

/-- The set `D = {β_{k,m} + γ_{k,i} : i < k}` of Example \ref{IB:ex:rigid}, with the labels
`β_{k,m} = λ_{2⟨k,m⟩}` and `γ_{k,i} = λ_{2⟨k,i⟩+1}` (the paper's `1 ≤ i ≤ k` becomes `i < k`). -/
def rigidD (lam : ℕ → ℕ) : Set ℕ :=
  {n | ∃ k m i, i < k ∧ n = lam (2 * Nat.pair k m) + lam (2 * Nat.pair k i + 1)}

/-- Paper, Example \ref{IB:ex:rigid}: for `p = 1_D` with `D = {β_{k,m} + γ_{k,i} : i < k}`,
`E_k` holds for every `k` (so `P(E_{<ω}) = 1`) but (N) fails. -/
theorem ex_rigid (h : IsRigidSeq lam) :
    HasAllFinite (rigidD lam) ∧
    (∀ᵐ ω ∂bernoulliSeq (indP (rigidD lam)), HasAllFinite (randSet ω)) ∧
    ¬ CondN (indP (rigidD lam)) := by
  have hinj := h.injective
  have hfin : HasAllFinite (rigidD lam) := by
    intro k
    refine ⟨(Finset.range k).image fun i => lam (2 * Nat.pair k i + 1), ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (show Function.Injective
        (fun i => lam (2 * Nat.pair k i + 1)) from hinj.comp fun a b e => by
        simpa [Nat.pair_eq_pair] using e), Finset.card_range]
    · refine ⟨Set.range fun m => lam (2 * Nat.pair k m),
        Set.infinite_range_of_injective (hinj.comp fun a b e => by
          simpa [Nat.pair_eq_pair] using e), ?_⟩
      rintro _ ⟨_, ⟨m, rfl⟩, _, hg, rfl⟩
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hg
      obtain ⟨i, hi, rfl⟩ := hg
      exact ⟨k, m, i, hi, rfl⟩
  refine ⟨hfin, (ae_indP_iff _ HasAllFinite).2 hfin, ?_⟩
  rintro ⟨-, C0, -, hC, -, hG⟩
  have hEF : ∀ G : Finset ℕ, G.Nonempty → ↑G ⊆ C0 →
      {n | ∀ g ∈ G, n + g ∈ rigidD lam}.Infinite := fun G hne hG' =>
    (EF_iff_infinite G _).1 ((SF_indP_eq_top_iff _ G).1 (hG G hne hG'))
  have hLL : ∀ n ∈ rigidD lam, InLL lam (n : ℤ) := by
    rintro n ⟨k, m, i, -, rfl⟩
    exact ⟨_, _, by push_cast; rfl⟩
  obtain ⟨c1, hc1, c2, hc2, hc12⟩ := hC.nontrivial
  set Γ := {n | ∀ g ∈ ({c1, c2} : Finset ℕ), n + g ∈ rigidD lam}
  have hΓ : Γ.Infinite := hEF {c1, c2} (by simp) (by simp [Set.insert_subset_iff, hc1, hc2])
  set X : Set ℤ := {(c1 : ℤ), (c2 : ℤ)}
  have hX : ∃ x1 ∈ X, ∃ x2 ∈ X, x1 ≠ x2 :=
    ⟨c1, by simp [X], c2, by simp [X], by exact_mod_cast hc12⟩
  obtain ⟨t, ht, -⟩ := lem_R h hX (infinite_image_cast hΓ).nontrivial (by
    rintro x hx _ ⟨n, hn, rfl⟩
    rcases hx with rfl | rfl
    · rw [add_comm]; exact_mod_cast hLL _ (hn c1 (by simp))
    · rw [add_comm]; exact_mod_cast hLL _ (hn c2 (by simp)))
  obtain ⟨j1, hj1⟩ := ht.1 c1 (by simp [X])
  have hl : ∀ n : ℕ, ∃ l, n ∈ Γ → (n : ℤ) + t = lam l := fun n => by
    by_cases hn : n ∈ Γ
    · obtain ⟨l, hl⟩ := ht.2.1 _ ⟨n, hn, rfl⟩; exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose l hl using hl
  -- `c₁ - t` is a `γ`-label `γ_{K,i}`, and every `n + t` (`n ∈ Γ`) a `β`-label `β_{K,m}`
  obtain ⟨K, hK⟩ : ∃ K, ∀ n ∈ Γ, ∃ m, l n = 2 * Nat.pair K m := by
    rcases Nat.even_or_odd j1 with ⟨r, hr⟩ | ⟨r, hr⟩
    · exfalso
      apply hΓ
      refine finite_of_cast_subset (T := (fun i : ℕ => (lam (2 * Nat.pair (Nat.unpair r).1 i + 1)
        : ℤ) - t) '' Set.Iio (Nat.unpair r).1) ((Set.finite_Iio _).image _) fun n hn => ?_
      obtain ⟨k, m, i, hik, e⟩ := hn c1 (by simp)
      rw [add_comm] at e
      rcases rigid_pair_shift h hj1 (hl n hn) e with ⟨e1, e2⟩ | ⟨e1, -⟩
      · have : Nat.pair k m = r := by omega
        refine ⟨i, ?_, ?_⟩
        · rw [← this, Nat.unpair_pair]; exact hik
        · simp only; rw [← this, Nat.unpair_pair, ← e2, ← hl n hn]; ring
      · omega
    · refine ⟨(Nat.unpair r).1, fun n hn => ?_⟩
      obtain ⟨k, m, i, -, e⟩ := hn c1 (by simp)
      rw [add_comm] at e
      rcases rigid_pair_shift h hj1 (hl n hn) e with ⟨e1, -⟩ | ⟨e1, e2⟩
      · omega
      · have : Nat.pair k i = r := by omega
        exact ⟨m, by rw [e2, ← this, Nat.unpair_pair]⟩
  -- every `c ∈ C₀` satisfies `c - t ∈ {γ_{K,i} : i < K}`
  apply hC
  refine finite_of_cast_subset (T := (fun i : ℕ => (lam (2 * Nat.pair K i + 1) : ℤ) + t) ''
    Set.Iio K) ((Set.finite_Iio _).image _) fun c hc => ?_
  set Γc := {n | ∀ g ∈ ({c1, c2, c} : Finset ℕ), n + g ∈ rigidD lam}
  have hΓc : Γc.Infinite := hEF {c1, c2, c} (by simp)
    (by simp [Set.insert_subset_iff, hc1, hc2, hc])
  have hΓcΓ : Γc ⊆ Γ := fun n hn g hg => hn g (by simp at hg ⊢; tauto)
  obtain ⟨tc, htc, -⟩ := lem_R h (X := {(c1 : ℤ), (c2 : ℤ), (c : ℤ)})
    ⟨c1, by simp, c2, by simp, by exact_mod_cast hc12⟩ (infinite_image_cast hΓc).nontrivial (by
      rintro x hx _ ⟨n, hn, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx <;> rw [hx, add_comm] <;>
        exact_mod_cast hLL _ (hn _ (by simp)))
  obtain ⟨n1, hn1, n2, hn2, hn12⟩ := hΓc.nontrivial
  have htt : t = tc := shift_unique h (c1 := n1) (c2 := n2) (by exact_mod_cast hn12)
    (ht.1 c1 (by simp [X])) (htc.1 c1 (by simp)) ⟨_, hl n1 (hΓcΓ hn1)⟩
    (htc.2.1 _ ⟨n1, hn1, rfl⟩) ⟨_, hl n2 (hΓcΓ hn2)⟩ (htc.2.1 _ ⟨n2, hn2, rfl⟩)
  obtain ⟨jc, hjc⟩ := htc.1 c (by simp)
  rw [← htt] at hjc
  obtain ⟨k, m, i, hik, e⟩ := hn1 c (by simp)
  rw [add_comm] at e
  obtain ⟨m1, hm1⟩ := hK n1 (hΓcΓ hn1)
  rcases rigid_pair_shift h hjc (hl n1 (hΓcΓ hn1)) e with ⟨-, e2⟩ | ⟨e1, e2⟩
  · omega
  · have : Nat.pair K m1 = Nat.pair k m := by omega
    rw [Nat.pair_eq_pair] at this
    refine ⟨i, by rw [Set.mem_Iio, this.1]; exact hik, ?_⟩
    simp only; rw [this.1, ← e1, ← hjc]; ring

end Examples

/-! ## Example \ref{IB:ex:tree} -/

/-- Comparability of finite sequences: one is an initial segment of the other. -/
def Comp {α : Type*} (a b : List α) : Prop := a <+: b ∨ b <+: a

lemma Comp.symm {α : Type*} {a b : List α} (h : Comp a b) : Comp b a := Or.symm h

/-- `θ_j = 1/(j+1)`, as an element of `[0, 1]`. -/
noncomputable def thetaI (j : ℕ) : I :=
  ⟨((j : ℝ) + 1)⁻¹, by positivity, inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])⟩

/-- `θ_j = 1/(j+1)` in `[0, ∞]`. -/
noncomputable def θE (j : ℕ) : ℝ≥0∞ := ((j : ℝ≥0∞) + 1)⁻¹

lemma coe_thetaI (j : ℕ) : ((toNNReal (thetaI j) : NNReal) : ℝ≥0∞) = θE j := by
  have : toNNReal (thetaI j) = ((j : NNReal) + 1)⁻¹ := by
    ext
    simp only [toNNReal, thetaI, NNReal.coe_inv, NNReal.coe_add,
      NNReal.coe_natCast, NNReal.coe_one]
    rfl
  rw [this, ENNReal.coe_inv (by positivity), θE]
  push_cast
  rfl

lemma θE_anti {i j : ℕ} (h : i ≤ j) : θE j ≤ θE i := by
  unfold θE
  exact ENNReal.inv_le_inv.2 (by gcongr)

lemma θE_ne_zero (j : ℕ) : θE j ≠ 0 := by simp [θE]

/-- `∑_j θ_j² < ∞`. -/
lemma tsum_θE_sq_ne_top : ∑' j, θE j ^ 2 ≠ ∞ := by
  have e : ∀ j : ℕ, θE j ^ 2 = ENNReal.ofReal (((j : ℝ) + 1) ^ 2)⁻¹ := by
    intro j
    rw [ENNReal.ofReal_inv_of_pos (by positivity), θE, ← ENNReal.inv_pow]
    congr 1
    rw [ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]
    simp
  simp only [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)]
  · exact ENNReal.ofReal_ne_top
  · have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 (by norm_num : 1 < 2))
    simpa using this

/-- For every `M`, `M (d + j + 1)^k ≤ 2^j` for some `j`. -/
lemma exists_two_pow_ge (M d k : ℕ) : ∃ j, M * (d + j + 1) ^ k ≤ 2 ^ j := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (r := 2) one_lt_two
  have hpos : (0 : ℝ) < ((M : ℝ) * 2 ^ (d + 1) + 1)⁻¹ := by positivity
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
  refine ⟨N + 1, ?_⟩
  have h1 := hN (d + N + 2) (by omega)
  rw [div_lt_iff₀ (by positivity), inv_mul_eq_div, lt_div_iff₀ (by positivity)] at h1
  set a : ℝ := 2 ^ (d + 1)
  set X : ℝ := ((d + N + 2 : ℕ) : ℝ) ^ k
  have ha : 0 < a := by positivity
  have hX : 0 ≤ X := by positivity
  have e : (2 : ℝ) ^ (d + N + 2) = 2 ^ (N + 1) * a := by rw [← pow_add]; ring_nf
  rw [e] at h1
  have h2 : (M : ℝ) * X * a < 2 ^ (N + 1) * a := by nlinarith
  have h3 : (M : ℝ) * X < 2 ^ (N + 1) := lt_of_mul_lt_mul_right h2 ha.le
  have h4 : ((M * (d + (N + 1) + 1) ^ k : ℕ) : ℝ) = (M : ℝ) * X := by
    simp only [X]; push_cast; ring_nf
  exact_mod_cast (h4 ▸ h3).le

/-- `∑_{η} θ_{d + |η|}^k = ∞`, the sum over all finite binary sequences `η`. -/
lemma tsum_θE_tree_eq_top (d k : ℕ) : ∑' η : List Bool, θE (d + η.length) ^ k = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨M, hM⟩ := exists_nat_gt (r : ℝ)
  obtain ⟨j, hj⟩ := exists_two_pow_ge M d k
  have h1 : ∑' v : List.Vector Bool j, θE (d + v.1.length) ^ k ≤
      ∑' η : List Bool, θE (d + η.length) ^ k :=
    ENNReal.tsum_comp_le_tsum_of_injective (f := fun v : List.Vector Bool j => v.1)
      (fun a b hab => Subtype.ext hab) (fun η : List Bool => θE (d + η.length) ^ k)
  refine le_trans ?_ h1
  have h2 : ∑' v : List.Vector Bool j, θE (d + v.1.length) ^ k = (2 ^ j : ℕ) * θE (d + j) ^ k := by
    have e : ∀ v : List.Vector Bool j, θE (d + v.1.length) ^ k = θE (d + j) ^ k := fun v => by
      rw [v.2]
    rw [tsum_congr e, tsum_fintype, Finset.sum_const, Finset.card_univ, card_vector,
      Fintype.card_bool, nsmul_eq_mul]
  rw [h2]
  have h3 : ((M : ℕ) : ℝ≥0∞) ≤ ((2 ^ j : ℕ) : ℝ≥0∞) * θE (d + j) ^ k := by
    rw [θE, ← ENNReal.inv_pow, ← div_eq_mul_inv,
      ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
    have : ((M * (d + j + 1) ^ k : ℕ) : ℝ≥0∞) ≤ ((2 ^ j : ℕ) : ℝ≥0∞) := by exact_mod_cast hj
    simpa using this
  refine le_trans ?_ h3
  have : (r : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hM.le
  exact this

section Tree

variable {lam : ℕ → ℕ}

/-- The label `β_a = λ_{2 ⌜a⌝}` of a node `a` of the binary tree (`⌜a⌝` an injective coding). -/
def tβ (lam : ℕ → ℕ) (a : List Bool) : ℕ := lam (2 * Encodable.encode a)

/-- The label `γ_a = λ_{2 ⌜a⌝ + 1}`. -/
def tγ (lam : ℕ → ℕ) (a : List Bool) : ℕ := lam (2 * Encodable.encode a + 1)

lemma tβ_injective (h : IsRigidSeq lam) : Function.Injective (tβ lam) := fun a b e =>
  Encodable.encode_injective (by have := h.injective e; omega)

lemma tγ_injective (h : IsRigidSeq lam) : Function.Injective (tγ lam) := fun a b e =>
  Encodable.encode_injective (by have := h.injective e; omega)

lemma tree_rep_unique (h : IsRigidSeq lam) {a b a' b' : List Bool}
    (e : tβ lam a + tγ lam b = tβ lam a' + tγ lam b') : a = a' ∧ b = b' := by
  rcases lem_rigid_pair h e with ⟨e1, e2⟩ | ⟨e1, -⟩
  · exact ⟨Encodable.encode_injective (by omega), Encodable.encode_injective (by omega)⟩
  · omega

open Classical in
/-- The sequence of Example \ref{IB:ex:tree}: `p_{β_a + γ_b} = θ_{max(|a|, |b|)}` for comparable
nodes `a, b` of the binary tree `{0,1}^{<ℕ}`, and `p_n = 0` otherwise. -/
noncomputable def treeP (lam : ℕ → ℕ) (n : ℕ) : I :=
  if hn : ∃ q : List Bool × List Bool, Comp q.1 q.2 ∧ n = tβ lam q.1 + tγ lam q.2 then
    thetaI (max hn.choose.1.length hn.choose.2.length) else 0

lemma pe_treeP_of_comp (h : IsRigidSeq lam) {a b : List Bool} (hab : Comp a b) :
    pe (treeP lam) (tβ lam a + tγ lam b) = θE (max a.length b.length) := by
  have hn : ∃ q : List Bool × List Bool, Comp q.1 q.2 ∧
      tβ lam a + tγ lam b = tβ lam q.1 + tγ lam q.2 := ⟨(a, b), hab, rfl⟩
  have hq := tree_rep_unique h hn.choose_spec.2
  unfold pe treeP
  rw [dif_pos hn, ← hq.1, ← hq.2]
  exact coe_thetaI _

lemma pe_treeP_of_not_comp (h : IsRigidSeq lam) {a b : List Bool} (hab : ¬ Comp a b) :
    pe (treeP lam) (tβ lam a + tγ lam b) = 0 := by
  have hn : ¬ ∃ q : List Bool × List Bool, Comp q.1 q.2 ∧
      tβ lam a + tγ lam b = tβ lam q.1 + tγ lam q.2 := by
    rintro ⟨q, hq, e⟩
    obtain ⟨rfl, rfl⟩ := tree_rep_unique h e
    exact hab hq
  unfold pe treeP
  rw [dif_neg hn]
  exact ENNReal.coe_zero

lemma pe_treeP_supp {n : ℕ} (hn : pe (treeP lam) n ≠ 0) :
    ∃ a b, Comp a b ∧ n = tβ lam a + tγ lam b := by
  by_contra hc
  apply hn
  unfold pe treeP
  rw [dif_neg (by rintro ⟨q, hq, e⟩; exact hc ⟨q.1, q.2, hq, e⟩)]
  exact ENNReal.coe_zero

lemma pe_treeP_le (h : IsRigidSeq lam) (a b : List Bool) :
    pe (treeP lam) (tβ lam a + tγ lam b) ≤ θE a.length ∧
      pe (treeP lam) (tβ lam a + tγ lam b) ≤ θE b.length := by
  by_cases hab : Comp a b
  · rw [pe_treeP_of_comp h hab]
    exact ⟨θE_anti (le_max_left _ _), θE_anti (le_max_right _ _)⟩
  · rw [pe_treeP_of_not_comp h hab]
    exact ⟨zero_le, zero_le⟩

/-- A finite set of nodes that is a chain. -/
def IsChain (R : Finset (List Bool)) : Prop := ∀ a ∈ R, ∀ b ∈ R, Comp a b

lemma chain_ub {R : Finset (List Bool)} (hR : IsChain R) : ∃ δ, ∀ a ∈ R, a <+: δ := by
  rcases R.eq_empty_or_nonempty with rfl | hne
  · exact ⟨[], by simp⟩
  · obtain ⟨δ, hδ, hmax⟩ := R.exists_max_image List.length hne
    refine ⟨δ, fun a ha => ?_⟩
    rcases hR a ha δ hδ with h1 | h1
    · exact h1
    · rw [h1.eq_of_length_le (hmax a ha)]

/-- The strategy of Example \ref{IB:ex:tree}: the pairs `({β_a}_{a ∈ P}, {γ_b}_{b ∈ Q})` with
`P ∪ Q` a finite chain. -/
def treeS (lam : ℕ → ℕ) : Set (Finset ℕ × Finset ℕ) :=
  {q | ∃ P Q : Finset (List Bool), q.1 = P.image (tβ lam) ∧ q.2 = Q.image (tγ lam) ∧
    IsChain (P ∪ Q)}

lemma chain_insert {P Q : Finset (List Bool)} (hc : IsChain (P ∪ Q)) {δ c : List Bool}
    (hδ : ∀ a ∈ P ∪ Q, a <+: δ) (hc' : δ <+: c) : IsChain (insert c (P ∪ Q)) := by
  intro a ha b hb
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact Or.inl (List.prefix_refl _)
  · exact Or.inr ((hδ b hb).trans hc')
  · exact Or.inl ((hδ a ha).trans hc')
  · exact hc a ha b hb

/-- `P(E_{BC}) = 1` in Example \ref{IB:ex:tree}: `treeS` is a `BC`-strategy for `treeP`. -/
theorem treeS_strategy (h : IsRigidSeq lam) : IsBCStrategy (treeP lam) (treeS lam) := by
  classical
  refine ⟨⟨∅, ∅, by simp, by simp, by simp [IsChain]⟩, ?_⟩
  rintro U V ⟨P, Q, rfl, rfl, hPQ⟩
  obtain ⟨δ, hδ⟩ := chain_ub hPQ
  set g : List Bool → List Bool := fun η => δ ++ false :: η
  have hg : Function.Injective g := fun a b e => by simpa [g] using e
  have hlen : ∀ η, (g η).length = (δ.length + 1) + η.length := fun η => by
    simp [g]; ring
  have hpre : ∀ η, δ <+: g η := fun η => List.prefix_append _ _
  have hlt : ∀ η, ∀ a ∈ P ∪ Q, a <+: g η ∧ a.length < (g η).length := fun η a ha =>
    ⟨(hδ a ha).trans (hpre η), by have := (hδ a ha).length_le; rw [hlen]; omega⟩
  have hnotin : ∀ η, g η ∉ P ∪ Q := fun η hm => by
    have := (hlt η _ hm).2; omega
  refine ⟨?_, ?_⟩
  · -- condition (a): new elements `γ_c` with `c` below the chain
    have key : ∀ η, θE ((δ.length + 1) + η.length) ^ P.card ≤
        (Xs (treeS lam) (P.image (tβ lam)) (Q.image (tγ lam))).indicator
          (w (treeP lam) (P.image (tβ lam))) (tγ lam (g η)) := by
      intro η
      rw [Set.indicator_of_mem]
      · rw [w_eq, Finset.prod_image fun a _ b _ e => tβ_injective h e]
        rw [← hlen, ← Finset.prod_const]
        refine le_of_eq (Finset.prod_congr rfl fun a ha => ?_)
        rw [add_comm, pe_treeP_of_comp h (Or.inl (hlt η a (Finset.mem_union_left _ ha)).1),
          max_eq_right (hlt η a (Finset.mem_union_left _ ha)).2.le]
      · refine ⟨fun hm => ?_, P, insert (g η) Q, rfl, by rw [Finset.image_insert], ?_⟩
        · obtain ⟨c, hc, e⟩ := Finset.mem_image.1 hm
          exact hnotin η (Finset.mem_union_right _ (tγ_injective h e ▸ hc))
        · rw [Finset.union_insert]; exact chain_insert hPQ hδ (hpre η)
    refine top_le_iff.1 ?_
    rw [← tsum_θE_tree_eq_top (δ.length + 1) P.card]
    exact (ENNReal.tsum_le_tsum key).trans
      (ENNReal.tsum_comp_le_tsum_of_injective ((tγ_injective h).comp hg) _)
  · -- condition (b): new elements `β_c`
    have key : ∀ η, θE ((δ.length + 1) + η.length) ^ Q.card ≤
        (Ys (treeS lam) (P.image (tβ lam)) (Q.image (tγ lam))).indicator
          (w (treeP lam) (Q.image (tγ lam))) (tβ lam (g η)) := by
      intro η
      rw [Set.indicator_of_mem]
      · rw [w_eq, Finset.prod_image fun a _ b _ e => tγ_injective h e]
        rw [← hlen, ← Finset.prod_const]
        refine le_of_eq (Finset.prod_congr rfl fun a ha => ?_)
        rw [pe_treeP_of_comp h (Or.inr (hlt η a (Finset.mem_union_right _ ha)).1),
          max_eq_left (hlt η a (Finset.mem_union_right _ ha)).2.le]
      · refine ⟨fun hm => ?_, insert (g η) P, Q, by rw [Finset.image_insert], rfl, ?_⟩
        · obtain ⟨c, hc, e⟩ := Finset.mem_image.1 hm
          exact hnotin η (Finset.mem_union_left _ (tβ_injective h e ▸ hc))
        · rw [Finset.insert_union]; exact chain_insert hPQ hδ (hpre η)
    refine top_le_iff.1 ?_
    rw [← tsum_θE_tree_eq_top (δ.length + 1) Q.card]
    exact (ENNReal.tsum_le_tsum key).trans
      (ENNReal.tsum_comp_le_tsum_of_injective ((tβ_injective h).comp hg) _)

end Tree

lemma w_ne_zero_iff {p : ℕ → I} {U : Finset ℕ} {x : ℕ} :
    w p U x ≠ 0 ↔ ∀ u ∈ U, pe p (x + u) ≠ 0 := by
  rw [w_eq, Finset.prod_ne_zero_iff]

lemma w_singleton (p : ℕ → I) (c x : ℕ) : w p {c} x = pe p (x + c) := by
  rw [w_eq, Finset.prod_singleton]

/-- If `∑_{c ∈ C} w_U(c) = ∞`, then infinitely many `c ∈ C` have `w_U(c) ≠ 0`. -/
lemma infinite_of_wsum_eq_top {p : ℕ → I} {U : Finset ℕ} {C : Set ℕ} (h : wsum p U C = ∞) :
    {c | c ∈ C ∧ w p U c ≠ 0}.Infinite := by
  intro hfin
  apply (show wsum p U C ≠ ∞ from ?_) h
  have e : wsum p U C = ∑' c, {c | c ∈ C ∧ w p U c ≠ 0}.indicator (w p U) c := by
    refine tsum_congr fun c => ?_
    by_cases hc : c ∈ C
    · by_cases hw : w p U c = 0
      · simp [hc, hw]
      · simp [hc, hw]
    · simp [hc]
  rw [e, ← tsum_subtype]
  have : Fintype {c | c ∈ C ∧ w p U c ≠ 0} := hfin.fintype
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun c _ => ne_top_of_le_ne_top ENNReal.one_ne_top (w_le_one p U c)

section TreeF

variable {lam : ℕ → ℕ}

/-- The core of the proof that (F) fails in Example \ref{IB:ex:tree}, for an abstract assignment of
the two label types `βs`, `γs` (used once as given and once with the roles exchanged). -/
lemma tree_core (h : IsRigidSeq lam) (βs γs : List Bool → ℕ) (hβ : Function.Injective βs)
    (hγ : Function.Injective γs) (hd : ∀ a b, βs a ≠ γs b) (p : ℕ → I)
    (hsupp : ∀ n, pe p n ≠ 0 → ∃ a b, Comp a b ∧ n = lam (βs a) + lam (γs b))
    (hval : ∀ a b, pe p (lam (βs a) + lam (γs b)) ≤ θE b.length)
    {B0 C0 : Set ℕ} (hB0 : B0.Infinite)
    (hU : ∀ U : Finset ℕ, ↑U ⊆ B0 → wsum p U C0 = ∞)
    (hV : ∀ V : Finset ℕ, ↑V ⊆ C0 → wsum p V B0 = ∞)
    (t : ℤ) (hB : ∀ b ∈ B0, ∃ a, (b : ℤ) - t = lam (βs a)) : False := by
  choose! σb hσb using hB
  have hσinj : ∀ b ∈ B0, ∀ b' ∈ B0, σb b = σb b' → b = b' := by
    intro b hb b' hb' e
    have h1 := hσb b hb
    have h2 := hσb b' hb'
    rw [e] at h1
    exact_mod_cast (by linarith : (b : ℤ) = b')
  -- (i) `C₀ + t` consists of `γ`-labels
  have hC : ∀ c ∈ C0, ∃ y, (c : ℤ) + t = lam (γs y) := by
    intro c hc
    have hinf := infinite_of_wsum_eq_top (hV {c} (by simpa using hc))
    obtain ⟨b, ⟨hb, hb0⟩, b', ⟨hb', hb0'⟩, hne⟩ := hinf.nontrivial
    rw [w_singleton] at hb0 hb0'
    obtain ⟨a1, c1, -, e1⟩ := hsupp _ hb0
    obtain ⟨a2, c2, -, e2⟩ := hsupp _ hb0'
    have hs1 := hσb b hb
    have hs2 := hσb b' hb'
    have hne' : σb b ≠ σb b' := fun e => hne (hσinj b hb b' hb' e)
    have hrel : (({βs a1, γs c1, βs (σb b')} : Multiset ℕ).map lam).sum =
        (({βs a2, γs c2, βs (σb b)} : Multiset ℕ).map lam).sum := by
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton]
      have e1' : ((b + c : ℕ) : ℤ) = lam (βs a1) + lam (γs c1) := by rw [e1]; push_cast; rfl
      have e2' : ((b' + c : ℕ) : ℤ) = lam (βs a2) + lam (γs c2) := by rw [e2]; push_cast; rfl
      push_cast at e1' e2'
      have h' : ((lam (βs a1) + (lam (γs c1) + lam (βs (σb b'))) : ℕ) : ℤ) =
          ((lam (βs a2) + (lam (γs c2) + lam (βs (σb b))) : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast h'
    have hms := rigid_ms h (by simp) hrel
    have hmem : γs c1 ∈ ({βs a2, γs c2, βs (σb b)} : Multiset ℕ) := hms ▸ by simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
    rcases hmem with hm | hm | hm
    · exact absurd hm.symm (hd _ _)
    · have e1' : ((b + c : ℕ) : ℤ) = lam (βs a1) + lam (γs c1) := by rw [e1]; push_cast; rfl
      have e2' : ((b' + c : ℕ) : ℤ) = lam (βs a2) + lam (γs c2) := by rw [e2]; push_cast; rfl
      push_cast at e1' e2'
      rw [← hm] at e2'
      rcases rigid_pair_int h (a := βs a1) (b := βs (σb b')) (c := βs a2) (d := βs (σb b))
        (by linarith) with ⟨-, e⟩ | ⟨e, -⟩
      · exact absurd (hβ e).symm hne'
      · exact ⟨c1, by rw [e] at e1'; linarith⟩
    · exact absurd hm.symm (hd _ _)
  choose! τc hτc using hC
  have hsum : ∀ b ∈ B0, ∀ c ∈ C0, b + c = lam (βs (σb b)) + lam (γs (τc c)) := by
    intro b hb c hc
    have h1 := hσb b hb
    have h2 := hτc c hc
    have : ((b + c : ℕ) : ℤ) = ((lam (βs (σb b)) + lam (γs (τc c)) : ℕ) : ℤ) := by
      push_cast; linarith
    exact_mod_cast this
  -- (ii) support means comparability
  have hcomp : ∀ b ∈ B0, ∀ c ∈ C0, pe p (b + c) ≠ 0 → Comp (σb b) (τc c) := by
    intro b hb c hc hne
    obtain ⟨a, a', hc', e⟩ := hsupp _ hne
    rw [hsum b hb c hc] at e
    rcases lem_rigid_pair h e with ⟨e1, e2⟩ | ⟨e1, -⟩
    · rw [hβ e1, hγ e2]; exact hc'
    · exact absurd e1 (hd _ _)
  -- (iii) the `γ`-labels of `C₀` form a chain
  have hchain : ∀ c ∈ C0, ∀ c' ∈ C0, Comp (τc c) (τc c') := by
    intro c hc c' hc'
    by_contra hnc
    have hcc : c ≠ c' := by rintro rfl; exact hnc (Or.inl (List.prefix_refl _))
    have hinf := infinite_of_wsum_eq_top (hV {c, c'} (by simp [Set.insert_subset_iff, hc, hc']))
    have hmaps : Set.MapsTo σb {b | b ∈ B0 ∧ w p {c, c'} b ≠ 0} {a | a ∈ (τc c).inits} := by
      rintro b ⟨hb, hw⟩
      rw [w_ne_zero_iff] at hw
      have h1 := hcomp b hb c hc (hw c (by simp))
      have h2 := hcomp b hb c' hc' (hw c' (by simp))
      show σb b ∈ (τc c).inits
      rw [List.mem_inits]
      rcases h1 with h1 | h1
      · exact h1
      · rcases h2 with h2 | h2
        · exact absurd (Or.inl (h1.trans h2)) hnc
        · exact absurd (List.prefix_or_prefix_of_prefix h1 h2) hnc
    obtain ⟨b, hb, b', hb', hne, he⟩ :=
      hinf.exists_ne_map_eq_of_mapsTo hmaps (List.finite_toSet _)
    exact hne (hσinj b hb.1 b' hb'.1 he)
  -- (iv) then `∑_{c ∈ C₀} w_{\{b₁, b₂\}}(c) < ∞`
  obtain ⟨b1, hb1, b2, hb2, hb12⟩ := hB0.nontrivial
  have hU2 := hU {b1, b2} (by simp [Set.insert_subset_iff, hb1, hb2])
  apply (show wsum p {b1, b2} C0 ≠ ∞ from ?_) hU2
  have hle : ∀ c ∈ C0, w p {b1, b2} c ≤ θE (τc c).length ^ 2 := by
    intro c hc
    rw [w_eq, Finset.prod_pair hb12, sq, add_comm c, add_comm c, hsum b1 hb1 c hc,
      hsum b2 hb2 c hc]
    exact mul_le_mul' (hval _ _) (hval _ _)
  have hinj : Function.Injective fun c : C0 => (τc c).length := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ e
    simp only at e
    have heq : τc c = τc c' := by
      rcases hchain c hc c' hc' with h1 | h1
      · exact h1.eq_of_length_le e.ge
      · exact (h1.eq_of_length_le e.le).symm
    have h1 := hτc c hc
    have h2 := hτc c' hc'
    rw [heq] at h1
    exact Subtype.ext (by exact_mod_cast (by linarith : (c : ℤ) = c'))
  have hb : wsum p {b1, b2} C0 ≤ ∑' j, θE j ^ 2 := by
    calc wsum p {b1, b2} C0 = ∑' c : C0, w p {b1, b2} c := by rw [wsum, tsum_subtype]
      _ ≤ ∑' c : C0, θE (τc c).length ^ 2 := ENNReal.tsum_le_tsum fun c => hle c c.2
      _ ≤ ∑' j, θE j ^ 2 := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun j => θE j ^ 2)
  exact ne_top_of_le_ne_top tsum_θE_sq_ne_top hb

/-- (F) fails in Example \ref{IB:ex:tree}. -/
theorem treeP_not_condF (h : IsRigidSeq lam) : ¬ CondF (treeP lam) := by
  rintro ⟨B0, C0, hB0, -, hU, hV⟩
  obtain ⟨b1, hb1, b2, hb2, hb12⟩ := hB0.nontrivial
  have hLL : ∀ n, pe (treeP lam) n ≠ 0 → InLL lam (n : ℤ) := by
    intro n hn
    obtain ⟨a, b, -, rfl⟩ := pe_treeP_supp hn
    exact ⟨2 * Encodable.encode a, 2 * Encodable.encode b + 1, by simp [tβ, tγ]⟩
  set Γ := {c | c ∈ C0 ∧ w (treeP lam) {b1, b2} c ≠ 0}
  have hΓ : Γ.Infinite :=
    infinite_of_wsum_eq_top (hU _ (by simp [Set.insert_subset_iff, hb1, hb2]))
  obtain ⟨t, ht, -⟩ := lem_R h (X := {(b1 : ℤ), (b2 : ℤ)})
    ⟨b1, by simp, b2, by simp, by exact_mod_cast hb12⟩ (infinite_image_cast hΓ).nontrivial (by
      rintro x hx _ ⟨c, hc, rfl⟩
      have hw := w_ne_zero_iff.1 hc.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · have := hLL _ (hw b1 (by simp)); rw [add_comm]; exact_mod_cast this
      · have := hLL _ (hw b2 (by simp)); rw [add_comm]; exact_mod_cast this)
  -- every `b ∈ B₀` has `b - t ∈ Λ`, witnessed against some `c ∈ Γ`
  have hBt : ∀ b ∈ B0, ∃ j, (b : ℤ) - t = lam j ∧ ∃ c ∈ Γ, pe (treeP lam) (b + c) ≠ 0 := by
    intro b hb
    set Γb := {c | c ∈ C0 ∧ w (treeP lam) {b1, b2, b} c ≠ 0}
    have hΓb : Γb.Infinite :=
      infinite_of_wsum_eq_top (hU _ (by simp [Set.insert_subset_iff, hb1, hb2, hb]))
    have hΓbΓ : Γb ⊆ Γ := fun c hc => ⟨hc.1, w_ne_zero_iff.2 fun u hu =>
      w_ne_zero_iff.1 hc.2 u (by simp at hu ⊢; tauto)⟩
    obtain ⟨tb, htb, -⟩ := lem_R h (X := {(b1 : ℤ), (b2 : ℤ), (b : ℤ)})
      ⟨b1, by simp, b2, by simp, by exact_mod_cast hb12⟩ (infinite_image_cast hΓb).nontrivial (by
        rintro x hx _ ⟨c, hc, rfl⟩
        have hw := w_ne_zero_iff.1 hc.2
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx | hx <;> rw [hx, add_comm] <;>
          exact_mod_cast hLL _ (hw _ (by simp)))
    obtain ⟨n1, hn1, n2, hn2, hn12⟩ := hΓb.nontrivial
    have htt : t = tb := shift_unique h (c1 := n1) (c2 := n2) (by exact_mod_cast hn12)
      (ht.1 b1 (by simp)) (htb.1 b1 (by simp)) (ht.2.1 _ ⟨n1, hΓbΓ hn1, rfl⟩)
      (htb.2.1 _ ⟨n1, hn1, rfl⟩) (ht.2.1 _ ⟨n2, hΓbΓ hn2, rfl⟩) (htb.2.1 _ ⟨n2, hn2, rfl⟩)
    obtain ⟨j, hj⟩ := htb.1 b (by simp)
    refine ⟨j, by rw [htt]; exact hj, n1, hΓbΓ hn1, ?_⟩
    rw [add_comm]; exact w_ne_zero_iff.1 hn1.2 b (by simp)
  choose! jb hjb hcb using hBt
  -- the parity of the index of `b - t` is the opposite of that of `c + t`
  have hpar : ∀ b ∈ B0, ∀ c ∈ Γ, pe (treeP lam) (b + c) ≠ 0 → ∀ jc, (c : ℤ) + t = lam jc →
      (∃ x : List Bool, jb b = 2 * Encodable.encode x ∧
        ∃ y : List Bool, jc = 2 * Encodable.encode y + 1) ∨
      (∃ y : List Bool, jb b = 2 * Encodable.encode y + 1 ∧
        ∃ x : List Bool, jc = 2 * Encodable.encode x) := by
    intro b hb c _ hne jc hjc
    obtain ⟨x, y, -, e⟩ := pe_treeP_supp hne
    rcases rigid_pair_shift h (hjb b hb) hjc e with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨x, e1, y, e2⟩
    · exact Or.inr ⟨y, e1, x, e2⟩
  have hb1c : ∀ c ∈ Γ, pe (treeP lam) (b1 + c) ≠ 0 := fun c hc => by
    rw [add_comm]; exact w_ne_zero_iff.1 hc.2 b1 (by simp)
  have hjc : ∀ c ∈ Γ, ∃ jc, (c : ℤ) + t = lam jc := fun c hc => ht.2.1 _ ⟨c, hc, rfl⟩
  rcases Nat.even_or_odd (jb b1) with hev | hod
  · -- `B₀ - t` consists of `β`-labels
    refine tree_core h (fun a => 2 * Encodable.encode a) (fun a => 2 * Encodable.encode a + 1)
      (fun a b e => by simpa using e) (fun a b e => by simpa using e)
      (fun a b => by omega) (treeP lam) (fun n hn => pe_treeP_supp hn)
      (fun a b => (pe_treeP_le h a b).2) hB0 hU hV t fun b hb => ?_
    obtain ⟨c, hc, hne⟩ := hcb b hb
    obtain ⟨jc, hjc'⟩ := hjc c hc
    rcases hpar b hb c hc hne jc hjc' with ⟨x, hx, -⟩ | ⟨y, hy, x, hx⟩
    · exact ⟨x, by rw [hjb b hb, hx]⟩
    · exfalso
      rcases hpar b1 hb1 c hc (hb1c c hc) jc hjc' with ⟨-, -, y', hy'⟩ | ⟨y', hy', -⟩
      · omega
      · obtain ⟨r, hr⟩ := hev; omega
  · -- `B₀ - t` consists of `γ`-labels: exchange the roles of `β` and `γ`
    refine tree_core h (fun a => 2 * Encodable.encode a + 1) (fun a => 2 * Encodable.encode a)
      (fun a b e => by simpa using e) (fun a b e => by simpa using e)
      (fun a b => by omega) (treeP lam) (fun n hn => ?_)
      (fun a b => by rw [add_comm]; exact (pe_treeP_le h b a).1) hB0 hU hV t fun b hb => ?_
    · obtain ⟨a, b, hab, rfl⟩ := pe_treeP_supp hn
      exact ⟨b, a, hab.symm, by simp only [tβ, tγ]; ring⟩
    · obtain ⟨c, hc, hne⟩ := hcb b hb
      obtain ⟨jc, hjc'⟩ := hjc c hc
      rcases hpar b hb c hc hne jc hjc' with ⟨x, hx, y, hy⟩ | ⟨y, hy, -⟩
      · exfalso
        rcases hpar b1 hb1 c hc (hb1c c hc) jc hjc' with ⟨x', hx', -⟩ | ⟨-, -, x', hx'⟩
        · obtain ⟨r, hr⟩ := hod; omega
        · omega
      · exact ⟨y, by rw [hjb b hb, hy]⟩

/-- Paper, Example \ref{IB:ex:tree}: `P(E_{BC}) = 1` but (F) fails. -/
theorem ex_tree (h : IsRigidSeq lam) :
    (∀ᵐ ω ∂bernoulliSeq (treeP lam), HasSumset (randSet ω)) ∧ ¬ CondF (treeP lam) :=
  ⟨ae_hasSumset_of_strategy (treeS_strategy h), treeP_not_condF h⟩

/-- Paper, Theorem \ref{IB:thm:hierarchy} (strictness): none of the three implications
`(F) ⇒ P(E_{BC}) = 1 ⇒ (N) ⇒ P(E_{<ω}) = 1` can be reversed (Examples \ref{IB:ex:tree},
\ref{IB:ex:half}, \ref{IB:ex:rigid}, with `λ_j = 9^j`). -/
theorem thm_hierarchy_strict :
    (∃ p : ℕ → I, (∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω)) ∧ ¬ CondF p) ∧
    (∃ p : ℕ → I, CondN p ∧ ¬ ∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω)) ∧
    (∃ p : ℕ → I, (∀ᵐ ω ∂bernoulliSeq p, HasAllFinite (randSet ω)) ∧ ¬ CondN p) := by
  refine ⟨⟨_, ex_tree isRigidSeq_nine⟩, ⟨_, (ex_half isRigidSeq_nine).1, fun h' => ?_⟩,
    ⟨_, (ex_rigid isRigidSeq_nine).2⟩⟩
  obtain ⟨ω, h1, h2⟩ := (h'.and (ex_half isRigidSeq_nine).2.1).exists
  exact h2 h1

end TreeF

/-! ## Trees and the non-Borel theorem (Theorem \ref{IB:thm:nonborel}) -/

/-- `Bool` (discrete) is a Polish space. -/
instance polishSpace_bool : PolishSpace Bool :=
  (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap (f := fun b : Bool => b.toNat)
    continuous_of_discreteTopology (fun a b h => by cases a <;> cases b <;> simp_all)
    (fun s _ => (Set.toFinite _).isClosed)).polishSpace

/-- The space `2^{ℕ^{<ℕ}}` of subsets of the set `ℕ^{<ℕ}` of finite sequences of naturals. -/
abbrev TreeSp := List ℕ → Bool

/-- `T` is a tree: closed under initial segments. -/
def IsTree (T : TreeSp) : Prop := ∀ s s' : List ℕ, s' <+: s → T s = true → T s' = true

/-- The set `Tr` of trees. -/
def TrSet : Set TreeSp := {T | IsTree T}

/-- `z|n`, the initial segment of length `n` of `z ∈ ℕ^ℕ`. -/
def res (z : ℕ → ℕ) (n : ℕ) : List ℕ := List.ofFn fun i : Fin n => z i

/-- The set `IF` of trees with an infinite branch (ill-founded trees). -/
def IFSet : Set TreeSp := {T | IsTree T ∧ ∃ z : ℕ → ℕ, ∀ n, T (res z n) = true}

lemma isClosed_eq_true {X : Type*} [TopologicalSpace X] {f : X → Bool} (hf : Continuous f) :
    IsClosed {x | f x = true} :=
  (isClosed_discrete {true}).preimage hf

lemma isClosed_TrSet : IsClosed TrSet := by
  have : TrSet = ⋂ s : List ℕ, ⋂ s' : List ℕ, ⋂ (_ : s' <+: s),
      ({T : TreeSp | T s = false} ∪ {T | T s' = true}) := by
    ext T
    simp only [TrSet, IsTree, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union]
    refine forall_congr' fun s => forall_congr' fun s' => forall_congr' fun _ => ?_
    cases T s <;> simp
  rw [this]
  refine isClosed_iInter fun s => isClosed_iInter fun s' => isClosed_iInter fun _ => ?_
  exact ((isClosed_discrete {false}).preimage (continuous_apply s)).union
    (isClosed_eq_true (f := fun T : TreeSp => T s') (continuous_apply s'))

lemma prefix_getD {q q' : List ℕ} (h : q <+: q') {i : ℕ} (hi : i < q.length) :
    q.getD i 0 = q'.getD i 0 := by
  obtain ⟨r, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- A tree containing an infinite set of pairwise comparable nodes has an infinite branch. -/
lemma branch_of_chain {T : TreeSp} (hT : IsTree T) {Q : Set (List ℕ)} (hQ : Q.Infinite)
    (hQT : ∀ q ∈ Q, T q = true) (hc : ∀ q ∈ Q, ∀ q' ∈ Q, Comp q q') : T ∈ IFSet := by
  have hlen : ∀ n, ∃ q, q ∈ Q ∧ n ≤ q.length := by
    intro n
    by_contra hn
    push Not at hn
    obtain ⟨q, hq, q', hq', hne, he⟩ := hQ.exists_ne_map_eq_of_mapsTo
      (f := List.length) (t := Set.Iio n) (fun q hq => hn q hq) (Set.finite_Iio n)
    rcases hc q hq q' hq' with h1 | h1
    · exact hne (h1.eq_of_length_le he.ge)
    · exact hne (h1.eq_of_length_le he.le).symm
  choose qn hqn hqlen using hlen
  have key : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ i, i < q.length → i < q'.length →
      q.getD i 0 = q'.getD i 0 := by
    intro q hq q' hq' i hi hi'
    rcases hc q hq q' hq' with h1 | h1
    · exact prefix_getD h1 hi
    · exact (prefix_getD h1 hi').symm
  refine ⟨hT, fun i => (qn (i + 1)).getD i 0, fun n => ?_⟩
  have e : res (fun i => (qn (i + 1)).getD i 0) n = (qn n).take n := by
    apply List.ext_getElem
    · simp [res, hqlen n]
    · intro i h1 h2
      simp only [res, List.length_ofFn] at h1
      simp only [res, List.getElem_ofFn, List.getElem_take]
      rw [key _ (hqn (i + 1)) _ (hqn n) i (by have := hqlen (i + 1); omega)
        (by have := hqlen n; omega)]
      rw [List.getD_eq_getElem _ _ (by have := hqlen n; omega)]
  rw [e]
  exact hT _ _ (List.take_prefix _ _) (hQT _ (hqn n))

/-- If a tree contains two infinite sets of nodes `Q₁, Q₂` such that every element of `Q₁` is
comparable with every element of `Q₂`, then it has an infinite branch. -/
lemma branch_of_cross {T : TreeSp} (hT : IsTree T) {Q1 Q2 : Set (List ℕ)} (h1 : Q1.Infinite)
    (h2 : Q2.Infinite) (hQ1 : ∀ q ∈ Q1, T q = true) (hc : ∀ q ∈ Q1, ∀ q' ∈ Q2, Comp q q') :
    T ∈ IFSet := by
  refine branch_of_chain hT h1 hQ1 fun q hq q' hq' => ?_
  by_contra hnc
  apply h2
  refine (List.finite_toSet q.inits).subset fun r hr => ?_
  show r ∈ q.inits
  rw [List.mem_inits]
  rcases hc q hq r hr with h | h
  · rcases hc q' hq' r hr with h' | h'
    · exact absurd (List.prefix_or_prefix_of_prefix h h') hnc
    · exact absurd (Or.inl (h.trans h')) hnc
  · exact h

section NonBorel

variable {lam : ℕ → ℕ}

/-- The labels `β_s = λ_{2⌜s⌝}`, `γ_s = λ_{2⌜s⌝+1}` of `s ∈ ℕ^{<ℕ}`. -/
def nβ (lam : ℕ → ℕ) (s : List ℕ) : ℕ := lam (2 * Encodable.encode s)

/-- See `nβ`. -/
def nγ (lam : ℕ → ℕ) (s : List ℕ) : ℕ := lam (2 * Encodable.encode s + 1)

lemma n_rep_unique (h : IsRigidSeq lam) {a b a' b' : List ℕ}
    (e : nβ lam a + nγ lam b = nβ lam a' + nγ lam b') : a = a' ∧ b = b' := by
  rcases lem_rigid_pair h e with ⟨e1, e2⟩ | ⟨e1, -⟩
  · exact ⟨Encodable.encode_injective (by omega), Encodable.encode_injective (by omega)⟩
  · omega

open Classical in
/-- `D_T = {β_s + γ_{s'} : s, s' ∈ T comparable}`, as a point of `2^ℕ`. -/
noncomputable def DBC (lam : ℕ → ℕ) (T : TreeSp) : ℕ → Bool := fun n =>
  if hn : ∃ q : List ℕ × List ℕ, Comp q.1 q.2 ∧ n = nβ lam q.1 + nγ lam q.2 then
    T hn.choose.1 && T hn.choose.2 else false

lemma DBC_eq_true (h : IsRigidSeq lam) (T : TreeSp) (n : ℕ) :
    DBC lam T n = true ↔ ∃ s s', T s = true ∧ T s' = true ∧ Comp s s' ∧
      n = nβ lam s + nγ lam s' := by
  unfold DBC
  split_ifs with hn
  · rw [Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, _, h1, h2, hn.choose_spec.1, hn.choose_spec.2⟩
    · rintro ⟨s, s', h1, h2, -, rfl⟩
      obtain ⟨e1, e2⟩ := n_rep_unique h hn.choose_spec.2
      rw [← e1, ← e2]
      exact ⟨h1, h2⟩
  · simp only [false_iff]
    rintro ⟨s, s', -, -, hc, e⟩
    exact hn ⟨(s, s'), hc, e⟩

lemma continuous_DBC (lam : ℕ → ℕ) : Continuous (DBC lam) := by
  refine continuous_pi fun n => ?_
  unfold DBC
  split_ifs with hn
  · exact (continuous_of_discreteTopology (f := fun x : Bool × Bool => x.1 && x.2)).comp
      ((continuous_apply (A := fun _ : List ℕ => Bool) hn.choose.1).prodMk
        (continuous_apply (A := fun _ : List ℕ => Bool) hn.choose.2))
  · exact continuous_const

end NonBorel

lemma res_length (z : ℕ → ℕ) (n : ℕ) : (res z n).length = n := by simp [res]

lemma res_prefix (z : ℕ → ℕ) {n m : ℕ} (h : n ≤ m) : res z n <+: res z m := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [res, h]
  · intro i h1 h2
    simp [res]

lemma res_comp (z : ℕ → ℕ) (n m : ℕ) : Comp (res z n) (res z m) := by
  rcases le_total n m with h | h
  · exact Or.inl (res_prefix z h)
  · exact Or.inr (res_prefix z h)

lemma res_injective (z : ℕ → ℕ) : Function.Injective (res z) := fun n m e => by
  simpa [res_length] using congrArg List.length e

/-- The common end of the reductions: two infinite families of nodes of `T` indexed by `B` and `C`,
injectively, with all cross pairs comparable, give an infinite branch. -/
lemma branch_of_families {T : TreeSp} (hT : IsTree T) {B C : Set ℕ} (hB : B.Infinite)
    (hC : C.Infinite) (f g : ℕ → List ℕ) (hf : Set.InjOn f B) (hg : Set.InjOn g C)
    (hfT : ∀ b ∈ B, T (f b) = true) (hc : ∀ b ∈ B, ∀ c ∈ C, Comp (f b) (g c)) : T ∈ IFSet :=
  branch_of_cross hT (hB.image hf) (hC.image hg) (by rintro _ ⟨b, hb, rfl⟩; exact hfT b hb)
    (by rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc', rfl⟩; exact hc b hb c hc')

section NonBorel2

variable {lam : ℕ → ℕ}

lemma nodes_of_shift (h : IsRigidSeq lam) {B C : Set ℕ} {t : ℤ} {jb jc : ℕ → ℕ}
    (hjb : ∀ b ∈ B, (b : ℤ) - t = lam (jb b)) (hjc : ∀ c ∈ C, (c : ℤ) + t = lam (jc c))
    {T : TreeSp} (hmem : ∀ b ∈ B, ∀ c ∈ C, ∃ s s', T s = true ∧ T s' = true ∧ Comp s s' ∧
      b + c = nβ lam s + nγ lam s') (hB : B.Infinite) (hC : C.Infinite) (hT : IsTree T) :
    T ∈ IFSet := by
  have hpair : ∀ b ∈ B, ∀ c ∈ C, ∃ s s', T s = true ∧ T s' = true ∧ Comp s s' ∧
      ((jb b = 2 * Encodable.encode s ∧ jc c = 2 * Encodable.encode s' + 1) ∨
       (jb b = 2 * Encodable.encode s' + 1 ∧ jc c = 2 * Encodable.encode s)) := by
    intro b hb c hc
    obtain ⟨s, s', h1, h2, h3, e⟩ := hmem b hb c hc
    exact ⟨s, s', h1, h2, h3, rigid_pair_shift h (hjb b hb) (hjc c hc) e⟩
  have hinjB : ∀ b ∈ B, ∀ b' ∈ B, jb b = jb b' → b = b' := fun b hb b' hb' e => by
    have h1 := hjb b hb; have h2 := hjb b' hb'; rw [e] at h1
    exact_mod_cast (by linarith : (b : ℤ) = b')
  have hinjC : ∀ c ∈ C, ∀ c' ∈ C, jc c = jc c' → c = c' := fun c hc c' hc' e => by
    have h1 := hjc c hc; have h2 := hjc c' hc'; rw [e] at h1
    exact_mod_cast (by linarith : (c : ℤ) = c')
  obtain ⟨b1, hb1⟩ := hB.nonempty
  obtain ⟨c1, hc1⟩ := hC.nonempty
  rcases Nat.even_or_odd (jb b1) with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- `B - t` are `β`-labels and `C + t` are `γ`-labels
    have hCodd : ∀ c ∈ C, ∃ s', jc c = 2 * Encodable.encode s' + 1 ∧ T s' = true := by
      intro c hc
      obtain ⟨s, s', -, h2, -, ⟨-, e⟩ | ⟨e, -⟩⟩ := hpair b1 hb1 c hc
      · exact ⟨s', e, h2⟩
      · omega
    obtain ⟨r1, hr1, -⟩ := hCodd c1 hc1
    have hBev : ∀ b ∈ B, ∃ s, jb b = 2 * Encodable.encode s ∧ T s = true := by
      intro b hb
      obtain ⟨s, s', h1, -, -, ⟨e, -⟩ | ⟨-, e⟩⟩ := hpair b hb c1 hc1
      · exact ⟨s, e, h1⟩
      · omega
    choose! f hf hfT using hBev
    choose! g hg hgT using hCodd
    refine branch_of_families hT hB hC f g (fun b hb b' hb' e => hinjB b hb b' hb'
      (by rw [hf b hb, hf b' hb', e])) (fun c hc c' hc' e => hinjC c hc c' hc'
      (by rw [hg c hc, hg c' hc', e])) hfT fun b hb c hc => ?_
    obtain ⟨s, s', -, -, hcomp, ⟨e1, e2⟩ | ⟨e1, -⟩⟩ := hpair b hb c hc
    · have h1 : f b = s := Encodable.encode_injective (by have := hf b hb; omega)
      have h2 : g c = s' := Encodable.encode_injective (by have := hg c hc; omega)
      rw [h1, h2]; exact hcomp
    · have := hf b hb; omega
  · -- `B - t` are `γ`-labels and `C + t` are `β`-labels
    have hCev : ∀ c ∈ C, ∃ s, jc c = 2 * Encodable.encode s ∧ T s = true := by
      intro c hc
      obtain ⟨s, s', h1, -, -, ⟨e, -⟩ | ⟨-, e⟩⟩ := hpair b1 hb1 c hc
      · omega
      · exact ⟨s, e, h1⟩
    obtain ⟨r1, hr1, -⟩ := hCev c1 hc1
    have hBodd : ∀ b ∈ B, ∃ s', jb b = 2 * Encodable.encode s' + 1 ∧ T s' = true := by
      intro b hb
      obtain ⟨s, s', -, h2, -, ⟨-, e⟩ | ⟨e, -⟩⟩ := hpair b hb c1 hc1
      · omega
      · exact ⟨s', e, h2⟩
    choose! f hf hfT using hBodd
    choose! g hg hgT using hCev
    refine branch_of_families hT hC hB g f (fun c hc c' hc' e => hinjC c hc c' hc'
      (by rw [hg c hc, hg c' hc', e])) (fun b hb b' hb' e => hinjB b hb b' hb'
      (by rw [hf b hb, hf b' hb', e])) hgT fun c hc b hb => ?_
    obtain ⟨s, s', -, -, hcomp, ⟨-, e2⟩ | ⟨e1, e2⟩⟩ := hpair b hb c hc
    · have := hg c hc; omega
    · have h1 : f b = s' := Encodable.encode_injective (by have := hf b hb; omega)
      have h2 : g c = s := Encodable.encode_injective (by have := hg c hc; omega)
      rw [h1, h2]; exact hcomp

/-- The reduction of Theorem \ref{IB:thm:nonborel}\ref{IB:nb1} for `B + C`: for a tree `T`,
`D_T ⊇ B + C` for some infinite `B, C` iff `T` has an infinite branch. -/
theorem DBC_reduction (h : IsRigidSeq lam) {T : TreeSp} (hT : IsTree T) :
    HasSumset (randSet (DBC lam T)) ↔ T ∈ IFSet := by
  constructor
  · rintro ⟨B, C, hB, hC, hBC⟩
    have hmem : ∀ b ∈ B, ∀ c ∈ C, ∃ s s', T s = true ∧ T s' = true ∧ Comp s s' ∧
        b + c = nβ lam s + nγ lam s' := fun b hb c hc =>
      (DBC_eq_true h T (b + c)).1 (hBC ⟨b, hb, c, hc, rfl⟩)
    obtain ⟨t, jb, jc, hjb, hjc⟩ := cor_R_nat h hB hC fun b hb c hc => by
      obtain ⟨s, s', -, -, -, e⟩ := hmem b hb c hc
      exact ⟨2 * Encodable.encode s, 2 * Encodable.encode s' + 1,
        by rw [← Nat.cast_add, e]; simp [nβ, nγ]⟩
    exact nodes_of_shift h hjb hjc hmem hB hC hT
  · rintro ⟨-, z, hz⟩
    have hinj : ∀ (f : List ℕ → ℕ), Function.Injective f → Function.Injective (f ∘ res z) :=
      fun f hf => hf.comp (res_injective z)
    refine ⟨Set.range (nβ lam ∘ res z), Set.range (nγ lam ∘ res z),
      Set.infinite_range_of_injective (hinj _ fun a b e => Encodable.encode_injective
        (by have := h.injective e; omega)),
      Set.infinite_range_of_injective (hinj _ fun a b e => Encodable.encode_injective
        (by have := h.injective e; omega)), ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, _, ⟨m, rfl⟩, rfl⟩
    exact (DBC_eq_true h T _).2 ⟨_, _, hz n, hz m, res_comp z n m, rfl⟩

end NonBorel2

section NonBorel3

variable {lam : ℕ → ℕ}

/-- The labels `γ_s = λ_{⌜s⌝}` used for `B ⊕ B` and `B + B`. -/
def nδ (lam : ℕ → ℕ) (s : List ℕ) : ℕ := lam (Encodable.encode s)

lemma nδ_rep (h : IsRigidSeq lam) {a b a' b' : List ℕ}
    (e : nδ lam a + nδ lam b = nδ lam a' + nδ lam b') : (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  rcases lem_rigid_pair h e with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨Encodable.encode_injective e1, Encodable.encode_injective e2⟩
  · exact Or.inr ⟨Encodable.encode_injective e1, Encodable.encode_injective e2⟩

open Classical in
/-- `D^⊕_T = {γ_s + γ_{s'} : s ≠ s' ∈ T comparable}` (`plus = false`) and
`D^+_T = {γ_s + γ_{s'} : s, s' ∈ T comparable}` (`plus = true`), as points of `2^ℕ`. -/
noncomputable def D1 (lam : ℕ → ℕ) (plus : Bool) (T : TreeSp) : ℕ → Bool := fun n =>
  if hn : ∃ q : List ℕ × List ℕ, Comp q.1 q.2 ∧ (plus = true ∨ q.1 ≠ q.2) ∧
      n = nδ lam q.1 + nδ lam q.2 then T hn.choose.1 && T hn.choose.2 else false

lemma D1_eq_true (h : IsRigidSeq lam) (plus : Bool) (T : TreeSp) (n : ℕ) :
    D1 lam plus T n = true ↔ ∃ s s', T s = true ∧ T s' = true ∧ Comp s s' ∧
      (plus = true ∨ s ≠ s') ∧ n = nδ lam s + nδ lam s' := by
  unfold D1
  split_ifs with hn
  · rw [Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, _, h1, h2, hn.choose_spec.1, hn.choose_spec.2.1, hn.choose_spec.2.2⟩
    · rintro ⟨s, s', h1, h2, -, -, rfl⟩
      rcases nδ_rep h hn.choose_spec.2.2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2]; exact ⟨h1, h2⟩
      · rw [← e1, ← e2]; exact ⟨h2, h1⟩
  · simp only [false_iff]
    rintro ⟨s, s', -, -, hc, hpl, e⟩
    exact hn ⟨(s, s'), hc, hpl, e⟩

lemma continuous_D1 (lam : ℕ → ℕ) (plus : Bool) : Continuous (D1 lam plus) := by
  refine continuous_pi fun n => ?_
  unfold D1
  split_ifs with hn
  · exact (continuous_of_discreteTopology (f := fun x : Bool × Bool => x.1 && x.2)).comp
      ((continuous_apply (A := fun _ : List ℕ => Bool) hn.choose.1).prodMk
        (continuous_apply (A := fun _ : List ℕ => Bool) hn.choose.2))
  · exact continuous_const

/-- Two disjoint infinite subsets of an infinite set. -/
lemma exists_two_infinite {B : Set ℕ} (hB : B.Infinite) :
    ∃ B1 B2 : Set ℕ, B1 ⊆ B ∧ B2 ⊆ B ∧ B1.Infinite ∧ B2.Infinite ∧
      ∀ b ∈ B1, ∀ c ∈ B2, b ≠ c := by
  set e := hB.natEmbedding
  have hinj : Function.Injective fun i => (e i : ℕ) := fun a b h' =>
    e.injective (Subtype.ext h')
  refine ⟨Set.range fun i => (e (2 * i) : ℕ), Set.range fun i => (e (2 * i + 1) : ℕ),
    by rintro _ ⟨i, rfl⟩; exact (e _).2, by rintro _ ⟨i, rfl⟩; exact (e _).2,
    Set.infinite_range_of_injective (hinj.comp fun a b h' => by simp at h'; omega),
    Set.infinite_range_of_injective (hinj.comp fun a b h' => by simp at h'; omega), ?_⟩
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h'
  have := hinj h'
  omega

/-- The reduction of Theorem \ref{IB:thm:nonborel}\ref{IB:nb1} for `B ⊕ B` (`plus = false`) and
`B + B` (`plus = true`). -/
theorem D1_reduction (h : IsRigidSeq lam) (plus : Bool) {T : TreeSp} (hT : IsTree T) :
    Has1 plus (randSet (D1 lam plus T)) ↔ T ∈ IFSet := by
  constructor
  · rintro ⟨B, hB, hBB, -⟩
    obtain ⟨B1, B2, h1, h2, hB1, hB2, hne⟩ := exists_two_infinite hB
    have hmem : ∀ b ∈ B1, ∀ c ∈ B2, ∃ s s', T s = true ∧ T s' = true ∧ Comp s s' ∧
        b + c = nδ lam s + nδ lam s' := by
      intro b hb c hc
      obtain ⟨s, s', h1', h2', h3', -, e⟩ :=
        (D1_eq_true h plus T (b + c)).1 (hBB ⟨b, h1 hb, c, h2 hc, hne b hb c hc, rfl⟩)
      exact ⟨s, s', h1', h2', h3', e⟩
    obtain ⟨t, jb, jc, hjb, hjc⟩ := cor_R_nat h hB1 hB2 fun b hb c hc => by
      obtain ⟨s, s', -, -, -, e⟩ := hmem b hb c hc
      exact ⟨Encodable.encode s, Encodable.encode s', by rw [← Nat.cast_add, e]; simp [nδ]⟩
    have hpair : ∀ b ∈ B1, ∀ c ∈ B2, ∃ s s', T s = true ∧ T s' = true ∧ Comp s s' ∧
        ((jb b = Encodable.encode s ∧ jc c = Encodable.encode s') ∨
         (jb b = Encodable.encode s' ∧ jc c = Encodable.encode s)) := by
      intro b hb c hc
      obtain ⟨s, s', h1', h2', h3', e⟩ := hmem b hb c hc
      exact ⟨s, s', h1', h2', h3', rigid_pair_shift h (hjb b hb) (hjc c hc) e⟩
    obtain ⟨b1, hb1⟩ := hB1.nonempty
    obtain ⟨c1, hc1⟩ := hB2.nonempty
    have hf : ∀ b ∈ B1, ∃ s, jb b = Encodable.encode s ∧ T s = true := by
      intro b hb
      obtain ⟨s, s', h1', h2', -, ⟨e, -⟩ | ⟨e, -⟩⟩ := hpair b hb c1 hc1
      · exact ⟨s, e, h1'⟩
      · exact ⟨s', e, h2'⟩
    have hg : ∀ c ∈ B2, ∃ s, jc c = Encodable.encode s ∧ T s = true := by
      intro c hc
      obtain ⟨s, s', h1', h2', -, ⟨-, e⟩ | ⟨-, e⟩⟩ := hpair b1 hb1 c hc
      · exact ⟨s', e, h2'⟩
      · exact ⟨s, e, h1'⟩
    choose! f hf hfT using hf
    choose! g hg hgT using hg
    refine branch_of_families hT hB1 hB2 f g (fun b hb b' hb' e => ?_) (fun c hc c' hc' e => ?_)
      hfT fun b hb c hc => ?_
    · have e1 := hjb b hb; have e2 := hjb b' hb'
      rw [hf b hb, e, ← hf b' hb'] at e1
      exact_mod_cast (by linarith : (b : ℤ) = b')
    · have e1 := hjc c hc; have e2 := hjc c' hc'
      rw [hg c hc, e, ← hg c' hc'] at e1
      exact_mod_cast (by linarith : (c : ℤ) = c')
    · obtain ⟨s, s', -, -, hcomp, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩ := hpair b hb c hc
      · rw [Encodable.encode_injective ((hf b hb).symm.trans e1),
          Encodable.encode_injective ((hg c hc).symm.trans e2)]
        exact hcomp
      · rw [Encodable.encode_injective ((hf b hb).symm.trans e1),
          Encodable.encode_injective ((hg c hc).symm.trans e2)]
        exact hcomp.symm
  · rintro ⟨-, z, hz⟩
    have hδ : Function.Injective (nδ lam) := fun a b e =>
      Encodable.encode_injective (h.injective e)
    have hinj : Function.Injective (nδ lam ∘ res z) := hδ.comp (res_injective z)
    refine ⟨Set.range (nδ lam ∘ res z), Set.infinite_range_of_injective hinj, ?_, ?_⟩
    · rintro _ ⟨_, ⟨n, rfl⟩, _, ⟨m, rfl⟩, hnm, rfl⟩
      refine (D1_eq_true h plus T _).2 ⟨_, _, hz n, hz m, res_comp z n m,
        Or.inr fun e => hnm (by rw [Function.comp_apply, e]; rfl), rfl⟩
    · rintro hp _ ⟨n, rfl⟩
      refine (D1_eq_true h plus T _).2 ⟨_, _, hz n, hz n, res_comp z n n, Or.inl hp, ?_⟩
      simp only [Function.comp_apply]; ring

end NonBorel3

/-! ### `Σ¹₁`-completeness -/

/-- A topological space is zero-dimensional if it has a basis of clopen sets. -/
def ZeroDimensional (W : Type) [TopologicalSpace W] : Prop :=
  ∃ 𝓑 : Set (Set W), TopologicalSpace.IsTopologicalBasis 𝓑 ∧ ∀ s ∈ 𝓑, IsClopen s

/-- `Z ⊆ W` is `Σ¹₁`-complete: it is analytic and for every analytic subset `Z'` of a
zero-dimensional Polish space `W'` there is a continuous `f : W' → W` with `Z' = f⁻¹(Z)`. -/
def Sigma11Complete {W : Type} [TopologicalSpace W] (Z : Set W) : Prop :=
  AnalyticSet Z ∧ ∀ (W' : Type) [TopologicalSpace W'] [PolishSpace W'], ZeroDimensional W' →
    ∀ Z' : Set W', AnalyticSet Z' → ∃ f : W' → W, Continuous f ∧ Z' = f ⁻¹' Z

/-- **Hypothesis** (Kechris, *Classical Descriptive Set Theory*, Theorem 27.1): the set `IF` of
ill-founded trees is a `Σ¹₁`-complete subset of the (Polish, zero-dimensional) space `Tr` of
trees. This classical theorem is not proved here; the statements below that need it take it as
an explicit hypothesis. -/
def KechrisIFComplete : Prop := Sigma11Complete {T : TrSet | T.1 ∈ IFSet}

/-- **Hypothesis** (Kechris, Theorem 27.1, together with the existence of analytic non-Borel
sets, Kechris, Theorem 14.2): `IF` is not a Borel subset of `2^{ℕ^{<ℕ}}` (equivalently, of the
closed subspace `Tr`). Not proved here; an explicit hypothesis. -/
def KechrisIFNotBorel : Prop := ¬ MeasurableSet[borel TreeSp] IFSet

lemma measurableSet_borel_TrSet : MeasurableSet[borel TreeSp] TrSet := by
  have : IsOpen TrSetᶜ := isClosed_TrSet.isOpen_compl
  have h := MeasurableSpace.measurableSet_generateFrom (s := {s : Set TreeSp | IsOpen s}) this
  exact (MeasurableSet.compl_iff (m := borel TreeSp)).1 (by rw [borel]; exact h)

/-- A continuous reduction of `IF` (on `Tr`) to an analytic set `Z` transfers `Σ¹₁`-completeness
and non-Borelness. -/
theorem complete_of_reduction {W : Type} [TopologicalSpace W] {Z : Set W} (hZ : AnalyticSet Z)
    (g : TreeSp → W) (hg : Continuous g) (hred : ∀ T ∈ TrSet, g T ∈ Z ↔ T ∈ IFSet) :
    (KechrisIFComplete → Sigma11Complete Z) ∧
    (KechrisIFNotBorel → ¬ MeasurableSet[borel W] Z) := by
  refine ⟨fun hK => ⟨hZ, fun W' _ _ hzd Z' hZ' => ?_⟩, fun hK hB => hK ?_⟩
  · obtain ⟨f, hf, hfZ⟩ := hK.2 W' hzd Z' hZ'
    refine ⟨g ∘ Subtype.val ∘ f, hg.comp (continuous_subtype_val.comp hf), ?_⟩
    rw [hfZ]
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Function.comp_apply]
    exact (hred _ (f x).2).symm
  · have h1 : MeasurableSet[borel TreeSp] (g ⁻¹' Z) := hg.borel_measurable hB
    have : IFSet = g ⁻¹' Z ∩ TrSet := by
      ext T
      constructor
      · intro hT; exact ⟨(hred T hT.1).2 hT, hT.1⟩
      · rintro ⟨h1, h2⟩; exact (hred T h2).1 h1
    rw [this]
    exact h1.inter measurableSet_borel_TrSet

/-! ### Part (a): the families `𝔇_{BC}`, `𝔇_⊕`, `𝔇_+` -/

/-- `𝔇_{BC} = {D ⊆ ℕ : ∃ infinite B, C, B + C ⊆ D}`, as a subset of `2^ℕ`. -/
def frakD_BC : Set (ℕ → Bool) := {x | HasSumset (randSet x)}

/-- `𝔇_⊕` (`plus = false`) and `𝔇_+` (`plus = true`), as subsets of `2^ℕ`. -/
def frakD1 (plus : Bool) : Set (ℕ → Bool) := {x | Has1 plus (randSet x)}

lemma measurable_apply_true {X : Type*} [MeasurableSpace X] {g : X → ℕ → Bool}
    (hg : Measurable g) (n : ℕ) : Measurable fun x => g x n = true :=
  ((measurable_pi_apply n).comp hg).eq_const true

lemma measurable_infinite {X : Type*} [MeasurableSpace X] {g : X → ℕ → Bool}
    (hg : Measurable g) : Measurable fun x => (randSet (g x)).Infinite := by
  have : (fun x => (randSet (g x)).Infinite) = fun x => ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ g x n = true := by
    ext x
    show {n | g x n = true}.Infinite ↔ _
    rw [← Nat.frequently_atTop_iff_infinite, Filter.frequently_atTop]
  rw [this]
  exact Measurable.forall fun N => Measurable.exists fun n =>
    (measurable_const (a := N ≤ n)).and (measurable_apply_true hg n)

open Classical in
lemma randSet_decide (B : Set ℕ) : randSet (fun n => decide (n ∈ B)) = B := by
  ext n; simp [randSet]

/-- Upper bound in Theorem \ref{IB:thm:nonborel}\ref{IB:nb1}: `𝔇_{BC}` is analytic (a projection
of a Borel subset of `2^ℕ × 2^ℕ × 2^ℕ`). -/
theorem analyticSet_frakD_BC : AnalyticSet frakD_BC := by
  classical
  set E : Set ((ℕ → Bool) × (ℕ → Bool) × (ℕ → Bool)) := {q | (randSet q.2.1).Infinite ∧
    (randSet q.2.2).Infinite ∧ ∀ b c, q.2.1 b = true → q.2.2 c = true → q.1 (b + c) = true}
  have hE : MeasurableSet E := by
    refine measurableSet_setOfPred.2 ?_
    refine (measurable_infinite (measurable_fst.comp measurable_snd)).and
      ((measurable_infinite (measurable_snd.comp measurable_snd)).and ?_)
    exact Measurable.forall fun b => Measurable.forall fun c =>
      (measurable_apply_true (measurable_fst.comp measurable_snd) b).imp
        ((measurable_apply_true (measurable_snd.comp measurable_snd) c).imp
          (measurable_apply_true measurable_fst (b + c)))
  have : frakD_BC = Prod.fst '' E := by
    ext x
    constructor
    · rintro ⟨B, C, hB, hC, hBC⟩
      refine ⟨(x, fun n => decide (n ∈ B), fun n => decide (n ∈ C)), ⟨?_, ?_, ?_⟩, rfl⟩
      · rwa [randSet_decide]
      · rwa [randSet_decide]
      · intro b c hb hc
        exact hBC ⟨b, by simpa using hb, c, by simpa using hc, rfl⟩
    · rintro ⟨⟨x, y, z⟩, ⟨hy, hz, hyz⟩, rfl⟩
      refine ⟨randSet y, randSet z, hy, hz, ?_⟩
      rintro _ ⟨b, hb, c, hc, rfl⟩
      exact hyz b c hb hc
  rw [this]
  exact hE.analyticSet_image measurable_fst

/-- Upper bound in Theorem \ref{IB:thm:nonborel}\ref{IB:nb1}: `𝔇_⊕` and `𝔇_+` are analytic. -/
theorem analyticSet_frakD1 (plus : Bool) : AnalyticSet (frakD1 plus) := by
  classical
  set E : Set ((ℕ → Bool) × (ℕ → Bool)) := {q | (randSet q.2).Infinite ∧
    (∀ b c, q.2 b = true → q.2 c = true → b ≠ c → q.1 (b + c) = true) ∧
    (plus = true → ∀ b, q.2 b = true → q.1 (2 * b) = true)}
  have hE : MeasurableSet E := by
    refine measurableSet_setOfPred.2 ?_
    refine (measurable_infinite measurable_snd).and (Measurable.and ?_ ?_)
    · exact Measurable.forall fun b => Measurable.forall fun c =>
        (measurable_apply_true measurable_snd b).imp
          ((measurable_apply_true measurable_snd c).imp
            ((measurable_const (a := b ≠ c)).imp (measurable_apply_true measurable_fst (b + c))))
    · exact (measurable_const (a := plus = true)).imp (Measurable.forall fun b =>
        (measurable_apply_true measurable_snd b).imp
          (measurable_apply_true measurable_fst (2 * b)))
  have : frakD1 plus = Prod.fst '' E := by
    ext x
    constructor
    · rintro ⟨B, hB, hBB, h2⟩
      refine ⟨(x, fun n => decide (n ∈ B)), ⟨?_, ?_, ?_⟩, rfl⟩
      · rwa [randSet_decide]
      · intro b c hb hc hne
        exact hBB ⟨b, by simpa using hb, c, by simpa using hc, hne, rfl⟩
      · intro hp b hb
        exact h2 hp b (by simpa using hb)
    · rintro ⟨⟨x, y⟩, ⟨hy, hyy, h2⟩, rfl⟩
      refine ⟨randSet y, hy, ?_, fun hp b hb => h2 hp b hb⟩
      rintro _ ⟨b, hb, c, hc, hne, rfl⟩
      exact hyy b c hb hc hne
  rw [this]
  exact hE.analyticSet_image measurable_fst

/-- Paper, Theorem \ref{IB:thm:nonborel}\ref{IB:nb1}, for `B + C`: `𝔇_{BC}` is analytic, the
continuous map `T ↦ D_T` reduces `IF` to it, and hence (given Kechris's theorem) it is
`Σ¹₁`-complete and not Borel. -/
theorem thm_nonborel_a_BC {lam : ℕ → ℕ} (h : IsRigidSeq lam) :
    AnalyticSet frakD_BC ∧
    (∃ g : TreeSp → (ℕ → Bool), Continuous g ∧ ∀ T ∈ TrSet, (g T ∈ frakD_BC ↔ T ∈ IFSet)) ∧
    (KechrisIFComplete → Sigma11Complete frakD_BC) ∧
    (KechrisIFNotBorel → ¬ MeasurableSet[borel (ℕ → Bool)] frakD_BC) :=
  ⟨analyticSet_frakD_BC, ⟨DBC lam, continuous_DBC lam, fun _ hT => DBC_reduction h hT⟩,
    complete_of_reduction analyticSet_frakD_BC _ (continuous_DBC lam)
      (fun _ hT => DBC_reduction h hT)⟩

/-- Paper, Theorem \ref{IB:thm:nonborel}\ref{IB:nb1}, for `B ⊕ B` (`plus = false`) and `B + B`
(`plus = true`). -/
theorem thm_nonborel_a_1 {lam : ℕ → ℕ} (h : IsRigidSeq lam) (plus : Bool) :
    AnalyticSet (frakD1 plus) ∧
    (∃ g : TreeSp → (ℕ → Bool), Continuous g ∧ ∀ T ∈ TrSet, (g T ∈ frakD1 plus ↔ T ∈ IFSet)) ∧
    (KechrisIFComplete → Sigma11Complete (frakD1 plus)) ∧
    (KechrisIFNotBorel → ¬ MeasurableSet[borel (ℕ → Bool)] (frakD1 plus)) :=
  ⟨analyticSet_frakD1 plus, ⟨D1 lam plus, continuous_D1 lam plus,
    fun _ hT => D1_reduction h plus hT⟩,
    complete_of_reduction (analyticSet_frakD1 plus) _ (continuous_D1 lam plus)
      (fun _ hT => D1_reduction h plus hT)⟩

/-! ### Part (b): the families `𝔄_*` -/

/-- `𝔄_{BC} = {p ∈ [0,1]^ℕ : P_p(E_{BC}) = 1}`. -/
def frakA_BC : Set (ℕ → I) := {p | ∀ᵐ ω ∂bernoulliSeq p, HasSumset (randSet ω)}

/-- `𝔄_⊕` (`plus = false`) and `𝔄_+` (`plus = true`). -/
def frakA1 (plus : Bool) : Set (ℕ → I) := {p | ∀ᵐ ω ∂bernoulliSeq p, Has1 plus (randSet ω)}

lemma continuous_pe (n : ℕ) : Continuous fun p : ℕ → I => pe p n :=
  ENNReal.continuous_coe.comp (toNNReal_continuous.comp (continuous_apply n))

lemma measurable_w {X : Type*} [MeasurableSpace X] {f : X → ℕ → I} (hf : Measurable f)
    (U : Finset ℕ) (x : ℕ) : Measurable fun y => w (f y) U x :=
  Finset.measurable_prod _ fun u _ => (continuous_pe (x + u)).measurable.comp hf

lemma measurable_apply_true' {X ι : Type*} [MeasurableSpace X] {g : X → ι → Bool} (hg : Measurable g) (i : ι) :
    Measurable fun x => g x i = true :=
  ((measurable_pi_apply i).comp hg).eq_const true

/-- Codes for strategies: a strategy `S` is the set of pairs where `χ` is `true`. -/
abbrev StratCode := Finset ℕ × Finset ℕ → Bool

lemma measurable_wsum_Xs (U V : Finset ℕ) :
    Measurable fun y : StratCode × (ℕ → I) => wsum y.2 U (Xs {q | y.1 q = true} U V) := by
  classical
  refine Measurable.tsum fun x => ?_
  simp only [Set.indicator_apply]
  refine Measurable.ite ?_ (measurable_w measurable_snd U x) measurable_const
  exact measurableSet_setOfPred.2 ((measurable_const (a := x ∉ V)).and
    (measurable_apply_true' measurable_fst (U, insert x V)))

lemma measurable_wsum_Ys (U V : Finset ℕ) :
    Measurable fun y : StratCode × (ℕ → I) => wsum y.2 V (Ys {q | y.1 q = true} U V) := by
  classical
  refine Measurable.tsum fun x => ?_
  simp only [Set.indicator_apply]
  refine Measurable.ite ?_ (measurable_w measurable_snd V x) measurable_const
  exact measurableSet_setOfPred.2 ((measurable_const (a := x ∉ U)).and
    (measurable_apply_true' measurable_fst (insert x U, V)))

/-- Upper bound in Theorem \ref{IB:thm:nonborel}\ref{IB:nb2}: `𝔄_{BC}` is analytic, being (by
Theorem \ref{IB:thm:strategy}) the projection of the Borel set of pairs `(S, p)` such that `S` is
a `BC`-strategy for `p`. -/
theorem analyticSet_frakA_BC : AnalyticSet frakA_BC := by
  classical
  set E : Set (StratCode × (ℕ → I)) := {y | IsBCStrategy y.2 {q | y.1 q = true}}
  have hE : MeasurableSet E := by
    refine measurableSet_setOfPred.2 ?_
    refine (measurable_apply_true' measurable_fst (∅, ∅)).and ?_
    refine Measurable.forall fun U => Measurable.forall fun V => ?_
    exact (measurable_apply_true' measurable_fst (U, V)).imp
      (((measurable_wsum_Xs U V).eq_const ∞).and ((measurable_wsum_Ys U V).eq_const ∞))
  have : frakA_BC = Prod.snd '' E := by
    ext p
    simp only [frakA_BC, Set.mem_ofPred_eq, (thm_strategy p).2, Set.mem_image, Prod.exists]
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨fun q => decide (q ∈ S), p, ?_, rfl⟩
      simpa [E] using hS
    · rintro ⟨χ, p', hp', rfl⟩
      exact ⟨_, hp'⟩
  rw [this]
  exact hE.analyticSet_image measurable_snd

/-- Codes for single-set strategies. -/
abbrev StratCode1 := Finset ℕ → Bool

lemma measurable_wstar (plus : Bool) (U : Finset ℕ) (x : ℕ) :
    Measurable fun p : ℕ → I => wstar p plus U x := by
  cases plus
  · exact measurable_w measurable_id U x
  · exact ((continuous_pe (2 * x)).measurable).mul (measurable_w measurable_id U x)

/-- Upper bound in Theorem \ref{IB:thm:nonborel}\ref{IB:nb2}: `𝔄_⊕` and `𝔄_+` are analytic. -/
theorem analyticSet_frakA1 (plus : Bool) : AnalyticSet (frakA1 plus) := by
  classical
  set E : Set (StratCode1 × (ℕ → I)) := {y | IsStrategy1 y.2 plus {U | y.1 U = true}}
  have hE : MeasurableSet E := by
    refine measurableSet_setOfPred.2 ?_
    refine (measurable_apply_true' measurable_fst ∅).and ?_
    refine Measurable.forall fun U => ?_
    refine (measurable_apply_true' measurable_fst U).imp (Measurable.eq_const ?_ ∞)
    refine Measurable.tsum fun x => ?_
    simp only [Set.indicator_apply]
    refine Measurable.ite ?_ ((measurable_wstar plus U x).comp measurable_snd) measurable_const
    exact measurableSet_setOfPred.2 ((measurable_const (a := x ∉ U)).and
      (measurable_apply_true' measurable_fst (insert x U)))
  have : frakA1 plus = Prod.snd '' E := by
    ext p
    simp only [frakA1, Set.mem_ofPred_eq, (thm_strategy1 p plus).2, Set.mem_image, Prod.exists]
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨fun q => decide (q ∈ S), p, ?_, rfl⟩
      simpa [E] using hS
    · rintro ⟨χ, p', hp', rfl⟩
      exact ⟨_, hp'⟩
  rw [this]
  exact hE.analyticSet_image measurable_snd

/-- The embedding `D ↦ 1_D` of `2^ℕ` into `[0,1]^ℕ`. -/
noncomputable def indEmb (x : ℕ → Bool) : ℕ → I := indP (randSet x)

lemma indEmb_apply (x : ℕ → Bool) (n : ℕ) : indEmb x n = if x n then 1 else 0 := by
  unfold indEmb indP
  by_cases h : x n = true <;> simp [randSet, h]

lemma continuous_indEmb : Continuous indEmb := by
  have : indEmb = fun x n => (fun b : Bool => if b then (1 : I) else 0) (x n) := by
    funext x n; exact indEmb_apply x n
  rw [this]
  exact continuous_pi fun n =>
    (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : I) else 0)).comp
      (continuous_apply n)

/-- Paper, Theorem \ref{IB:thm:nonborel}\ref{IB:nb2}, for `B + C` in `[0,1]^ℕ`. -/
theorem thm_nonborel_b_BC {lam : ℕ → ℕ} (h : IsRigidSeq lam) :
    AnalyticSet frakA_BC ∧
    (∃ g : TreeSp → (ℕ → I), Continuous g ∧ ∀ T ∈ TrSet, (g T ∈ frakA_BC ↔ T ∈ IFSet)) ∧
    (KechrisIFComplete → Sigma11Complete frakA_BC) ∧
    (KechrisIFNotBorel → ¬ MeasurableSet[borel (ℕ → I)] frakA_BC) := by
  have hred : ∀ T ∈ TrSet, (indEmb (DBC lam T) ∈ frakA_BC ↔ T ∈ IFSet) := fun T hT => by
    rw [← DBC_reduction h hT]
    exact ae_indP_iff _ HasSumset
  have hc := continuous_indEmb.comp (continuous_DBC lam)
  exact ⟨analyticSet_frakA_BC, ⟨_, hc, hred⟩,
    complete_of_reduction analyticSet_frakA_BC _ hc hred⟩

/-- Paper, Theorem \ref{IB:thm:nonborel}\ref{IB:nb2}, for `B ⊕ B` and `B + B` in `[0,1]^ℕ`. -/
theorem thm_nonborel_b_1 {lam : ℕ → ℕ} (h : IsRigidSeq lam) (plus : Bool) :
    AnalyticSet (frakA1 plus) ∧
    (∃ g : TreeSp → (ℕ → I), Continuous g ∧ ∀ T ∈ TrSet, (g T ∈ frakA1 plus ↔ T ∈ IFSet)) ∧
    (KechrisIFComplete → Sigma11Complete (frakA1 plus)) ∧
    (KechrisIFNotBorel → ¬ MeasurableSet[borel (ℕ → I)] (frakA1 plus)) := by
  have hred : ∀ T ∈ TrSet, (indEmb (D1 lam plus T) ∈ frakA1 plus ↔ T ∈ IFSet) := fun T hT => by
    rw [← D1_reduction h plus hT]
    exact ae_indP_iff _ (Has1 plus)
  have hc := continuous_indEmb.comp (continuous_D1 lam plus)
  exact ⟨analyticSet_frakA1 plus, ⟨_, hc, hred⟩,
    complete_of_reduction (analyticSet_frakA1 plus) _ hc hred⟩

/-! ### Part (b) in `(0,1)^ℕ` -/

/-- The open interval `(0, 1)`. -/
abbrev Ioo01 := Set.Ioo (0 : ℝ) 1

instance polishSpace_Ioo01 : PolishSpace Ioo01 := isOpen_Ioo.polishSpace

/-- The Polish space `(0,1)^ℕ`. -/
abbrev OpenCube := ℕ → Ioo01

/-- The inclusion `(0,1)^ℕ → [0,1]^ℕ`. -/
def cubeIncl (p : OpenCube) : ℕ → I := fun n => ⟨(p n).1, (p n).2.1.le, (p n).2.2.le⟩

lemma continuous_cubeIncl : Continuous cubeIncl :=
  continuous_pi fun n => (continuous_subtype_val.comp (continuous_apply n)).subtype_mk _

/-- `𝔄_{BC} ∩ (0,1)^ℕ`, as a subset of `(0,1)^ℕ`. -/
def frakA_BC' : Set OpenCube := cubeIncl ⁻¹' frakA_BC

/-- `𝔄_⊕ ∩ (0,1)^ℕ` and `𝔄_+ ∩ (0,1)^ℕ`, as subsets of `(0,1)^ℕ`. -/
def frakA1' (plus : Bool) : Set OpenCube := cubeIncl ⁻¹' frakA1 plus

lemma half_mem : (1 / 2 : ℝ) ∈ Ioo01 := ⟨by norm_num, by norm_num⟩

lemma pow_half_mem (n : ℕ) : ((1 / 2 : ℝ) ^ (n + 2)) ∈ Ioo01 :=
  ⟨by positivity, pow_lt_one₀ (by norm_num) (by norm_num) (by omega)⟩

/-- `p^D_n = 1/2` for `n ∈ D` and `p^D_n = 2^{-n-2}` for `n ∉ D`. -/
noncomputable def pD (x : ℕ → Bool) : OpenCube := fun n =>
  if x n then ⟨1 / 2, half_mem⟩ else ⟨(1 / 2) ^ (n + 2), pow_half_mem n⟩

lemma continuous_pD : Continuous pD := by
  have : pD = fun x n => (fun b : Bool => if b then (⟨1 / 2, half_mem⟩ : Ioo01)
      else ⟨(1 / 2) ^ (n + 2), pow_half_mem n⟩) (x n) := rfl
  rw [this]
  exact continuous_pi fun n => (continuous_of_discreteTopology (f := fun b : Bool =>
    if b then (⟨1 / 2, half_mem⟩ : Ioo01) else ⟨(1 / 2) ^ (n + 2), pow_half_mem n⟩)).comp
      (continuous_apply n)

lemma pe_pD (x : ℕ → Bool) (n : ℕ) :
    pe (cubeIncl (pD x)) n = if x n then 2⁻¹ else 2⁻¹ ^ (n + 2) := by
  unfold pe cubeIncl pD
  by_cases hx : x n = true
  · simp only [hx, if_true]
    have : toNNReal ⟨(1 / 2 : ℝ), half_mem.1.le, half_mem.2.le⟩ = 2⁻¹ := by
      ext; simp [toNNReal]; rfl
    rw [this, ENNReal.coe_inv two_ne_zero]; rfl
  · simp only [hx, Bool.false_eq_true, if_false]
    have : toNNReal ⟨((1 / 2 : ℝ) ^ (n + 2)), (pow_half_mem n).1.le, (pow_half_mem n).2.le⟩ =
        2⁻¹ ^ (n + 2) := by
      ext; simp [toNNReal]; rfl
    rw [this, ENNReal.coe_pow, ENNReal.coe_inv two_ne_zero]; rfl

lemma two_inv_pow_ne_zero (k : ℕ) : (2⁻¹ : ℝ≥0∞) ^ k ≠ 0 :=
  pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)

/-- Under `P_{p^D}`, almost surely `A \ D` is finite (first Borel–Cantelli lemma). -/
lemma ae_finite_outside (x : ℕ → Bool) :
    ∀ᵐ ω ∂bernoulliSeq (cubeIncl (pD x)), {n | n ∈ randSet ω ∧ n ∉ randSet x}.Finite := by
  classical
  let s : ℕ → Set (ℕ → Bool) := fun n => if x n = true then ∅ else cyl {n}
  have hs : ∑' n, bernoulliSeq (cubeIncl (pD x)) (s n) ≠ ∞ := by
    have hle : ∀ n, bernoulliSeq (cubeIncl (pD x)) (s n) ≤ 2⁻¹ ^ n := by
      intro n
      by_cases hx : x n = true
      · simp [s, hx]
      · simp only [s, hx, Bool.false_eq_true, if_false]
        rw [measure_cyl, Finset.prod_singleton]
        change pe _ n ≤ _
        rw [pe_pD, if_neg hx]
        exact pow_le_pow_of_le_one (by simp) (ENNReal.inv_le_one.2 one_le_two) (by omega)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  filter_upwards [ae_finite_setOfPred_mem hs] with ω hω
  refine hω.subset fun n hn => ?_
  have hx : x n ≠ true := hn.2
  simp only [s, Set.mem_ofPred_eq, hx]
  exact fun j hj => by rw [Finset.mem_singleton] at hj; subst hj; exact hn.1

lemma hasSumset_of_finite_diff {A D : Set ℕ} (hA : HasSumset A)
    (hF : {n | n ∈ A ∧ n ∉ D}.Finite) : HasSumset D := by
  obtain ⟨B, C, hB, hC, hBC⟩ := hA
  obtain ⟨M, hM⟩ := hF.bddAbove
  refine ⟨B \ Set.Iic M, C, hB.sdiff (Set.finite_Iic M), hC, ?_⟩
  rintro _ ⟨b, hb, c, hc, rfl⟩
  by_contra hD
  have := hM ⟨hBC ⟨b, hb.1, c, hc, rfl⟩, hD⟩
  have hb2 : M < b := not_le.1 hb.2
  omega

lemma has1_of_finite_diff {plus : Bool} {A D : Set ℕ} (hA : Has1 plus A)
    (hF : {n | n ∈ A ∧ n ∉ D}.Finite) : Has1 plus D := by
  obtain ⟨B, hB, hBB, h2⟩ := hA
  obtain ⟨M, hM⟩ := hF.bddAbove
  refine ⟨B \ Set.Iic M, hB.sdiff (Set.finite_Iic M), ?_, fun hp b hb => ?_⟩
  · rintro _ ⟨b, hb, c, hc, hne, rfl⟩
    by_contra hD
    have := hM ⟨hBB ⟨b, hb.1, c, hc.1, hne, rfl⟩, hD⟩
    have hb2 : M < b := not_le.1 hb.2
    omega
  · by_contra hD
    have := hM ⟨h2 hp b hb.1, hD⟩
    have hb2 : M < b := not_le.1 hb.2
    omega

lemma pD_mem_iff (x : ℕ → Bool) : cubeIncl (pD x) ∈ frakA_BC ↔ x ∈ frakD_BC := by
  constructor
  · intro h
    have h' : ∀ᵐ ω ∂bernoulliSeq (cubeIncl (pD x)), HasSumset (randSet ω) := h
    obtain ⟨ω, h1, h2⟩ := (h'.and (ae_finite_outside x)).exists
    exact hasSumset_of_finite_diff h1 h2
  · rintro ⟨B0, C0, hB0, hC0, hBC⟩
    refine ae_hasSumset_of_strategy (pairsOf_strategy (B0 := B0) (C0 := C0) fun U V hU hV =>
      ⟨tsum_indicator_eq_top (hC0.sdiff V.finite_toSet) (two_inv_pow_ne_zero U.card)
        fun c hc => le_of_eq ?_, tsum_indicator_eq_top (hB0.sdiff U.finite_toSet)
        (two_inv_pow_ne_zero V.card) fun b hb => le_of_eq ?_⟩)
    · rw [w_eq, ← Finset.prod_const]
      refine Finset.prod_congr rfl fun u hu => ?_
      rw [pe_pD, if_pos (show x (c + u) = true from by
        rw [add_comm]; exact hBC ⟨u, hU hu, c, hc.1, rfl⟩)]
    · rw [w_eq, ← Finset.prod_const]
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [pe_pD, if_pos (show x (b + v) = true from hBC ⟨b, hb.1, v, hV hv, rfl⟩)]

lemma pD_mem_iff1 (plus : Bool) (x : ℕ → Bool) :
    cubeIncl (pD x) ∈ frakA1 plus ↔ x ∈ frakD1 plus := by
  constructor
  · intro h
    have h' : ∀ᵐ ω ∂bernoulliSeq (cubeIncl (pD x)), Has1 plus (randSet ω) := h
    obtain ⟨ω, h1, h2⟩ := (h'.and (ae_finite_outside x)).exists
    exact has1_of_finite_diff h1 h2
  · rintro ⟨B0, hB0, hBB, h2⟩
    refine ae_has1_of_strategy (setsOf_strategy (B0 := B0) fun U hU =>
      tsum_indicator_eq_top (hB0.sdiff U.finite_toSet) (two_inv_pow_ne_zero (U.card + 1))
        fun y hy => ?_)
    have hw : w (cubeIncl (pD x)) U y = 2⁻¹ ^ U.card := by
      rw [w_eq, ← Finset.prod_const]
      refine Finset.prod_congr rfl fun u hu => ?_
      rw [pe_pD, if_pos (show x (y + u) = true from
        hBB ⟨y, hy.1, u, hU hu, fun e => hy.2 (e ▸ hu), rfl⟩)]
    cases plus
    · simp only [wstar, Bool.false_eq_true, if_false, hw, pow_succ]
      exact mul_le_of_le_one_right zero_le (ENNReal.inv_le_one.2 one_le_two)
    · simp only [wstar, if_true, hw, pe_pD]
      rw [if_pos (show x (2 * y) = true from h2 rfl y hy.1), pow_succ, mul_comm]

/-- Paper, Theorem \ref{IB:thm:nonborel}\ref{IB:nb2}, for `B + C` in `(0,1)^ℕ`. -/
theorem thm_nonborel_b_BC_open {lam : ℕ → ℕ} (h : IsRigidSeq lam) :
    AnalyticSet frakA_BC' ∧
    (∃ g : TreeSp → OpenCube, Continuous g ∧ ∀ T ∈ TrSet, (g T ∈ frakA_BC' ↔ T ∈ IFSet)) ∧
    (KechrisIFComplete → Sigma11Complete frakA_BC') ∧
    (KechrisIFNotBorel → ¬ MeasurableSet[borel OpenCube] frakA_BC') := by
  have hA : AnalyticSet frakA_BC' := analyticSet_frakA_BC.preimage continuous_cubeIncl
  have hred : ∀ T ∈ TrSet, (pD (DBC lam T) ∈ frakA_BC' ↔ T ∈ IFSet) := fun T hT => by
    rw [← DBC_reduction h hT]
    exact pD_mem_iff _
  have hc := continuous_pD.comp (continuous_DBC lam)
  exact ⟨hA, ⟨_, hc, hred⟩, complete_of_reduction hA _ hc hred⟩

/-- Paper, Theorem \ref{IB:thm:nonborel}\ref{IB:nb2}, for `B ⊕ B` and `B + B` in `(0,1)^ℕ`. -/
theorem thm_nonborel_b_1_open {lam : ℕ → ℕ} (h : IsRigidSeq lam) (plus : Bool) :
    AnalyticSet (frakA1' plus) ∧
    (∃ g : TreeSp → OpenCube, Continuous g ∧ ∀ T ∈ TrSet, (g T ∈ frakA1' plus ↔ T ∈ IFSet)) ∧
    (KechrisIFComplete → Sigma11Complete (frakA1' plus)) ∧
    (KechrisIFNotBorel → ¬ MeasurableSet[borel OpenCube] (frakA1' plus)) := by
  have hA : AnalyticSet (frakA1' plus) := (analyticSet_frakA1 plus).preimage continuous_cubeIncl
  have hred : ∀ T ∈ TrSet, (pD (D1 lam plus T) ∈ frakA1' plus ↔ T ∈ IFSet) := fun T hT => by
    rw [← D1_reduction h plus hT]
    exact pD_mem_iff1 plus _
  have hc := continuous_pD.comp (continuous_D1 lam plus)
  exact ⟨hA, ⟨_, hc, hred⟩, complete_of_reduction hA _ hc hred⟩

/-! ### Part (c): the poset `𝒩` and the reduction into `{p ∈ (0,1)^ℕ : p_n → 0}` -/

/-- Elements `x = (s, η)` of `𝒩`, with `s ∈ ℕ^{<ℕ}` and `η` a finite `0`-`1` sequence. -/
abbrev NNode := List ℕ × List Bool

/-- `ℓ(s) = |s| + ∑ᵢ sᵢ`. -/
def ell (s : List ℕ) : ℕ := s.length + s.sum

/-- `x = (s, η) ∈ 𝒩` iff `η ∈ {0,1}^{ℓ(s)}`. -/
def InN (x : NNode) : Prop := x.2.length = ell x.1

/-- The partial order `(s, η) ≼ (s', η')` iff `s ⊆ s'` and `η` is an initial segment of `η'`. -/
def LeN (x y : NNode) : Prop := x.1 <+: y.1 ∧ x.2 <+: y.2

/-- Comparability in `𝒩`. -/
def CompN (x y : NNode) : Prop := LeN x y ∨ LeN y x

lemma CompN.symm {x y : NNode} (h : CompN x y) : CompN y x := Or.symm h

lemma LeN.trans {x y z : NNode} (h1 : LeN x y) (h2 : LeN y z) : LeN x z :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

lemma ell_mono {s s' : List ℕ} (h : s <+: s') : ell s ≤ ell s' := by
  obtain ⟨r, rfl⟩ := h
  simp [ell, List.sum_append]; omega

lemma ell_ge_length (s : List ℕ) : s.length ≤ ell s := Nat.le_add_right _ _

lemma ell_res (z : ℕ → ℕ) (m : ℕ) : m ≤ ell (res z m) := by
  have := ell_ge_length (res z m); rwa [res_length] at this

lemma eq_of_LeN_of_ell {x y : NNode} (hx : InN x) (hy : InN y) (h : LeN x y)
    (he : ell y.1 ≤ ell x.1) : x = y := by
  have h2 : x.2 = y.2 := h.2.eq_of_length_le (by rw [hx, hy]; exact he)
  have h1 : x.1 = y.1 := by
    obtain ⟨r, hr⟩ := h.1
    have : ell y.1 = ell x.1 + r.length + r.sum := by
      rw [← hr]; simp [ell, List.sum_append]; ring
    have hr0 : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [← hr, hr0, List.append_nil]
  exact Prod.ext h1 h2

/-- Every element of `𝒩` has finitely many predecessors. -/
lemma finite_preds (y : NNode) : {x : NNode | LeN x y}.Finite := by
  refine ((List.finite_toSet y.1.inits).prod (List.finite_toSet y.2.inits)).subset ?_
  rintro x ⟨h1, h2⟩
  exact ⟨(List.mem_inits _ _).2 h1, (List.mem_inits _ _).2 h2⟩

lemma finite_ell_le (L : ℕ) : {s : List ℕ | ell s ≤ L}.Finite := by
  refine ((List.finite_length_le (Fin (L + 1)) L).image (List.map Fin.val)).subset ?_
  intro s hs
  simp only [Set.mem_ofPred_eq, ell] at hs
  have hle : ∀ i ∈ s, i < L + 1 := fun i hi => by
    have := List.le_sum_of_mem hi; omega
  refine ⟨s.attach.map fun i => ⟨i.1, hle i.1 i.2⟩, by simp; omega, ?_⟩
  simp only [List.map_map]
  conv_rhs => rw [← List.attach_map_subtype_val s]
  rfl

/-- For each `L`, finitely many `x ∈ 𝒩` have `ℓ(x) ≤ L`. -/
lemma finite_InN_ell_le (L : ℕ) : {x : NNode | InN x ∧ ell x.1 ≤ L}.Finite := by
  refine ((finite_ell_le L).prod (List.finite_length_le Bool L)).subset ?_
  rintro x ⟨hx, hL⟩
  exact ⟨hL, by show x.2.length ≤ L; rw [hx]; exact hL⟩

lemma CompN_of_LeN_LeN {x x' r : NNode} (hx : InN x) (hx' : InN x') (h : LeN x r)
    (h' : LeN x' r) : CompN x x' := by
  rcases List.prefix_or_prefix_of_prefix h.1 h'.1 with a | a
  · have hl : x.2.length ≤ x'.2.length := by rw [hx, hx']; exact ell_mono a
    exact Or.inl ⟨a, List.prefix_of_prefix_length_le h.2 h'.2 hl⟩
  · have hl : x'.2.length ≤ x.2.length := by rw [hx, hx']; exact ell_mono a
    exact Or.inr ⟨a, List.prefix_of_prefix_length_le h'.2 h.2 hl⟩

/-- Two infinite subsets `Q₁, Q₂` of `𝒩` with all cross pairs comparable: `Q₁` is a chain
(this only uses that every element of `𝒩` has finitely many predecessors). -/
lemma chainN_of_cross {Q1 Q2 : Set NNode} (hQ1 : ∀ q ∈ Q1, InN q) (h2 : Q2.Infinite)
    (hc : ∀ q ∈ Q1, ∀ q' ∈ Q2, CompN q q') : ∀ q ∈ Q1, ∀ q' ∈ Q1, CompN q q' := by
  intro q hq q' hq'
  by_contra hnc
  apply h2
  refine (finite_preds q).subset fun r hr => ?_
  show LeN r q
  rcases hc q hq r hr with h | h
  · rcases hc q' hq' r hr with h' | h'
    · exact absurd (CompN_of_LeN_LeN (hQ1 q hq) (hQ1 q' hq') h h') hnc
    · exact absurd (Or.inl (h.trans h')) hnc
  · exact h

/-- A tree `T` such that `𝒩` contains two infinite sets `Q₁, Q₂`, all cross pairs comparable and
the first coordinates of `Q₁` in `T`, has an infinite branch. -/
lemma branch_of_crossN {T : TreeSp} (hT : IsTree T) {Q1 Q2 : Set NNode} (h1 : Q1.Infinite)
    (h2 : Q2.Infinite) (hQ1 : ∀ q ∈ Q1, InN q) (hQT : ∀ q ∈ Q1, T q.1 = true)
    (hc : ∀ q ∈ Q1, ∀ q' ∈ Q2, CompN q q') : T ∈ IFSet := by
  have hch := chainN_of_cross hQ1 h2 hc
  -- distinct comparable elements of `𝒩` have distinct first coordinates
  have hinj : Set.InjOn Prod.fst Q1 := by
    intro q hq q' hq' e
    rcases hch q hq q' hq' with h | h
    · exact eq_of_LeN_of_ell (hQ1 q hq) (hQ1 q' hq') h (by rw [e])
    · exact (eq_of_LeN_of_ell (hQ1 q' hq') (hQ1 q hq) h (by rw [e])).symm
  refine branch_of_chain hT (h1.image hinj) (by rintro _ ⟨q, hq, rfl⟩; exact hQT q hq) ?_
  rintro _ ⟨q, hq, rfl⟩ _ ⟨q', hq', rfl⟩
  rcases hch q hq q' hq' with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

section NB3

variable {lam : ℕ → ℕ}

/-- The labels `β_x = λ_{2⌜x⌝}`, `γ_x = λ_{2⌜x⌝+1}` of `x ∈ 𝒩`. -/
def bN (lam : ℕ → ℕ) (x : NNode) : ℕ := lam (2 * Encodable.encode x)

/-- See `bN`. -/
def gN (lam : ℕ → ℕ) (x : NNode) : ℕ := lam (2 * Encodable.encode x + 1)

lemma bN_injective (h : IsRigidSeq lam) : Function.Injective (bN lam) := fun a b e =>
  Encodable.encode_injective (by have := h.injective e; omega)

lemma gN_injective (h : IsRigidSeq lam) : Function.Injective (gN lam) := fun a b e =>
  Encodable.encode_injective (by have := h.injective e; omega)

lemma N_rep_unique (h : IsRigidSeq lam) {x y x' y' : NNode}
    (e : bN lam x + gN lam y = bN lam x' + gN lam y') : x = x' ∧ y = y' := by
  rcases lem_rigid_pair h e with ⟨e1, e2⟩ | ⟨e1, -⟩
  · exact ⟨Encodable.encode_injective (by omega), Encodable.encode_injective (by omega)⟩
  · omega

/-- Valid pairs: `x, y ∈ 𝒩` comparable. -/
def ValidN (x y : NNode) : Prop := InN x ∧ InN y ∧ CompN x y

/-- `θ_L = 1/(L+2)`. -/
noncomputable def thetaR (L : ℕ) : ℝ := ((L : ℝ) + 2)⁻¹

lemma thetaR_mem (L : ℕ) : thetaR L ∈ Ioo01 :=
  ⟨by unfold thetaR; positivity, inv_lt_one_of_one_lt₀ (by
    have := (Nat.cast_nonneg L : (0 : ℝ) ≤ L); linarith)⟩

/-- The value of `p^T` at `n = β_x + γ_y` (`q = (x, y)` valid). -/
noncomputable def pTval (T : TreeSp) (n : ℕ) (q : NNode × NNode) : Ioo01 :=
  if T q.1.1 = true ∧ T q.2.1 = true then ⟨thetaR (max (ell q.1.1) (ell q.2.1)), thetaR_mem _⟩
  else ⟨(1 / 2) ^ (n + 2), pow_half_mem n⟩

open Classical in
/-- The reduction `g(T) = p^T` of Theorem \ref{IB:thm:nonborel}\ref{IB:nb3}:
`p^T_n = θ_{max(ℓ(x), ℓ(y))}` if `n = β_x + γ_y` with `x, y ∈ 𝒩` comparable and with first
coordinates in `T`, and `p^T_n = 2^{-n-2}` otherwise. -/
noncomputable def pT (lam : ℕ → ℕ) (T : TreeSp) : OpenCube := fun n =>
  if hn : ∃ q : NNode × NNode, ValidN q.1 q.2 ∧ n = bN lam q.1 + gN lam q.2 then
    pTval T n hn.choose else ⟨(1 / 2) ^ (n + 2), pow_half_mem n⟩

lemma continuous_pT (lam : ℕ → ℕ) : Continuous (pT lam) := by
  refine continuous_pi fun n => ?_
  unfold pT
  split_ifs with hn
  · exact (continuous_of_discreteTopology (f := fun u : Bool × Bool =>
      if u.1 = true ∧ u.2 = true then
        (⟨thetaR (max (ell hn.choose.1.1) (ell hn.choose.2.1)), thetaR_mem _⟩ : Ioo01)
      else ⟨(1 / 2) ^ (n + 2), pow_half_mem n⟩)).comp
      ((continuous_apply (A := fun _ : List ℕ => Bool) hn.choose.1.1).prodMk
        (continuous_apply (A := fun _ : List ℕ => Bool) hn.choose.2.1))
  · exact continuous_const

/-- The support of `q^T`. -/
def suppQ (lam : ℕ → ℕ) (T : TreeSp) : Set ℕ :=
  {n | ∃ x y, ValidN x y ∧ T x.1 = true ∧ T y.1 = true ∧ n = bN lam x + gN lam y}

lemma pT_val (h : IsRigidSeq lam) {T : TreeSp} {x y : NNode} (hv : ValidN x y)
    (hx : T x.1 = true) (hy : T y.1 = true) :
    cubeIncl (pT lam T) (bN lam x + gN lam y) = thetaI (max (ell x.1) (ell y.1) + 1) := by
  have hn : ∃ q : NNode × NNode, ValidN q.1 q.2 ∧
      bN lam x + gN lam y = bN lam q.1 + gN lam q.2 := ⟨(x, y), hv, rfl⟩
  obtain ⟨e1, e2⟩ := N_rep_unique h hn.choose_spec.2
  apply Subtype.ext
  simp only [cubeIncl, pT, dif_pos hn, pTval, ← e1, ← e2, hx, hy, and_self, if_true, thetaR,
    thetaI]
  push_cast; ring

lemma pe_pT_val (h : IsRigidSeq lam) {T : TreeSp} {x y : NNode} (hv : ValidN x y)
    (hx : T x.1 = true) (hy : T y.1 = true) :
    pe (cubeIncl (pT lam T)) (bN lam x + gN lam y) = θE (max (ell x.1) (ell y.1) + 1) := by
  unfold pe; rw [pT_val h hv hx hy, coe_thetaI]

lemma pe_pT_le (T : TreeSp) {n : ℕ} (hn : n ∉ suppQ lam T) :
    pe (cubeIncl (pT lam T)) n ≤ 2⁻¹ ^ n := by
  have hval : cubeIncl (pT lam T) n = ⟨(1 / 2) ^ (n + 2), (pow_half_mem n).1.le,
      (pow_half_mem n).2.le⟩ := by
    apply Subtype.ext
    simp only [cubeIncl, pT]
    split_ifs with h1
    · simp only [pTval]
      split_ifs with h2
      · exact absurd ⟨_, _, h1.choose_spec.1, h2.1, h2.2, h1.choose_spec.2⟩ hn
      · rfl
    · rfl
  have : toNNReal ⟨((1 / 2 : ℝ) ^ (n + 2)), (pow_half_mem n).1.le, (pow_half_mem n).2.le⟩ =
      2⁻¹ ^ (n + 2) := by
    ext; simp [toNNReal]; rfl
  unfold pe
  rw [hval, this, ENNReal.coe_pow, ENNReal.coe_inv two_ne_zero]
  exact pow_le_pow_of_le_one (by simp) (ENNReal.inv_le_one.2 one_le_two) (by omega)

end NB3

section NB3b

variable {lam : ℕ → ℕ}

/-- `𝔆 = {p ∈ (0,1)^ℕ : p_n → 0}`. -/
def frakC : Set OpenCube := {p | Tendsto (fun n => ((p n : Ioo01) : ℝ)) atTop (𝓝 0)}

lemma pT_mem_frakC (T : TreeSp) : pT lam T ∈ frakC := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans (pT lam T n).2.1,
    fun ε hε => ?_⟩
  -- the set of `n` with `p^T_n ≥ ε` is finite
  obtain ⟨N, hN⟩ := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).eventually (gt_mem_nhds hε) |>.exists_forall_of_atTop
  set L0 := ⌈ε⁻¹⌉₊
  set F := {x : NNode | InN x ∧ ell x.1 ≤ L0}
  have hF : (F ×ˢ F).Finite := (finite_InN_ell_le L0).prod (finite_InN_ell_le L0)
  have hfin : {n | ε ≤ ((pT lam T n : Ioo01) : ℝ)}.Finite := by
    refine ((Set.finite_Iio (N + 2)).union (hF.image fun q => bN lam q.1 + gN lam q.2)).subset ?_
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    by_cases hsmall : n < N + 2
    · exact Or.inl hsmall
    right
    have hnot : ¬ ε ≤ (1 / 2 : ℝ) ^ (n + 2) := not_le.2 (hN _ (by omega))
    unfold pT at hn
    split_ifs at hn with h1
    · unfold pTval at hn
      split_ifs at hn with h2
      · refine ⟨h1.choose, ⟨⟨h1.choose_spec.1.1, ?_⟩, ⟨h1.choose_spec.1.2.1, ?_⟩⟩,
          h1.choose_spec.2.symm⟩
        all_goals
          by_contra hL
          push Not at hL
          have hle : ((L0 : ℝ) + 2)⁻¹ < ε := by
            have h3 : ε⁻¹ ≤ (L0 : ℝ) := Nat.le_ceil _
            rw [inv_lt_comm₀ (by positivity) hε]
            linarith
          have hmono : thetaR (max (ell h1.choose.1.1) (ell h1.choose.2.1)) ≤ ((L0 : ℝ) + 2)⁻¹ := by
            unfold thetaR
            refine inv_anti₀ (by positivity) ?_
            have : (L0 : ℝ) ≤ (max (ell h1.choose.1.1) (ell h1.choose.2.1) : ℕ) := by
              exact_mod_cast (show L0 ≤ max (ell h1.choose.1.1) (ell h1.choose.2.1) by omega)
            linarith
          exact absurd hn (not_le.2 (hmono.trans_lt hle))
      · exact absurd hn hnot
    · exact absurd hn hnot
  filter_upwards [hfin.eventually_cofinite_notMem.filter_mono Nat.cofinite_eq_atTop.ge] with n hn
  exact not_le.1 hn

/-- A general first Borel–Cantelli statement: if `p_n ≤ 2^{-n}` off `D`, then a.s. `A \ D` is
finite. -/
lemma ae_finite_outside_gen (p : ℕ → I) (D : Set ℕ) (hp : ∀ n ∉ D, pe p n ≤ 2⁻¹ ^ n) :
    ∀ᵐ ω ∂bernoulliSeq p, {n | n ∈ randSet ω ∧ n ∉ D}.Finite := by
  classical
  let s : ℕ → Set (ℕ → Bool) := fun n => if n ∈ D then ∅ else cyl {n}
  have hs : ∑' n, bernoulliSeq p (s n) ≠ ∞ := by
    have hle : ∀ n, bernoulliSeq p (s n) ≤ 2⁻¹ ^ n := by
      intro n
      by_cases hx : n ∈ D
      · simp [s, hx]
      · simp only [s, hx, if_false]
        rw [measure_cyl, Finset.prod_singleton]
        exact hp n hx
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  filter_upwards [ae_finite_setOfPred_mem hs] with ω hω
  refine hω.subset fun n hn => ?_
  simp only [s, Set.mem_ofPred_eq, if_neg hn.2]
  exact fun j hj => by rw [Finset.mem_singleton] at hj; subst hj; exact hn.1

/-- The generic node-extraction step (as in `nodes_of_shift`), for labels indexed by an encodable
type and a relation `R` between the `β`- and the `γ`-index. -/
lemma cross_of_shift {α : Type*} [Encodable α] [Inhabited α] (h : IsRigidSeq lam) {B C : Set ℕ} {t : ℤ}
    {jb jc : ℕ → ℕ} (hjb : ∀ b ∈ B, (b : ℤ) - t = lam (jb b))
    (hjc : ∀ c ∈ C, (c : ℤ) + t = lam (jc c)) (R : α → α → Prop) (P : α → Prop)
    (hmem : ∀ b ∈ B, ∀ c ∈ C, ∃ x y, P x ∧ P y ∧ R x y ∧
      b + c = lam (2 * Encodable.encode x) + lam (2 * Encodable.encode y + 1))
    (hB : B.Infinite) (hC : C.Infinite) :
    ∃ Q1 Q2 : Set α, Q1.Infinite ∧ Q2.Infinite ∧ (∀ q ∈ Q1, P q) ∧
      ∀ q ∈ Q1, ∀ q' ∈ Q2, R q q' := by
  have hpair : ∀ b ∈ B, ∀ c ∈ C, ∃ x y, P x ∧ P y ∧ R x y ∧
      ((jb b = 2 * Encodable.encode x ∧ jc c = 2 * Encodable.encode y + 1) ∨
       (jb b = 2 * Encodable.encode y + 1 ∧ jc c = 2 * Encodable.encode x)) := by
    intro b hb c hc
    obtain ⟨x, y, h1, h2, h3, e⟩ := hmem b hb c hc
    exact ⟨x, y, h1, h2, h3, rigid_pair_shift h (hjb b hb) (hjc c hc) e⟩
  have hinjB : ∀ b ∈ B, ∀ b' ∈ B, jb b = jb b' → b = b' := fun b hb b' hb' e => by
    have h1 := hjb b hb; have h2 := hjb b' hb'; rw [e] at h1
    exact_mod_cast (by linarith : (b : ℤ) = b')
  have hinjC : ∀ c ∈ C, ∀ c' ∈ C, jc c = jc c' → c = c' := fun c hc c' hc' e => by
    have h1 := hjc c hc; have h2 := hjc c' hc'; rw [e] at h1
    exact_mod_cast (by linarith : (c : ℤ) = c')
  obtain ⟨b1, hb1⟩ := hB.nonempty
  obtain ⟨c1, hc1⟩ := hC.nonempty
  rcases Nat.even_or_odd (jb b1) with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hCodd : ∀ c ∈ C, ∃ y, jc c = 2 * Encodable.encode y + 1 ∧ P y := by
      intro c hc
      obtain ⟨x, y, -, h2, -, ⟨-, e⟩ | ⟨e, -⟩⟩ := hpair b1 hb1 c hc
      · exact ⟨y, e, h2⟩
      · omega
    obtain ⟨r1, hr1, -⟩ := hCodd c1 hc1
    have hBev : ∀ b ∈ B, ∃ x, jb b = 2 * Encodable.encode x ∧ P x := by
      intro b hb
      obtain ⟨x, y, h1, -, -, ⟨e, -⟩ | ⟨-, e⟩⟩ := hpair b hb c1 hc1
      · exact ⟨x, e, h1⟩
      · omega
    choose! f hf hfP using hBev
    choose! g hg hgP using hCodd
    refine ⟨f '' B, g '' C, hB.image fun b hb b' hb' e => hinjB b hb b' hb'
      (by rw [hf b hb, hf b' hb', e]), hC.image fun c hc c' hc' e => hinjC c hc c' hc'
      (by rw [hg c hc, hg c' hc', e]), by rintro _ ⟨b, hb, rfl⟩; exact hfP b hb, ?_⟩
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    obtain ⟨x, y, -, -, hxy, ⟨e1, e2⟩ | ⟨e1, -⟩⟩ := hpair b hb c hc
    · have h1 : f b = x := Encodable.encode_injective (by have := hf b hb; omega)
      have h2 : g c = y := Encodable.encode_injective (by have := hg c hc; omega)
      rw [h1, h2]; exact hxy
    · have := hf b hb; omega
  · have hCev : ∀ c ∈ C, ∃ x, jc c = 2 * Encodable.encode x ∧ P x := by
      intro c hc
      obtain ⟨x, y, h1, -, -, ⟨e, -⟩ | ⟨-, e⟩⟩ := hpair b1 hb1 c hc
      · omega
      · exact ⟨x, e, h1⟩
    obtain ⟨r1, hr1, -⟩ := hCev c1 hc1
    have hBodd : ∀ b ∈ B, ∃ y, jb b = 2 * Encodable.encode y + 1 ∧ P y := by
      intro b hb
      obtain ⟨x, y, -, h2, -, ⟨-, e⟩ | ⟨e, -⟩⟩ := hpair b hb c1 hc1
      · omega
      · exact ⟨y, e, h2⟩
    choose! f hf hfP using hBodd
    choose! g hg hgP using hCev
    refine ⟨g '' C, f '' B, hC.image fun c hc c' hc' e => hinjC c hc c' hc'
      (by rw [hg c hc, hg c' hc', e]), hB.image fun b hb b' hb' e => hinjB b hb b' hb'
      (by rw [hf b hb, hf b' hb', e]), by rintro _ ⟨c, hc, rfl⟩; exact hgP c hc, ?_⟩
    rintro _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨x, y, -, -, hxy, ⟨-, e2⟩ | ⟨e1, e2⟩⟩ := hpair b hb c hc
    · have := hg c hc; omega
    · have h1 : f b = y := Encodable.encode_injective (by have := hf b hb; omega)
      have h2 : g c = x := Encodable.encode_injective (by have := hg c hc; omega)
      rw [h1, h2]; exact hxy

/-- The converse half of Theorem \ref{IB:thm:nonborel}\ref{IB:nb3}: if `P_{p^T}(E_{BC}) > 0` (here:
`= 1`), then `T` has an infinite branch. -/
theorem pT_converse (h : IsRigidSeq lam) {T : TreeSp} (hT : IsTree T)
    (hA : ∀ᵐ ω ∂bernoulliSeq (cubeIncl (pT lam T)), HasSumset (randSet ω)) : T ∈ IFSet := by
  obtain ⟨ω, h1, h2⟩ := (hA.and (ae_finite_outside_gen _ (suppQ lam T)
    fun n hn => pe_pT_le T hn)).exists
  obtain ⟨B, C, hB, hC, hBC⟩ := hasSumset_of_finite_diff h1 h2
  have hmem : ∀ b ∈ B, ∀ c ∈ C, ∃ x y, (InN x ∧ T x.1 = true) ∧ (InN y ∧ T y.1 = true) ∧
      CompN x y ∧ b + c = lam (2 * Encodable.encode x) + lam (2 * Encodable.encode y + 1) := by
    intro b hb c hc
    obtain ⟨x, y, ⟨hx, hy, hxy⟩, hTx, hTy, e⟩ := hBC ⟨b, hb, c, hc, rfl⟩
    exact ⟨x, y, ⟨hx, hTx⟩, ⟨hy, hTy⟩, hxy, e⟩
  obtain ⟨t, jb, jc, hjb, hjc⟩ := cor_R_nat h hB hC fun b hb c hc => by
    obtain ⟨x, y, -, -, -, e⟩ := hmem b hb c hc
    exact ⟨_, _, by rw [← Nat.cast_add, e]; push_cast; rfl⟩
  obtain ⟨Q1, Q2, hQ1, hQ2, hP, hc⟩ := cross_of_shift h hjb hjc CompN
    (fun x => InN x ∧ T x.1 = true) hmem hB hC
  exact branch_of_crossN hT hQ1 hQ2 (fun q hq => (hP q hq).1) (fun q hq => (hP q hq).2) hc

end NB3b

section NB3c

variable {lam : ℕ → ℕ}

/-- For all large `j`, `M (a + j + 2)^k ≤ 2^j`. -/
lemma eventually_two_pow_ge (M a k : ℕ) : ∃ J, ∀ j ≥ J, M * (a + j + 2) ^ k ≤ 2 ^ j := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (r := 2) one_lt_two
  have hpos : (0 : ℝ) < ((M : ℝ) * 2 ^ (a + 2) + 1)⁻¹ := by positivity
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
  refine ⟨N, fun j hj => ?_⟩
  have h1 := hN (a + j + 2) (by omega)
  rw [div_lt_iff₀ (by positivity), inv_mul_eq_div, lt_div_iff₀ (by positivity)] at h1
  set b : ℝ := 2 ^ (a + 2)
  set X : ℝ := ((a + j + 2 : ℕ) : ℝ) ^ k
  have hb : 0 < b := by positivity
  have hX : 0 ≤ X := by positivity
  have e : (2 : ℝ) ^ (a + j + 2) = 2 ^ j * b := by rw [← pow_add]; ring_nf
  rw [e] at h1
  have h2 : (M : ℝ) * X * b < 2 ^ j * b := by nlinarith
  have h3 : (M : ℝ) * X < 2 ^ j := lt_of_mul_lt_mul_right h2 hb.le
  have h4 : ((M * (a + j + 2) ^ k : ℕ) : ℝ) = (M : ℝ) * X := by simp only [X]; push_cast; ring
  exact_mod_cast (h4 ▸ h3).le

/-- The divergence estimate in Theorem \ref{IB:thm:nonborel}\ref{IB:nb3}: below `δ = (z|d, η)`,
the elements `y = (z|m, η')` (`m > d`, `η'` extending `η`) contribute `∑ θ_{ℓ(y)}^k = ∞`. -/
lemma tsum_candidates (z : ℕ → ℕ) (d : ℕ) (δ : NNode) (hδ1 : δ.1 = res z d) (hδ2 : InN δ)
    (k : ℕ) (F : NNode → ℕ) (hF : Function.Injective F) (g : ℕ → ℝ≥0∞)
    (hg : ∀ m, d < m → ∀ y : NNode, InN y → y.1 = res z m → LeN δ y →
      θE (ell y.1 + 1) ^ k ≤ g (F y)) : ∑' n, g n = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨M, hM⟩ := exists_nat_gt (r : ℝ)
  set a := ell (res z d)
  obtain ⟨J, hJ⟩ := eventually_two_pow_ge M a k
  set m := d + 1 + a + J
  set ℓm := ell (res z m)
  have hℓm : m ≤ ℓm := ell_res z m
  have ha : a ≤ ℓm := ell_mono (res_prefix z (by omega))
  set j := ℓm - a
  have hδlen : δ.2.length = a := by rw [hδ2, hδ1]
  let y : List.Vector Bool j → NNode := fun ζ => (res z m, δ.2 ++ ζ.1)
  have hyN : ∀ ζ, InN (y ζ) := fun ζ => by
    show (δ.2 ++ ζ.1).length = ell (res z m)
    rw [List.length_append, hδlen, ζ.2]; omega
  have hyle : ∀ ζ, LeN δ (y ζ) := fun ζ =>
    ⟨by rw [hδ1]; exact res_prefix z (by omega), List.prefix_append _ _⟩
  have hinj : Function.Injective fun ζ => F (y ζ) := by
    intro ζ ζ' e
    have := congrArg Prod.snd (hF e)
    exact Subtype.ext (List.append_cancel_left this)
  have h1 : ∑' ζ : List.Vector Bool j, g (F (y ζ)) ≤ ∑' n, g n :=
    ENNReal.tsum_comp_le_tsum_of_injective (f := fun ζ => F (y ζ)) hinj g
  have h2 : ∑' _ζ : List.Vector Bool j, θE (ℓm + 1) ^ k ≤ ∑' ζ : List.Vector Bool j, g (F (y ζ)) :=
    ENNReal.tsum_le_tsum fun ζ => hg m (by omega) (y ζ) (hyN ζ) rfl (hyle ζ)
  have h3 : ∑' _ζ : List.Vector Bool j, θE (ℓm + 1) ^ k = ((2 ^ j : ℕ) : ℝ≥0∞) * θE (ℓm + 1) ^ k := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, card_vector, Fintype.card_bool,
      nsmul_eq_mul]
  have h4 : ((M : ℕ) : ℝ≥0∞) ≤ ((2 ^ j : ℕ) : ℝ≥0∞) * θE (ℓm + 1) ^ k := by
    rw [θE, ← ENNReal.inv_pow, ← div_eq_mul_inv,
      ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
    have hj := hJ j (by omega)
    have e : a + j + 2 = ℓm + 1 + 1 := by omega
    rw [e] at hj
    have : ((M * (ℓm + 1 + 1) ^ k : ℕ) : ℝ≥0∞) ≤ ((2 ^ j : ℕ) : ℝ≥0∞) := by exact_mod_cast hj
    simpa using this
  have hr : (r : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hM.le
  exact hr.trans (h4.trans (h3 ▸ h2 |>.trans h1))

/-- The strategy of Theorem \ref{IB:thm:nonborel}\ref{IB:nb3} along a branch `z`: the pairs
`({β_x}_{x ∈ P}, {γ_y}_{y ∈ Q})` with `P, Q ⊆ 𝒩_z` finite and `P ∪ Q` a chain. -/
def Sbranch (lam : ℕ → ℕ) (z : ℕ → ℕ) : Set (Finset ℕ × Finset ℕ) :=
  {q | ∃ P Q : Finset NNode, (∀ x ∈ P ∪ Q, InN x ∧ ∃ m, x.1 = res z m) ∧
    q.1 = P.image (bN lam) ∧ q.2 = Q.image (gN lam) ∧ ∀ x ∈ P ∪ Q, ∀ y ∈ P ∪ Q, CompN x y}

lemma LeN.refl (x : NNode) : LeN x x := ⟨List.prefix_refl _, List.prefix_refl _⟩

lemma chainN_ub (z : ℕ → ℕ) {R : Finset NNode} (hR : ∀ x ∈ R, InN x ∧ ∃ m, x.1 = res z m)
    (hc : ∀ x ∈ R, ∀ y ∈ R, CompN x y) :
    ∃ δ : NNode, ∃ d, δ.1 = res z d ∧ InN δ ∧ ∀ x ∈ R, LeN x δ := by
  rcases R.eq_empty_or_nonempty with rfl | hne
  · exact ⟨([], []), 0, by simp [res], by simp [InN, ell], by simp⟩
  · obtain ⟨δ, hδ, hmax⟩ := R.exists_max_image (fun x => ell x.1) hne
    obtain ⟨hδN, d, hd⟩ := hR δ hδ
    refine ⟨δ, d, hd, hδN, fun x hx => ?_⟩
    rcases hc x hx δ hδ with h1 | h1
    · exact h1
    · rw [eq_of_LeN_of_ell hδN (hR x hx).1 h1 (hmax x hx)]; exact LeN.refl _

lemma prod_pe_pT_eq (h : IsRigidSeq lam) {T : TreeSp} (z : ℕ → ℕ)
    (hz : ∀ n, T (res z n) = true) {P : Finset NNode}
    (hP : ∀ x ∈ P, InN x ∧ ∃ m, x.1 = res z m) {y : NNode} (hy : InN y) (m : ℕ)
    (hym : y.1 = res z m) (hle : ∀ x ∈ P, LeN x y) :
    (∏ x ∈ P, pe (cubeIncl (pT lam T)) (bN lam x + gN lam y) = θE (ell y.1 + 1) ^ P.card) ∧
    (∏ x ∈ P, pe (cubeIncl (pT lam T)) (bN lam y + gN lam x) = θE (ell y.1 + 1) ^ P.card) := by
  have hTx : ∀ x ∈ P, T x.1 = true := fun x hx => by
    obtain ⟨-, m', hm'⟩ := hP x hx; rw [hm']; exact hz m'
  have hTy : T y.1 = true := by rw [hym]; exact hz m
  have hmax : ∀ x ∈ P, max (ell x.1) (ell y.1) = ell y.1 := fun x hx =>
    max_eq_right (ell_mono (hle x hx).1)
  constructor
  · rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [pe_pT_val h ⟨(hP x hx).1, hy, Or.inl (hle x hx)⟩ (hTx x hx) hTy, hmax x hx]
  · rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [pe_pT_val h ⟨hy, (hP x hx).1, Or.inr (hle x hx)⟩ hTy (hTx x hx), max_comm, hmax x hx]

/-- The direct half of Theorem \ref{IB:thm:nonborel}\ref{IB:nb3}: if `z` is an infinite branch of
`T`, then `Sbranch z` is a `BC`-strategy for `p^T`, so `P_{p^T}(E_{BC}) = 1`. -/
theorem pT_strategy (h : IsRigidSeq lam) {T : TreeSp} (z : ℕ → ℕ)
    (hz : ∀ n, T (res z n) = true) : IsBCStrategy (cubeIncl (pT lam T)) (Sbranch lam z) := by
  classical
  refine ⟨⟨∅, ∅, by simp, by simp, by simp, by simp⟩, ?_⟩
  rintro U V ⟨P, Q, hPQ, rfl, rfl, hch⟩
  obtain ⟨δ, d, hδ1, hδ2, hδ⟩ := chainN_ub z hPQ hch
  have hnot : ∀ m, d < m → ∀ y : NNode, y.1 = res z m → LeN δ y → y ∉ P ∪ Q := by
    intro m hm y hym hδy hy
    have h1 := (hδ y hy).1
    have h2 := hδy.1
    rw [hym, hδ1] at h1 h2
    have := congrArg List.length (h1.eq_of_length_le h2.length_le)
    rw [res_length, res_length] at this
    omega
  have hext : ∀ y : NNode, InN y → (∃ m, y.1 = res z m) → LeN δ y →
      (∀ x ∈ insert y (P ∪ Q), InN x ∧ ∃ m, x.1 = res z m) ∧
      ∀ x ∈ insert y (P ∪ Q), ∀ x' ∈ insert y (P ∪ Q), CompN x x' := by
    intro y hy hym hδy
    refine ⟨fun x hx => ?_, fun x hx x' hx' => ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨hy, hym⟩
      · exact hPQ x hx
    · rcases Finset.mem_insert.1 hx with hx1 | hx1 <;>
        rcases Finset.mem_insert.1 hx' with hx2 | hx2
      · rw [hx1, hx2]; exact Or.inl (LeN.refl _)
      · rw [hx1]; exact Or.inr ((hδ x' hx2).trans hδy)
      · rw [hx2]; exact Or.inl ((hδ x hx1).trans hδy)
      · exact hch x hx1 x' hx2
  refine ⟨?_, ?_⟩
  · refine tsum_candidates z d δ hδ1 hδ2 P.card (gN lam) (gN_injective h) _ ?_
    intro m hm y hy hym hδy
    rw [Set.indicator_of_mem]
    · rw [w_eq, Finset.prod_image fun a _ b _ e => bN_injective h e]
      simp_rw [add_comm (gN lam y)]
      exact ((prod_pe_pT_eq h z hz (fun x hx => hPQ x (Finset.mem_union_left _ hx)) hy m hym
        fun x hx => (hδ x (Finset.mem_union_left _ hx)).trans hδy).1).ge
    · refine ⟨fun hm' => ?_, P, insert y Q, ?_, rfl, by rw [Finset.image_insert], ?_⟩
      · obtain ⟨x, hx, e⟩ := Finset.mem_image.1 hm'
        exact hnot m hm y hym hδy (Finset.mem_union_right _ (gN_injective h e ▸ hx))
      · rw [Finset.union_insert]; exact (hext y hy ⟨m, hym⟩ hδy).1
      · rw [Finset.union_insert]; exact (hext y hy ⟨m, hym⟩ hδy).2
  · refine tsum_candidates z d δ hδ1 hδ2 Q.card (bN lam) (bN_injective h) _ ?_
    intro m hm y hy hym hδy
    rw [Set.indicator_of_mem]
    · rw [w_eq, Finset.prod_image fun a _ b _ e => gN_injective h e]
      exact ((prod_pe_pT_eq h z hz (fun x hx => hPQ x (Finset.mem_union_right _ hx)) hy m hym
        fun x hx => (hδ x (Finset.mem_union_right _ hx)).trans hδy).2).ge
    · refine ⟨fun hm' => ?_, insert y P, Q, ?_, by rw [Finset.image_insert], rfl, ?_⟩
      · obtain ⟨x, hx, e⟩ := Finset.mem_image.1 hm'
        exact hnot m hm y hym hδy (Finset.mem_union_left _ (bN_injective h e ▸ hx))
      · rw [Finset.insert_union]; exact (hext y hy ⟨m, hym⟩ hδy).1
      · rw [Finset.insert_union]; exact (hext y hy ⟨m, hym⟩ hδy).2

/-- Paper, Theorem \ref{IB:thm:nonborel}\ref{IB:nb3}: there is a continuous
`g : 2^{ℕ^{<ℕ}} → 𝔆 = {p ∈ (0,1)^ℕ : p_n → 0}` with `g(T) ∈ 𝔄_{BC} ⇔ T ∈ IF` for every tree `T`;
in particular (given that `IF` is not Borel) there is no Borel `W ⊆ [0,1]^ℕ` with
`W ∩ 𝔆 = 𝔄_{BC} ∩ 𝔆`. -/
theorem thm_nonborel_c (h : IsRigidSeq lam) :
    (∃ g : TreeSp → OpenCube, Continuous g ∧ (∀ T, g T ∈ frakC) ∧
      ∀ T ∈ TrSet, (cubeIncl (g T) ∈ frakA_BC ↔ T ∈ IFSet)) ∧
    (KechrisIFNotBorel → ¬ ∃ W : Set (ℕ → I), MeasurableSet[borel (ℕ → I)] W ∧
      W ∩ (cubeIncl '' frakC) = frakA_BC ∩ (cubeIncl '' frakC)) := by
  have hred : ∀ T ∈ TrSet, (cubeIncl (pT lam T) ∈ frakA_BC ↔ T ∈ IFSet) := by
    intro T hT
    constructor
    · exact pT_converse h hT
    · rintro ⟨-, z, hz⟩
      exact ae_hasSumset_of_strategy (pT_strategy h z hz)
  refine ⟨⟨pT lam, continuous_pT lam, pT_mem_frakC, hred⟩, fun hK ⟨W, hW, hWC⟩ => hK ?_⟩
  have hc : Continuous (cubeIncl ∘ pT lam) := continuous_cubeIncl.comp (continuous_pT lam)
  have h1 : MeasurableSet[borel TreeSp] ((cubeIncl ∘ pT lam) ⁻¹' W) := hc.borel_measurable hW
  have : IFSet = (cubeIncl ∘ pT lam) ⁻¹' W ∩ TrSet := by
    ext T
    have hmemC : cubeIncl (pT lam T) ∈ cubeIncl '' frakC := ⟨_, pT_mem_frakC T, rfl⟩
    have hx := Set.ext_iff.1 hWC (cubeIncl (pT lam T))
    have key : cubeIncl (pT lam T) ∈ W ↔ cubeIncl (pT lam T) ∈ frakA_BC :=
      ⟨fun hw => (hx.1 ⟨hw, hmemC⟩).1, fun ha => (hx.2 ⟨ha, hmemC⟩).1⟩
    constructor
    · intro hT
      exact ⟨key.2 ((hred T hT.1).2 hT), hT.1⟩
    · rintro ⟨h1, h2⟩
      exact (hred T h2).1 (key.1 h1)
  rw [this]
  exact h1.inter measurableSet_borel_TrSet

end NB3c

end Kmrr25.S44b
