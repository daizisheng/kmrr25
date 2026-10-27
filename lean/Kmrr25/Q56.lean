import Kmrr25.Basic

/-!
# Sums and products in `ℚ` along double Følner sequences

Paper, Section \ref{SP:sec:q56}: Theorem \ref{SP:thm:q56} together with
Lemmas \ref{SP:lem:folner} and \ref{SP:lem:noconf}.

A *double Følner sequence* in `ℚ` is a sequence `(F N)` of nonempty finite subsets of `ℚ` with
`|F_N ∩ (x + F_N)| / |F_N| → 1` for every `x ∈ ℚ` and `|F_N ∩ x F_N| / |F_N| → 1` for every
`x ∈ ℚ^*` (`IsDoubleFolner`). The density of `A ⊆ ℚ` along `(F N)` is the limit of
`|A ∩ F_N| / |F_N|` (`relDens`).

Main results:
* `card_tendsto_atTop`, `relDens_tendsto_zero_of_bounded`, `relDens_neg_tendsto` :
  Lemma \ref{SP:lem:folner} (i), (ii), (iii);
* `no_config_of_locallyFinite` : Lemma \ref{SP:lem:noconf};
* `theoremN` : Theorem \ref{SP:thm:q56}: for every double Følner sequence `Φ` there is a set
  `A ⊆ ℚ_{<0}` of density `1/2` along `Φ` such that there are no infinite `B, C ⊆ ℚ` with
  `B + C ⊆ A` and `BC ⊆ A`.

The existence of a double Følner sequence in `ℚ` (a result of Bergelson and Moreira quoted in
the paper) is proved in `Kmrr25.DoubleFolnerQ`, where `theoremN` is combined with it to give
the negative answer to Question \ref{SP:q:56} (`Kmrr25.DoubleFolnerQ.q56_negative`).
-/

open Filter Topology Finset
open scoped Classical

noncomputable section

namespace Kmrr25.Q56

/-- The product set `BC = {b c | b ∈ B, c ∈ C}`. -/
def prodset (B C : Set ℚ) : Set ℚ := {x | ∃ b ∈ B, ∃ c ∈ C, x = b * c}

/-- A *double Følner sequence* in `ℚ`: a sequence `(F N)_{N ∈ ℕ}` of nonempty finite subsets
of `ℚ` such that `|F_N ∩ (x + F_N)| / |F_N| → 1` for every `x ∈ ℚ` and
`|F_N ∩ x F_N| / |F_N| → 1` for every nonzero `x ∈ ℚ`. -/
structure IsDoubleFolner (F : ℕ → Finset ℚ) : Prop where
  nonempty : ∀ N, (F N).Nonempty
  add_invariant : ∀ x : ℚ,
    Tendsto (fun N => (#(F N ∩ (F N).image (x + ·)) : ℝ) / #(F N)) atTop (𝓝 1)
  mul_invariant : ∀ x : ℚ, x ≠ 0 →
    Tendsto (fun N => (#(F N ∩ (F N).image (x * ·)) : ℝ) / #(F N)) atTop (𝓝 1)

/-- The relative density `|A ∩ F| / |F|` of a set `A ⊆ ℚ` in a finite set `F ⊆ ℚ`. The density
`d_Φ(A)` along `Φ = (F N)` is the limit of `relDens (F N) A` as `N → ∞`. -/
def relDens (F : Finset ℚ) (A : Set ℚ) : ℝ := (#{x ∈ F | x ∈ A} : ℝ) / #F

variable {F : ℕ → Finset ℚ}

/-- `relDens` computed with an arbitrary decidability instance for membership. -/
lemma relDens_eq (F : Finset ℚ) (A : Set ℚ) [DecidablePred (· ∈ A)] :
    relDens F A = (#{x ∈ F | x ∈ A} : ℝ) / #F := by
  unfold relDens
  congr 3
  ext x
  simp only [mem_filter]

/-- `relDens` of a set given by a decidable predicate. -/
lemma relDens_setOf (F : Finset ℚ) (p : ℚ → Prop) [DecidablePred p] :
    relDens F {x | p x} = (#{x ∈ F | p x} : ℝ) / #F := by
  unfold relDens
  congr 3
  ext x
  simp only [mem_filter, Set.mem_ofPred_eq]

/-- Counting transfer along an injective map: if `φ` maps the points of `F ∩ G` back into `F`
and sends `P` to `Q`, then `|F ∩ P| ≤ |F ∩ Q| + (|F| - |F ∩ G|)`. -/
lemma card_filter_le_transfer (F G : Finset ℚ) (φ : ℚ → ℚ) (hφ : Function.Injective φ)
    (hG : ∀ x ∈ F, x ∈ G → φ x ∈ F) (P Q : ℚ → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x → Q (φ x)) :
    (#{x ∈ F | P x} : ℝ) ≤ #{x ∈ F | Q x} + ((#F : ℝ) - #(F ∩ G)) := by
  have h1 : {x ∈ F | P x} ⊆ {x ∈ F ∩ G | P x} ∪ {x ∈ F | x ∉ G} := by
    intro x hx
    rw [mem_filter] at hx
    simp only [mem_union, mem_filter, mem_inter]
    by_cases h : x ∈ G
    · exact Or.inl ⟨⟨hx.1, h⟩, hx.2⟩
    · exact Or.inr ⟨hx.1, h⟩
  have h2 : #{x ∈ F ∩ G | P x} ≤ #{x ∈ F | Q x} := by
    apply card_le_card_of_injOn φ
    · intro x hx
      simp only [coe_filter, mem_inter, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨hG x hx.1.1 hx.1.2, hPQ x hx.2⟩
    · exact hφ.injOn
  have h3 := card_union_le {x ∈ F ∩ G | P x} {x ∈ F | x ∉ G}
  have h4 := card_le_card h1
  have h5 := card_filter_add_card_filter_not (s := F) (fun x => x ∈ G)
  rw [filter_mem_eq_inter] at h5
  have : #{x ∈ F | P x} + #(F ∩ G) ≤ #{x ∈ F | Q x} + #F := by omega
  have := (Nat.cast_le (α := ℝ)).2 this
  push_cast at this
  linarith

/-- Paper, Lemma \ref{SP:lem:folner}(i). The sets of a double Følner sequence in `ℚ` have
cardinalities tending to infinity. -/
theorem card_tendsto_atTop (hF : IsDoubleFolner F) :
    Tendsto (fun N => #(F N)) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  have hlt : ∀ N, #(F N ∩ (F N).image (1 + ·)) < #(F N) := by
    intro N
    apply card_lt_card
    rw [ssubset_iff_of_subset inter_subset_left]
    refine ⟨(F N).min' (hF.nonempty N), min'_mem _ _, fun hm => ?_⟩
    obtain ⟨-, hm⟩ := mem_inter.1 hm
    obtain ⟨y, hy, hy'⟩ := mem_image.1 hm
    have := min'_le (F N) y hy
    linarith
  have hM : (1 : ℝ) - 1 / (M + 1) < 1 := by
    have : (0 : ℝ) < 1 / (M + 1) := by positivity
    linarith
  filter_upwards [(hF.add_invariant 1).eventually (lt_mem_nhds hM)] with N hN
  by_contra hcon
  push Not at hcon
  have hc : (0 : ℝ) < #(F N) := by exact_mod_cast (hF.nonempty N).card_pos
  have hd : (#(F N ∩ (F N).image (1 + ·)) : ℝ) + 1 ≤ #(F N) := by exact_mod_cast hlt N
  have hcM : (#(F N) : ℝ) < M + 1 := by
    have : (#(F N) : ℝ) < M := by exact_mod_cast hcon
    linarith
  rw [lt_div_iff₀ hc] at hN
  have : (#(F N) : ℝ) / (M + 1) < 1 := (div_lt_one (by positivity)).2 hcM
  have e : (1 - 1 / ((M : ℝ) + 1)) * #(F N) = #(F N) - #(F N) / (M + 1) := by ring
  linarith

/-- Paper, Lemma \ref{SP:lem:folner}(ii). For every bounded set `X ⊆ ℚ`,
`|F_N ∩ X| / |F_N| → 0`. -/
theorem relDens_tendsto_zero_of_bounded (hF : IsDoubleFolner F) {X : Set ℚ}
    (hX : ∃ R : ℚ, ∀ x ∈ X, |x| ≤ R) :
    Tendsto (fun N => relDens (F N) X) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hX
  set R' := max R 0 with hR'def
  have hR' : ∀ x ∈ X, |x| ≤ R' := fun x hx => (hR x hx).trans (le_max_left _ _)
  have hR0 : 0 ≤ R' := le_max_right _ _
  set t : ℕ → ℚ := fun j => j * (2 * R' + 1) with ht
  -- `d j N = |F_N ∩ (-t_j + F_N)|`
  set d : ℕ → ℕ → ℝ := fun j N => (#(F N ∩ (F N).image ((-t j) + ·)) : ℝ) with hd
  have key : ∀ (k N : ℕ), (k : ℝ) * #{x ∈ F N | x ∈ X} ≤
      #(F N) + ∑ j ∈ range k, ((#(F N) : ℝ) - d j N) := by
    intro k N
    have hj : ∀ j, (#{x ∈ F N | x ∈ X} : ℝ) ≤
        #{y ∈ F N | y - t j ∈ X} + ((#(F N) : ℝ) - d j N) := by
      intro j
      refine card_filter_le_transfer (F N) ((F N).image ((-t j) + ·)) (· + t j)
        (add_left_injective _) ?_ _ _ ?_
      · intro x _ hx
        obtain ⟨f, hf, rfl⟩ := mem_image.1 hx
        simpa using hf
      · intro x hx
        simpa using hx
    have hdisj : (#((range k).biUnion fun j => {y ∈ F N | y - t j ∈ X}) : ℝ) =
        ∑ j ∈ range k, (#{y ∈ F N | y - t j ∈ X} : ℝ) := by
      rw [card_biUnion]
      · push_cast; rfl
      · intro i _ j _ hij
        rw [Function.onFun, disjoint_left]
        intro y hyi hyj
        simp only [mem_filter] at hyi hyj
        have hi := abs_le.1 (hR' _ hyi.2)
        have hj := abs_le.1 (hR' _ hyj.2)
        rcases Nat.lt_or_gt_of_ne hij with h | h
        · have h' : (i : ℚ) + 1 ≤ j := by exact_mod_cast h
          have : ((i : ℚ) + 1) * (2 * R' + 1) ≤ j * (2 * R' + 1) :=
            mul_le_mul_of_nonneg_right h' (by linarith)
          simp only [ht] at hi hj
          nlinarith
        · have h' : (j : ℚ) + 1 ≤ i := by exact_mod_cast h
          have : ((j : ℚ) + 1) * (2 * R' + 1) ≤ i * (2 * R' + 1) :=
            mul_le_mul_of_nonneg_right h' (by linarith)
          simp only [ht] at hi hj
          nlinarith
    have hsub : (#((range k).biUnion fun j => {y ∈ F N | y - t j ∈ X}) : ℝ) ≤ #(F N) := by
      exact_mod_cast card_le_card (biUnion_subset.2 fun j _ => filter_subset _ _)
    have hsum := sum_le_sum fun j (_ : j ∈ range k) => hj j
    rw [sum_add_distrib] at hsum
    simp only [sum_const, card_range, nsmul_eq_mul] at hsum
    linarith
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun N => ?_, fun ε hε => ?_⟩
  · exact lt_of_lt_of_le ha (div_nonneg (by positivity) (by positivity))
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  set h : ℕ → ℝ := fun N =>
    (1 / ((k : ℝ) + 1)) * (1 + ∑ j ∈ range (k + 1), (1 - d j N / #(F N))) with hh
  have hlim : Tendsto h atTop (𝓝 ((1 / ((k : ℝ) + 1)) * (1 + ∑ j ∈ range (k + 1), (1 - 1)))) := by
    refine tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_finsetSum _ fun j _ => ?_))
    exact tendsto_const_nhds.sub (hF.add_invariant (-t j))
  simp only [sub_self, sum_const_zero, add_zero, mul_one] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hk)] with N hN
  refine lt_of_le_of_lt ?_ hN
  have hc : (0 : ℝ) < #(F N) := by exact_mod_cast (hF.nonempty N).card_pos
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have := key (k + 1) N
  push_cast at this
  simp only [relDens, hh]
  rw [div_le_iff₀ hc]
  have e : (1 / ((k : ℝ) + 1)) * (1 + ∑ j ∈ range (k + 1), (1 - d j N / #(F N))) * #(F N) =
      (1 / ((k : ℝ) + 1)) * (#(F N) + ∑ j ∈ range (k + 1), ((#(F N) : ℝ) - d j N)) := by
    rw [mul_assoc, add_mul, sum_mul]
    congr 2
    · ring
    · refine sum_congr rfl fun j _ => ?_
      field_simp
  rw [e, div_mul_eq_mul_div, one_mul, le_div_iff₀ hk1]
  linarith

/-- Paper, Lemma \ref{SP:lem:folner}(iii). `|F_N ∩ ℚ_{<0}| / |F_N| → 1/2`. -/
theorem relDens_neg_tendsto (hF : IsDoubleFolner F) :
    Tendsto (fun N => relDens (F N) {x | x < 0}) atTop (𝓝 (1 / 2)) := by
  have hG : ∀ N, ∀ x ∈ F N, x ∈ (F N).image ((-1 : ℚ) * ·) → -x ∈ F N := by
    intro N x _ hx
    obtain ⟨f, hf, rfl⟩ := mem_image.1 hx
    simpa using hf
  -- notation: `n = |F ∩ ℚ_{<0}|`, `p = |F ∩ ℚ_{>0}|`, `c = |F|`, `d = |F ∩ (-F)|`
  have key : ∀ N, ∀ n p c d : ℝ, n = #{x ∈ F N | x < 0} → p = #{x ∈ F N | 0 < x} →
      c = #(F N) → d = #(F N ∩ (F N).image ((-1 : ℚ) * ·)) →
      n ≤ p + (c - d) ∧ p ≤ n + (c - d) ∧ n + p ≤ c ∧ c - 1 ≤ n + p := by
    intro N n p c d hn hp hc hd
    subst hn hp hc hd
    refine ⟨card_filter_le_transfer (F N) _ (fun x => -x) neg_injective (hG N) _ _
      (fun x hx => by simpa using hx),
      card_filter_le_transfer (F N) _ (fun x => -x) neg_injective (hG N) _ _
      (fun x hx => by simpa using hx), ?_, ?_⟩
    · have h := card_filter_add_card_filter_not (s := F N) (fun x : ℚ => x < 0)
      have h2 : #{x ∈ F N | 0 < x} ≤ #{x ∈ F N | ¬ x < 0} :=
        card_le_card (monotone_filter_right _ fun x _ hx => not_lt.2 (le_of_lt hx))
      have : #{x ∈ F N | x < 0} + #{x ∈ F N | 0 < x} ≤ #(F N) := by omega
      exact_mod_cast this
    · have h := card_filter_add_card_filter_not (s := F N) (fun x : ℚ => x < 0)
      have h2 : {x ∈ F N | ¬ x < 0} ⊆ insert 0 {x ∈ F N | 0 < x} := by
        intro x hx
        simp only [mem_filter, not_lt, mem_insert] at hx ⊢
        rcases hx.2.eq_or_lt with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨hx.1, h⟩
      have h3 := (card_le_card h2).trans (card_insert_le _ _)
      have : #(F N) ≤ #{x ∈ F N | x < 0} + #{x ∈ F N | 0 < x} + 1 := by omega
      have := (Nat.cast_le (α := ℝ)).2 this
      push_cast at this
      linarith
  have hdc := hF.mul_invariant (-1) (by norm_num)
  have hinv : Tendsto (fun N => 1 / (#(F N) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (card_tendsto_atTop hF)
  have hlow : Tendsto (fun N => ((#(F N ∩ (F N).image ((-1 : ℚ) * ·)) : ℝ) / #(F N)
      - 1 / (#(F N) : ℝ)) / 2) atTop (𝓝 (1 / 2)) := by
    have := (hdc.sub hinv).div_const 2
    rwa [sub_zero] at this
  have hup : Tendsto (fun N => (2 - (#(F N ∩ (F N).image ((-1 : ℚ) * ·)) : ℝ) / #(F N)) / 2)
      atTop (𝓝 (1 / 2)) := by
    have := ((tendsto_const_nhds (x := (2 : ℝ))).sub hdc).div_const 2
    rwa [show ((2 : ℝ) - 1) = 1 by norm_num] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun N => ?_) (fun N => ?_)
  · obtain ⟨h1, h2, h3, h4⟩ := key N _ _ _ _ rfl rfl rfl rfl
    have hcN : (0 : ℝ) < #(F N) := by exact_mod_cast (hF.nonempty N).card_pos
    simp only [relDens, Set.mem_ofPred_eq]
    generalize (#{x ∈ F N | x < 0} : ℝ) = n at *
    generalize (#{x ∈ F N | 0 < x} : ℝ) = p at *
    generalize (#(F N ∩ (F N).image ((-1 : ℚ) * ·)) : ℝ) = d at *
    generalize (#(F N) : ℝ) = c at *
    rw [show (d / c - 1 / c) / 2 = (d - 1) / (2 * c) by field_simp,
      div_le_div_iff₀ (by positivity) hcN]
    have h5 : d - 1 ≤ 2 * n := by linarith
    have := mul_le_mul_of_nonneg_right h5 hcN.le
    linarith
  · obtain ⟨h1, h2, h3, h4⟩ := key N _ _ _ _ rfl rfl rfl rfl
    have hcN : (0 : ℝ) < #(F N) := by exact_mod_cast (hF.nonempty N).card_pos
    simp only [relDens, Set.mem_ofPred_eq]
    generalize (#{x ∈ F N | x < 0} : ℝ) = n at *
    generalize (#{x ∈ F N | 0 < x} : ℝ) = p at *
    generalize (#(F N ∩ (F N).image ((-1 : ℚ) * ·)) : ℝ) = d at *
    generalize (#(F N) : ℝ) = c at *
    rw [show (2 - d / c) / 2 = (2 * c - d) / (2 * c) by field_simp,
      div_le_div_iff₀ hcN (by positivity)]
    have h5 : 2 * n ≤ 2 * c - d := by linarith
    have := mul_le_mul_of_nonneg_right h5 hcN.le
    linarith

lemma no_config_aux {A : Set ℚ} (hneg : A ⊆ {x | x < 0})
    (hfin : ∀ R : ℚ, 0 < R → {x ∈ A | |x| ≤ R}.Finite) {b : ℚ} (hb : b < 0) {C : Set ℚ}
    (hC : C.Infinite) (hsum : ∀ c ∈ C, b + c ∈ A) (hprod : ∀ c ∈ C, b * c ∈ A)
    (hpos : ∀ c ∈ C, 0 < c) : False := by
  have hsub : (fun c => b * c) '' C ⊆ {x ∈ A | |x| ≤ b ^ 2} := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨hprod c hc, ?_⟩
    have h1 : b + c < 0 := hneg (hsum c hc)
    have h2 := hpos c hc
    rw [abs_le]
    constructor <;> nlinarith
  have hinf : ((fun c => b * c) '' C).Infinite := hC.image (mul_right_injective₀ hb.ne).injOn
  exact hinf ((hfin (b ^ 2) (by nlinarith)).subset hsub)

/-- Paper, Lemma \ref{SP:lem:noconf}. Let `A ⊆ ℚ_{<0}` be such that `A ∩ [-R, R]` is finite for
every `R > 0`. Then there are no infinite sets `B, C ⊆ ℚ` with `B + C ⊆ A` and `BC ⊆ A`. -/
theorem no_config_of_locallyFinite {A : Set ℚ} (hneg : A ⊆ {x | x < 0})
    (hfin : ∀ R : ℚ, 0 < R → {x ∈ A | |x| ≤ R}.Finite) :
    ¬ ∃ B C : Set ℚ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ A ∧ prodset B C ⊆ A := by
  rintro ⟨B, C, hB, hC, hs, hp⟩
  have hprod : ∀ b ∈ B, ∀ c ∈ C, b * c < 0 := fun b hb c hc => hneg (hp ⟨b, hb, c, hc, rfl⟩)
  have hsum : ∀ b ∈ B, ∀ c ∈ C, b + c ∈ A := fun b hb c hc => hs ⟨b, hb, c, hc, rfl⟩
  obtain ⟨b0, hb0⟩ := hB.nonempty
  rcases lt_or_ge b0 0 with h | h
  · exact no_config_aux hneg hfin h hC (fun c hc => hsum b0 hb0 c hc)
      (fun c hc => hp ⟨b0, hb0, c, hc, rfl⟩)
      (fun c hc => pos_of_mul_neg_right (hprod b0 hb0 c hc) h.le)
  · obtain ⟨c0, hc0⟩ := hC.nonempty
    have hc0n : c0 < 0 := neg_of_mul_neg_right (hprod b0 hb0 c0 hc0) h
    exact no_config_aux hneg hfin hc0n hB (fun b hb => by rw [add_comm]; exact hsum b hb c0 hc0)
      (fun b hb => by rw [mul_comm]; exact hp ⟨b, hb, c0, hc0, rfl⟩)
      (fun b hb => pos_of_mul_neg_left (hprod b hb c0 hc0) hc0n.le)

/-- Paper, Theorem \ref{SP:thm:q56} (Theorem N). Let `Φ = (F N)` be any double Følner sequence
in `ℚ`. There is a set `A ⊆ ℚ_{<0}` with `d_Φ(A) = lim_N |A ∩ F_N| / |F_N| = 1/2` such that there
are no infinite sets `B, C ⊆ ℚ` with `B + C ⊆ A` and `BC ⊆ A`. -/
theorem theoremN (hF : IsDoubleFolner F) :
    ∃ A : Set ℚ, A ⊆ {x | x < 0} ∧
      Tendsto (fun N => relDens (F N) A) atTop (𝓝 (1 / 2)) ∧
      ¬ ∃ B C : Set ℚ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ A ∧ prodset B C ⊆ A := by
  -- thresholds `T0 R` after which `|F_N ∩ [-R, R]| < |F_N| / (R + 1)`
  have h2 : ∀ R : ℕ, ∃ N0 : ℕ, ∀ N ≥ N0, relDens (F N) {x | |x| ≤ R} < 1 / ((R : ℝ) + 1) :=
    fun R => eventually_atTop.1 ((relDens_tendsto_zero_of_bounded hF ⟨R, fun x hx => hx⟩).eventually
      (gt_mem_nhds (by positivity)))
  choose T0 hT0 using h2
  set T : ℕ → ℕ := fun R => R + ∑ r ∈ range (R + 1), T0 r with hT
  have hTmono : Monotone T := by
    intro a b hab
    simp only [hT]
    have : ∑ r ∈ range (a + 1), T0 r ≤ ∑ r ∈ range (b + 1), T0 r :=
      sum_le_sum_of_subset (range_subset_range.2 (by omega))
    omega
  have hTge : ∀ R, R ≤ T R := fun R => Nat.le_add_right _ _
  have hT0le : ∀ R, T0 R ≤ T R := fun R =>
    (single_le_sum (fun _ _ => Nat.zero_le _) (self_mem_range_succ R)).trans (Nat.le_add_left _ _)
  set A : Set ℚ := {x | x < 0 ∧ ∃ N < T ⌈|x|⌉₊, x ∈ F N} with hA
  have hneg : A ⊆ {x | x < 0} := fun x hx => hx.1
  refine ⟨A, hneg, ?_, ?_⟩
  swap
  · -- bounded parts of `A` are finite
    refine no_config_of_locallyFinite hneg fun R _ => ?_
    refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_lt_nat (T ⌈R⌉₊))
      fun N _ => (F N).finite_toSet) ?_
    rintro x ⟨⟨-, N, hN, hxN⟩, hxR⟩
    exact Set.mem_biUnion (lt_of_lt_of_le hN (hTmono (Nat.ceil_mono hxR))) hxN
  -- `R(N)`: the largest `R ≤ N` with `T R ≤ N`
  set Rf : ℕ → ℕ := fun N => Nat.findGreatest (fun R => T R ≤ N) N with hRf
  have hRf_tend : Tendsto (fun N => ((Rf N : ℝ) + 1)) atTop atTop := by
    refine tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp ?_)
    rw [tendsto_atTop]
    intro R0
    filter_upwards [eventually_ge_atTop (T R0)] with N hN
    exact Nat.le_findGreatest ((hTge R0).trans hN) hN
  have hbad : ∀ N, T 0 ≤ N →
      (#{x ∈ F N | x < 0 ∧ x ∉ A} : ℝ) / #(F N) ≤ 1 / ((Rf N : ℝ) + 1) := by
    intro N hN
    have hspec : T (Rf N) ≤ N := Nat.findGreatest_spec (P := fun R => T R ≤ N) (Nat.zero_le N) hN
    have hlt := hT0 (Rf N) N ((hT0le _).trans hspec)
    rw [relDens_setOf] at hlt
    have hsub : {x ∈ F N | x < 0 ∧ x ∉ A} ⊆ {x ∈ F N | |x| ≤ (Rf N : ℚ)} := by
      intro x hx
      simp only [mem_filter, Set.mem_ofPred_eq, hA, not_and, not_exists] at hx ⊢
      refine ⟨hx.1, ?_⟩
      have h1 : T ⌈|x|⌉₊ ≤ N := by
        by_contra hc
        exact hx.2.2 hx.2.1 N (not_le.1 hc) hx.1
      have h2 : ⌈|x|⌉₊ ≤ Rf N := Nat.le_findGreatest ((hTge _).trans h1) h1
      exact (Nat.le_ceil _).trans (by exact_mod_cast h2)
    refine le_trans ?_ hlt.le
    exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsub) (by positivity)
  have hbad0 : Tendsto (fun N => (#{x ∈ F N | x < 0 ∧ x ∉ A} : ℝ) / #(F N)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hRf_tend) (Eventually.of_forall fun N => by positivity) ?_
    filter_upwards [eventually_ge_atTop (T 0)] with N hN
    exact hbad N hN
  have hsplit : ∀ N, relDens (F N) A =
      relDens (F N) {x | x < 0} - (#{x ∈ F N | x < 0 ∧ x ∉ A} : ℝ) / #(F N) := by
    intro N
    have h := card_filter_add_card_filter_not (s := {x ∈ F N | x < 0}) (fun x => x ∈ A)
    rw [filter_filter, filter_filter] at h
    have e : {x ∈ F N | x < 0 ∧ x ∈ A} = {x ∈ F N | x ∈ A} :=
      filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
    rw [e] at h
    rw [relDens_eq (F N) A, relDens_setOf (F N) (fun x => x < 0), ← h]
    push_cast
    ring
  simp_rw [hsplit]
  simpa using (relDens_neg_tendsto hF).sub hbad0

end Kmrr25.Q56

end
