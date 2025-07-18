/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Algebra.Order.Archimedean.Submonoid

/-!
# Necessary and sufficient conditions for a locally compact valued field

## Main Definitions
* `totallyBounded_iff_finite_residueField`: when the valuation ring is a DVR,
  it is totally bounded iff the residue field is finite.

## Tags

norm, nonarchimedean, rank one, compact, locally compact
-/

open NNReal

section NormedField

open scoped NormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

@[simp]
lemma NormedField.v_eq_valuation (x : K) : Valued.v x = NormedField.valuation x := rfl

namespace Valued.integer

-- should we do this all in the Valuation namespace instead?

/-- An element is in the valuation ring if the norm is bounded by 1. This is a variant of
`Valuation.mem_integer_iff`, phrased using norms instead of the valuation. -/
lemma mem_iff {x : K} : x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by
  simp [Valuation.mem_integer_iff, ← NNReal.coe_le_coe]

lemma norm_le_one (x : 𝒪[K]) : ‖x‖ ≤ 1 := mem_iff.mp x.prop

@[simp]
lemma norm_coe_unit (u : 𝒪[K]ˣ) : ‖((u : 𝒪[K]) : K)‖ = 1 := by
  simpa [← NNReal.coe_inj] using
    (Valuation.integer.integers (NormedField.valuation (K := K))).valuation_unit u

lemma norm_unit (u : 𝒪[K]ˣ) : ‖(u : 𝒪[K])‖ = 1 := by
  simp

lemma isUnit_iff_norm_eq_one {u : 𝒪[K]} : IsUnit u ↔ ‖u‖ = 1 := by
  simpa [← NNReal.coe_inj] using
    (Valuation.integer.integers (NormedField.valuation (K := K))).isUnit_iff_valuation_eq_one

lemma norm_irreducible_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : ‖ϖ‖ < 1 :=
  Valuation.integer.v_irreducible_lt_one h

lemma norm_irreducible_pos {ϖ : 𝒪[K]} (h : Irreducible ϖ) : 0 < ‖ϖ‖ :=
  Valuation.integer.v_irreducible_pos h

lemma coe_span_singleton_eq_closedBall (x : 𝒪[K]) :
    (Ideal.span {x} : Set 𝒪[K]) = Metric.closedBall 0 ‖x‖ := by
  simp [Valuation.integer.coe_span_singleton_eq_setOf_le_v_coe, Set.ext_iff, ← NNReal.coe_le_coe]

lemma _root_.Irreducible.maximalIdeal_eq_closedBall [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    (𝓂[K] : Set 𝒪[K]) = Metric.closedBall 0 ‖ϖ‖ := by
  simp [h.maximalIdeal_eq_setOf_le_v_coe, Set.ext_iff, ← NNReal.coe_le_coe]

lemma _root_.Irreducible.maximalIdeal_pow_eq_closedBall_pow [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) (n : ℕ) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = Metric.closedBall 0 (‖ϖ‖ ^ n) := by
  simp [h.maximalIdeal_pow_eq_setOf_le_v_coe_pow, Set.ext_iff, ← NNReal.coe_le_coe]

variable (K) in
lemma exists_norm_coe_lt_one : ∃ x : 𝒪[K], 0 < ‖(x : K)‖ ∧ ‖(x : K)‖ < 1 := by
  obtain ⟨x, hx, hx'⟩ := NormedField.exists_norm_lt_one K
  refine ⟨⟨x, hx'.le⟩, ?_⟩
  simpa [hx', Subtype.ext_iff] using hx

variable (K) in
lemma exists_norm_lt_one : ∃ x : 𝒪[K], 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_coe_lt_one K

variable (K) in
lemma exists_nnnorm_lt_one : ∃ x : 𝒪[K], 0 < ‖x‖₊ ∧ ‖x‖₊ < 1 :=
  exists_norm_coe_lt_one K

end Valued.integer

end NormedField

namespace Valued.integer

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

section FiniteResidueField

open Valued

lemma finite_quotient_maximalIdeal_pow_of_finite_residueField [IsDiscreteValuationRing 𝒪[K]]
    (h : Finite 𝓀[K]) (n : ℕ) :
    Finite (𝒪[K] ⧸ 𝓂[K] ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    exact Finite.of_fintype (↥𝒪[K] ⧸ ⊤)
  | succ n ih =>
    have : 𝓂[K] ^ (n + 1) ≤ 𝓂[K] ^ n := Ideal.pow_le_pow_right (by simp)
    replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE this).symm.toEquiv
    suffices Finite (Ideal.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))) (𝓂[K] ^ n)) from
      Finite.of_finite_quot_finite_ideal
        (I := Ideal.map (Ideal.Quotient.mk _) (𝓂[K] ^ n))
    exact @Finite.of_equiv _ _ h
      ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal 𝓂[K])
        (IsDiscreteValuationRing.not_a_field _) n).trans
        (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ n))

open scoped Valued
lemma totallyBounded_iff_finite_residueField [(Valued.v : Valuation K Γ₀).RankOne]
    [IsDiscreteValuationRing 𝒪[K]] :
    TotallyBounded (Set.univ (α := 𝒪[K])) ↔ Finite 𝓀[K] := by
  constructor
  · intro H
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    have := Metric.finite_approx_of_totallyBounded H ‖p‖ (norm_pos_iff.mpr hp.ne_zero)
    simp only [Set.subset_univ, Set.univ_subset_iff, true_and] at this
    obtain ⟨t, ht, ht'⟩ := this
    rw [← Set.finite_univ_iff]
    refine (ht.image (IsLocalRing.residue _)).subset ?_
    rintro ⟨x⟩
    replace ht' := ht'.ge (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at ht'
    obtain ⟨y, hy, hy'⟩ := ht'
    simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Set.mem_univ,
      IsLocalRing.residue, Set.mem_image, true_implies]
    refine ⟨y, hy, ?_⟩
    convert (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := 𝓂[K]) y x).mpr _
    -- TODO: make Valued.maximalIdeal abbreviations instead of def
    rw [Valued.maximalIdeal, hp.maximalIdeal_eq, ← SetLike.mem_coe,
      (Valuation.integer.integers _).coe_span_singleton_eq_setOf_le_v_algebraMap]
    rw [dist_comm] at hy'
    simpa [dist_eq_norm] using hy'.le
  · intro H
    rw [Metric.totallyBounded_iff]
    intro ε εpos
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    have hp' := Valuation.integer.v_irreducible_lt_one hp
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(p : K)‖ ^ n < ε := exists_pow_lt_of_lt_one εpos
      (toNormedField.norm_lt_one_iff.mpr hp')
    have hF := finite_quotient_maximalIdeal_pow_of_finite_residueField H n
    refine ⟨Quotient.out '' (Set.univ (α := 𝒪[K] ⧸ (𝓂[K] ^ n))), Set.toFinite _, ?_⟩
    have : {y : 𝒪[K] | v (y : K) ≤ v (p : K) ^ n} = Metric.closedBall 0 (‖p‖ ^ n)  := by
      ext
      simp [← norm_pow]
    simp only [Ideal.univ_eq_iUnion_image_add (𝓂[K] ^ n), hp.maximalIdeal_pow_eq_setOf_le_v_coe_pow,
      this, AddSubgroupClass.coe_norm, Set.image_univ, Set.mem_range, Set.iUnion_exists,
      Set.iUnion_iUnion_eq', Set.iUnion_subset_iff, Metric.vadd_closedBall, vadd_eq_add, add_zero]
    intro
    exact (Metric.closedBall_subset_ball hn).trans (Set.subset_iUnion_of_subset _ le_rfl)

end FiniteResidueField

section CompactDVR

open Valued

lemma isPrincipalIdealRing_of_compactSpace [CompactSpace 𝒪[K]]
    [MulArchimedean (MonoidHom.mrange (Valued.v : Valuation K Γ₀))]
    [hv : Valuation.IsNontrivial (Valued.v : Valuation K Γ₀)] :
    IsPrincipalIdealRing 𝒪[K] := by
  -- TODO: generalize to `Valuation.Integer`, which will require showing that `IsCompact`
  -- pulls back across `TopologicalSpace.induced` from a `LocallyCompactSpace`.
  -- The strategy to show that we have a PIR is by contradiction,
  -- assuming that the range of the valuation is densely ordered.
  -- We can construct a family of spheres at every single element of the valuation ring
  -- outside of a closed ball, which will cover.
  -- Since we are in a compact space, this cover has a finite subcover.
  -- This subcover, when excluding the sphere at 1, then has a max element since it is finite.
  -- However, since we are densely ordered, we can find an element with a valuation between
  -- the max element and 1, which is a contradiction, since it is outside the cover.

  -- First, we need to pick a threshold element with a nontrivial valuation less than 1,
  -- which will form -- the inner closed ball of the cover, which we need to cover 0.
  -- We have such an element by construction.
  obtain ⟨x, hx, hx'⟩ : ∃ x : 𝒪[K], 0 < v (x : K) ∧ v (x : K) < 1 := by
    obtain ⟨x, hx, hx'⟩ := hv.exists_lt_one
    exact ⟨⟨x, hx'.le⟩, by simpa [zero_lt_iff] using hx, hx'⟩
  -- the key result is that a valuation ring that maps into a `MulArchimedean` value group
  -- is a PIR iff the value group is not densely ordered.
  have hi : Valuation.Integers (R := K) Valued.v 𝒪[K] := Valuation.integer.integers v
  rw [hi.isPrincipalIdealRing_iff_not_denselyOrdered]
  intro H
  -- Construct our cover, which has an inner closed ball, and spheres for each element
  -- outside of the closed ball. These are all open sets by the nonarchimedean property.
  let U : 𝒪[K] → Set 𝒪[K] := fun y ↦ if v (y : K) < v (x : K)
    then {z | v (z : K) ≤ v (x : K)}
    else {z | v (z : K) = v (y : K)}
  -- Extract out the finite subcover from our cover, which is a finite set of elements of
  -- the valuation ring, whose spheres cover the whole ring.
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U <| by
    intro y
    simp only [U]
    split_ifs with hy
    · refine IsOpen.mem_nhds ((Valued.isOpen_closedball _ hx.ne').preimage ?_) ?_
      · exact continuous_subtype_val
      · simp [hy.le]
    · refine IsOpen.mem_nhds ((Valued.isOpen_sphere _ ?_).preimage ?_) ?_
      · simp only [not_lt] at hy
        exact (hx.trans_le hy).ne'
      · exact continuous_subtype_val
      · simp
  -- For each element of the valuation ring that is bigger than our threshold element above,
  -- then there must be something in the cover that has the precise valuation of the element,
  -- because it must be outside the inner closed ball, and thus is covered by some sphere.
  have htm : ∀ y : 𝒪[K], v (x : K) < v (y : K) → ∃ z ∈ t, v (z : K) = v (y : K) := by
    intro y hy
    have := ht.ge (Set.mem_univ y)
    simp only [Set.mem_iUnion, exists_prop', nonempty_prop, U] at this
    -- we get the `z` from the cover that covers our arbitrary `y` with its set
    obtain ⟨z, hz, hz'⟩ := this
    -- and this `z` is either less than or greater than (or equal to) the threshold element
    split_ifs at hz' with h
    -- the `z` is inside closed ball case, which is a contradiction since we know `y` is outside
    · simp [hy.not_ge] at hz'
    -- the `z` is gives a sphere, so we plug it in
    · simp only [Set.mem_setOf_eq] at hz'
      exact ⟨z, hz, hz'.symm⟩
  -- Pick an element of the valuation ring to use as the excluded element of the subcover
  -- (since we know that all elements of the valuation ring have valuation less than or equal to 1).
  obtain ⟨y, _, hy'⟩ : ∃ y : 𝒪[K], y ∈ t ∧ v (y : K)= 1 := by simpa using htm 1 (by simpa using hx')
  -- And pick an element in the subcover that is greater than the threshold element, but less
  -- than valuation 1. We will need this to show that the subcover excluding the element
  -- with valuation 1 is nonempty, which will allow us to take a max element.
  obtain ⟨w, hwt, hw1, hxw⟩ : ∃ w : 𝒪[K], w ∈ t ∧ v (w : K) < 1 ∧ v (x : K) < v (w : K) := by
    replace hx' : (⟨_, x, rfl⟩ : Set.range (v : K → Γ₀)) < ⟨_, 1, rfl⟩ := by simpa using hx'
    obtain ⟨⟨_, w, rfl⟩, hw, hw'⟩ := exists_between hx'
    obtain ⟨u, hu, hu'⟩ := htm ⟨w, by simpa using hw'.le⟩ hw
    exact ⟨u, hu, hu' ▸ by simpa using hw', hu' ▸ by simpa using hw⟩
  -- We're ready to work with the cover that excludes elements with valuation 1.
  let u := t.filter (fun a : 𝒪[K] ↦ v (a : K) < 1)
  have hwu : w ∈ u := by simp [u, hwt, hw1] -- and it is nonempty.
  -- So the element that takes on the largest valuation in this partial cover is in the cover itself
  -- which is the case because this partial cover is closed under the max (`⊔`) operation:
  -- if `‖x‖ ∈ u` and `‖y‖ ∈ u`, then `max ‖x‖ ‖y‖ ∈ u`
  obtain hl' := (u.image (v ∘ ((↑) : 𝒪[K] → K))).max'_mem <| by simpa using ⟨_, hwu⟩
  simp only [Finset.mem_image, Finset.mem_filter, Function.comp_apply, u] at hl'
  obtain ⟨l, ⟨hl, hl'⟩, hvl⟩ := hl'
  -- we know that this largest element must have valuation less than 1,
  -- since it is in the partial cover, and this is the property of the partial cover
  have hm : (⟨v (l : K), l, rfl⟩ : Set.range (v : K → Γ₀)) < (⟨1, y, hy'⟩) := by simpa using hl'
  -- Prepare the contradiction, pick an element that has a valuation between the max element and 1.
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := exists_between hm
  simp only [Subtype.mk_lt_mk] at hm
  -- well, it is in the ring, so there is something in the cover that covers it,
  -- and it must be a sphere since it is larger than the threshold element by virtue of
  -- `v x < v l < v m`.
  obtain ⟨n, hn, hn'⟩ : ∃ n ∈ t, v (n : K) = v m := by
    refine htm ⟨m, hm.right.le⟩ (hxw.trans (hm.left.trans_le' ?_))
    rw [hvl]
    refine Finset.le_max' _ _ ?_
    simp only [Finset.mem_image, Finset.mem_filter, Function.comp_apply]
    exact ⟨w, ⟨hwt, hw1⟩, rfl⟩
  rw [← hn'] at hm -- clean up what valuations we refer to
  -- to supply the contradiction, we have `v l < v n`, now prove that also `v n ≤ v l`
  refine hm.left.not_ge ?_
  -- which is the case since `‖l‖ = u.max' ..` and the property of `Finset.max'`
  rw [hvl]
  refine Finset.le_max' _ _ ?_
  simp only [Finset.mem_image, Finset.mem_filter, Function.comp_apply]
  use n
  simp [hn, hm.right]

lemma isDiscreteValuationRing_of_compactSpace [hv : (Valued.v : Valuation K Γ₀).RankOne]
    [CompactSpace 𝒪[K]] : IsDiscreteValuationRing 𝒪[K] := by
  -- To prove we have a DVR, we need to show it is
  -- a local ring (instance is directly inferred) and a PIR and not a field.
  have hn : Valuation.IsNontrivial (Valued.v : Valuation K Γ₀) := inferInstance
  have hm : MulArchimedean Γ₀ := .comap hv.hom.toMonoidHom hv.strictMono
  obtain ⟨x, hx, hx'⟩ := hn.exists_lt_one
  have key : IsPrincipalIdealRing 𝒪[K] := isPrincipalIdealRing_of_compactSpace
  exact {
    not_a_field' := by
      -- here is the other place where the nontriviality of the valuation comes in,
      -- since if we had `v x = 0 ∨ v x = 1`, then the maximal ideal would be `⊥`.
      simp only [ne_eq, Ideal.ext_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Ideal.mem_bot, not_forall, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      refine ⟨⟨x, hx'.le⟩, ?_⟩
      simpa [Subtype.ext_iff, hx'] using hx
  }

end CompactDVR

lemma compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    [(Valued.v : Valuation K Γ₀).RankOne] :
    CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, h⟩ ↦ ⟨?_⟩⟩
  · have : IsDiscreteValuationRing 𝒪[K] := isDiscreteValuationRing_of_compactSpace
    refine ⟨complete_of_compact, by assumption, ?_⟩
    rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete,
        totallyBounded_iff_finite_residueField] at h
    exact h.left
  · rw [← totallyBounded_iff_finite_residueField] at h
    rw [isCompact_iff_totallyBounded_isComplete]
    exact ⟨h, completeSpace_iff_isComplete_univ.mp ‹_›⟩

lemma properSpace_iff_compactSpace_integer [(Valued.v : Valuation K Γ₀).RankOne] :
    ProperSpace K ↔ CompactSpace 𝒪[K] := by
  simp only [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype,
             toNormedField.setOf_mem_integer_eq_closedBall]
  constructor <;> intro h
  · exact isCompact_closedBall 0 1
  · suffices LocallyCompactSpace K from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup h <|
      Metric.closedBall_mem_nhds 0 zero_lt_one

lemma properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    [(Valued.v : Valuation K Γ₀).RankOne] :
    ProperSpace K ↔ CompleteSpace K ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  simp only [properSpace_iff_compactSpace_integer,
      compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField,
      toNormedField.setOf_mem_integer_eq_closedBall,
      completeSpace_iff_isComplete_univ (α := 𝒪[K]), Subtype.isComplete_iff,
      NormedField.completeSpace_iff_isComplete_closedBall, Set.image_univ,
      Subtype.range_coe_subtype]

end Valued.integer
