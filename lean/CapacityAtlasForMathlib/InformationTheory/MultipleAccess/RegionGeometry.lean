/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.

Adapted from TomasOrtega/CapacityAtlasMAC, commit ec5be554b9644df94dd58190963793f3f1d1da52,
CapacityAtlasMAC/RegionGeometry.lean. Imports and certificate types use the monorepo modules.
-/

import CapacityAtlasForMathlib.InformationTheory.MultipleAccess
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded

open scoped BigOperators
open Set

namespace CapacityAtlas.MultipleAccess

attribute [local instance] Classical.propDecidable

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

private abbrev Simplex (X : Type*) [Fintype X] := stdSimplex ℝ X

private def ofSimplex {X : Type*} [Fintype X] (p : Simplex X) : FiniteDistribution X :=
  ⟨p.1, p.2.1, p.2.2⟩

private def toSimplex {X : Type*} [Fintype X] (p : FiniteDistribution X) : Simplex X :=
  ⟨p, p.nonnegative, p.sum_probability⟩

/-- The two conditional information bounds and the joint information bound. -/
noncomputable def informationTriple (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) : Fin 3 → ℝ :=
  ![leftInformation W p₁ p₂, rightInformation W p₁ p₂, jointInformation W p₁ p₂]

@[simp]
theorem informationTriple_zero (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) :
    informationTriple W p₁ p₂ 0 = leftInformation W p₁ p₂ := rfl

@[simp]
theorem informationTriple_one (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) :
    informationTriple W p₁ p₂ 1 = rightInformation W p₁ p₂ := rfl

@[simp]
theorem informationTriple_two (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) :
    informationTriple W p₁ p₂ 2 = jointInformation W p₁ p₂ := rfl

private noncomputable def rawTriple (W : FiniteChannel (X₁ × X₂) Y)
    (p : (X₁ → ℝ) × (X₂ → ℝ)) : Fin 3 → ℝ :=
  ![∑ x₂, p.2 x₂ *
      (((∑ y, Real.negMulLog (∑ x₁, p.1 x₁ * W.transition (x₁, x₂) y)) -
        ∑ x₁, p.1 x₁ * (W.rowDistribution (x₁, x₂)).entropy) / Real.log 2),
    ∑ x₁, p.1 x₁ *
      (((∑ y, Real.negMulLog (∑ x₂, p.2 x₂ * W.transition (x₁, x₂) y)) -
        ∑ x₂, p.2 x₂ * (W.rowDistribution (x₁, x₂)).entropy) / Real.log 2),
    ((∑ y, Real.negMulLog (∑ x : X₁ × X₂, (p.1 x.1 * p.2 x.2) * W.transition x y)) -
      ∑ x : X₁ × X₂, (p.1 x.1 * p.2 x.2) * (W.rowDistribution x).entropy) / Real.log 2]

private theorem rawTriple_eq (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) :
    rawTriple W (p₁, p₂) = informationTriple W p₁ p₂ := rfl

private theorem continuous_rawTriple (W : FiniteChannel (X₁ × X₂) Y) :
    Continuous (rawTriple W) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [rawTriple] <;> fun_prop

private noncomputable def simplexTriple (W : FiniteChannel (X₁ × X₂) Y)
    (p : Simplex X₁ × Simplex X₂) : Fin 3 → ℝ :=
  rawTriple W (p.1.1, p.2.1)

private theorem continuous_simplexTriple (W : FiniteChannel (X₁ × X₂) Y) :
    Continuous (simplexTriple W) :=
  (continuous_rawTriple W).comp (continuous_subtype_val.prodMap continuous_subtype_val)

/-- All finite time-sharing averages of product-input information triples. -/
noncomputable def informationTriples (W : FiniteChannel (X₁ × X₂) Y) : Set (Fin 3 → ℝ) :=
  convexHull ℝ (Set.range (simplexTriple W))

theorem weighted_informationTriple_mem (W : FiniteChannel (X₁ × X₂) Y)
    (k : ℕ) (weights : FiniteDistribution (Fin k))
    (p₁ : Fin k → FiniteDistribution X₁) (p₂ : Fin k → FiniteDistribution X₂) :
    (∑ q, weights q • informationTriple W (p₁ q) (p₂ q)) ∈ informationTriples W := by
  apply mem_convexHull_of_exists_fintype (fun q ↦ weights q)
    (fun q ↦ informationTriple W (p₁ q) (p₂ q)) weights.nonnegative weights.sum_probability
  · intro q
    exact ⟨(toSimplex (p₁ q), toSimplex (p₂ q)), rfl⟩
  · rfl

private abbrev SharingParameters (X₁ X₂ : Type*) [Fintype X₁] [Fintype X₂] (k : ℕ) :=
  Simplex (Fin k) × (Fin k → (Simplex X₁ × Simplex X₂))

private noncomputable def sharingTriple (W : FiniteChannel (X₁ × X₂) Y) (k : ℕ)
    (parameters : SharingParameters X₁ X₂ k) : Fin 3 → ℝ :=
  ∑ q, parameters.1.1 q • simplexTriple W (parameters.2 q)

private theorem continuous_sharingTriple (W : FiniteChannel (X₁ × X₂) Y) (k : ℕ) :
    Continuous (sharingTriple W k) := by
  unfold sharingTriple
  apply continuous_finsetSum
  intro q _
  exact ((continuous_apply q).comp (continuous_subtype_val.comp continuous_fst)).smul
    ((continuous_simplexTriple W).comp ((continuous_apply q).comp continuous_snd))

private theorem small_representation (W : FiniteChannel (X₁ × X₂) Y)
    {v : Fin 3 → ℝ} (hv : v ∈ informationTriples W) :
    ∃ k : Fin 5, ∃ parameters : SharingParameters X₁ X₂ k.val,
      sharingTriple W k.val parameters = v := by
  classical
  obtain ⟨ι, hι, z, w, hz, hindependent, hpositive, hsum, hvalue⟩ :=
    eq_pos_convex_span_of_mem_convexHull hv
  letI := hι
  have hcard : Fintype.card ι ≤ 4 := by
    calc
      Fintype.card ι ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
        hindependent.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (Fin 3 → ℝ) + 1 :=
        Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = 4 := by simp [Module.finrank_fintype_fun_eq_card]
  have hsource : ∀ i, ∃ p : Simplex X₁ × Simplex X₂, simplexTriple W p = z i := by
    intro i
    exact hz (Set.mem_range_self i)
  choose p hp using hsource
  let e := Fintype.equivFin ι
  let weights : Simplex (Fin (Fintype.card ι)) :=
    ⟨fun i ↦ w (e.symm i), fun i ↦ (hpositive (e.symm i)).le,
      (e.symm.sum_comp w).trans hsum⟩
  refine ⟨⟨Fintype.card ι, by omega⟩, (weights, fun i ↦ p (e.symm i)), ?_⟩
  change (∑ i : Fin (Fintype.card ι), w (e.symm i) • simplexTriple W (p (e.symm i))) = v
  simp_rw [hp]
  exact (e.symm.sum_comp (fun i ↦ w i • z i)).trans hvalue

/-- Three information coordinates require at most four time-sharing values. -/
theorem informationTriples_exists_card_le_four (W : FiniteChannel (X₁ × X₂) Y)
    {v : Fin 3 → ℝ} (hv : v ∈ informationTriples W) :
    ∃ k : ℕ, k ≤ 4 ∧ ∃ weights : FiniteDistribution (Fin k),
      ∃ p₁ : Fin k → FiniteDistribution X₁, ∃ p₂ : Fin k → FiniteDistribution X₂,
        (∑ q, weights q • informationTriple W (p₁ q) (p₂ q)) = v := by
  obtain ⟨k, parameters, hvalue⟩ := small_representation W hv
  refine ⟨k.val, by omega, ofSimplex parameters.1,
    (fun q ↦ ofSimplex (parameters.2 q).1), (fun q ↦ ofSimplex (parameters.2 q).2), ?_⟩
  exact hvalue

theorem isCompact_informationTriples (W : FiniteChannel (X₁ × X₂) Y) :
    IsCompact (informationTriples W) := by
  have heq : informationTriples W =
      ⋃ k : Fin 5, Set.range (sharingTriple W k.val) := by
    ext v
    constructor
    · intro hv
      obtain ⟨k, parameters, hvalue⟩ := small_representation W hv
      exact Set.mem_iUnion.mpr ⟨k, ⟨parameters, hvalue⟩⟩
    · intro hv
      obtain ⟨k, parameters, rfl⟩ := Set.mem_iUnion.mp hv
      exact weighted_informationTriple_mem W k.val (ofSimplex parameters.1)
        (fun q ↦ ofSimplex (parameters.2 q).1) (fun q ↦ ofSimplex (parameters.2 q).2)
  rw [heq]
  apply isCompact_iUnion
  intro k
  exact isCompact_range (continuous_sharingTriple W k.val)

theorem mem_informationRegion_iff_triple (W : FiniteChannel (X₁ × X₂) Y) (r : RatePair) :
    r ∈ informationRegion W ↔ 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ v ∈ informationTriples W,
      r.1 ≤ v 0 ∧ r.2 ≤ v 1 ∧ r.1 + r.2 ≤ v 2 := by
  constructor
  · rintro ⟨h₁, h₂, k, weights, p₁, p₂, ha, hb, hc⟩
    refine ⟨h₁, h₂, ∑ q, weights q • informationTriple W (p₁ q) (p₂ q),
      weighted_informationTriple_mem W k weights p₁ p₂, ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, informationTriple_zero,
      informationTriple_one, informationTriple_two]
    exact ⟨ha, hb, hc⟩
  · rintro ⟨h₁, h₂, v, hv, ha, hb, hc⟩
    obtain ⟨k, _, weights, p₁, p₂, rfl⟩ := informationTriples_exists_card_le_four W hv
    refine ⟨h₁, h₂, k, weights, p₁, p₂, ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, informationTriple_zero,
      informationTriple_one, informationTriple_two] at ha hb hc
    exact ⟨ha, hb, hc⟩

/-- Arbitrarily small common slack in all three inequalities yields an exact finite witness. -/
theorem mem_informationRegion_of_approx (W : FiniteChannel (X₁ × X₂) Y) (r : RatePair)
    (hr₁ : 0 ≤ r.1) (hr₂ : 0 ≤ r.2)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ k : ℕ, ∃ weights : FiniteDistribution (Fin k),
      ∃ p₁ : Fin k → FiniteDistribution X₁, ∃ p₂ : Fin k → FiniteDistribution X₂,
        r.1 ≤ (∑ q, weights q * leftInformation W (p₁ q) (p₂ q)) + δ ∧
        r.2 ≤ (∑ q, weights q * rightInformation W (p₁ q) (p₂ q)) + δ ∧
        r.1 + r.2 ≤ (∑ q, weights q * jointInformation W (p₁ q) (p₂ q)) + δ) :
    r ∈ informationRegion W := by
  let gap : (Fin 3 → ℝ) → ℝ := fun v ↦
    max (r.1 - v 0) (max (r.2 - v 1) (r.1 + r.2 - v 2))
  have hgapContinuous : Continuous gap := by dsimp [gap]; fun_prop
  have hwitness : ∀ δ : ℝ, 0 < δ → ∃ v ∈ informationTriples W, gap v ≤ δ := by
    intro δ hδ
    obtain ⟨k, weights, p₁, p₂, ha, hb, hc⟩ := happrox δ hδ
    refine ⟨∑ q, weights q • informationTriple W (p₁ q) (p₂ q),
      weighted_informationTriple_mem W k weights p₁ p₂, ?_⟩
    simp only [gap, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, informationTriple_zero,
      informationTriple_one, informationTriple_two, max_le_iff]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hnonempty : (informationTriples W).Nonempty := by
    obtain ⟨v, hv, _⟩ := hwitness 1 (by norm_num)
    exact ⟨v, hv⟩
  obtain ⟨v, hv, hmin⟩ := (isCompact_informationTriples W).exists_isMinOn
    hnonempty hgapContinuous.continuousOn
  have hgap : gap v ≤ 0 := by
    by_contra h
    have hpositive : 0 < gap v := lt_of_not_ge h
    obtain ⟨u, hu, hbound⟩ := hwitness (gap v / 2) (by positivity)
    have hminimum : gap v ≤ gap u := hmin hu
    linarith
  apply (mem_informationRegion_iff_triple W r).2
  refine ⟨hr₁, hr₂, v, hv, ?_⟩
  dsimp [gap] at hgap
  rw [max_le_iff, max_le_iff] at hgap
  exact ⟨by linarith [hgap.1], by linarith [hgap.2.1], by linarith [hgap.2.2]⟩

/-- The finite-time-sharing region already contains its boundary. -/
theorem isCompact_informationRegion (W : FiniteChannel (X₁ × X₂) Y) :
    IsCompact (informationRegion W) := by
  obtain ⟨bound, _, hbound⟩ := (isCompact_informationTriples W).isBounded.exists_pos_norm_le
  let box : Set RatePair := Set.Icc (0, 0) (bound, bound)
  let constraints : Set (RatePair × (Fin 3 → ℝ)) :=
    {point | point.1.1 ≤ point.2 0 ∧ point.1.2 ≤ point.2 1 ∧
      point.1.1 + point.1.2 ≤ point.2 2}
  have hclosed : IsClosed constraints := by
    have hfirst : IsClosed {point : RatePair × (Fin 3 → ℝ) | point.1.1 ≤ point.2 0} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hsecond : IsClosed {point : RatePair × (Fin 3 → ℝ) | point.1.2 ≤ point.2 1} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hsum : IsClosed {point : RatePair × (Fin 3 → ℝ) |
        point.1.1 + point.1.2 ≤ point.2 2} :=
      isClosed_le (by fun_prop) (by fun_prop)
    exact hfirst.inter (hsecond.inter hsum)
  have hcompact : IsCompact ((box ×ˢ informationTriples W) ∩ constraints) :=
    (isCompact_Icc.prod (isCompact_informationTriples W)).inter_right hclosed
  have heq : informationRegion W = Prod.fst '' ((box ×ˢ informationTriples W) ∩ constraints) := by
    ext r
    constructor
    · intro hr
      obtain ⟨hr₁, hr₂, v, hv, ha, hb, hc⟩ := (mem_informationRegion_iff_triple W r).1 hr
      have hcoordinate (i : Fin 3) : v i ≤ bound := by
        have hnorm := (norm_le_pi_norm v i).trans (hbound v hv)
        exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hnorm)
      refine ⟨(r, v), ⟨⟨?_, hv⟩, ha, hb, hc⟩, rfl⟩
      exact ⟨⟨hr₁, hr₂⟩, ⟨ha.trans (hcoordinate 0), hb.trans (hcoordinate 1)⟩⟩
    · rintro ⟨⟨r, v⟩, ⟨⟨hr, hv⟩, ha, hb, hc⟩, rfl⟩
      exact (mem_informationRegion_iff_triple W r).2
        ⟨hr.1.1, hr.1.2, v, hv, ha, hb, hc⟩
  rw [heq]
  exact hcompact.image continuous_fst

theorem isClosed_informationRegion (W : FiniteChannel (X₁ × X₂) Y) :
    IsClosed (informationRegion W) :=
  (isCompact_informationRegion W).isClosed

end CapacityAtlas.MultipleAccess
