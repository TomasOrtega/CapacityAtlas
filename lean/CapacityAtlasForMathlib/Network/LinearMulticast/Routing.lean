/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.LinearMulticast.Circuit

open scoped BigOperators Classical

namespace CapacityAtlas.LinearMulticast.Circuit

variable {I W : Type} [Fintype W] (G : Circuit I W)

/-- Edge-disjoint routes label each used wire by the input symbol it carries. -/
structure Routing (output : I → I ⊕ W) where
  label : W → Option I
  previous : W → Option W
  start : ∀ e i, label e = some i → previous e = none → G.input e i
  step : ∀ e i p, label e = some i → previous e = some p →
    G.parent e p ∧ label p = some i
  finish : ∀ i, output i = Sum.inl i ∨
    ∃ e, output i = Sum.inr e ∧ label e = some i

namespace Routing

variable {G} {output : I → I ⊕ W} (r : G.Routing output)

noncomputable def coefficient {R : Type*} [Semiring R] : G.Variable → R :=
  fun (e, port) ↦ match port with
    | Sum.inl j => if r.label e = some j ∧ r.previous e = none then 1 else 0
    | Sum.inr p => if r.previous e = some p ∧ (r.label e).isSome then 1 else 0

theorem transfer_eq {R : Type*} [CommSemiring R] (e : W) (i : I)
    (he : r.label e = some i) (j : I) :
    G.transfer (r.coefficient (R := R)) e j = if i = j then 1 else 0 := by
  induction h : G.height e using Nat.strong_induction_on generalizing e with
  | h n ih =>
    rw [transfer]
    cases hp : r.previous e with
    | none =>
      have hi := r.start e i he hp
      by_cases hij : i = j
      · subst j
        simp [coefficient, he, hp, hi]
      · simp [coefficient, he, hp, hij]
    | some p =>
      obtain ⟨hpar, hlabel⟩ := r.step e i p he hp
      have hsum : (∑ q : W, if hq : G.parent e q then
          r.coefficient (e, Sum.inr q) * G.transfer r.coefficient q j else 0) =
          G.transfer (r.coefficient (R := R)) p j := by
        rw [Finset.sum_eq_single p]
        · simp [hpar, coefficient, hp, he]
        · intro q _ hqp
          simp [coefficient, hp, he, Ne.symm hqp]
        · simp
      rw [hsum]
      simpa [coefficient, hp] using ih _ (h ▸ G.parent_lt e p hpar) p hlabel rfl

theorem matrix_eq_one {R : Type*} [CommSemiring R] :
    G.outputMatrix (r.coefficient (R := R)) output = 1 := by
  ext i j
  obtain hi | ⟨e, hi, he⟩ := r.finish i
  · simp [outputMatrix, hi, observed, Matrix.one_apply]
  · simpa [outputMatrix, hi, observed, Matrix.one_apply] using r.transfer_eq e i he j

end Routing

/-- Local predecessor certificates suffice to construct routing coefficients. -/
noncomputable def routingOfLabel (output : I → I ⊕ W) (label : W → Option I)
    (hlocal : ∀ e i, label e = some i → G.input e i ∨
      ∃ p, G.parent e p ∧ label p = some i)
    (hfinish : ∀ i, output i = Sum.inl i ∨
      ∃ e, output i = Sum.inr e ∧ label e = some i) : G.Routing output where
  label := label
  previous e := if h : ∃ p, G.parent e p ∧ label p = label e then some h.choose else none
  start e i he hp := by
    split_ifs at hp with h
    obtain hi | ⟨p, hpar, hlabel⟩ := hlocal e i he
    · exact hi
    · exact False.elim (h ⟨p, hpar, hlabel.trans he.symm⟩)
  step e i p he hp := by
    split_ifs at hp with h
    have hval : h.choose = p := Option.some.inj hp
    obtain ⟨hpar, hlabel⟩ := h.choose_spec
    exact ⟨hval ▸ hpar, hval ▸ hlabel.trans he⟩
  finish := hfinish

/-- Disjoint path memberships determine one input label per wire. -/
noncomputable def routingOfPaths (output : I → I ⊕ W) (paths : I → List W)
    (hdisjoint : ∀ e i j, e ∈ paths i → e ∈ paths j → i = j)
    (hlocal : ∀ i e, e ∈ paths i → G.input e i ∨
      ∃ p, p ∈ paths i ∧ G.parent e p)
    (hfinish : ∀ i, output i = Sum.inl i ∨
      ∃ e, output i = Sum.inr e ∧ e ∈ paths i) : G.Routing output := by
  let label : W → Option I := fun e ↦
    if h : ∃ i, e ∈ paths i then some h.choose else none
  have hlabel : ∀ e i, label e = some i ↔ e ∈ paths i := by
    intro e i
    dsimp only [label]
    split_ifs with h
    · constructor
      · intro he
        exact Option.some.inj he ▸ h.choose_spec
      · intro he
        exact congrArg some (hdisjoint e h.choose i h.choose_spec he)
    · simp only [false_iff]
      exact fun he ↦ h ⟨i, he⟩
  refine G.routingOfLabel output label ?_ ?_
  · intro e i he
    obtain hi | ⟨p, hp, hpar⟩ := hlocal i e ((hlabel e i).mp he)
    · exact Or.inl hi
    · exact Or.inr ⟨p, hpar, (hlabel p i).mpr hp⟩
  · intro i
    obtain hi | ⟨e, he, hm⟩ := hfinish i
    · exact Or.inl hi
    · exact Or.inr ⟨e, he, (hlabel e i).mpr hm⟩

theorem simultaneous_of_routing [Fintype I] {T : Type} [Fintype T]
    (output : T → I → I ⊕ W) (routes : ∀ t, G.Routing (output t)) :
    ∃ b : ℕ, 0 < b ∧ ∃ c : G.Variable → GaloisField 2 b,
      ∀ t, (G.outputMatrix c (output t)).det ≠ 0 :=
  G.simultaneous output fun t ↦ ⟨(routes t).coefficient, (routes t).matrix_eq_one⟩

end CapacityAtlas.LinearMulticast.Circuit
