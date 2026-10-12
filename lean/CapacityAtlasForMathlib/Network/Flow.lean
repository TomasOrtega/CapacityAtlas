/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace CapacityAtlas.NetworkFlow

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def divergence (src dst : E → V) (f : E → ℤ) (v : V) : ℤ :=
  ∑ e, f e * ((if src e = v then 1 else 0) - (if dst e = v then 1 else 0))

def Bounded (cap : E → ℕ) (f : E → ℤ) : Prop :=
  ∀ e, 0 ≤ f e ∧ f e ≤ cap e

def Residual (src dst : E → V) (cap : E → ℕ) (f : E → ℤ) (a b : V) : Prop :=
  ∃ e, (src e = a ∧ dst e = b ∧ f e < cap e) ∨
    (dst e = a ∧ src e = b ∧ 0 < f e)

def push (f : E → ℤ) (e : E) (d : ℤ) : E → ℤ :=
  fun x ↦ f x + if x = e then d else 0

omit [Fintype V] in
theorem divergence_push (src dst : E → V) (f : E → ℤ) (e : E) (d : ℤ) (v : V) :
    divergence src dst (push f e d) v = divergence src dst f v +
      d * ((if src e = v then 1 else 0) - (if dst e = v then 1 else 0)) := by
  simp only [divergence, push, add_mul, Finset.sum_add_distrib]
  congr 1
  simp

omit [Fintype V] in
theorem exists_nodup_chain {r : V → V → Prop} {a b : V}
    (h : Relation.ReflTransGen r a b) :
    ∃ l : List V, (a :: l).Nodup ∧ (a :: l).IsChain r ∧
      (a :: l).getLast (by simp) = b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], by simp, .singleton _, rfl⟩
  | @head a c hac _ ih =>
    obtain ⟨l, hn, hc, hl⟩ := ih
    by_cases ha : a ∈ c :: l
    · obtain ⟨p, q, heq⟩ := List.mem_iff_append.mp ha
      refine ⟨q, ?_, ?_, ?_⟩
      · exact (heq ▸ hn).of_append_right
      · exact (heq ▸ hc).right_of_append
      · have hopt : (c :: l).getLast? = some b := by
          rw [List.getLast?_eq_some_getLast (by simp), hl]
        rw [heq, List.getLast?_append_of_ne_nil _ (by simp),
          List.getLast?_eq_some_getLast (by simp)] at hopt
        exact Option.some.inj hopt
    · exact ⟨c :: l, List.nodup_cons.mpr ⟨ha, hn⟩, .cons_cons hac hc, by simpa using hl⟩

omit [Fintype V] in
theorem augment_chain (src dst : E → V) (cap : E → ℕ) (f : E → ℤ)
    (hf : Bounded cap f) (a : V) (l : List V) (hn : (a :: l).Nodup)
    (hc : (a :: l).IsChain (Residual src dst cap f)) :
    ∃ g : E → ℤ, Bounded cap g ∧
      (∀ v, divergence src dst g v = divergence src dst f v +
        ((if a = v then 1 else 0) - (if (a :: l).getLast (by simp) = v then 1 else 0))) ∧
      (∀ e, src e ∉ a :: l ∨ dst e ∉ a :: l → g e = f e) := by
  induction l generalizing a with
  | nil =>
    refine ⟨f, hf, ?_, ?_⟩
    · intro v
      simp only [List.getLast_singleton]
      split_ifs <;> omega
    · intro e _
      rfl
  | cons b l ih =>
    obtain ⟨hna, hnt⟩ := List.nodup_cons.mp hn
    obtain ⟨hab, hct⟩ := List.isChain_cons_cons.mp hc
    obtain ⟨g, hg, hdiv, hsupport⟩ := ih b hnt hct
    obtain ⟨e, hforward | hbackward⟩ := hab
    · obtain ⟨hes, het, hecap⟩ := hforward
      have hge : g e = f e := hsupport e (Or.inl (hes ▸ hna))
      refine ⟨push g e 1, ?_, ?_, ?_⟩
      · intro x
        by_cases hx : x = e
        · subst x
          simp only [push, hge]
          have := hf e
          constructor <;> omega
        · simpa [push, hx] using hg x
      · intro v
        rw [divergence_push, hdiv]
        simp only [hes, het, List.getLast_cons_cons, one_mul]
        ring_nf
      · intro x hx
        have hxe : x ≠ e := by
          intro h
          subst x
          rcases hx with hx | hx
          · exact hx (by simp [hes])
          · exact hx (by simp [het])
        rw [push, if_neg hxe, add_zero]
        apply hsupport
        rcases hx with hx | hx
        · exact Or.inl (fun h ↦ hx (List.mem_cons_of_mem _ h))
        · exact Or.inr (fun h ↦ hx (List.mem_cons_of_mem _ h))
    · obtain ⟨het, hes, hepos⟩ := hbackward
      have hge : g e = f e := hsupport e (Or.inr (het ▸ hna))
      refine ⟨push g e (-1), ?_, ?_, ?_⟩
      · intro x
        by_cases hx : x = e
        · subst x
          simp only [push, hge]
          have := hf e
          constructor <;> omega
        · simpa [push, hx] using hg x
      · intro v
        rw [divergence_push, hdiv]
        simp only [hes, het, List.getLast_cons_cons]
        ring_nf
      · intro x hx
        have hxe : x ≠ e := by
          intro h
          subst x
          rcases hx with hx | hx
          · exact hx (by simp [hes])
          · exact hx (by simp [het])
        rw [push, if_neg hxe, add_zero]
        apply hsupport
        rcases hx with hx | hx
        · exact Or.inl (fun h ↦ hx (List.mem_cons_of_mem _ h))
        · exact Or.inr (fun h ↦ hx (List.mem_cons_of_mem _ h))


def Conserved (src dst : E → V) (s t : V) (f : E → ℤ) : Prop :=
  ∀ v, v ≠ s → v ≠ t → divergence src dst f v = 0

omit [Fintype V] [DecidableEq E] in
theorem exists_max_flow (src dst : E → V) (cap : E → ℕ) (s t : V) :
    ∃ f : E → ℤ, Bounded cap f ∧ Conserved src dst s t f ∧
      ∀ g, Bounded cap g → Conserved src dst s t g →
        divergence src dst g s ≤ divergence src dst f s := by
  classical
  let F := {p : (e : E) → Fin (cap e + 1) //
    Conserved src dst s t (fun e ↦ (p e).val)}
  have hz : Conserved src dst s t (fun _ ↦ (0 : ℤ)) := by
    intro v _ _
    simp [divergence]
  letI : Nonempty F := ⟨⟨fun e ↦ ⟨0, by omega⟩, hz⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_max (fun p : F ↦
    divergence src dst (fun e ↦ (p.val e).val) s)
  refine ⟨fun e ↦ (p.val e).val, ?_, p.property, ?_⟩
  · intro e
    have := (p.val e).isLt
    dsimp
    constructor <;> omega
  · intro g hg hc
    let q : (e : E) → Fin (cap e + 1) := fun e ↦
      ⟨(g e).toNat, by have := hg e; omega⟩
    have heq : (fun e ↦ ((q e).val : ℤ)) = g := by
      funext e
      exact Int.toNat_of_nonneg (hg e).1
    simpa only [heq] using hp ⟨q, heq ▸ hc⟩

omit [Fintype V] in
theorem residual_not_reachable_of_max (src dst : E → V) (cap : E → ℕ)
    (s t : V) (hst : s ≠ t) (f : E → ℤ) (hf : Bounded cap f)
    (hc : Conserved src dst s t f)
    (hm : ∀ g, Bounded cap g → Conserved src dst s t g →
      divergence src dst g s ≤ divergence src dst f s) :
    ¬ Relation.ReflTransGen (Residual src dst cap f) s t := by
  intro h
  obtain ⟨l, hn, hl, ht⟩ := exists_nodup_chain h
  obtain ⟨g, hg, hd, _⟩ := augment_chain src dst cap f hf s l hn hl
  have hgc : Conserved src dst s t g := by
    intro v hvs hvt
    rw [hd, hc v hvs hvt, ht]
    simp [Ne.symm hvs, Ne.symm hvt]
  have := hm g hg hgc
  rw [hd, ht] at this
  simp only [ite_true, Ne.symm hst, if_false] at this
  omega

noncomputable def cutCapacity (src dst : E → V) (cap : E → ℕ) (S : Finset V) : ℕ :=
  ∑ e, if src e ∈ S ∧ dst e ∉ S then cap e else 0

omit [Fintype V] [DecidableEq E] in
theorem sum_divergence (src dst : E → V) (f : E → ℤ) (S : Finset V) :
    ∑ v ∈ S, divergence src dst f v =
      ∑ e, f e * ((if src e ∈ S then 1 else 0) - (if dst e ∈ S then 1 else 0)) := by
  simp only [divergence]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  congr 2 <;> simp [eq_comm]

omit [Fintype V] [DecidableEq E] in
theorem sum_divergence_eq_value (src dst : E → V) (s t : V) (f : E → ℤ)
    (hc : Conserved src dst s t f) (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    ∑ v ∈ S, divergence src dst f v = divergence src dst f s := by
  apply Finset.sum_eq_single s
  · intro v hv hvs
    exact hc v hvs (fun h ↦ ht (h ▸ hv))
  · exact fun h ↦ False.elim (h hs)

/-- An integral flow attains the capacity of a separating cut. -/
theorem integral_max_flow_min_cut (src dst : E → V) (cap : E → ℕ)
    (s t : V) (hst : s ≠ t) :
    ∃ f : E → ℤ, ∃ S : Finset V, Bounded cap f ∧ Conserved src dst s t f ∧
      s ∈ S ∧ t ∉ S ∧ divergence src dst f s = cutCapacity src dst cap S := by
  classical
  obtain ⟨f, hf, hc, hm⟩ := exists_max_flow src dst cap s t
  let S := Finset.univ.filter (Relation.ReflTransGen (Residual src dst cap f) s)
  have hs : s ∈ S := by simp [S, Relation.ReflTransGen.refl]
  have ht : t ∉ S := by
    simpa [S] using residual_not_reachable_of_max src dst cap s t hst f hf hc hm
  refine ⟨f, S, hf, hc, hs, ht, ?_⟩
  rw [← sum_divergence_eq_value src dst s t f hc S hs ht,
    sum_divergence, cutCapacity, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hse : src e ∈ S <;> by_cases hte : dst e ∈ S
  · simp [hse, hte]
  · have he : f e = cap e := by
      have hn : ¬ f e < cap e := by
        intro h
        have ha : Relation.ReflTransGen (Residual src dst cap f) s (src e) :=
          (Finset.mem_filter.mp hse).2
        have hb := ha.tail (show Residual src dst cap f (src e) (dst e) from
          ⟨e, Or.inl ⟨rfl, rfl, h⟩⟩)
        exact hte (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
      have := hf e
      omega
    simp [hse, hte, he]
  · have he : f e = 0 := by
      have hn : ¬ 0 < f e := by
        intro h
        have ha : Relation.ReflTransGen (Residual src dst cap f) s (dst e) :=
          (Finset.mem_filter.mp hte).2
        have hb := ha.tail (show Residual src dst cap f (dst e) (src e) from
          ⟨e, Or.inr ⟨rfl, rfl, h⟩⟩)
        exact hse (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
      have := hf e
      omega
    simp [hse, hte, he]
  · simp [hse, hte]


def Route (src dst : E → V) : V → V → List E → Prop
  | s, t, [] => s = t
  | s, t, e :: es => src e = s ∧ Route src dst (dst e) t es

def Positive (src dst : E → V) (f : E → ℤ) (a b : V) : Prop :=
  ∃ e, src e = a ∧ dst e = b ∧ 0 < f e

omit [Fintype V] in
theorem subtract_chain (src dst : E → V) (cap : E → ℕ) (f : E → ℤ)
    (hf : Bounded cap f) (a : V) (l : List V) (hn : (a :: l).Nodup)
    (hc : (a :: l).IsChain (Positive src dst f)) :
    ∃ es : List E, Route src dst a ((a :: l).getLast (by simp)) es ∧ es.Nodup ∧
      (∀ e ∈ es, src e ∈ a :: l ∧ dst e ∈ a :: l) ∧
      Bounded cap (fun e ↦ f e - (es.count e : ℤ)) ∧
      (∀ v, divergence src dst (fun e ↦ f e - (es.count e : ℤ)) v =
        divergence src dst f v -
          ((if a = v then 1 else 0) - (if (a :: l).getLast (by simp) = v then 1 else 0))) := by
  induction l generalizing a with
  | nil =>
    refine ⟨[], rfl, by simp, by simp, ?_, ?_⟩
    · simpa using hf
    · intro v
      simp only [List.count_nil, Nat.cast_zero, sub_zero, List.getLast_singleton]
      change divergence src dst f v = divergence src dst f v - _
      split_ifs <;> omega
  | cons b l ih =>
    obtain ⟨hna, hnt⟩ := List.nodup_cons.mp hn
    obtain ⟨hab, hct⟩ := List.isChain_cons_cons.mp hc
    obtain ⟨es, hr, hnes, hmem, hg, hdiv⟩ := ih b hnt hct
    obtain ⟨e, hes, het, hepos⟩ := hab
    have he : e ∉ es := by
      intro h
      exact hna (hes ▸ (hmem e h).1)
    have hcount : es.count e = 0 := List.count_eq_zero.mpr he
    have heq : (fun x ↦ f x - ((e :: es).count x : ℤ)) =
        push (fun x ↦ f x - (es.count x : ℤ)) e (-1) := by
      funext x
      by_cases hx : x = e
      · subst x
        simp [push, hcount, sub_eq_add_neg]
      · simp [push, hx, Ne.symm hx]
    refine ⟨e :: es, ?_, List.nodup_cons.mpr ⟨he, hnes⟩, ?_, ?_, ?_⟩
    · exact ⟨hes, by simpa only [het, List.getLast_cons_cons] using hr⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [hes, het]
      · exact ⟨List.mem_cons_of_mem _ (hmem x hx).1,
          List.mem_cons_of_mem _ (hmem x hx).2⟩
    · rw [heq]
      intro x
      by_cases hx : x = e
      · subst x
        simp only [push, hcount, Nat.cast_zero, sub_zero]
        have := hf e
        constructor <;> omega
      · simpa [push, hx] using hg x
    · intro v
      rw [heq, divergence_push, hdiv]
      simp only [hes, het, List.getLast_cons_cons]
      ring_nf

omit [DecidableEq E] in
theorem positive_reachable (src dst : E → V) (cap : E → ℕ)
    (s t : V) (f : E → ℤ) (hf : Bounded cap f)
    (hc : Conserved src dst s t f) (hpos : 0 < divergence src dst f s) :
    Relation.ReflTransGen (Positive src dst f) s t := by
  classical
  by_contra ht
  let S := Finset.univ.filter (Relation.ReflTransGen (Positive src dst f) s)
  have hs : s ∈ S := by simp [S, Relation.ReflTransGen.refl]
  have hts : t ∉ S := by simpa [S] using ht
  have hsum : divergence src dst f s ≤ 0 := by
    rw [← sum_divergence_eq_value src dst s t f hc S hs hts, sum_divergence]
    apply Finset.sum_nonpos
    intro e _
    by_cases hse : src e ∈ S <;> by_cases hte : dst e ∈ S
    · simp [hse, hte]
    · have he : f e = 0 := by
        have hn : ¬ 0 < f e := by
          intro h
          have ha : Relation.ReflTransGen (Positive src dst f) s (src e) :=
            (Finset.mem_filter.mp hse).2
          have hb := ha.tail ⟨e, rfl, rfl, h⟩
          exact hte (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
        have := hf e
        omega
      simp [hse, hte, he]
    · simpa [hse, hte] using (hf e).1
    · simp [hse, hte]
  omega

/-- A positive integral flow contains a simple source-to-sink route. -/
theorem subtract_route (src dst : E → V) (cap : E → ℕ)
    (s t : V) (f : E → ℤ) (hf : Bounded cap f)
    (hc : Conserved src dst s t f) (hpos : 0 < divergence src dst f s) :
    ∃ es : List E, Route src dst s t es ∧ es.Nodup ∧
      Bounded cap (fun e ↦ f e - (es.count e : ℤ)) ∧
      Conserved src dst s t (fun e ↦ f e - (es.count e : ℤ)) ∧
      (∀ v, divergence src dst (fun e ↦ f e - (es.count e : ℤ)) v =
        divergence src dst f v - ((if s = v then 1 else 0) - (if t = v then 1 else 0))) := by
  obtain ⟨l, hn, hl, ht⟩ := exists_nodup_chain (positive_reachable src dst cap s t f hf hc hpos)
  obtain ⟨es, hr, he, _, hg, hd⟩ := subtract_chain src dst cap f hf s l hn hl
  rw [ht] at hr hd
  refine ⟨es, hr, he, hg, ?_, hd⟩
  intro v hvs hvt
  rw [hd, hc v hvs hvt]
  simp [Ne.symm hvs, Ne.symm hvt]


/-- Integral flow decomposes into routes, with unused flow allowed. -/
theorem route_packing_of_flow (src dst : E → V) (cap : E → ℕ)
    (s t : V) (hst : s ≠ t) (k : ℕ) (f : E → ℤ) (hf : Bounded cap f)
    (hc : Conserved src dst s t f) (hk : (k : ℤ) ≤ divergence src dst f s) :
    ∃ routes : Fin k → List E,
      (∀ i, Route src dst s t (routes i) ∧ (routes i).Nodup) ∧
      ∀ e, (∑ i, ((routes i).count e : ℤ)) ≤ f e := by
  induction k generalizing f with
  | zero =>
    refine ⟨Fin.elim0, by simp, ?_⟩
    intro e
    simpa using (hf e).1
  | succ k ih =>
    have hpos : 0 < divergence src dst f s := by omega
    obtain ⟨es, hr, hn, hg, hgc, hd⟩ := subtract_route src dst cap s t f hf hc hpos
    have hkg : (k : ℤ) ≤ divergence src dst (fun e ↦ f e - (es.count e : ℤ)) s := by
      rw [hd]
      simp only [ite_true, Ne.symm hst, if_false]
      omega
    obtain ⟨routes, hrs, hbound⟩ := ih _ hg hgc hkg
    refine ⟨Fin.cons es routes, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact ⟨hr, hn⟩
      · exact hrs j
    · intro e
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have := hbound e
      omega

/-- Directed integral max-flow/min-cut in path-packing form. -/
theorem route_packing_of_cut (src dst : E → V) (cap : E → ℕ)
    (s t : V) (hst : s ≠ t) (k : ℕ)
    (hcut : ∀ S : Finset V, s ∈ S → t ∉ S → k ≤ cutCapacity src dst cap S) :
    ∃ routes : Fin k → List E,
      (∀ i, Route src dst s t (routes i) ∧ (routes i).Nodup) ∧
      ∀ e, (∑ i, (routes i).count e) ≤ cap e := by
  obtain ⟨f, S, hf, hc, hs, ht, hv⟩ := integral_max_flow_min_cut src dst cap s t hst
  have hk : (k : ℤ) ≤ divergence src dst f s := by
    rw [hv]
    exact_mod_cast hcut S hs ht
  obtain ⟨routes, hr, hb⟩ := route_packing_of_flow src dst cap s t hst k f hf hc hk
  refine ⟨routes, hr, ?_⟩
  intro e
  have hh := (hb e).trans (hf e).2
  exact_mod_cast hh


omit [Fintype V] [DecidableEq V] [Fintype E] in
theorem packed_routes_unique {I : Type*} [Fintype I] (routes : I → List E)
    (hbound : ∀ e, (∑ i, (routes i).count e) ≤ 1)
    {e : E} {i j : I} (hi : e ∈ routes i) (hj : e ∈ routes j) : i = j := by
  classical
  by_contra hij
  have hsum : (routes i).count e + (routes j).count e ≤ ∑ a, (routes a).count e := by
    simpa [hij] using (Finset.sum_le_sum_of_subset (f := fun a ↦ (routes a).count e)
      (show ({i, j} : Finset I) ⊆ Finset.univ from Finset.subset_univ _))
  have hci := List.count_pos_iff.mpr hi
  have hcj := List.count_pos_iff.mpr hj
  have hb := hbound e
  omega

namespace Route

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem first_source {src dst : E → V} {s t : V} {e : E} {es : List E}
    (h : Route src dst s t (e :: es)) : src e = s := h.1

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem last_target {src dst : E → V} {s t : V} {es : List E}
    (h : Route src dst s t es) (hne : es ≠ []) : dst (es.getLast hne) = t := by
  induction es generalizing s with
  | nil => exact False.elim (hne rfl)
  | cons e es ih =>
    cases es with
    | nil => exact h.2
    | cons e' es => exact ih h.2 (by simp)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem source_or_predecessor {src dst : E → V} {s t : V} {es : List E}
    (h : Route src dst s t es) {e : E} (he : e ∈ es) :
    src e = s ∨ ∃ p ∈ es, dst p = src e := by
  induction es generalizing s with
  | nil => simp at he
  | cons p es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact Or.inl h.1
    · rcases ih h.2 he with hp | ⟨q, hq, hqe⟩
      · exact Or.inr ⟨p, by simp, hp.symm⟩
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hqe⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem eq_nil_of_no_source {src dst : E → V} {s t : V} {es : List E}
    (h : Route src dst s t es) (hn : ∀ e ∈ es, src e ≠ s) : es = [] := by
  cases es with
  | nil => rfl
  | cons e es => exact False.elim (hn e (by simp) h.1)

end Route

end CapacityAtlas.NetworkFlow
