/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.Multisource.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Logic.Equiv.Prod

open scoped BigOperators

namespace CapacityAtlas.Multisource.Network.Code

variable {vertices edges sources : ℕ} {G : Multisource.Network vertices edges sources}
  {n : ℕ} (c : G.Code n)

/-- The cut transcript and messages outside the cut determine every packet
sent by a vertex outside the cut. -/
theorem packet_eq_of_cut (cut : Finset (Fin vertices))
    (m m' : Message c.messages)
    (hmessage : ∀ i, G.sourceNode i ∉ cut → m i = m' i)
    (hcut : ∀ e, G.source e ∈ cut → G.target e ∉ cut → c.packet m e = c.packet m' e) :
    ∀ e, G.source e ∉ cut → c.packet m e = c.packet m' e := by
  intro e he
  induction h : (G.source e).val using Nat.strong_induction_on generalizing e with
  | h k ih =>
    apply c.packet_local e m m'
    · intro i hi
      exact hmessage i (by simpa [hi] using he)
    · intro a ha
      by_cases hacut : G.source a ∈ cut
      · exact hcut a hacut (by simpa [ha] using he)
      · apply ih (G.source a).val _ a hacut rfl
        rw [← h, ← ha]
        exact G.increasing a

theorem decode_eq_of_cut (cut : Finset (Fin vertices))
    (m m' : Message c.messages)
    (hmessage : ∀ i, G.sourceNode i ∉ cut → m i = m' i)
    (hcut : ∀ e, G.source e ∈ cut → G.target e ∉ cut → c.packet m e = c.packet m' e)
    (v : Fin vertices) (hv : v ∈ G.sinks) (hout : v ∉ cut) :
    c.decode v hv m = c.decode v hv m' := by
  apply c.decode_local v hv m m'
  · intro i hi
    exact hmessage i (by simpa [hi] using hout)
  · intro a ha
    by_cases hacut : G.source a ∈ cut
    · exact hcut a hacut (by simpa [ha] using hout)
    · exact c.packet_eq_of_cut cut m m' hmessage hcut a hacut

abbrev CutKey (cut : Finset (Fin vertices)) :=
  ((i : {i : Fin sources // G.sourceNode i ∉ cut}) → Fin (c.messages i.val)) ×
  ((e : {e : Fin edges // G.source e ∈ cut ∧ G.target e ∉ cut}) → G.Packet n e.val)

noncomputable def cutKey (cut : Finset (Fin vertices))
    (m : Message c.messages) : c.CutKey cut :=
  (fun i ↦ m i.val, fun e ↦ c.packet m e.val)

theorem successful_cutKey_injective (cut : Finset (Fin vertices))
    (v : Fin vertices) (hv : v ∈ G.sinks) (hout : v ∉ cut) :
    Function.Injective (fun m : {m : Message c.messages // c.Successful m} ↦
      c.cutKey cut m.val) := by
  intro m m' heq
  apply Subtype.ext
  have hdecoded := c.decode_eq_of_cut cut m.val m'.val
    (fun i hi ↦ congrFun (congrArg Prod.fst heq) ⟨i, hi⟩)
    (fun e hsrc htar ↦ congrFun (congrArg Prod.snd heq) ⟨e, hsrc, htar⟩) v hv hout
  exact (m.property v hv).symm.trans (hdecoded.trans (m'.property v hv))

theorem successCount_le_cutKey (cut : Finset (Fin vertices))
    (v : Fin vertices) (hv : v ∈ G.sinks) (hout : v ∉ cut) :
    c.successCount ≤ Fintype.card (c.CutKey cut) := by
  classical
  exact Fintype.card_le_of_injective _ (c.successful_cutKey_injective cut v hv hout)

theorem card_message_le_twice_cutKey (cut : Finset (Fin vertices))
    (v : Fin vertices) (hv : v ∈ G.sinks) (hout : v ∉ cut)
    (herr : c.error ≤ 1 / 2) :
    (Fintype.card (Message c.messages) : ℝ) ≤ 2 * Fintype.card (c.CutKey cut) := by
  have hpos : (0 : ℝ) < Fintype.card (Message c.messages) := by
    exact_mod_cast Fintype.card_pos
  have hs : (c.successCount : ℝ) ≤ Fintype.card (c.CutKey cut) := by
    exact_mod_cast c.successCount_le_cutKey cut v hv hout
  have hf : (1 / 2 : ℝ) ≤ (c.successCount : ℝ) /
      Fintype.card (Message c.messages) := by
    unfold error at herr
    linarith
  have := (le_div_iff₀ hpos).mp hf
  linarith

theorem logb_card_message :
    Real.logb 2 (Fintype.card (Message c.messages)) =
      ∑ i, Real.logb 2 (c.messages i) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, Nat.cast_prod]
  exact Real.logb_prod _ _ (fun i _ ↦ by exact_mod_cast (c.messages_pos i).ne')

theorem logb_card_cutKey (cut : Finset (Fin vertices)) :
    Real.logb 2 (Fintype.card (c.CutKey cut)) =
      (∑ i : {i : Fin sources // G.sourceNode i ∉ cut}, Real.logb 2 (c.messages i.val)) +
      ∑ e : {e : Fin edges // G.source e ∈ cut ∧ G.target e ∉ cut},
        (G.packetBits n e.val : ℝ) := by
  classical
  have hm : (∏ i : {i : Fin sources // G.sourceNode i ∉ cut}, (c.messages i.val : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ ↦ by exact_mod_cast (c.messages_pos i.val).ne')
  have hp : (∏ e : {e : Fin edges // G.source e ∈ cut ∧ G.target e ∉ cut},
      (2 : ℝ) ^ G.packetBits n e.val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun e _ ↦ pow_ne_zero _ (by norm_num))
  simp only [CutKey, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_prod, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.logb_mul hm hp, Real.logb_prod _ _
    (fun i _ ↦ by exact_mod_cast (c.messages_pos i.val).ne'),
    Real.logb_prod _ _ (fun e _ ↦ pow_ne_zero _ (by norm_num))]
  simp [Real.logb_pow]

theorem sum_logb_messages_le_cutBits (cut : Finset (Fin vertices))
    (v : Fin vertices) (hv : v ∈ G.sinks) (hout : v ∉ cut)
    (herr : c.error ≤ 1 / 2) :
    (∑ i : {i : Fin sources // G.sourceNode i ∈ cut}, Real.logb 2 (c.messages i.val)) ≤
      (∑ e : {e : Fin edges // G.source e ∈ cut ∧ G.target e ∉ cut},
        (G.packetBits n e.val : ℝ)) + 1 := by
  classical
  have hcardpos : (0 : ℝ) < Fintype.card (Message c.messages) := by
    exact_mod_cast Fintype.card_pos
  have hcard := c.card_message_le_twice_cutKey cut v hv hout herr
  have hkpos : (0 : ℝ) < Fintype.card (c.CutKey cut) := by nlinarith
  have hlog := (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hcardpos hcard)
  rw [Real.logb_mul (by norm_num) hkpos.ne', Real.logb_self_eq_one (by norm_num), c.logb_card_message, c.logb_card_cutKey] at hlog
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin sources ↦ G.sourceNode i ∈ cut) (fun i ↦ Real.logb 2 (c.messages i))
  linarith

end CapacityAtlas.Multisource.Network.Code

namespace CapacityAtlas.Multisource.Network

variable {vertices edges sources : ℕ} (G : Multisource.Network vertices edges sources)

theorem cutDemand_eq_subtype (cut : Finset (Fin vertices)) (r : Fin sources → ℝ) :
    G.cutDemand cut r = ∑ i : {i : Fin sources // G.sourceNode i ∈ cut}, r i.val := by
  classical
  rw [cutDemand, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem cutRate_eq_subtype (cut : Finset (Fin vertices)) :
    G.cutRate cut = ∑ e : {e : Fin edges // G.source e ∈ cut ∧ G.target e ∉ cut},
      G.linkRate e.val := by
  classical
  rw [cutRate, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem cutRate_nonneg (cut : Finset (Fin vertices)) : 0 ≤ G.cutRate cut := by
  rw [G.cutRate_eq_subtype]
  exact Finset.sum_nonneg (fun e _ ↦ G.linkRate_nonneg e.val)

/-- A block code with joint error at most one half has at most one bit of
excess total message rate across any cut. -/
theorem code_cutDemand_le {n : ℕ} (c : G.Code n) (hn : 0 < n)
    (cut : Finset (Fin vertices)) (v : Fin vertices) (hv : v ∈ G.sinks)
    (hout : v ∉ cut) (herr : c.error ≤ 1 / 2) :
    G.cutDemand cut c.rate ≤ G.cutRate cut + (n : ℝ)⁻¹ := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hfinite := c.sum_logb_messages_le_cutBits cut v hv hout herr
  have hbits :
      (∑ e : {e : Fin edges // G.source e ∈ cut ∧ G.target e ∉ cut},
        (G.packetBits n e.val : ℝ)) ≤ (n : ℝ) * G.cutRate cut := by
    rw [G.cutRate_eq_subtype, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    exact Nat.floor_le (mul_nonneg hn'.le (G.linkRate_nonneg e.val))
  rw [G.cutDemand_eq_subtype]
  simp only [Code.rate, Operational.messageRate, ← Finset.sum_div]
  apply (div_le_iff₀ hn').mpr
  have hinv : (n : ℝ)⁻¹ * n = 1 := inv_mul_cancel₀ hn'.ne'
  nlinarith

theorem cutDemand_le_of_coordinate_le (cut : Finset (Fin vertices))
    {r s : Fin sources → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i, r i - ε ≤ s i) :
    G.cutDemand cut r ≤ G.cutDemand cut s + (sources : ℝ) * ε := by
  classical
  have hi (i : Fin sources) :
      (if G.sourceNode i ∈ cut then r i else 0) ≤
        (if G.sourceNode i ∈ cut then s i else 0) + ε := by
    by_cases hc : G.sourceNode i ∈ cut
    · simp only [hc, ite_true]
      linarith [h i]
    · simp [hc, hε]
  simpa [cutDemand, Finset.sum_add_distrib, mul_comm] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)

/-- The cut-set outer bound permits arbitrary nonlinear local encoders and
vanishing joint average error. -/
theorem capacityRegion_subset_cutRegion : G.capacityRegion ⊆ G.cutRegion := by
  intro r hr
  refine ⟨hr.1, fun v hv cut hout ↦ ?_⟩
  by_contra hbound
  have hgap : 0 < G.cutDemand cut r - G.cutRate cut := sub_pos.mpr (lt_of_not_ge hbound)
  let ε : ℝ := min (1 / 2) ((G.cutDemand cut r - G.cutRate cut) /
    (2 * ((sources : ℝ) + 1)))
  have hdenom : (0 : ℝ) < 2 * ((sources : ℝ) + 1) := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hgap hdenom)
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hεgap : ε * (2 * ((sources : ℝ) + 1)) ≤
      G.cutDemand cut r - G.cutRate cut := by
    exact (le_div_iff₀ hdenom).mp (min_le_right _ _)
  obtain ⟨N, hN, hcodes⟩ := hr.2 ε hε
  have hlim : Filter.Tendsto
      (fun n : ℕ ↦ G.cutRate cut + (sources : ℝ) * ε + (n : ℝ)⁻¹)
      Filter.atTop (nhds (G.cutRate cut + (sources : ℝ) * ε)) := by
    simpa using tendsto_const_nhds.add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hfin : G.cutDemand cut r ≤ G.cutRate cut + (sources : ℝ) * ε := by
    apply ge_of_tendsto hlim
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    obtain ⟨c, _, herr, hrate⟩ := hcodes n hn
    have hb := G.code_cutDemand_le c (hN.trans_le hn) cut v hv hout (herr.trans hεhalf)
    have hrates := G.cutDemand_le_of_coordinate_le cut hε.le hrate
    linarith
  have hsrc : (0 : ℝ) ≤ sources := Nat.cast_nonneg sources
  nlinarith

end CapacityAtlas.Multisource.Network
