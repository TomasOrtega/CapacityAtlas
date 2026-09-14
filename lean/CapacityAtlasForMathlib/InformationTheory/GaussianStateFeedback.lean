/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMultiuser
import CapacityAtlasForMathlib.InformationTheory.CausalHistories

open MeasureTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian

structure DirtyPaperCode (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → (Fin n → ℝ) → Fin n → ℝ
  encode_measurable : ∀ m, Measurable (encode m)
  decode : Decoder (Fin n → ℝ) messages

def PerMessageStateAveragePowerAdmissible (P Q : ℝ) {n : ℕ} (c : DirtyPaperCode n) : Prop :=
  ∀ m, Integrable (fun s ↦ ∑ t, (c.encode m s t) ^ 2) (noise Q n) ∧
    (∫ s, ∑ t, (c.encode m s t) ^ 2 ∂noise Q n) ≤ (n : ℝ) * P

noncomputable def dirtyPaperError (Q N : ℝ) {n : ℕ} (c : DirtyPaperCode n) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m,
    (((noise Q n).prod (noise N n)) {sz |
      c.decode.apply (fun t ↦ c.encode m sz.1 t + sz.1 t + sz.2 t) ≠ m}).toReal

noncomputable def dirtyPaperCapacity (P Q N : ℝ) : ℝ :=
  Operational.capacity DirtyPaperCode (fun _ c ↦ PerMessageStateAveragePowerAdmissible P Q c)
    (fun _ c ↦ dirtyPaperError Q N c)
    (fun n c ↦ Operational.messageRate c.messages n)

structure FeedbackCode (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → (t : Fin n) → (Fin t.val → ℝ) → ℝ
  encode_measurable : ∀ m t, Measurable (encode m t)
  decode : Decoder (Fin n → ℝ) messages

noncomputable def feedbackOutput {n : ℕ} (c : FeedbackCode n)
    (m : Fin c.messages) (z : Fin n → ℝ) : Fin n → ℝ :=
  CausalHistories.run 0 (fun t history zt ↦ c.encode m t history + zt) z

noncomputable def feedbackEnergy {n : ℕ} (c : FeedbackCode n)
    (m : Fin c.messages) (z : Fin n → ℝ) : ℝ :=
  ∑ t, (c.encode m t (CausalHistories.past (feedbackOutput c m z) t)) ^ 2

/-- Integrability prevents totalized integrals from admitting infinite-energy policies. -/
def MessageNoiseAveragePowerAdmissible (P N : ℝ) {n : ℕ} (c : FeedbackCode n) : Prop :=
  (∀ m, Integrable (feedbackEnergy c m) (noise N n)) ∧
    (c.messages : ℝ)⁻¹ * (∑ m, ∫ z, feedbackEnergy c m z ∂noise N n) ≤ (n : ℝ) * P

noncomputable def feedbackError (N : ℝ) {n : ℕ} (c : FeedbackCode n) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m,
    ((noise N n) {z | c.decode.apply (feedbackOutput c m z) ≠ m}).toReal

noncomputable def feedbackCapacity (P N : ℝ) : ℝ :=
  Operational.capacity FeedbackCode (fun _ c ↦ MessageNoiseAveragePowerAdmissible P N c)
    (fun _ c ↦ feedbackError N c) (fun n c ↦ Operational.messageRate c.messages n)

structure FeedbackMACCode (n : ℕ) where
  messages₁ : ℕ
  messages₂ : ℕ
  messages₁_pos : 0 < messages₁
  messages₂_pos : 0 < messages₂
  encode₁ : Fin messages₁ → (t : Fin n) → (Fin t.val → ℝ) → ℝ
  encode₂ : Fin messages₂ → (t : Fin n) → (Fin t.val → ℝ) → ℝ
  encode₁_measurable : ∀ m t, Measurable (encode₁ m t)
  encode₂_measurable : ∀ m t, Measurable (encode₂ m t)
  decode₁ : Decoder (Fin n → ℝ) messages₁
  decode₂ : Decoder (Fin n → ℝ) messages₂

noncomputable def feedbackMACOutput {n : ℕ} (c : FeedbackMACCode n)
    (m₁ : Fin c.messages₁) (m₂ : Fin c.messages₂) (z : Fin n → ℝ) : Fin n → ℝ :=
  CausalHistories.run 0
    (fun t history zt ↦ c.encode₁ m₁ t history + c.encode₂ m₂ t history + zt) z

noncomputable def feedbackMACEnergy {n : ℕ} (c : FeedbackMACCode n) (user : Bool)
    (m₁ : Fin c.messages₁) (m₂ : Fin c.messages₂) (z : Fin n → ℝ) : ℝ :=
  let y := feedbackMACOutput c m₁ m₂ z
  ∑ t, (if user then c.encode₂ m₂ t (CausalHistories.past y t)
    else c.encode₁ m₁ t (CausalHistories.past y t)) ^ 2

def SeparateMessageNoiseAveragePowerAdmissible (P₁ P₂ N : ℝ) {n : ℕ} (c : FeedbackMACCode n) : Prop :=
  ∀ user : Bool,
    (∀ m₁ m₂, Integrable (feedbackMACEnergy c user m₁ m₂) (noise N n)) ∧
    (c.messages₁ * c.messages₂ : ℝ)⁻¹ *
      (∑ m₁, ∑ m₂, ∫ z, feedbackMACEnergy c user m₁ m₂ z ∂noise N n) ≤
        (n : ℝ) * (if user then P₂ else P₁)

noncomputable def feedbackMACError (N : ℝ) {n : ℕ} (c : FeedbackMACCode n) : ℝ :=
  (c.messages₁ * c.messages₂ : ℝ)⁻¹ * ∑ m₁, ∑ m₂,
    ((noise N n) {z | let y := feedbackMACOutput c m₁ m₂ z
      ¬(c.decode₁.apply y = m₁ ∧ c.decode₂.apply y = m₂)}).toReal

noncomputable def feedbackMACCapacityRegion (P₁ P₂ N : ℝ) : Set RatePair :=
  Operational.achievableRegion FeedbackMACCode
    (fun _ c ↦ SeparateMessageNoiseAveragePowerAdmissible P₁ P₂ N c)
    (fun _ c ↦ feedbackMACError N c)
    (fun n c ↦ (Operational.messageRate c.messages₁ n, Operational.messageRate c.messages₂ n))

noncomputable def ozarowRegion (P₁ P₂ N : ℝ) : Set RatePair :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ 1 ∧
    r.1 ≤ awgnFormula (P₁ * (1 - ρ ^ 2)) N ∧
    r.2 ≤ awgnFormula (P₂ * (1 - ρ ^ 2)) N ∧
    r.1 + r.2 ≤ awgnFormula (P₁ + P₂ + 2 * ρ * Real.sqrt (P₁ * P₂)) N}

structure FadingCode (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → Fin n → ℝ
  decode : Decoder ((Fin n → ℝ) × (Fin n → ℝ)) messages

noncomputable def fadingError (law : Measure ℝ) [IsProbabilityMeasure law]
    (N : ℝ) {n : ℕ} (c : FadingCode n) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m,
    (((Measure.pi (fun _ : Fin n ↦ law)).prod (noise N n)) {hz |
      c.decode.apply (hz.1, fun t ↦ hz.1 t * c.encode m t + hz.2 t) ≠ m}).toReal

/-- Every deterministic codeword obeys the block-average power constraint.
There is no power adaptation to the iid gain known only to the receiver. -/
def FadingCodewordPowerAdmissible (P : ℝ) {n : ℕ} (c : FadingCode n) : Prop :=
  ∀ m, (∑ t, (c.encode m t) ^ 2) ≤ (n : ℝ) * P

noncomputable def fadingCapacity (law : Measure ℝ) [IsProbabilityMeasure law]
    (P N : ℝ) : ℝ :=
  Operational.capacity FadingCode
    (fun _ c ↦ FadingCodewordPowerAdmissible P c)
    (fun _ c ↦ fadingError law N c) (fun n c ↦ Operational.messageRate c.messages n)

noncomputable def fadingFormula (law : Measure ℝ) (P N : ℝ) : ℝ :=
  ∫ h, awgnFormula (h ^ 2 * P) N ∂law

end CapacityAtlas.Gaussian
