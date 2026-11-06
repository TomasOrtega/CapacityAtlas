/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianWiretap

namespace CapacityAtlas.Tests

private def distinctSymbolWiretapCode : Gaussian.WiretapCode 1 where
  messages := 2
  messages_pos := by decide
  seeds := 1
  seeds_pos := by decide
  encode := fun m _ _ ↦ (m.val : ℝ)
  decode := {
    apply := fun _ ↦ 0
    measurable_fiber := fun m ↦ by
      by_cases h : (0 : Fin 2) = m <;> simp [h] }

/-- Nonpositive variance gives a totalized density formula, outside its information domain. -/
@[capacity_test]
theorem gaussianWiretap_density_formula_nonpositive_noise {n : ℕ} (N : ℝ) (hN : N ≤ 0)
    (c : Gaussian.WiretapCode (n + 1)) :
    (∀ m z, Gaussian.wiretapConditionalDensity N c m z = 0) ∧
      (∀ z, Gaussian.wiretapOutputDensity N c z = 0) ∧
      Gaussian.wiretapLeakage N c = 0 := by
  simp [Gaussian.wiretapConditionalDensity, Gaussian.wiretapOutputDensity,
    Gaussian.wiretapLeakage, Real.toNNReal_of_nonpos hN]

/-- Distinct noiseless outputs coexist with the density formula's zero boundary value. -/
@[capacity_test]
theorem gaussianWiretap_zero_noise_density_boundary :
    Function.Injective (fun m ↦ distinctSymbolWiretapCode.encode m ⟨0, by decide⟩ 0) ∧
      Gaussian.wiretapLeakage 0 distinctSymbolWiretapCode = 0 := by
  constructor
  · intro m m' h
    apply Fin.ext
    change (m.val : ℝ) = (m'.val : ℝ) at h
    exact_mod_cast h
  · exact (gaussianWiretap_density_formula_nonpositive_noise 0 le_rfl
      distinctSymbolWiretapCode).2.2

end CapacityAtlas.Tests
