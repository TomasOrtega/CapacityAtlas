/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Basic
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace CapacityAtlas.Gaussian.Interference

theorem measurePreserving_pi_select {α S T : Type*} [MeasurableSpace α]
    [Fintype S] [Fintype T] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : S → T) (hf : Function.Injective f) :
    MeasurePreserving (fun x : T → α => x ∘ f)
      (Measure.pi fun _ : T => ν) (Measure.pi fun _ : S => ν) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  have hind : iIndepFun (fun t (x : T → α) => x t) (Measure.pi fun _ : T => ν) :=
    iIndepFun_pi fun _ => measurable_id.aemeasurable
  have h := (hind.precomp hf).map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (f i)).aemeasurable)
  simpa only [Function.comp_def, (measurePreserving_eval (fun _ : T => ν) _).map_eq] using h

theorem measurePreserving_pi_curry {α S T : Type*} [MeasurableSpace α]
    [Fintype S] [Fintype T] (ν : S → T → Measure α)
    [∀ s t, IsProbabilityMeasure (ν s t)] :
    MeasurePreserving (fun x : S × T → α => fun s t => x (s, t))
      (Measure.pi fun p : S × T => ν p.1 p.2)
      (Measure.pi fun s => Measure.pi fun t => ν s t) := by
  refine ⟨by fun_prop, ?_⟩
  convert Measure.infinitePi_map_curry ν using 1 <;>
    simp only [Measure.infinitePi_eq_pi]
  rfl

theorem measurePreserving_pi_uncurry {α S T : Type*} [MeasurableSpace α]
    [Fintype S] [Fintype T] (ν : S → T → Measure α)
    [∀ s t, IsProbabilityMeasure (ν s t)] :
    MeasurePreserving (fun x : S → T → α => fun p : S × T => x p.1 p.2)
      (Measure.pi fun s => Measure.pi fun t => ν s t)
      (Measure.pi fun p : S × T => ν p.1 p.2) := by
  refine ⟨by fun_prop, ?_⟩
  convert Measure.infinitePi_map_curry_symm ν using 1 <;>
    simp only [Measure.infinitePi_eq_pi]
  rfl

theorem measurePreserving_pi_swap {α S T : Type*} [MeasurableSpace α]
    [Fintype S] [Fintype T] (ν : Measure α) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun x : S → T → α => fun t s => x s t)
      (Measure.pi fun _ : S => Measure.pi fun _ : T => ν)
      (Measure.pi fun _ : T => Measure.pi fun _ : S => ν) := by
  have hf := measurePreserving_pi_uncurry (fun _ : S => fun _ : T => ν)
  have hs := measurePreserving_pi_select ν (Prod.swap : T × S → S × T)
    (Equiv.prodComm T S).injective
  exact (measurePreserving_pi_curry (fun _ : T => fun _ : S => ν)).comp (hs.comp hf)

def blockPosition {b L n : ℕ} (h : b * L ≤ n) (p : Fin b × Fin L) : Fin n :=
  Fin.castLE h (finProdFinEquiv p)

theorem blockPosition_injective {b L n : ℕ} (h : b * L ≤ n) :
    Function.Injective (blockPosition h) := by
  exact (Fin.castLE_injective h).comp finProdFinEquiv.injective

def takeStateBlocks {K b L n : ℕ} (h : b * L ≤ n) (H : StateBlock K n) :
    Fin b → StateBlock K L := fun s t => H (blockPosition h (s, t))

def takeNoiseBlocks {K b L n : ℕ} (h : b * L ≤ n) (z : Noise K n) :
    Fin b → Noise K L := fun s i t => z i (blockPosition h (s, t))

theorem measurePreserving_takeStateBlocks (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {K b L n : ℕ} (h : b * L ≤ n) :
    MeasurePreserving (takeStateBlocks (K := K) h) (stateLaw μ K n)
      (Measure.pi fun _ : Fin b => stateLaw μ K L) := by
  exact (measurePreserving_pi_curry (fun _ : Fin b => fun _ : Fin L =>
    Measure.pi fun _ : Fin K => Measure.pi fun _ : Fin K => μ)).comp
      (measurePreserving_pi_select _ (blockPosition h) (blockPosition_injective h))

theorem measurePreserving_takeNoiseBlocks {K b L n : ℕ} (h : b * L ≤ n) :
    MeasurePreserving (takeNoiseBlocks (K := K) h) (blockNoise K n)
      (Measure.pi fun _ : Fin b => blockNoise K L) := by
  let ν := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
    ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
  have ht : MeasurePreserving (fun z : Fin n → EuclideanSpace ℝ (Fin 2) =>
      fun s t => z (blockPosition h (s, t)))
      (Measure.pi fun _ : Fin n => ν)
      (Measure.pi fun _ : Fin b => Measure.pi fun _ : Fin L => ν) :=
    (measurePreserving_pi_curry (fun _ : Fin b => fun _ : Fin L => ν)).comp
      (measurePreserving_pi_select ν (blockPosition h) (blockPosition_injective h))
  exact (measurePreserving_pi_swap (S := Fin K) (T := Fin b)
    (Measure.pi fun _ : Fin L => ν)).comp
      (measurePreserving_pi _ _ (fun _ : Fin K => ht))

theorem measurePreserving_takeBlocks (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {K b L n : ℕ} (h : b * L ≤ n) :
    MeasurePreserving (fun hz : StateBlock K n × Noise K n =>
      fun s => (takeStateBlocks h hz.1 s, takeNoiseBlocks h hz.2 s))
      ((stateLaw μ K n).prod (blockNoise K n))
      (Measure.pi fun _ : Fin b => (stateLaw μ K L).prod (blockNoise K L)) := by
  exact (measurePreserving_arrowProdEquivProdArrow (StateBlock K L) (Noise K L) (Fin b)
    (fun _ => stateLaw μ K L) (fun _ => blockNoise K L)).symm.comp
      ((measurePreserving_takeStateBlocks μ h).prod
        (measurePreserving_takeNoiseBlocks h))

end CapacityAtlas.Gaussian.Interference
