/-
Yang Mills Gap — the Wilson measure: integration over configurations, partition function,
expectations, correlations.

The configuration measure is the product of Haar measures `μG` over all links. The weight of a
configuration is `exp(−S(U))`, where `S` is the Wilson action.
-/
import YangMillsGap.Lattice
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace YangMillsGap

open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] {d L : ℕ} [NeZero L]

/-- The configuration measure: the product of `μG` over all links `(x, μ)`. -/
noncomputable def configMeasure (μG : Measure G) [SigmaFinite μG] : Measure (GaugeField G d L) :=
  Measure.pi fun _ : Site d L => Measure.pi fun _ : Fin d => μG

/-- The Boltzmann weight `exp(−S(U))`. -/
noncomputable def boltzmann (f : G → ℝ) (β : ℝ) (U : GaugeField G d L) : ℝ :=
  Real.exp (-wilsonAction f β U)

/-- The partition function `Z = ∫ exp(−S) dU`. -/
noncomputable def partitionFunction (μG : Measure G) [SigmaFinite μG] (f : G → ℝ) (β : ℝ) : ℝ :=
  ∫ U, boltzmann f β U ∂(configMeasure (d := d) (L := L) μG)

/-- The expectation of an observable `⟨O⟩ = Z⁻¹ ∫ O(U) exp(−S(U)) dU`. -/
noncomputable def expectation (μG : Measure G) [SigmaFinite μG] (f : G → ℝ) (β : ℝ)
    (O : GaugeField G d L → ℝ) : ℝ :=
  (∫ U, O U * boltzmann f β U ∂(configMeasure μG)) / partitionFunction (d := d) (L := L) μG f β

/-- The connected correlation `⟨O₁ O₂⟩ − ⟨O₁⟩⟨O₂⟩`. -/
noncomputable def covariance (μG : Measure G) [SigmaFinite μG] (f : G → ℝ) (β : ℝ)
    (O₁ O₂ : GaugeField G d L → ℝ) : ℝ :=
  expectation μG f β (fun U => O₁ U * O₂ U) - expectation μG f β O₁ * expectation μG f β O₂

/-- Translation of a configuration by `a`: `(τ_a U)_{x,μ} = U_{x+a,μ}`. -/
def translate (a : Site d L) (U : GaugeField G d L) : GaugeField G d L := fun x μ => U (x + a) μ

/-- The plaquette observable `χ(U_{x,μν})`. -/
def plaquetteObs (χ : G → ℝ) (x : Site d L) (μ ν : Fin d) (U : GaugeField G d L) : ℝ :=
  χ (plaquette U x μ ν)

/-- The Wilson loop observable `χ(holonomy of the loop p from x)`. -/
def wilsonLoop (χ : G → ℝ) (x : Site d L) (p : List (Step d)) (U : GaugeField G d L) : ℝ :=
  χ (holonomy U x p)

end YangMillsGap
