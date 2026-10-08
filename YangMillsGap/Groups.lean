/-
Yang Mills Gap — concrete gauge groups: SU(n) and U(1).
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace YangMillsGap

open MeasureTheory

/-- The special unitary group `SU(n)` with the subspace topology of matrices. -/
abbrev SU (n : ℕ) := ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)

/-- The Borel σ-algebra on `SU(n)`. -/
noncomputable instance (n : ℕ) : MeasurableSpace (SU n) := borel _

instance (n : ℕ) : BorelSpace (SU n) := ⟨rfl⟩

/-- Real part of the trace: the standard plaquette weight and observable for `SU(n)`. -/
noncomputable def reTr {n : ℕ} (U : SU n) : ℝ := (Matrix.trace (U : Matrix (Fin n) (Fin n) ℂ)).re

/-- Real part of the trace on the unitary group `U(n)`. -/
noncomputable def reTrU {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) : ℝ :=
  (Matrix.trace (U : Matrix (Fin n) (Fin n) ℂ)).re

/-- The Borel σ-algebra on the circle `U(1)`. -/
noncomputable instance : MeasurableSpace Circle := borel _

instance : BorelSpace Circle := ⟨rfl⟩

/-- Plaquette weight and observable for `U(1)`: `Re z = cos θ`. -/
noncomputable def reCircle (z : Circle) : ℝ := (z : ℂ).re

end YangMillsGap
