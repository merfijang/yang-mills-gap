import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.endpoint_rectangle
import YangMillsGap.Proved.expectation_const
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_append
import YangMillsGap.Proved.holonomy_gaugeAct
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.partitionFunction_le_one
import YangMillsGap.Proved.partitionFunction_pos
import YangMillsGap.Proved.partitionFunction_zero
import YangMillsGap.Proved.plaquette_eq_holonomy
import YangMillsGap.Proved.plaquette_gaugeAct
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_eq_iff
import YangMillsGap.Proved.reTrU_inv
import YangMillsGap.Proved.reTrU_isClassFunction
import YangMillsGap.Proved.reTrU_le
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_continuous
import YangMillsGap.Proved.wilsonAction_gaugeAct
import YangMillsGap.Proved.wilsonAction_le
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_translate
import YangMillsGap.Proved.wilsonAction_trivialField
import YangMillsGap.Proved.wilsonLoop_gaugeAct

-- Proved by agent 1pE2 (#6) on Yang Mills Gap
namespace YangMillsGap

theorem Proved.abs_reTrU_le : Stmt.abs_reTrU_le := by
  intro n U
  have h1 : reTrU U ≤ (n : ℝ) := Proved.reTrU_le n U
  have hinv : reTrU (U⁻¹ : Matrix.unitaryGroup (Fin n) ℂ) = reTrU U :=
    Proved.reTrU_inv n U
  have hneg : reTrU (-U : Matrix.unitaryGroup (Fin n) ℂ) = -reTrU U := by
    unfold reTrU
    rw [show ((↑(-U) : Matrix (Fin n) (Fin n) ℂ)) = -(↑U) from rfl]
    rw [Matrix.trace_neg]
    simp
  have h4 : reTrU (-U : Matrix.unitaryGroup (Fin n) ℂ) ≤ (n : ℝ) :=
    Proved.reTrU_le n (-U : Matrix.unitaryGroup (Fin n) ℂ)
  rw [abs_le]
  constructor <;> linarith

end YangMillsGap
