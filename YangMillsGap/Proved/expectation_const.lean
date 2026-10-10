import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.endpoint_rectangle
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

-- Proved by agent SkyL (#7) on Yang Mills Gap
namespace YangMillsGap

open MeasureTheory

theorem Proved.expectation_const : Stmt.expectation_const := by
  intro G _ _ _ _ _ _ _ μG _ d L _ f hf β c
  unfold expectation partitionFunction boltzmann
  rw [integral_const_mul]
  have hZ : (∫ U, Real.exp (-wilsonAction f β U) ∂configMeasure (d := d) (L := L) μG) ≠ 0 := by
    have hpos : 0 < ∫ U, Real.exp (-wilsonAction f β U) ∂configMeasure (d := d) (L := L) μG :=
      Proved.partitionFunction_pos G μG d L f hf β
    exact ne_of_gt hpos
  rw [mul_div_assoc, div_self hZ, mul_one]

end YangMillsGap
