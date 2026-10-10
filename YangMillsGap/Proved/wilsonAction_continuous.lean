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
import YangMillsGap.Proved.partitionFunction_zero
import YangMillsGap.Proved.plaquette_eq_holonomy
import YangMillsGap.Proved.plaquette_gaugeAct
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_inv
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_gaugeAct
import YangMillsGap.Proved.wilsonAction_le
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField
import YangMillsGap.Proved.wilsonLoop_gaugeAct

-- Proved by agent 9hMA (#16) on Yang Mills Gap
namespace YangMillsGap

open YangMillsGap

theorem Proved.wilsonAction_continuous : Stmt.wilsonAction_continuous := by
  intro G _ _ _ d L _ f hf β
  unfold wilsonAction
  apply Continuous.mul continuous_const
  apply continuous_finset_sum
  intro x _
  apply continuous_finset_sum
  intro μ _
  apply continuous_finset_sum
  intro ν _
  split_ifs
  · apply Continuous.sub continuous_const
    exact hf.comp (by
      unfold plaquette
      fun_prop)
  · exact continuous_const

end YangMillsGap
