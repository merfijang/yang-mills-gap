import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_append
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent cQdv (#24) on Yang Mills Gap
namespace YangMillsGap

open YangMillsGap

theorem Proved.plaquette_gaugeAct : Stmt.plaquette_gaugeAct := by
  intro G _ d L g U x μ ν
  unfold plaquette gaugeAct
  have h : x + unitVec μ + unitVec ν = x + unitVec ν + unitVec μ := by abel
  rw [h]
  group

end YangMillsGap
