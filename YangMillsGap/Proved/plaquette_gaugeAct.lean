import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.plaquette_trivialField
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent em15 (#2) on Yang Mills Gap
theorem YangMillsGap.Proved.plaquette_gaugeAct : YangMillsGap.Stmt.plaquette_gaugeAct := by
  intro G _ d L g U x μ ν
  have h : x + unitVec μ + unitVec ν = x + unitVec ν + unitVec μ := by
    ext i
    simp only [Pi.add_apply]
    abel
  simp only [plaquette, gaugeAct]
  rw [h]
  group
