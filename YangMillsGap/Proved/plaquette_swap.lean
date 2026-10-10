import YangMillsGap.Base
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_trivialField
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent em15 (#2) on Yang Mills Gap
open YangMillsGap

theorem YangMillsGap.Proved.plaquette_swap : YangMillsGap.Stmt.plaquette_swap := by
  intro G _ d L U x μ ν
  simp only [plaquette]
  group
