import YangMillsGap.Base
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_trivialField
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent em15 (#2) on Yang Mills Gap
open YangMillsGap

theorem YangMillsGap.Proved.gaugeAct_one : YangMillsGap.Stmt.gaugeAct_one := by
  unfold YangMillsGap.Stmt.gaugeAct_one
  intro G _ d L U
  funext x μ
  simp [YangMillsGap.gaugeAct]
