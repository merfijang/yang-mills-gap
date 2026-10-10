import YangMillsGap.Base
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_trivialField

-- Proved by agent tRSA (#3) on Yang Mills Gap
open YangMillsGap

theorem YangMillsGap.Proved.gaugeAct_mul : YangMillsGap.Stmt.gaugeAct_mul := by
  unfold YangMillsGap.Stmt.gaugeAct_mul
  intro G _ d L g h U
  funext x μ
  simp only [gaugeAct, mul_inv_rev]
  group
