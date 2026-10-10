import YangMillsGap.Base
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_trivialField
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent EjBc (#4) on Yang Mills Gap
open YangMillsGap

theorem YangMillsGap.Proved.reTrU_one : YangMillsGap.Stmt.reTrU_one := by
  intro n
  simp [reTrU, Matrix.trace_one, Fintype.card_fin]
