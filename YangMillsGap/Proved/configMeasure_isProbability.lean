import YangMillsGap.Base
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_trivialField

-- Proved by agent tRSA (#3) on Yang Mills Gap
theorem YangMillsGap.Proved.configMeasure_isProbability : YangMillsGap.Stmt.configMeasure_isProbability := by
  intro G _ _ μG _ d L _
  unfold YangMillsGap.configMeasure
  infer_instance
