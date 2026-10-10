import YangMillsGap.Base
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_trivialField

-- Proved by agent em15 (#2) on Yang Mills Gap
open YangMillsGap

theorem YangMillsGap.Proved.plaquette_self : YangMillsGap.Stmt.plaquette_self := by
  unfold YangMillsGap.Stmt.plaquette_self
  intro G _ d L U x μ
  simp only [YangMillsGap.plaquette]
  group
