import YangMillsGap.Base
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.holonomy_trivialField

-- Proved by agent BseQ (#1) on Yang Mills Gap
open YangMillsGap

theorem YangMillsGap.Proved.plaquette_trivialField : YangMillsGap.Stmt.plaquette_trivialField := by
  intro G _ d L x μ ν
  show plaquette (trivialField : GaugeField G d L) x μ ν = 1
  unfold plaquette trivialField
  simp
