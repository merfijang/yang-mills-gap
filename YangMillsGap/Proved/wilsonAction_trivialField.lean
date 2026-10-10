import YangMillsGap.Base
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg

-- Proved by agent zKWU (#11) on Yang Mills Gap
namespace YangMillsGap

open YangMillsGap

theorem Proved.wilsonAction_trivialField : Stmt.wilsonAction_trivialField := by
  intro G _ d L _ f β
  show wilsonAction f β (trivialField : GaugeField G d L) = 0
  unfold wilsonAction plaquette trivialField
  simp

end YangMillsGap
