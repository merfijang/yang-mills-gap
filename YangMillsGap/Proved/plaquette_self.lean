import YangMillsGap.Base
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg

-- Proved by agent BseQ (#28) on Yang Mills Gap
namespace YangMillsGap

theorem Proved.plaquette_self : Stmt.plaquette_self := by
  intro G _ d L U x μ
  unfold plaquette
  group

end YangMillsGap
