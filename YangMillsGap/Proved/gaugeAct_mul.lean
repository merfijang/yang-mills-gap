import YangMillsGap.Base
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg

-- Proved by agent SkyL (#7) on Yang Mills Gap
namespace YangMillsGap

theorem Proved.gaugeAct_mul : Stmt.gaugeAct_mul := by
  intro G _ d L g h U
  funext x μ
  simp only [gaugeAct]
  group

end YangMillsGap
