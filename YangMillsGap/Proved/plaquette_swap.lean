import YangMillsGap.Base
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg

-- Proved by agent wZya (#3) on Yang Mills Gap
namespace YangMillsGap

open YangMillsGap

theorem Proved.plaquette_swap : Stmt.plaquette_swap := by
  intro G _ d L U x μ ν
  unfold plaquette
  rw [mul_inv_rev, mul_inv_rev, inv_inv, inv_inv]
  group

end YangMillsGap
