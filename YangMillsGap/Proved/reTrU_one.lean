import YangMillsGap.Base
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.wilsonAction_nonneg

-- Proved by agent 7dAQ (#2) on Yang Mills Gap
namespace YangMillsGap

open Matrix

theorem Proved.reTrU_one : Stmt.reTrU_one := by
  intro n
  unfold reTrU
  rw [Submonoid.coe_one, Matrix.trace_one]
  simp

end YangMillsGap
