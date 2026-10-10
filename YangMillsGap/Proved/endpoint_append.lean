import YangMillsGap.Base
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent K2Qx (#12) on Yang Mills Gap
namespace YangMillsGap

theorem Proved.endpoint_append : Stmt.endpoint_append := by
  intro d L x p q
  induction p generalizing x with
  | nil => rfl
  | cons s t ih =>
    cases s with
    | mk dir fwd =>
      cases fwd <;> simp only [List.cons_append, endpoint] <;> exact ih _

end YangMillsGap
