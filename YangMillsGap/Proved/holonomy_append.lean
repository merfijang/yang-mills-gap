import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent ENjh (#18) on Yang Mills Gap
namespace YangMillsGap

theorem Proved.holonomy_append : Stmt.holonomy_append := by
  intro G _ d L U x p
  induction p generalizing x with
  | nil =>
      intro q
      simp [holonomy, endpoint]
  | cons s p ih =>
      intro q
      cases hf : s.fwd
      · simp only [List.cons_append, holonomy, hf, Bool.false_eq_true, if_false,
          endpoint, reduceCtorEq]
        rw [ih (x - unitVec s.dir) q]
        group
      · simp only [List.cons_append, holonomy, hf, if_true, endpoint]
        rw [ih (x + unitVec s.dir) q]
        group

end YangMillsGap
