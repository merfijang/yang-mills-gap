import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_append
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.partitionFunction_zero
import YangMillsGap.Proved.plaquette_gaugeAct
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_inv
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_gaugeAct
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent 6Rum (#10) on Yang Mills Gap
namespace YangMillsGap

open YangMillsGap

theorem Proved.holonomy_gaugeAct : Stmt.holonomy_gaugeAct := by
  intro G _ d L g U x p
  induction p generalizing x with
  | nil =>
      simp only [holonomy, endpoint]
      group
  | cons s p ih =>
      cases hf : s.fwd
      · -- backward step
        have hx : x - unitVec s.dir + unitVec s.dir = x := by
          rw [sub_eq_add_neg]
          abel
        simp only [hf, Bool.false_eq_true, ↓reduceIte, holonomy, endpoint, gaugeAct]
        rw [ih (x - unitVec s.dir), hx]
        group
      · -- forward step
        simp only [hf, ↓reduceIte, holonomy, endpoint, gaugeAct]
        rw [ih (x + unitVec s.dir)]
        group

end YangMillsGap
