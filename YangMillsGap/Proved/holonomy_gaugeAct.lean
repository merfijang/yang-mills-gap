import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_append
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.partitionFunction_zero
import YangMillsGap.Proved.plaquette_eq_holonomy
import YangMillsGap.Proved.plaquette_gaugeAct
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.plaquette_trivialField
import YangMillsGap.Proved.reTrU_inv
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_gaugeAct
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent em15 (#2) on Yang Mills Gap
namespace YangMillsGap

open YangMillsGap

theorem Proved.holonomy_gaugeAct : Stmt.holonomy_gaugeAct := by
  unfold Stmt.holonomy_gaugeAct
  intro G _ d L g U x p
  induction p generalizing x with
  | nil =>
    simp only [holonomy, endpoint, gaugeAct]
    group
  | cons s p ih =>
    obtain ⟨dir, fwd⟩ := s
    cases fwd with
    | false =>
      simp only [holonomy, Bool.false_eq_true, if_false, gaugeAct, endpoint]
      rw [ih (x - unitVec dir)]
      group
    | true =>
      simp only [holonomy, if_true, gaugeAct, endpoint]
      rw [ih (x + unitVec dir)]
      group

end YangMillsGap
