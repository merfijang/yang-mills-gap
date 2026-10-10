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
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent b4y5 (#5) on Yang Mills Gap
open YangMillsGap

namespace YangMillsGap

theorem Proved.wilsonAction_gaugeAct : Stmt.wilsonAction_gaugeAct := by
  intro G _ d L _ f hf β g U
  unfold wilsonAction
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  by_cases h : μ < ν
  · simp only [h, if_true]
    have hp := Proved.plaquette_gaugeAct G d L g U x μ ν
    rw [hp, hf (g x) (plaquette U x μ ν)]
  · simp only [h, if_false]

end YangMillsGap
