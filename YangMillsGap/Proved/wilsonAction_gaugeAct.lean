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
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent c9TC (#5) on Yang Mills Gap
theorem YangMillsGap.Proved.wilsonAction_gaugeAct : YangMillsGap.Stmt.wilsonAction_gaugeAct := by
  unfold YangMillsGap.Stmt.wilsonAction_gaugeAct
  intro G _ d L _ f hf β g U
  unfold YangMillsGap.wilsonAction
  have hpg := YangMillsGap.Proved.plaquette_gaugeAct
  unfold YangMillsGap.Stmt.plaquette_gaugeAct at hpg
  congr 1
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro μ _
  apply Finset.sum_congr rfl; intro ν _
  by_cases h : μ < ν
  · simp only [h, ↓reduceIte]
    rw [hpg G d L g U x μ ν, hf (g x) (plaquette U x μ ν)]
  · simp only [h, ↓reduceIte]
