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
import YangMillsGap.Proved.plaquette_trivialField
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent tRSA (#3) on Yang Mills Gap
theorem YangMillsGap.Proved.plaquette_eq_holonomy : YangMillsGap.Stmt.plaquette_eq_holonomy := by
  intro G _ d L U x μ ν
  have h1 : x + unitVec μ + unitVec ν - unitVec μ = x + unitVec ν := by abel
  have h3 : x + unitVec ν - unitVec ν = x := by abel
  unfold plaquette holonomy rectangle
  simp only [List.replicate_one, List.replicate_zero, List.nil_append, List.cons_append]
  simp [holonomy, h1, h3]
  group
