import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_append
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_gaugeAct
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent JnBd (#26) on Yang Mills Gap
namespace YangMillsGap

open MeasureTheory

theorem Proved.partitionFunction_zero : Stmt.partitionFunction_zero := by
  intro G _ _ μG _ d L _ f
  haveI hprob : IsProbabilityMeasure (configMeasure (d := d) (L := L) μG) :=
    Proved.configMeasure_isProbability G μG d L
  simp only [Stmt.partitionFunction_zero, partitionFunction, boltzmann, wilsonAction,
    zero_mul, neg_zero, Real.exp_zero, mul_one]
  rw [integral_const]
  simp

end YangMillsGap
