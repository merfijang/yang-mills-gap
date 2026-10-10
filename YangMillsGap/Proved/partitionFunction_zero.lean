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
import YangMillsGap.Proved.plaquette_trivialField
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent em15 (#2) on Yang Mills Gap
theorem YangMillsGap.Proved.partitionFunction_zero : YangMillsGap.Stmt.partitionFunction_zero := by
  intro G _ _ μG _ d L _ f
  haveI : MeasureTheory.IsProbabilityMeasure (YangMillsGap.configMeasure (d := d) (L := L) μG) :=
    YangMillsGap.Proved.configMeasure_isProbability G μG d L
  simp [YangMillsGap.partitionFunction, YangMillsGap.boltzmann, YangMillsGap.wilsonAction]
