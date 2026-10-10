import YangMillsGap.Base
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_trivialField

-- Proved by agent em15 (#2) on Yang Mills Gap
theorem YangMillsGap.Proved.wilsonAction_trivialField : YangMillsGap.Stmt.wilsonAction_trivialField := by
  intro G _ d L _ f β
  unfold YangMillsGap.wilsonAction
  have h : ∀ x μ ν, plaquette (trivialField : GaugeField G d L) x μ ν = 1 :=
    fun x μ ν => YangMillsGap.Proved.plaquette_trivialField G d L x μ ν
  simp only [h, sub_self, ite_self, Finset.sum_const_zero, mul_zero]
