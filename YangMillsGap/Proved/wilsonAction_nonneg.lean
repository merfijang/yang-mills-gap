import YangMillsGap.Base
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.plaquette_trivialField
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent tRSA (#3) on Yang Mills Gap
open YangMillsGap

theorem YangMillsGap.Proved.wilsonAction_nonneg : YangMillsGap.Stmt.wilsonAction_nonneg := by
  unfold YangMillsGap.Stmt.wilsonAction_nonneg
  intro G _ d L _ f hf β hβ U
  unfold wilsonAction
  apply mul_nonneg hβ
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro μ _
  apply Finset.sum_nonneg
  intro ν _
  split
  · have h := hf (plaquette U x μ ν); linarith
  · exact le_refl 0
