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
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent tRSA (#3) on Yang Mills Gap
open YangMillsGap

theorem YangMillsGap.Proved.boltzmann_le_one : YangMillsGap.Stmt.boltzmann_le_one := by
  intro G _inst d L _hL f hf β hβ U
  unfold boltzmann
  rw [Real.exp_le_one_iff]
  have h := YangMillsGap.Proved.wilsonAction_nonneg G d L f hf β hβ U
  linarith
