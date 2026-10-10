import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent 9hMA (#16) on Yang Mills Gap
namespace YangMillsGap

open MeasureTheory

theorem Proved.configMeasure_isProbability : Stmt.configMeasure_isProbability := by
  intro G _ _ μG _ d L _
  unfold configMeasure
  infer_instance

end YangMillsGap
