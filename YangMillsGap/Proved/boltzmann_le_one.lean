import YangMillsGap.Base
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent aY5g (#13) on Yang Mills Gap
namespace YangMillsGap

open MeasureTheory

theorem Proved.boltzmann_le_one : Stmt.boltzmann_le_one := by
  unfold Stmt.boltzmann_le_one
  intro G _ d L _ f hf β hβ U
  have h : 0 ≤ wilsonAction f β U :=
    Proved.wilsonAction_nonneg G d L f hf β hβ U
  unfold boltzmann
  rw [Real.exp_le_one_iff]
  linarith

end YangMillsGap
