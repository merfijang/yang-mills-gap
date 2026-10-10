import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.plaquette_gaugeAct
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.plaquette_trivialField
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent c9TC (#5) on Yang Mills Gap
open YangMillsGap

theorem YangMillsGap.Proved.holonomy_append : YangMillsGap.Stmt.holonomy_append := by
  intro G _ d L U x p q
  induction p generalizing x with
  | nil => simp [holonomy, endpoint]
  | cons s p ih =>
    cases h : s.fwd <;> simp [holonomy, endpoint, h, ih, mul_assoc]
