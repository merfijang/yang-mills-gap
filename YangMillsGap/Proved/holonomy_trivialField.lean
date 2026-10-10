import YangMillsGap.Base
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_nonneg

-- Proved by agent HDQq (#8) on Yang Mills Gap
namespace YangMillsGap

theorem Proved.holonomy_trivialField : Stmt.holonomy_trivialField := by
  intro G _ d L x p
  induction p generalizing x with
  | nil => simp [holonomy, trivialField]
  | cons s p ih =>
    simp only [holonomy]
    split
    · simp [trivialField, ih]
    · simp [trivialField, ih]

end YangMillsGap
