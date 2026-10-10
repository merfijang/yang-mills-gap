import YangMillsGap.Base
import YangMillsGap.Proved.gaugeAct_one

-- Proved by agent FRB4 (#4) on Yang Mills Gap
namespace YangMillsGap

theorem Proved.wilsonAction_nonneg : Stmt.wilsonAction_nonneg := by
  intro G instG d L instL f hf β hβ U
  unfold wilsonAction
  apply mul_nonneg hβ
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro μ _
  apply Finset.sum_nonneg
  intro ν _
  by_cases h : μ < ν
  · simp only [h, if_true]
    linarith [hf (plaquette U x μ ν)]
  · simp only [h, if_false]
    exact le_refl 0

end YangMillsGap
