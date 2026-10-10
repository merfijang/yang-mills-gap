import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.endpoint_rectangle
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_append
import YangMillsGap.Proved.holonomy_gaugeAct
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.partitionFunction_le_one
import YangMillsGap.Proved.partitionFunction_zero
import YangMillsGap.Proved.plaquette_eq_holonomy
import YangMillsGap.Proved.plaquette_gaugeAct
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_inv
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_continuous
import YangMillsGap.Proved.wilsonAction_gaugeAct
import YangMillsGap.Proved.wilsonAction_le
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField
import YangMillsGap.Proved.wilsonLoop_gaugeAct

-- Proved by agent kUFB (#27) on Yang Mills Gap
namespace YangMillsGap

open YangMillsGap

theorem Proved.wilsonAction_translate : Stmt.wilsonAction_translate := by
  intro G _ d L _ f β a U
  unfold wilsonAction
  congr 1
  have hkey : ∀ (y : Site d L) (μ ν : Fin d),
      plaquette (translate a U) y μ ν = plaquette U (y + a) μ ν := by
    intro y μ ν
    unfold plaquette translate
    rw [show y + unitVec μ + a = y + a + unitVec μ from by abel,
        show y + unitVec ν + a = y + a + unitVec ν from by abel]
  have hcomp : ∀ y : Site d L,
      (∑ μ : Fin d, ∑ ν : Fin d,
        (if μ < ν then f 1 - f (plaquette (translate a U) y μ ν) else 0))
      = (∑ μ : Fin d, ∑ ν : Fin d,
        (if μ < ν then f 1 - f (plaquette U (y + a) μ ν) else 0)) := by
    intro y
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    rw [hkey y μ ν]
  rw [Finset.sum_congr rfl (fun y _ => hcomp y)]
  exact (Equiv.sum_comp (Equiv.addRight a)
    (fun y : Site d L => ∑ μ : Fin d, ∑ ν : Fin d,
      if μ < ν then f 1 - f (plaquette U y μ ν) else 0))

end YangMillsGap
