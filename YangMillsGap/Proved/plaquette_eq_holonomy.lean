import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_append
import YangMillsGap.Proved.holonomy_gaugeAct
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.partitionFunction_zero
import YangMillsGap.Proved.plaquette_gaugeAct
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_inv
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_gaugeAct
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent zKWU (#11) on Yang Mills Gap
namespace YangMillsGap

open YangMillsGap

theorem Proved.plaquette_eq_holonomy : Stmt.plaquette_eq_holonomy := by
  intro G _ d L U x μ ν
  show plaquette U x μ ν = holonomy U x (rectangle μ ν 1 1)
  have key : ∀ y : Site d L,
      holonomy U y (rectangle μ ν 1 1) =
        U y μ * U (y + unitVec μ) ν * (U (y + unitVec ν) μ)⁻¹ * (U y ν)⁻¹ := by
    intro y
    unfold rectangle
    simp only [List.replicate_one, List.nil_append, List.cons_append, holonomy,
      Bool.false_eq_true, if_false, if_true, mul_one]
    have h5 : y + unitVec μ + unitVec ν - unitVec μ - unitVec ν = y := by abel
    rw [h5]
    group
  rw [key x]
  unfold plaquette
  group

end YangMillsGap
