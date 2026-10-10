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
import YangMillsGap.Proved.reTrU_isClassFunction
import YangMillsGap.Proved.reTrU_le
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_continuous
import YangMillsGap.Proved.wilsonAction_gaugeAct
import YangMillsGap.Proved.wilsonAction_le
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_translate
import YangMillsGap.Proved.wilsonAction_trivialField
import YangMillsGap.Proved.wilsonLoop_gaugeAct

-- Proved by agent b4y5 (#5) on Yang Mills Gap
namespace YangMillsGap

open MeasureTheory

theorem Proved.partitionFunction_pos : Stmt.partitionFunction_pos := by
  intro G _ _ _ _ _ _ _ μG _ d L _ f hf β
  unfold partitionFunction boltzmann
  haveI hprob : IsProbabilityMeasure (configMeasure (d := d) (L := L) μG) :=
    Proved.configMeasure_isProbability G μG d L
  have hcont : Continuous (fun U : GaugeField G d L => Real.exp (-wilsonAction f β U)) :=
    Real.continuous_exp.comp (Proved.wilsonAction_continuous G d L f hf β).neg
  have hnonneg : 0 ≤ᵐ[(configMeasure (d := d) (L := L) μG)]
      (fun U : GaugeField G d L => Real.exp (-wilsonAction f β U)) :=
    Filter.Eventually.of_forall fun U => (Real.exp_pos _).le
  have hint : Integrable (fun U : GaugeField G d L => Real.exp (-wilsonAction f β U))
      (configMeasure (d := d) (L := L) μG) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hsupp : Function.support (fun U : GaugeField G d L => Real.exp (-wilsonAction f β U))
      = Set.univ := by
    ext U
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (Real.exp_pos _)
  rw [hsupp, measure_univ]
  exact one_pos

end YangMillsGap
