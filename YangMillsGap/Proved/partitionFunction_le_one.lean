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
import YangMillsGap.Proved.partitionFunction_zero
import YangMillsGap.Proved.plaquette_eq_holonomy
import YangMillsGap.Proved.plaquette_gaugeAct
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_inv
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_gaugeAct
import YangMillsGap.Proved.wilsonAction_le
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField
import YangMillsGap.Proved.wilsonLoop_gaugeAct

-- Proved by agent eJue (#23) on Yang Mills Gap
namespace YangMillsGap

open MeasureTheory

theorem Proved.partitionFunction_le_one : Stmt.partitionFunction_le_one := by
  intro G _ _ _ _ _ _ _ μG _ d L _ f hf hle β hβ
  unfold partitionFunction boltzmann
  haveI : IsProbabilityMeasure (configMeasure (d := d) (L := L) μG) :=
    Proved.configMeasure_isProbability G μG d L
  have h1 : ∀ U : GaugeField G d L, boltzmann f β U ≤ 1 :=
    Proved.boltzmann_le_one G d L f hle β hβ
  have h2 : ∀ U : GaugeField G d L, (0:ℝ) ≤ boltzmann f β U := fun U => (Real.exp_pos _).le
  have hcont : Continuous (fun U : GaugeField G d L => boltzmann f β U) := by
    unfold boltzmann wilsonAction
    apply Real.continuous_exp.comp
    apply Continuous.neg
    apply Continuous.const_mul
    apply continuous_finset_sum
    intro x _
    apply continuous_finset_sum
    intro μ _
    apply continuous_finset_sum
    intro ν _
    split_ifs with h
    · apply Continuous.sub continuous_const
      apply hf.comp
      unfold plaquette
      fun_prop
    · exact continuous_const
  have hmeas : AEStronglyMeasurable (fun U : GaugeField G d L => boltzmann f β U)
      (configMeasure (d := d) (L := L) μG) := hcont.aestronglyMeasurable
  have hint1 : Integrable (fun _ : GaugeField G d L => (1:ℝ))
      (configMeasure (d := d) (L := L) μG) := integrable_const _
  have hint : Integrable (fun U : GaugeField G d L => boltzmann f β U)
      (configMeasure (d := d) (L := L) μG) := by
    apply Integrable.mono' (g := fun _ : GaugeField G d L => (1:ℝ))
    · exact hint1
    · exact hmeas
    · filter_upwards with U
      rw [Real.norm_eq_abs, abs_of_nonneg (h2 U)]
      exact h1 U
  have hmono := integral_mono_of_nonneg (μ := configMeasure (d := d) (L := L) μG)
    (f := fun U : GaugeField G d L => boltzmann f β U) (g := fun _ => (1:ℝ))
    (Filter.Eventually.of_forall h2) hint1 (Filter.Eventually.of_forall h1)
  rw [integral_const, probReal_univ, smul_eq_mul, mul_one] at hmono
  exact hmono

end YangMillsGap
