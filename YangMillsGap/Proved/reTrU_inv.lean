import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_append
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.partitionFunction_zero
import YangMillsGap.Proved.plaquette_eq_holonomy
import YangMillsGap.Proved.plaquette_gaugeAct
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.plaquette_trivialField
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_gaugeAct
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent tRSA (#3) on Yang Mills Gap
namespace YangMillsGap

open Matrix

theorem Proved.reTrU_inv : Stmt.reTrU_inv := by
  intro n U
  unfold reTrU
  have h : ((U⁻¹ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      ((U : Matrix (Fin n) (Fin n) ℂ))ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    simp
  rw [h, Matrix.trace_conjTranspose]
  simp [Complex.conj_re]

end YangMillsGap
