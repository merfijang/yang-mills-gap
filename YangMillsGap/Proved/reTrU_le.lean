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
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_continuous
import YangMillsGap.Proved.wilsonAction_gaugeAct
import YangMillsGap.Proved.wilsonAction_le
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_translate
import YangMillsGap.Proved.wilsonAction_trivialField
import YangMillsGap.Proved.wilsonLoop_gaugeAct

-- Proved by agent JnBd (#26) on Yang Mills Gap
namespace YangMillsGap

open Matrix

theorem Proved.reTrU_le : Stmt.reTrU_le := by
  intro n U
  unfold reTrU
  have hre : (Matrix.trace (U : Matrix (Fin n) (Fin n) ℂ)).re ≤ ‖Matrix.trace (U : Matrix (Fin n) (Fin n) ℂ)‖ :=
    Complex.re_le_norm _
  have htr : Matrix.trace (U : Matrix (Fin n) (Fin n) ℂ) = ∑ i, (U : Matrix (Fin n) (Fin n) ℂ) i i := rfl
  have hnorm : ‖Matrix.trace (U : Matrix (Fin n) (Fin n) ℂ)‖ ≤ ∑ i, ‖(U : Matrix (Fin n) (Fin n) ℂ) i i‖ := by
    rw [htr]
    exact norm_sum_le _ _
  have hentry : ∀ i, ‖(U : Matrix (Fin n) (Fin n) ℂ) i i‖ ≤ 1 := by
    intro i
    have hmem : (U : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := U.2
    have hunit := (Matrix.mem_unitaryGroup_iff).mp hmem
    have h1 : ((U : Matrix (Fin n) (Fin n) ℂ) * star (U : Matrix (Fin n) (Fin n) ℂ)) i i = 1 := by
      rw [hunit]; simp
    have h2 : ((U : Matrix (Fin n) (Fin n) ℂ) * star (U : Matrix (Fin n) (Fin n) ℂ)) i i
        = ∑ j, (U : Matrix (Fin n) (Fin n) ℂ) i j * star ((U : Matrix (Fin n) (Fin n) ℂ) i j) := by
      simp [Matrix.mul_apply]
    have h3 : (∑ j, (U : Matrix (Fin n) (Fin n) ℂ) i j * star ((U : Matrix (Fin n) (Fin n) ℂ) i j)).re = 1 := by
      rw [← h2, h1]; simp
    have hterm : ∀ j, ((U : Matrix (Fin n) (Fin n) ℂ) i j * star ((U : Matrix (Fin n) (Fin n) ℂ) i j)).re
        = ‖(U : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 := by
      intro j
      rw [Complex.sq_norm]
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      rw [Complex.normSq_apply]
      ring
    have hsum : ∑ j, ‖(U : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = 1 := by
      rw [← h3, Complex.re_sum]
      exact Finset.sum_congr rfl (fun j _ => (hterm j).symm)
    have hi : ‖(U : Matrix (Fin n) (Fin n) ℂ) i i‖ ^ 2 ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun j => ‖(U : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hnn : 0 ≤ ‖(U : Matrix (Fin n) (Fin n) ℂ) i i‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖(U : Matrix (Fin n) (Fin n) ℂ) i i‖ - 1)]
  calc (Matrix.trace (U : Matrix (Fin n) (Fin n) ℂ)).re
      ≤ ‖Matrix.trace (U : Matrix (Fin n) (Fin n) ℂ)‖ := hre
    _ ≤ ∑ i, ‖(U : Matrix (Fin n) (Fin n) ℂ) i i‖ := hnorm
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hentry i)
    _ = n := by simp

end YangMillsGap
