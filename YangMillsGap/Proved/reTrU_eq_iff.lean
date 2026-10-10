import YangMillsGap.Base
import YangMillsGap.Proved.boltzmann_le_one
import YangMillsGap.Proved.configMeasure_isProbability
import YangMillsGap.Proved.endpoint_append
import YangMillsGap.Proved.endpoint_rectangle
import YangMillsGap.Proved.expectation_const
import YangMillsGap.Proved.gaugeAct_mul
import YangMillsGap.Proved.gaugeAct_one
import YangMillsGap.Proved.holonomy_append
import YangMillsGap.Proved.holonomy_gaugeAct
import YangMillsGap.Proved.holonomy_trivialField
import YangMillsGap.Proved.partitionFunction_le_one
import YangMillsGap.Proved.partitionFunction_pos
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

-- Proved by agent z1Xi (#21) on Yang Mills Gap
namespace YangMillsGap

open Matrix

private lemma trace_conjTranspose_sub_mul_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ((A - 1)ᴴ * (A - 1)).trace = (Aᴴ * A).trace - Aᴴ.trace - A.trace + (1 : Matrix (Fin n) (Fin n) ℂ).trace := by
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one]
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub]
  ring

private lemma trace_conjTranspose_mul_self_eq_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (Mᴴ * M).trace = ∑ i : Fin n, ∑ j : Fin n, (star (M j i) * M j i) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.conjTranspose_apply]

private lemma re_sum_normSq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ((Mᴴ * M).trace).re = ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (M j i) := by
  rw [trace_conjTranspose_mul_self_eq_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private lemma trace_one_re {n : ℕ} : ((1 : Matrix (Fin n) (Fin n) ℂ).trace).re = (n : ℝ) := by
  rw [Matrix.trace_one]
  simp

theorem Proved.reTrU_eq_iff : Stmt.reTrU_eq_iff := by
  intro n U
  constructor
  · intro h
    have hunit : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      have h2 := U.2
      rw [Matrix.mem_unitaryGroup_iff'] at h2
      rw [Matrix.star_eq_conjTranspose] at h2
      exact h2
    set A : Matrix (Fin n) (Fin n) ℂ := (U : Matrix (Fin n) (Fin n) ℂ) with hA
    set M : Matrix (Fin n) (Fin n) ℂ := A - 1 with hM
    have htr : (Mᴴ * M).trace = (Aᴴ * A).trace - Aᴴ.trace - A.trace + (1 : Matrix (Fin n) (Fin n) ℂ).trace := by
      rw [hM, hA]
      exact trace_conjTranspose_sub_mul_self _
    have hreA : (A.trace).re = (n : ℝ) := by
      rw [hA]
      exact h
    have hreAst : (Aᴴ.trace).re = (n : ℝ) := by
      rw [Matrix.trace_conjTranspose]
      simp only [Complex.star_def]
      rw [Complex.conj_re]
      exact hreA
    have hre : ((Mᴴ * M).trace).re = 0 := by
      rw [htr]
      rw [Complex.add_re, Complex.sub_re, Complex.sub_re]
      rw [hunit, trace_one_re]
      rw [hreAst, hreA]
      ring
    have hexp : ((Mᴴ * M).trace).re = ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (M j i) :=
      re_sum_normSq M
    have hsum : ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (M j i) = 0 := by
      rw [← hexp]
      exact hre
    have hMzero : M = 0 := by
      have hinner : ∀ i : Fin n, ∑ j : Fin n, Complex.normSq (M j i) = 0 := by
        intro i
        have h1 : ∀ k ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ∑ j : Fin n, Complex.normSq (M j k) := by
          intro k _
          exact Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
        exact (Finset.sum_eq_zero_iff_of_nonneg h1).mp hsum i (Finset.mem_univ i)
      ext i j
      have h2 := hinner j
      have h3 : ∀ k ∈ (Finset.univ : Finset (Fin n)), 0 ≤ Complex.normSq (M k j) :=
        fun k _ => Complex.normSq_nonneg _
      have h4 := (Finset.sum_eq_zero_iff_of_nonneg h3).mp h2
      have hz := h4 i (Finset.mem_univ i)
      have hz' : M i j = 0 := by
        have := Complex.normSq_eq_zero.mp hz
        simpa using this
      simpa using hz'
    apply Subtype.ext
    have h5 : A - 1 = 0 := by
      rw [← hM]
      exact hMzero
    have h6 : A = 1 := sub_eq_zero.mp h5
    rw [hA] at h6
    exact h6
  · intro h
    rw [h]
    exact Proved.reTrU_one n

end YangMillsGap
