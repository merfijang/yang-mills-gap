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
import YangMillsGap.Proved.plaquette_eq_holonomy
import YangMillsGap.Proved.plaquette_gaugeAct
import YangMillsGap.Proved.plaquette_self
import YangMillsGap.Proved.plaquette_swap
import YangMillsGap.Proved.reTrU_inv
import YangMillsGap.Proved.reTrU_one
import YangMillsGap.Proved.wilsonAction_gaugeAct
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField

-- Proved by agent z1Xi (#21) on Yang Mills Gap
namespace YangMillsGap

open Finset

theorem Proved.wilsonAction_le : Stmt.wilsonAction_le := by
  intro G _ d L _ f M hM β hβ U
  unfold wilsonAction
  have hterm : ∀ g : G, f 1 - f g ≤ 2 * M := by
    intro g
    have h1 : |f 1| ≤ M := hM 1
    have h2 : |f g| ≤ M := hM g
    have h3 : -f g ≤ |f g| := neg_le_abs _
    have h4 : f 1 ≤ |f 1| := le_abs_self _
    linarith
  have hsum : ∑ x : Site d L, ∑ μ : Fin d, ∑ ν : Fin d,
      (if μ < ν then f 1 - f (plaquette U x μ ν) else 0)
      ≤ (L : ℝ) ^ d * (d : ℝ) ^ 2 * (2 * M) := by
    have hx : ∀ x : Site d L,
        (∑ μ : Fin d, ∑ ν : Fin d,
          (if μ < ν then f 1 - f (plaquette U x μ ν) else 0))
        ≤ (d : ℝ) ^ 2 * (2 * M) := by
      intro x
      have hinner : ∀ μ : Fin d,
          (∑ ν : Fin d, (if μ < ν then f 1 - f (plaquette U x μ ν) else 0))
          ≤ (d : ℝ) * (2 * M) := by
        intro μ
        calc ∑ ν : Fin d, (if μ < ν then f 1 - f (plaquette U x μ ν) else 0)
            ≤ ∑ _ν : Fin d, (2 * M) := by
              apply Finset.sum_le_sum
              intro ν _
              by_cases h : μ < ν
              · simp only [h, if_true]
                exact hterm _
              · simp only [h, if_false]
                have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 1)
                linarith
          _ = (d : ℝ) * (2 * M) := by
              simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc ∑ μ : Fin d, (∑ ν : Fin d, (if μ < ν then f 1 - f (plaquette U x μ ν) else 0))
          ≤ ∑ _μ : Fin d, (d : ℝ) * (2 * M) := by
            apply Finset.sum_le_sum
            intro μ _
            exact hinner μ
        _ = (d : ℝ) * ((d : ℝ) * (2 * M)) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (d : ℝ) ^ 2 * (2 * M) := by ring
    calc ∑ x : Site d L, (∑ μ : Fin d, ∑ ν : Fin d,
            (if μ < ν then f 1 - f (plaquette U x μ ν) else 0))
        ≤ ∑ _x : Site d L, ((d : ℝ) ^ 2 * (2 * M)) := by
          apply Finset.sum_le_sum
          intro x _
          exact hx x
      _ = (L : ℝ) ^ d * ((d : ℝ) ^ 2 * (2 * M)) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            ZMod.card, nsmul_eq_mul]
      _ = (L : ℝ) ^ d * (d : ℝ) ^ 2 * (2 * M) := by ring
  have := mul_le_mul_of_nonneg_left hsum hβ
  linarith [this]

end YangMillsGap
