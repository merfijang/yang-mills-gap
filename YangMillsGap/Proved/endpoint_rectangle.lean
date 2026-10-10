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
import YangMillsGap.Proved.wilsonAction_le
import YangMillsGap.Proved.wilsonAction_nonneg
import YangMillsGap.Proved.wilsonAction_trivialField
import YangMillsGap.Proved.wilsonLoop_gaugeAct

-- Proved by agent 6NuK (#20) on Yang Mills Gap
namespace YangMillsGap

open YangMillsGap

theorem Proved.endpoint_rectangle : Stmt.endpoint_rectangle := by
  intro d L x μ ν R T
  unfold rectangle
  have key : ∀ (y : Site d L) (p q : List (Step d)),
      endpoint y (p ++ q) = endpoint (endpoint y p) q :=
    Proved.endpoint_append d L
  have hμ : ∀ (k : ℕ) (y : Site d L),
      endpoint y (List.replicate k ⟨μ, true⟩) = y + k • unitVec μ := by
    intro k
    induction k with
    | zero =>
      intro y
      simp [endpoint]
    | succ k ih =>
      intro y
      rw [List.replicate_succ]
      simp only [List.cons_append, List.nil_append, endpoint, if_true]
      rw [ih]
      rw [add_smul, one_smul]
      abel
  have hν : ∀ (k : ℕ) (y : Site d L),
      endpoint y (List.replicate k ⟨ν, true⟩) = y + k • unitVec ν := by
    intro k
    induction k with
    | zero =>
      intro y
      simp [endpoint]
    | succ k ih =>
      intro y
      rw [List.replicate_succ]
      simp only [List.cons_append, List.nil_append, endpoint, if_true]
      rw [ih]
      rw [add_smul, one_smul]
      abel
  have hμb : ∀ (k : ℕ) (y : Site d L),
      endpoint y (List.replicate k ⟨μ, false⟩) = y - k • unitVec μ := by
    intro k
    induction k with
    | zero =>
      intro y
      simp [endpoint]
    | succ k ih =>
      intro y
      rw [List.replicate_succ]
      simp only [List.cons_append, List.nil_append, endpoint, Bool.false_eq_true, if_false]
      rw [ih]
      rw [add_smul, one_smul]
      abel
  have hνb : ∀ (k : ℕ) (y : Site d L),
      endpoint y (List.replicate k ⟨ν, false⟩) = y - k • unitVec ν := by
    intro k
    induction k with
    | zero =>
      intro y
      simp [endpoint]
    | succ k ih =>
      intro y
      rw [List.replicate_succ]
      simp only [List.cons_append, List.nil_append, endpoint, Bool.false_eq_true, if_false]
      rw [ih]
      rw [add_smul, one_smul]
      abel
  rw [List.append_assoc, List.append_assoc]
  rw [key]
  rw [key]
  rw [key]
  rw [hν T, hμ R, hμb R, hνb T]
  abel

end YangMillsGap
