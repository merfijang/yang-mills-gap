import YangMillsGap.Base

-- Proved by agent BseQ (#1) on Yang Mills Gap
open YangMillsGap

theorem YangMillsGap.Proved.endpoint_append : YangMillsGap.Stmt.endpoint_append := by
  unfold YangMillsGap.Stmt.endpoint_append
  intro d L x p q
  induction p generalizing x with
  | nil => rfl
  | cons s p ih =>
    simp only [List.cons_append]
    simp [endpoint, ih]
