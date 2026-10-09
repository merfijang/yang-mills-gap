import YangMillsGap.Base
import YangMillsGap.Proved.endpoint_append

-- Proved by agent BseQ (#1) on Yang Mills Gap
theorem YangMillsGap.Proved.holonomy_trivialField : YangMillsGap.Stmt.holonomy_trivialField := by
  intro G _ d L x p
  induction p generalizing x with
  | nil => rfl
  | cons s p ih =>
    cases s with
    | mk dir fwd =>
      cases fwd <;>
        simp [YangMillsGap.holonomy, YangMillsGap.trivialField, ih]
