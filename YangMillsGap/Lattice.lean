/-
Yang Mills Gap — lattice gauge theory: basic definitions.

The lattice is the periodic torus `(ℤ/L)^d`. A gauge field assigns a group element of `G` to every
positively oriented link `(x, μ)`. Everything here is frozen: blueprint statements refer to these
definitions, so they never change.
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic

namespace YangMillsGap

/-- A site of the periodic lattice `(ℤ/L)^d`. -/
abbrev Site (d L : ℕ) := Fin d → ZMod L

/-- The unit step in direction `μ`. -/
def unitVec {d L : ℕ} (μ : Fin d) : Site d L := Pi.single μ 1

/-- A gauge field: an element of `G` on the link from `x` to `x + e_μ`. -/
abbrev GaugeField (G : Type*) (d L : ℕ) := Site d L → Fin d → G

/-- A gauge transformation: an element of `G` at every site. -/
abbrev GaugeTransform (G : Type*) (d L : ℕ) := Site d L → G

section Group

variable {G : Type*} [Group G] {d L : ℕ}

/-- Plaquette holonomy `U_{x,μν} = U_{x,μ} U_{x+μ,ν} U_{x+ν,μ}⁻¹ U_{x,ν}⁻¹`. -/
def plaquette (U : GaugeField G d L) (x : Site d L) (μ ν : Fin d) : G :=
  U x μ * U (x + unitVec μ) ν * (U (x + unitVec ν) μ)⁻¹ * (U x ν)⁻¹

/-- Action of a gauge transformation: `(g·U)_{x,μ} = g_x U_{x,μ} g_{x+μ}⁻¹`. -/
def gaugeAct (g : GaugeTransform G d L) (U : GaugeField G d L) : GaugeField G d L :=
  fun x μ => g x * U x μ * (g (x + unitVec μ))⁻¹

/-- The trivial field: `1` on every link. -/
def trivialField : GaugeField G d L := fun _ _ => 1

/-- A class function: invariant under conjugation. -/
def IsClassFunction (f : G → ℝ) : Prop := ∀ g h : G, f (g * h * g⁻¹) = f h

/-- A lattice path step: direction and orientation (`true` along `e_μ`, `false` against it). -/
structure Step (d : ℕ) where
  dir : Fin d
  fwd : Bool

/-- The endpoint of a path starting at `x`. -/
def endpoint (x : Site d L) : List (Step d) → Site d L
  | [] => x
  | s :: p => endpoint (if s.fwd then x + unitVec s.dir else x - unitVec s.dir) p

/-- The holonomy (ordered product of link variables) of a path starting at `x`. -/
def holonomy (U : GaugeField G d L) (x : Site d L) : List (Step d) → G
  | [] => 1
  | s :: p =>
    if s.fwd then U x s.dir * holonomy U (x + unitVec s.dir) p
    else (U (x - unitVec s.dir) s.dir)⁻¹ * holonomy U (x - unitVec s.dir) p

/-- The rectangular `R × T` loop in the `(μ, ν)` plane: `R` steps along `μ`, `T` along `ν`, then back. -/
def rectangle (μ ν : Fin d) (R T : ℕ) : List (Step d) :=
  List.replicate R ⟨μ, true⟩ ++ List.replicate T ⟨ν, true⟩ ++
    List.replicate R ⟨μ, false⟩ ++ List.replicate T ⟨ν, false⟩

end Group

section Action

variable {G : Type*} [Group G] {d L : ℕ} [NeZero L]

/-- The Wilson action with plaquette weight `f`:
`S(U) = β · Σ_x Σ_{μ<ν} (f(1) − f(U_{x,μν}))`. For `SU(N)` one takes `f = Re tr`. -/
def wilsonAction (f : G → ℝ) (β : ℝ) (U : GaugeField G d L) : ℝ :=
  β * ∑ x : Site d L, ∑ μ : Fin d, ∑ ν : Fin d,
    if μ < ν then f 1 - f (plaquette U x μ ν) else 0

end Action

end YangMillsGap
