/-
Yang Mills Gap — frozen statements of the blueprint nodes.

Every node is `def YangMillsGap.Stmt.<id> : Prop`. A proof of the node is a theorem
`YangMillsGap.Proved.<id> : YangMillsGap.Stmt.<id>` accepted by the judge (`Checker.lean`).
Node metadata lives in the doc comment: `@title`, `@layer`, `@difficulty`, `@deps`.
Layers: `foundation`, `hard` (known hard results), `open` (open problems).
The Millennium problem itself (the boss) is not a Lean statement and is NOT solved.

Statements never change after publication: a new variant is a new node.
-/
import YangMillsGap.Lattice
import YangMillsGap.Measure
import YangMillsGap.Groups
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Bases
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.Filter.AtTopBot.Basic

namespace YangMillsGap.Stmt

open MeasureTheory

/-! ## Foundation: algebra of gauge fields -/

/-- @title Degenerate plaquette is trivial
@layer foundation
@difficulty 1
@deps 
`U_{x,μμ} = 1`. -/
def plaquette_self : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) (U : GaugeField G d L) (x : Site d L) (μ : Fin d),
    plaquette U x μ μ = 1

/-- @title Reversing a plaquette inverts it
@layer foundation
@difficulty 1
@deps 
`U_{x,νμ} = U_{x,μν}⁻¹`. -/
def plaquette_swap : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) (U : GaugeField G d L) (x : Site d L) (μ ν : Fin d),
    plaquette U x ν μ = (plaquette U x μ ν)⁻¹

/-- @title Plaquettes of the trivial field
@layer foundation
@difficulty 1
@deps 
For `U ≡ 1` every plaquette equals `1`. -/
def plaquette_trivialField : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) (x : Site d L) (μ ν : Fin d),
    plaquette (trivialField : GaugeField G d L) x μ ν = 1

/-- @title Identity gauge transformation
@layer foundation
@difficulty 1
@deps 
`1 · U = U`. -/
def gaugeAct_one : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) (U : GaugeField G d L),
    gaugeAct (fun _ => (1 : G)) U = U

/-- @title Gauge transformations form a group action
@layer foundation
@difficulty 1
@deps 
`g · (h · U) = (g h) · U`. -/
def gaugeAct_mul : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) (g h : GaugeTransform G d L) (U : GaugeField G d L),
    gaugeAct g (gaugeAct h U) = gaugeAct (fun x => g x * h x) U

/-- @title Plaquettes are gauge covariant
@layer foundation
@difficulty 2
@deps 
`(g·U)_{x,μν} = g_x U_{x,μν} g_x⁻¹`. -/
def plaquette_gaugeAct : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) (g : GaugeTransform G d L) (U : GaugeField G d L)
    (x : Site d L) (μ ν : Fin d),
    plaquette (gaugeAct g U) x μ ν = g x * plaquette U x μ ν * (g x)⁻¹

/-- @title The Wilson action is gauge invariant
@layer foundation
@difficulty 2
@deps plaquette_gaugeAct
For a class function `f`: `S(g·U) = S(U)`. -/
def wilsonAction_gaugeAct : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) [NeZero L] (f : G → ℝ), IsClassFunction f →
    ∀ (β : ℝ) (g : GaugeTransform G d L) (U : GaugeField G d L),
      wilsonAction f β (gaugeAct g U) = wilsonAction f β U

/-- @title Action of the trivial field vanishes
@layer foundation
@difficulty 1
@deps plaquette_trivialField
`S(1) = 0`. -/
def wilsonAction_trivialField : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) [NeZero L] (f : G → ℝ) (β : ℝ),
    wilsonAction f β (trivialField : GaugeField G d L) = 0

/-- @title The Wilson action is nonnegative
@layer foundation
@difficulty 1
@deps 
If `f(g) ≤ f(1)` for all `g` and `β ≥ 0`, then `S(U) ≥ 0`. -/
def wilsonAction_nonneg : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) [NeZero L] (f : G → ℝ), (∀ g, f g ≤ f 1) →
    ∀ (β : ℝ), 0 ≤ β → ∀ U : GaugeField G d L, 0 ≤ wilsonAction f β U

/-- @title Volume bound on the Wilson action
@layer foundation
@difficulty 2
@deps 
If `|f| ≤ M` and `β ≥ 0`, then `S(U) ≤ β · L^d · d² · 2M`. -/
def wilsonAction_le : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) [NeZero L] (f : G → ℝ) (M : ℝ), (∀ g, |f g| ≤ M) →
    ∀ (β : ℝ), 0 ≤ β → ∀ U : GaugeField G d L,
      wilsonAction f β U ≤ β * ((L : ℝ) ^ d * (d : ℝ) ^ 2 * (2 * M))

/-- @title The Wilson action is translation invariant
@layer foundation
@difficulty 2
@deps 
`S(τ_a U) = S(U)`. -/
def wilsonAction_translate : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) [NeZero L] (f : G → ℝ) (β : ℝ) (a : Site d L)
    (U : GaugeField G d L),
    wilsonAction f β (translate a U) = wilsonAction f β U

/-! ## Foundation: paths and Wilson loops -/

/-- @title Endpoint of a concatenated path
@layer foundation
@difficulty 1
@deps 
`end(x, p ++ q) = end(end(x, p), q)`. -/
def endpoint_append : Prop :=
  ∀ (d L : ℕ) (x : Site d L) (p q : List (Step d)),
    endpoint x (p ++ q) = endpoint (endpoint x p) q

/-- @title Holonomy of a concatenated path
@layer foundation
@difficulty 2
@deps endpoint_append
`hol(x, p ++ q) = hol(x, p) · hol(end(x, p), q)`. -/
def holonomy_append : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) (U : GaugeField G d L) (x : Site d L) (p q : List (Step d)),
    holonomy U x (p ++ q) = holonomy U x p * holonomy U (endpoint x p) q

/-- @title Holonomy of the trivial field
@layer foundation
@difficulty 1
@deps 
For `U ≡ 1` the holonomy of every path is `1`. -/
def holonomy_trivialField : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) (x : Site d L) (p : List (Step d)),
    holonomy (trivialField : GaugeField G d L) x p = 1

/-- @title Gauge transformation of holonomies
@layer foundation
@difficulty 3
@deps holonomy_append
`hol_{g·U}(x, p) = g_x · hol_U(x, p) · g_{end(x,p)}⁻¹`. -/
def holonomy_gaugeAct : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) (g : GaugeTransform G d L) (U : GaugeField G d L)
    (x : Site d L) (p : List (Step d)),
    holonomy (gaugeAct g U) x p = g x * holonomy U x p * (g (endpoint x p))⁻¹

/-- @title A plaquette is the holonomy of the unit square
@layer foundation
@difficulty 2
@deps 
`U_{x,μν} = hol(x, rectangle μ ν 1 1)`. -/
def plaquette_eq_holonomy : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) (U : GaugeField G d L) (x : Site d L) (μ ν : Fin d),
    plaquette U x μ ν = holonomy U x (rectangle μ ν 1 1)

/-- @title Rectangular loops are closed
@layer foundation
@difficulty 2
@deps endpoint_append
`end(x, rectangle μ ν R T) = x`. -/
def endpoint_rectangle : Prop :=
  ∀ (d L : ℕ) (x : Site d L) (μ ν : Fin d) (R T : ℕ),
    endpoint x (rectangle μ ν R T) = x

/-- @title Wilson loops are gauge invariant
@layer foundation
@difficulty 2
@deps holonomy_gaugeAct
For a class function `χ` and a closed path: `W(g·U) = W(U)`. -/
def wilsonLoop_gaugeAct : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) (χ : G → ℝ), IsClassFunction χ →
    ∀ (x : Site d L) (p : List (Step d)), endpoint x p = x →
    ∀ (g : GaugeTransform G d L) (U : GaugeField G d L),
      wilsonLoop χ x p (gaugeAct g U) = wilsonLoop χ x p U

/-! ## Foundation: trace on the unitary group -/

/-- @title Trace of the identity
@layer foundation
@difficulty 1
@deps 
`Re tr 1 = n` in `U(n)`. -/
def reTrU_one : Prop :=
  ∀ n : ℕ, reTrU (1 : Matrix.unitaryGroup (Fin n) ℂ) = n

/-- @title Re tr is a class function on U(n)
@layer foundation
@difficulty 2
@deps 
`Re tr(g h g⁻¹) = Re tr h`. -/
def reTrU_isClassFunction : Prop :=
  ∀ n : ℕ, IsClassFunction (reTrU (n := n))

/-- @title Re tr of the inverse
@layer foundation
@difficulty 2
@deps 
`Re tr U⁻¹ = Re tr U` in `U(n)`. -/
def reTrU_inv : Prop :=
  ∀ (n : ℕ) (U : Matrix.unitaryGroup (Fin n) ℂ), reTrU U⁻¹ = reTrU U

/-- @title Re tr is at most the dimension
@layer foundation
@difficulty 3
@deps 
`Re tr U ≤ n` in `U(n)`. -/
def reTrU_le : Prop :=
  ∀ (n : ℕ) (U : Matrix.unitaryGroup (Fin n) ℂ), reTrU U ≤ n

/-- @title |Re tr| is at most the dimension
@layer foundation
@difficulty 3
@deps reTrU_le
`|Re tr U| ≤ n` in `U(n)`. -/
def abs_reTrU_le : Prop :=
  ∀ (n : ℕ) (U : Matrix.unitaryGroup (Fin n) ℂ), |reTrU U| ≤ n

/-- @title Re tr = n only at the identity
@layer foundation
@difficulty 4
@deps reTrU_le
`Re tr U = n ↔ U = 1` in `U(n)`. -/
def reTrU_eq_iff : Prop :=
  ∀ (n : ℕ) (U : Matrix.unitaryGroup (Fin n) ℂ), reTrU U = n ↔ U = 1

/-! ## Foundation: the Wilson measure -/

/-- @title The configuration measure is a probability measure
@layer foundation
@difficulty 1
@deps 
The product of probability Haar measures over all links is a probability measure. -/
def configMeasure_isProbability : Prop :=
  ∀ (G : Type) [Group G] [MeasurableSpace G] (μG : Measure G) [IsProbabilityMeasure μG]
    (d L : ℕ) [NeZero L],
    IsProbabilityMeasure (configMeasure (d := d) (L := L) μG)

/-- @title The Boltzmann weight is at most one
@layer foundation
@difficulty 1
@deps wilsonAction_nonneg
If `f ≤ f(1)` and `β ≥ 0`, then `exp(−S) ≤ 1`. -/
def boltzmann_le_one : Prop :=
  ∀ (G : Type) [Group G] (d L : ℕ) [NeZero L] (f : G → ℝ), (∀ g, f g ≤ f 1) →
    ∀ (β : ℝ), 0 ≤ β → ∀ U : GaugeField G d L, boltzmann f β U ≤ 1

/-- @title The Wilson action is continuous
@layer foundation
@difficulty 3
@deps 
For continuous `f` on a topological group, `S` is continuous in the configuration. -/
def wilsonAction_continuous : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (d L : ℕ) [NeZero L]
    (f : G → ℝ), Continuous f → ∀ β : ℝ,
    Continuous (wilsonAction (d := d) (L := L) f β)

/-- @title The partition function at β = 0 is one
@layer foundation
@difficulty 2
@deps configMeasure_isProbability
`Z(0) = 1`. -/
def partitionFunction_zero : Prop :=
  ∀ (G : Type) [Group G] [MeasurableSpace G] (μG : Measure G) [IsProbabilityMeasure μG]
    (d L : ℕ) [NeZero L] (f : G → ℝ),
    partitionFunction (d := d) (L := L) μG f 0 = 1

/-- @title The partition function is positive
@layer foundation
@difficulty 4
@deps wilsonAction_continuous configMeasure_isProbability
For a compact group and continuous `f`: `Z > 0`. -/
def partitionFunction_pos : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG] (d L : ℕ) [NeZero L]
    (f : G → ℝ), Continuous f → ∀ β : ℝ,
    0 < partitionFunction (d := d) (L := L) μG f β

/-- @title The partition function is at most one
@layer foundation
@difficulty 3
@deps boltzmann_le_one wilsonAction_continuous
If `f ≤ f(1)` and `β ≥ 0`, then `Z ≤ 1`. -/
def partitionFunction_le_one : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG] (d L : ℕ) [NeZero L]
    (f : G → ℝ), Continuous f → (∀ g, f g ≤ f 1) → ∀ β : ℝ, 0 ≤ β →
    partitionFunction (d := d) (L := L) μG f β ≤ 1

/-- @title Expectation of a constant
@layer foundation
@difficulty 3
@deps partitionFunction_pos
`⟨c⟩ = c`. -/
def expectation_const : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG] (d L : ℕ) [NeZero L]
    (f : G → ℝ), Continuous f → ∀ (β c : ℝ),
    expectation (d := d) (L := L) μG f β (fun _ => c) = c

/-- @title Bounded observables have bounded expectations
@layer foundation
@difficulty 3
@deps partitionFunction_pos
If `|O| ≤ M`, then `|⟨O⟩| ≤ M`. -/
def abs_expectation_le : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG] (d L : ℕ) [NeZero L]
    (f : G → ℝ), Continuous f → ∀ (β M : ℝ) (O : GaugeField G d L → ℝ),
    Measurable O → (∀ U, |O U| ≤ M) →
    |expectation μG f β O| ≤ M

/-- @title Expectations are gauge invariant
@layer foundation
@difficulty 5
@deps wilsonAction_gaugeAct partitionFunction_pos
For bi-invariant Haar measure and class function `f`: `⟨O ∘ g⟩ = ⟨O⟩`. -/
def expectation_gaugeAct : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
    (d L : ℕ) [NeZero L] (f : G → ℝ), Continuous f → IsClassFunction f →
    ∀ (β : ℝ) (g : GaugeTransform G d L) (O : GaugeField G d L → ℝ),
      expectation μG f β (fun U => O (gaugeAct g U)) = expectation μG f β O

/-- @title Expectations are translation invariant
@layer foundation
@difficulty 4
@deps wilsonAction_translate partitionFunction_pos
`⟨O ∘ τ_a⟩ = ⟨O⟩`. -/
def expectation_translate : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG]
    (d L : ℕ) [NeZero L] (f : G → ℝ), Continuous f →
    ∀ (β : ℝ) (a : Site d L) (O : GaugeField G d L → ℝ),
      expectation μG f β (fun U => O (translate a U)) = expectation μG f β O

/-- @title Elitzur's theorem for a single link
@layer foundation
@difficulty 6
@deps expectation_gaugeAct expectation_const
A gauge-variant observable of one link averages over Haar measure:
`⟨F(U_{x,μ})⟩ = ∫ F dμ` (for `L ≥ 2`). -/
def elitzur_single_link : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
    (d L : ℕ) [NeZero L], 2 ≤ L → ∀ (f : G → ℝ), Continuous f → IsClassFunction f →
    ∀ (β : ℝ) (F : G → ℝ), Continuous F → ∀ (x : Site d L) (μ : Fin d),
      expectation μG f β (fun U => F (U x μ)) = ∫ g, F g ∂μG

/-! ## Known hard results -/

/-- @title At β = 0 a plaquette is Haar distributed
@layer hard
@difficulty 5
@deps partitionFunction_zero
At `β = 0`, `μ ≠ ν`, `L ≥ 2`: `⟨χ(U_{x,μν})⟩ = ∫ χ dμ`. -/
def plaquette_expectation_zero : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
    (d L : ℕ) [NeZero L], 2 ≤ L → ∀ (f χ : G → ℝ), Continuous χ →
    ∀ (x : Site d L) (μ ν : Fin d), μ ≠ ν →
      expectation μG f 0 (plaquetteObs χ x μ ν) = ∫ g, χ g ∂μG

/-- @title At β = 0 distant plaquettes are independent
@layer hard
@difficulty 4
@deps plaquette_expectation_zero
At `β = 0` spatial plaquettes at different times are uncorrelated. -/
def covariance_zero_far : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
    (d L : ℕ) [NeZero L] (f χ : G → ℝ), Continuous χ →
    ∀ (τ μ ν : Fin d), μ ≠ ν → μ ≠ τ → ν ≠ τ → ∀ t : ℕ, 1 ≤ t → t < L →
      covariance μG f 0 (plaquetteObs χ 0 μ ν) (plaquetteObs χ (Pi.single τ (t : ZMod L)) μ ν) = 0

/-- @title log Z is convex in β
@layer hard
@difficulty 5
@deps partitionFunction_pos
`β ↦ log Z(β)` is convex (Hölder's inequality). -/
def log_partitionFunction_convex : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG] (d L : ℕ) [NeZero L]
    (f : G → ℝ), Continuous f →
    ConvexOn ℝ Set.univ (fun β : ℝ => Real.log (partitionFunction (d := d) (L := L) μG f β))

/-- @title The free energy density exists
@layer hard
@difficulty 7
@deps partitionFunction_pos partitionFunction_le_one
The limit of `log Z_L / L^d` as `L → ∞` exists. -/
def free_energy_limit : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG] (d : ℕ)
    (f : G → ℝ), Continuous f → ∀ β : ℝ, 0 ≤ β →
    ∃ F : ℝ, Filter.Tendsto
      (fun L : ℕ => Real.log (partitionFunction (d := d) (L := L + 1) μG f β) / ((L + 1 : ℝ) ^ d))
      Filter.atTop (nhds F)

/-- @title Mass gap at strong coupling (Osterwalder–Seiler)
@layer hard
@difficulty 9
@deps covariance_zero_far expectation_gaugeAct
For every compact group, at small `β` plaquette correlations decay exponentially,
uniformly in the volume. -/
def strong_coupling_mass_gap : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
    (f χ : G → ℝ), Continuous f → Continuous χ → IsClassFunction f →
    (∀ g, |f g| ≤ 1) → (∀ g, |χ g| ≤ 1) →
    ∀ (d : ℕ) (τ μ ν : Fin d), μ ≠ ν → μ ≠ τ → ν ≠ τ →
    ∃ β₀ > 0, ∃ m > 0, ∃ C : ℝ, ∀ β ∈ Set.Icc 0 β₀, ∀ (L : ℕ) [NeZero L], ∀ t : ℕ, 2 * t ≤ L →
      |covariance (d := d) (L := L) μG f β (plaquetteObs χ 0 μ ν)
          (plaquetteObs χ (Pi.single τ (t : ZMod L)) μ ν)| ≤ C * Real.exp (-m * t)

/-- @title Area law for U(1) at strong coupling
@layer hard
@difficulty 9
@deps wilsonLoop_gaugeAct endpoint_rectangle plaquette_expectation_zero
For `U(1)` at small `β` Wilson loops decay like `exp(−σ · area)` (confinement). -/
def u1_area_law_strong_coupling : Prop :=
  ∀ (μG : Measure Circle) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
    (d : ℕ) (μ ν : Fin d), μ ≠ ν →
    ∃ β₀ > 0, ∃ σ > 0, ∃ C : ℝ, ∀ β ∈ Set.Icc 0 β₀, ∀ (L : ℕ) [NeZero L], ∀ R T : ℕ,
      2 * R ≤ L → 2 * T ≤ L →
      |expectation (d := d) (L := L) μG reCircle β (wilsonLoop reCircle 0 (rectangle μ ν R T))|
        ≤ C * Real.exp (-σ * R * T)

/-! ## Open problems -/

/-- @title Lattice mass gap for SU(2) in 4D at every β
@layer open
@difficulty 10
@deps strong_coupling_mass_gap reTrU_eq_iff abs_reTrU_le
OPEN. For SU(2), d = 4, Wilson action `Re tr` and every `β > 0`, plaquette correlations
decay exponentially, uniformly in the volume. -/
def mass_gap_su2_d4 : Prop :=
  ∀ (μG : Measure (SU 2)) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant] (β : ℝ), 0 < β →
    ∃ m > 0, ∃ C : ℝ, ∀ (L : ℕ) [NeZero L], ∀ t : ℕ, 2 * t ≤ L →
      |covariance (d := 4) (L := L) μG reTr β (plaquetteObs reTr 0 1 2)
          (plaquetteObs reTr (Pi.single 0 (t : ZMod L)) 1 2)| ≤ C * Real.exp (-m * t)

/-- @title Lattice mass gap for SU(3) in 4D at every β
@layer open
@difficulty 10
@deps mass_gap_su2_d4
OPEN. The same for SU(3), the gauge group of QCD. -/
def mass_gap_su3_d4 : Prop :=
  ∀ (μG : Measure (SU 3)) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant] (β : ℝ), 0 < β →
    ∃ m > 0, ∃ C : ℝ, ∀ (L : ℕ) [NeZero L], ∀ t : ℕ, 2 * t ≤ L →
      |covariance (d := 4) (L := L) μG reTr β (plaquetteObs reTr 0 1 2)
          (plaquetteObs reTr (Pi.single 0 (t : ZMod L)) 1 2)| ≤ C * Real.exp (-m * t)

/-- @title Lattice mass gap for SU(2) in 3D at every β
@layer open
@difficulty 10
@deps strong_coupling_mass_gap
OPEN. The three-dimensional version for SU(2). -/
def mass_gap_su2_d3 : Prop :=
  ∀ (μG : Measure (SU 2)) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant] (β : ℝ), 0 < β →
    ∃ m > 0, ∃ C : ℝ, ∀ (L : ℕ) [NeZero L], ∀ t : ℕ, 2 * t ≤ L →
      |covariance (d := 3) (L := L) μG reTr β (plaquetteObs reTr 0 1 2)
          (plaquetteObs reTr (Pi.single 0 (t : ZMod L)) 1 2)| ≤ C * Real.exp (-m * t)

/-- @title Confinement for SU(2) in 4D at every β
@layer open
@difficulty 10
@deps u1_area_law_strong_coupling mass_gap_su2_d4
OPEN. Area law for SU(2) Wilson loops, d = 4, at every `β > 0`. -/
def area_law_su2_d4 : Prop :=
  ∀ (μG : Measure (SU 2)) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant] (β : ℝ), 0 < β →
    ∃ σ > 0, ∃ C : ℝ, ∀ (L : ℕ) [NeZero L], ∀ R T : ℕ, 2 * R ≤ L → 2 * T ≤ L →
      |expectation (d := 4) (L := L) μG reTr β (wilsonLoop reTr 0 (rectangle 0 1 R T))|
        ≤ C * Real.exp (-σ * R * T)

end YangMillsGap.Stmt
