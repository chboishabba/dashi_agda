import HornedC3.ThreeArmHatcherGroupTransport
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# Actual radius-cut open cover: elementary metric geometry, not a postulate

The previously constructed C3 exterior cover has:
C = E intersect every complement of a radius r_- closed satellite ball,
S_i = E intersect the open radius r_+ satellite ball.
Here E is ANY subspace of a metric ambient Y and f : E -> Y is its
continuous inclusion. Thus the centres remain in Y (the actual horn
centres lie INSIDE the removed solid and cannot be used as points of E).

This source proves openness, complete coverage and off-diagonal
satellite disjointness FROM the elementary hypotheses r_-<r_+ and
2*r_+<dist(c_i,c_j), rather than assuming those cover fields.
Connectivity and fundamental groups require real geometry and remain
precisely named inputs.

Original van Kampen, Hatcher AT Ex 2B.2 and Alexander wild-ball
results retain their original authors; pinned Hatcher-at supplies
the existing kernel-level cover consumer. The radius placement and
this glue are DASHI #1244. Exact-head typecheck is pending.
-/

noncomputable section

open scoped ContinuousMap

open Set

namespace DASHI.AlexanderHornedC3

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [PseudoMetricSpace Y]

def radiusCore (f : C(X, Y)) (centres : Fin 3 → Y)
    (inner : ℝ) : Set X :=
  f ⁻¹' (⋃ i, Metric.closedBall (centres i) inner)ᶜ

def radiusArm (f : C(X, Y)) (centres : Fin 3 → Y)
    (outer : ℝ) (i : Fin 3) : Set X :=
  f ⁻¹' Metric.ball (centres i) outer

theorem radiusCore_open (f : C(X, Y))
    (centres : Fin 3 → Y) (inner : ℝ) :
    IsOpen (radiusCore f centres inner) := by
  unfold radiusCore
  exact ((isClosed_iUnion fun i => Metric.isClosed_closedBall).isOpen_compl).preimage
    f.continuous

theorem radiusArm_open (f : C(X, Y))
    (centres : Fin 3 → Y) (outer : ℝ) :
    ∀ i, IsOpen (radiusArm f centres outer i) := by
  intro i
  exact Metric.isOpen_ball.preimage f.continuous

theorem radiusArms_disjoint
    (f : C(X, Y)) (centres : Fin 3 → Y) (outer : ℝ)
    (hsep : ∀ i j, i ≠ j →
       (2 : ℝ) * outer < dist (centres i) (centres j)) :
    ∀ i j, i ≠ j →
      Disjoint (radiusArm f centres outer i)
               (radiusArm f centres outer j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi : dist (f x) (centres i) < outer :=
    Metric.mem_ball.mp hxi
  have hj : dist (f x) (centres j) < outer :=
    Metric.mem_ball.mp hxj
  have hi' : dist (centres i) (f x) < outer := by
    simpa only [dist_comm] using hi
  have htri : dist (centres i) (centres j) ≤
      dist (centres i) (f x) + dist (f x) (centres j) :=
    dist_triangle _ _ _
  linarith [hsep i j hij]

theorem radiusCover_full
    (f : C(X, Y)) (centres : Fin 3 → Y)
    (inner outer : ℝ) (hcut : inner < outer) :
    Set.univ ⊆
      ⋃ i, collarMember (radiusCore f centres inner)
        (radiusArm f centres outer) i := by
  intro x _
  by_cases hinner : f x ∈ ⋃ i, Metric.closedBall (centres i) inner
  · rcases Set.mem_iUnion.mp hinner with ⟨i, hi⟩
    have hdist : dist (f x) (centres i) ≤ inner :=
      Metric.mem_closedBall.mp hi
    have hxarm : x ∈ radiusArm f centres outer i :=
      Metric.mem_ball.mpr (lt_of_le_of_lt hdist hcut)
    exact Set.mem_iUnion.mpr ⟨i, Or.inr hxarm⟩
  · have hxcore : x ∈ radiusCore f centres inner := hinner
    exact Set.mem_iUnion.mpr
      ⟨(0 : Fin 3), Or.inl hxcore⟩

theorem radiusCore_basepoint
    (f : C(X, Y)) (centres : Fin 3 → Y)
    (inner : ℝ) (x₀ : X)
    (hclear : ∀ i, inner < dist (f x₀) (centres i)) :
    x₀ ∈ radiusCore f centres inner := by
  change f x₀ ∉ ⋃ i, Metric.closedBall (centres i) inner
  intro hmem
  rcases Set.mem_iUnion.mp hmem with ⟨i, hi⟩
  exact (not_lt_of_ge (Metric.mem_closedBall.mp hi)) (hclear i)

/-- All *elementary* radius-cover data are now computed.
The remaining hypotheses (connected cover members, connected simply
connected central region) concern the actual chosen wild exterior. -/
def radiusCutCentralCertificates
    (f : C(X, Y)) (centres : Fin 3 → Y)
    (inner outer : ℝ) (x₀ : X)
    (hcut : inner < outer)
    (hsep : ∀ i j, i ≠ j →
       (2 : ℝ) * outer < dist (centres i) (centres j))
    (hclear : ∀ i, inner < dist (f x₀) (centres i))
    (hcoreConnected : IsPathConnected (radiusCore f centres inner))
    (hmemberConnected : ∀ i,
      IsPathConnected
        (collarMember (radiusCore f centres inner)
          (radiusArm f centres outer) i))
    (hcorePi1 : Subsingleton
       (FundamentalGroup (radiusCore f centres inner)
         (⟨x₀, radiusCore_basepoint f centres inner x₀ hclear⟩ :
           radiusCore f centres inner))) :
    CentralPi1CoverCertificates x₀
      (radiusCore f centres inner) (radiusArm f centres outer) where
  central_open := radiusCore_open f centres inner
  sector_open := radiusArm_open f centres outer
  satellite_disjoint := radiusArms_disjoint f centres outer hsep
  all_covered := radiusCover_full f centres inner outer hcut
  each_connected := hmemberConnected
  central_connected := hcoreConnected
  central_basepoint := radiusCore_basepoint f centres inner x₀ hclear
  central_pi1_trivial := hcorePi1

end DASHI.AlexanderHornedC3
