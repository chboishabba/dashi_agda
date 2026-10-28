import HornedC3.ThreeArmRadiusConnectedAssembly
import HornedC3.ThreeArmRadiusCutHatcherTransport

/-!
# Radius cuts + actual overlap points + Hatcher free-product endgame.

All already-paid algebra is reused:
* radiusCutSourceGroupsEquivPi1 from ThreeArmRadiusCutHatcherTransport
* IsPathConnected.union from Mathlib, via radiusCover_member_pathConnected
* actual overlap witness points from radiusArms_meet_of_points.

The new statement needs only connected central C, connected individual
satellite pieces S_i, X-valued overlap points, central pi1 and the
actual Hatcher meridian-group identifications on U_i. There is NO
independent IsPathConnected(U_i) hypothesis.

This source is a conditional theorem, not a claim that the exact
supported infinite wild ball maps have been supplied or compiled.

Mathematical attribution: Alexander (1924), Hatcher AT Example 2B.2,
classical van Kampen and path-connected-union theorem.
Formal owner: pinned Deicyde/hatcher-at and Mathlib; geometry and
source-specific composition in DASHI #1244.
-/

noncomputable section
open scoped ContinuousMap
open Hatcher.VanKampen

namespace DASHI.AlexanderHornedC3

universe u v w
variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [PseudoMetricSpace Y]

/-- The most concise geometry-shaped algebraic endgame yet:
the connectivity of each U_i is DERIVED, not another axiom. -/
def radiusCutSourceGroupsEquivPi1OfArms
    (f : C(X, Y)) (centres : Fin 3 → Y)
    (inner outer : ℝ) (x₀ : X)
    (hcut : inner < outer)
    (hsep : ∀ i j, i ≠ j →
      (2 : ℝ) * outer < dist (centres i) (centres j))
    (hclear : ∀ i, inner < dist (f x₀) (centres i))
    (hcore : IsPathConnected (radiusCore f centres inner))
    (harms : ∀ i, IsPathConnected (radiusArm f centres outer i))
    (p : Fin 3 → X)
    (hpC : ∀ i, p i ∈ radiusCore f centres inner)
    (hpS : ∀ i, p i ∈ radiusArm f centres outer i)
    (hcorePi1 : Subsingleton
      (FundamentalGroup (radiusCore f centres inner)
        (⟨x₀, radiusCore_basepoint f centres inner x₀ hclear⟩ :
          radiusCore f centres inner)))
    (G : Fin 3 → Type w) [∀ i, Group (G i)]
    (hmemberGroups : ∀ i, G i ≃*
      CoverGroup
        (collarMember (radiusCore f centres inner)
          (radiusArm f centres outer))
        x₀
        (collarBasepoint
          (radiusCore f centres inner)
          (radiusArm f centres outer)
          x₀ (radiusCore_basepoint f centres inner x₀ hclear)) i) :
    Monoid.CoprodI G ≃* FundamentalGroup X x₀ :=
  radiusCutSourceGroupsEquivPi1 f centres inner outer x₀
    hcut hsep hclear hcore
    (radiusCover_member_pathConnected f centres inner outer hcore
      harms (radiusArms_meet_of_points f centres inner outer p hpC hpS))
    hcorePi1 G hmemberGroups

end DASHI.AlexanderHornedC3
