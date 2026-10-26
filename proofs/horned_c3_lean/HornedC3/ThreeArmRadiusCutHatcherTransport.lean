import HornedC3.ThreeArmRadiusCutGeometry

/-!
# One end-to-end kernel-target consumer for the selected 3-arm radius cover.

Given an actual exterior X continuously embedded in a pseudo-metric
ambient Y, the chosen nested-radius cuts determine all OPEN COVER,
COVERAGE and DISJOINTNESS fields. Only the *geometric* central-space
simple connectivity/path connectivity, three member path-connectivity
witnesses, and source-group identifications remain as arguments.

This def composes, without new van Kampen theory:
  ThreeArmRadiusCutGeometry.radiusCutCentralCertificates,
  ThreeArmCentralPi1Reduction.centralPi1CoverFreeProduct,
  Hatcher.coprodIEquiv (from pinned Deicyde/hatcher-at).

A smooth/tame clopen-ball model, finite 2I quotient, or end-point
Cantor cylinder is not a witness for any source meridian-group field.
Mathematical roots: Alexander, Hatcher, classical van Kampen and
tame Schoenflies. User-directed DASHI #1244 owns this glue only.
No exact-head kernel receipt in this session.
-/

noncomputable section

open scoped ContinuousMap

open Hatcher.VanKampen

namespace DASHI.AlexanderHornedC3

universe u v w

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [PseudoMetricSpace Y]

def radiusCutSourceGroupsEquivPi1
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
  (Hatcher.coprodIEquiv hmemberGroups).trans
    (centralPi1CoverFreeProduct x₀
      (radiusCore f centres inner) (radiusArm f centres outer)
      (radiusCutCentralCertificates f centres inner outer x₀
        hcut hsep hclear hcoreConnected hmemberConnected hcorePi1))

end DASHI.AlexanderHornedC3
