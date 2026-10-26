import HornedC3.ThreeArmRadiusCutGeometry

/-!
# Three-arm radius cover: member connectivity from the ACTUAL overlap points

Reuses Mathlib's IsPathConnected.union theorem. For every chosen
C3 sector U_i = C ∪ S_i, path-connectedness follows from
(a) a path-connected central C, (b) a path-connected satellite piece
S_i, and (c) a single actual point p_i in C ∩ S_i.

This avoids postulating IsPathConnected(U_i) separately.
Existing DASHI exact rational C3 endpoint p_i=13e_i establishes (c)
at the paper/geometric level. This theorem accepts verified X-valued
witnesses rather than pretending that every ambient p_i lies in
X = R^3 minus the chosen wild solid.

Mathematical owners: classical path-connected union theorem,
Alexander (1924), Hatcher AT Example 2B.2 (source geometry).
Formal owner: existing Mathlib IsPathConnected.union.
This glue is DASHI PR #1244; exact-head Lean compile pending.
-/

noncomputable section

open Set

namespace DASHI.AlexanderHornedC3

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [PseudoMetricSpace Y]

/-- A chosen point in each actual central/satellite overlap.
In the intended R3 placement, p_i = 13*e_i. -/
theorem radiusArms_meet_of_points
    (f : C(X, Y)) (centres : Fin 3 → Y)
    (inner outer : ℝ)
    (p : Fin 3 → X)
    (hpC : ∀ i, p i ∈ radiusCore f centres inner)
    (hpS : ∀ i, p i ∈ radiusArm f centres outer i) :
    ∀ i, (radiusCore f centres inner ∩
      radiusArm f centres outer i).Nonempty := by
  intro i
  exact ⟨p i, hpC i, hpS i⟩

/-- Every cover MEMBER is path-connected by the pre-existing
union theorem; the intersection is not guessed from a sketch. -/
theorem radiusCover_member_pathConnected
    (f : C(X, Y)) (centres : Fin 3 → Y)
    (inner outer : ℝ)
    (hcore : IsPathConnected (radiusCore f centres inner))
    (harms : ∀ i, IsPathConnected (radiusArm f centres outer i))
    (hmeets : ∀ i, (radiusCore f centres inner ∩
      radiusArm f centres outer i).Nonempty) :
    ∀ i, IsPathConnected
      (collarMember (radiusCore f centres inner)
        (radiusArm f centres outer) i) := by
  intro i
  exact hcore.union (harms i) (hmeets i)

/-- Refined minimal geometric contract.
The member-connectedness slots are filled mechanically from
the genuine connectedness and intersection-point certificates. -/
def radiusCutCentralCertificatesOfArms
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
          radiusCore f centres inner))) :
    CentralPi1CoverCertificates x₀
      (radiusCore f centres inner) (radiusArm f centres outer) :=
  radiusCutCentralCertificates f centres inner outer x₀
    hcut hsep hclear hcore
    (radiusCover_member_pathConnected f centres inner outer hcore
      harms (radiusArms_meet_of_points f centres inner outer p hpC hpS))
    hcorePi1

end DASHI.AlexanderHornedC3
