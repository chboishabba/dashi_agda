import HornedC3.ThreeArmCentralPi1Reduction

/-!
# Three-sector Hatcher group endgame: reuse existing van Kampen

This is a COMPOSITION theorem. The DASHI shared-central cover certificates
yield an isomorphism from the free product of the actual cover members'
fundamental groups to the ambient fundamental group. Given SEPARATE actual
geometric group equivalences from source groups into those cover members,
the existing Hatcher-at coprodIEquiv transports their free product.

Mathematical attribution: Alexander 1924; Hatcher Algebraic Topology
Example 2B.2; classical Seifert--van Kampen. Formal implementation
donor: Deicyde/hatcher-at. The chosen C3 cover is DASHI #1244.
No all-depth wild embedding or satellite homotopy has been created.
Exact-head Lean kernel verification NOT run.
-/

noncomputable section

open Hatcher.VanKampen

namespace DASHI.AlexanderHornedC3

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- The precise needed geometric-to-group interface. Each member
equivalence refers to its actual selected cover subset, and no
disconnected clopen endpoint set is silently equated with it. -/
structure ThreeArmSourceGroupCertificates
    (x₀ : X) (C : Set X) (S : Fin 3 → Set X)
    (G : Fin 3 → Type v) [∀ i, Group (G i)] where
  cover : CentralPi1CoverCertificates x₀ C S
  member_group : ∀ i : Fin 3,
    G i ≃*
      CoverGroup (collarMember C S) x₀
        (collarBasepoint C S x₀ cover.central_basepoint) i

/-- Formal group-theoretic endgame, conditional on actual geometry.
Do NOT replace member_group by finite holonomy or clopen labels. -/
def sourceGroupsEquivAmbientPi1
    (x₀ : X) (C : Set X) (S : Fin 3 → Set X)
    (G : Fin 3 → Type v) [∀ i, Group (G i)]
    (h : ThreeArmSourceGroupCertificates x₀ C S G) :
    Monoid.CoprodI G ≃* FundamentalGroup X x₀ :=
  (Hatcher.coprodIEquiv h.member_group).trans
    (centralPi1CoverFreeProduct x₀ C S h.cover)

/-- All three sources specialize to Hatcher's one-sector group.
The only remaining member_group witnesses come from the actual
satellite relative collar/homeotopy geometry, not from this code. -/
def threeHatcherGroupsEquivAmbientPi1
    (x₀ : X) (C : Set X) (S : Fin 3 → Set X)
    (G_A : Type v) [Group G_A]
    (h : ThreeArmSourceGroupCertificates x₀ C S
      (fun _ : Fin 3 => G_A)) :
    Monoid.CoprodI (fun _ : Fin 3 => G_A) ≃*
      FundamentalGroup X x₀ :=
  sourceGroupsEquivAmbientPi1 x₀ C S
    (fun _ : Fin 3 => G_A) h

end DASHI.AlexanderHornedC3
