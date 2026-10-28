import HornedC3.ThreeArmCollarCoverAssembly

/-!
# Central pi1 reduction of the three-arm collar cover

Reuses the exact Subsingleton/OverlapGroup interface from the pinned
Deicyde/hatcher-at dependency and the existing DASHI intersection lemma.

For U_i = C ∪ S_i with pairwise disjoint satellite-only regions S_i,
all off-diagonal overlap groups are π₁(C,x₀). Thus ONE certificate
of central π₁-triviality replaces the family of off-diagonal group
certificates in CollarCoverCertificates.

Mathematical roots: Seifert--van Kampen, Hatcher Algebraic Topology
§1.2 and Example 2B.2; Alexander 1924 for the horned sphere.
This file does NOT construct the actual infinite wild satellite or
its geometric collar maps. Exact-head Lean typechecking is required
before treating this source as kernel-verified.
-/

noncomputable section

open Set
open Hatcher.VanKampen

namespace DASHI.AlexanderHornedC3

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The common central region is only required to have trivial π₁.
It need NOT be contractible: nonzero higher homotopy is permitted. -/
structure CentralPi1CoverCertificates (x₀ : X)
    (C : Set X) (S : Fin 3 → Set X) where
  central_open : IsOpen C
  sector_open : ∀ i, IsOpen (S i)
  satellite_disjoint : ∀ i j, i ≠ j → Disjoint (S i) (S j)
  all_covered : univ ⊆ ⋃ i, collarMember C S i
  each_connected : ∀ i, IsPathConnected (collarMember C S i)
  central_connected : IsPathConnected C
  central_basepoint : x₀ ∈ C
  central_pi1_trivial :
    Subsingleton (FundamentalGroup C (⟨x₀, central_basepoint⟩ : C))

/-- The central π₁ certificate transports to every off-diagonal
overlap after rewriting by the actual set-intersection equality. -/
def centralPi1ToCollarCertificates
    (x₀ : X) (C : Set X) (S : Fin 3 → Set X)
    (h : CentralPi1CoverCertificates x₀ C S) :
    CollarCoverCertificates x₀ C S where
  central_open := h.central_open
  sector_open := h.sector_open
  satellite_disjoint := h.satellite_disjoint
  all_covered := h.all_covered
  each_connected := h.each_connected
  central_connected := h.central_connected
  central_basepoint := h.central_basepoint
  central_pi1_trivial := by
    intro i j hij
    change Subsingleton
      (FundamentalGroup
        (collarMember C S i ∩ collarMember C S j)
        (⟨x₀, (collarBasepoint C S x₀ h.central_basepoint i,
                   collarBasepoint C S x₀ h.central_basepoint j)⟩ :
          collarMember C S i ∩ collarMember C S j))
    rw [collarPairIntersectionEq C S h.satellite_disjoint i j hij]
    exact h.central_pi1_trivial

/-- The same existing Hatcher/van Kampen consumer now needs only one
based central-group certificate rather than three overlap certificates. -/
def centralPi1CoverFreeProduct
    (x₀ : X) (C : Set X) (S : Fin 3 → Set X)
    (h : CentralPi1CoverCertificates x₀ C S) :
    CoverFreeProduct (collarMember C S) x₀
      (collarBasepoint C S x₀ h.central_basepoint) ≃*
      FundamentalGroup X x₀ :=
  collarCertificatesPi1FreeProduct x₀ C S
    (centralPi1ToCollarCertificates x₀ C S h)

end DASHI.AlexanderHornedC3
