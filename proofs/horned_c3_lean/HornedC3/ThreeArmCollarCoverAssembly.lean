import HornedC3.ThreeArmCollarIntersections

/-!
# Reusable collar-cover assembly, not a new geometric existence assertion

The previously established pair/triple intersection identities identify
all off-diagonal overlaps with the common central open region. This file
packages the precise remaining *actual point-set* hypotheses into the
existing Hatcher van Kampen consumer. No postulates, axioms, or synthetic
wild embedding are introduced here.

Original van Kampen: Seifert / van Kampen; the selected horned sphere:
Alexander 1924; Hatcher, Algebraic Topology, Example 2B.2.
The formal consumer here is existing DASHI/Hatcher-at work.

This source requires exact-head Lean typechecking before claiming
kernel verification.
-/

noncomputable section

open Set
open Hatcher.VanKampen

namespace DASHI.AlexanderHornedC3

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The minimal additional obligations after proving that the three
satellite-only open subsets are disjoint. Unlike overlap geometry,
these cannot be discharged using only finite coordinate samples. -/
structure CollarCoverCertificates (x₀ : X)
    (C : Set X) (S : Fin 3 → Set X) where
  central_open : IsOpen C
  sector_open : ∀ i, IsOpen (S i)
  satellite_disjoint : ∀ i j, i ≠ j → Disjoint (S i) (S j)
  all_covered : univ ⊆ ⋃ i, collarMember C S i
  each_connected : ∀ i, IsPathConnected (collarMember C S i)
  central_connected : IsPathConnected C
  central_basepoint : x₀ ∈ C
  central_pi1_trivial :
    ∀ i j, i ≠ j →
      Subsingleton
        (OverlapGroup (collarMember C S) x₀
          (collarBasepoint C S x₀ central_basepoint) i j)

/-- All van Kampen cover fields except connectivity of each arm
follow from the shared central piece and satellite disjointness.
The overlap fundamental-group certificate is explicitly retained:
a homeomorphic disk picture alone does not define the based overlap
group in the chosen full cover. -/
def collarCertificatesToCover
    (x₀ : X) (C : Set X) (S : Fin 3 → Set X)
    (h : CollarCoverCertificates x₀ C S) :
    ThreeArmCollarCover x₀ where
  U := collarMember C S
  open_member := collarCoverOpen C S h.central_open h.sector_open
  covers := h.all_covered
  connected_member := h.each_connected
  connected_pair := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa only [Set.inter_self] using h.each_connected i
    · rw [collarPairIntersectionEq C S h.satellite_disjoint i j hij]
      exact h.central_connected
  connected_triple := by
    intro i j k
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simpa only [Set.inter_self] using h.each_connected i
      · rw [Set.inter_self]
        rw [collarPairIntersectionEq C S h.satellite_disjoint i k hik]
        exact h.central_connected
    · rw [collarTripleIntersectionEq C S h.satellite_disjoint i j k hij]
      exact h.central_connected
  basepoint := collarBasepoint C S x₀ h.central_basepoint
  off_diagonal_overlap_pi1_trivial := h.central_pi1_trivial

/-- Reuse the existing formal van Kampen consumer without redefining
fundamental groups or any source-side free products. -/
def collarCertificatesPi1FreeProduct
    (x₀ : X) (C : Set X) (S : Fin 3 → Set X)
    (h : CollarCoverCertificates x₀ C S) :
    CoverFreeProduct (collarMember C S) x₀
      (collarBasepoint C S x₀ h.central_basepoint) ≃*
      FundamentalGroup X x₀ :=
  threeArmCoverPi1FreeProduct x₀
    (collarCertificatesToCover x₀ C S h)

end DASHI.AlexanderHornedC3
