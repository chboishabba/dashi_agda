import Hatcher.VanKampen.WedgeFundamentalGroup

/-!
# Three-region van Kampen consumer for the C3 horned-ball exterior

Published mathematical sources: Hatcher, Algebraic Topology, section 1.2
and Example 2B.2.
Kernel dependency: Deicyde/hatcher-at, pinned to
fb20d71b6a7561c80f66350c14af118f3962377a.
Named already-proved declarations:
relationSubgroup_eq_bot_of_overlap_subsingleton
freeProductEquivFundamentalGroupOfRelationsTrivial

This proves the three-region free-product result for an actual open
cover with actual connectivity/trivial-overlap certificates.
The horned-ball collars, compactness, stage maps and geometric
identification remain separate concrete obligations.
-/

noncomputable section

open Set
open Hatcher.VanKampen

namespace DASHI.AlexanderHornedC3

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Data for the real three-piece geometric open cover. A source
drawing, an abstract group, or disjointness of Euclidean envelopes
does not itself inhabit these fields. -/
structure ThreeArmCollarCover (x₀ : X) where
  U : Fin 3 → Set X
  open_member : ∀ i, IsOpen (U i)
  covers : univ ⊆ ⋃ i, U i
  connected_member : ∀ i, IsPathConnected (U i)
  connected_pair : ∀ i j, IsPathConnected (U i ∩ U j)
  connected_triple : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k)
  basepoint : ∀ i, x₀ ∈ U i
  off_diagonal_overlap_pi1_trivial :
    ∀ i j, i ≠ j →
      Subsingleton (OverlapGroup U x₀ basepoint i j)

/-- Proof-bearing van Kampen consumer: conditional on genuine
point-set certificates, this is the actual ambient fundamental group. -/
def threeArmCoverPi1FreeProduct
    (x₀ : X) (C : ThreeArmCollarCover x₀) :
    CoverFreeProduct C.U x₀ C.basepoint ≃* FundamentalGroup X x₀ :=
  freeProductEquivFundamentalGroupOfRelationsTrivial
    C.U x₀ C.open_member C.covers C.connected_member
    C.connected_pair C.connected_triple C.basepoint
    (relationSubgroup_eq_bot_of_overlap_subsingleton
      C.U x₀ C.basepoint C.off_diagonal_overlap_pi1_trivial)

/-- Inclusion-induced naturality on individual free-product words. -/
theorem threeArmCoverPi1FreeProduct_apply
    (x₀ : X) (C : ThreeArmCollarCover x₀)
    (w : CoverFreeProduct C.U x₀ C.basepoint) :
    threeArmCoverPi1FreeProduct x₀ C w =
      coverMap C.U x₀ C.basepoint w :=
  freeProductEquivFundamentalGroupOfRelationsTrivial_apply
    C.U x₀ C.open_member C.covers C.connected_member
    C.connected_pair C.connected_triple C.basepoint
    (relationSubgroup_eq_bot_of_overlap_subsingleton
      C.U x₀ C.basepoint C.off_diagonal_overlap_pi1_trivial)
    w

end DASHI.AlexanderHornedC3
