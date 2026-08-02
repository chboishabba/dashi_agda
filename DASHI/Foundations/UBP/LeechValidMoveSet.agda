module DASHI.Foundations.UBP.LeechValidMoveSet where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.ExternalRepositoryProvenance as Provenance

------------------------------------------------------------------------
-- Lattice-valid dynamics boundary.
--
-- Ambient one-coordinate probes are not silently treated as Leech moves.
-- A move must carry membership and closure receipts on the chosen lattice
-- presentation. Paths form a compositional transition surface, allowing an
-- endpoint TAX observable and a genuinely path-sensitive observer to coexist.
------------------------------------------------------------------------

record AdditiveLattice : Set₁ where
  field
    Point : Set
    zero : Point
    add : Point → Point → Point
    addIdentityLeft : (x : Point) → add zero x ≡ x
    addIdentityRight : (x : Point) → add x zero ≡ x
    addAssociative :
      (x y z : Point) → add (add x y) z ≡ add x (add y z)

open AdditiveLattice public

record CertifiedMove (lattice : AdditiveLattice) : Set where
  constructor certifiedMove
  field
    displacement : Point lattice
    membershipWitness : Set
    displacementIsLatticePoint : membershipWitness
    moveLabel : String

open CertifiedMove public

applyMove :
  (lattice : AdditiveLattice) →
  CertifiedMove lattice →
  Point lattice →
  Point lattice
applyMove lattice move point = add lattice point (displacement move)

record MoveClosureReceipt
    (lattice : AdditiveLattice)
    (move : CertifiedMove lattice) : Set₁ where
  field
    closureWitness :
      (point : Point lattice) →
      Set
    closureProof :
      (point : Point lattice) →
      closureWitness point

open MoveClosureReceipt public

data Path (lattice : AdditiveLattice) :
  Point lattice → Point lattice → Set where
  identityPath :
    (point : Point lattice) →
    Path lattice point point
  movePath :
    (start : Point lattice) →
    (move : CertifiedMove lattice) →
    Path lattice start (applyMove lattice move start)
  composePath :
    ∀ {start middle finish} →
    Path lattice start middle →
    Path lattice middle finish →
    Path lattice start finish

record EndpointAndPathObservation
    (lattice : AdditiveLattice)
    (Value Observation : Set) : Set₁ where
  field
    endpointValue : Point lattice → Value
    pathObservation :
      ∀ {start finish} →
      Path lattice start finish →
      Observation
    identityObservation :
      (point : Point lattice) →
      Set
    compositionLaw :
      ∀ {start middle finish}
        (left : Path lattice start middle)
        (right : Path lattice middle finish) →
      Set
    pathCanDistinguishEqualEndpoints : Set

open EndpointAndPathObservation public

record BinaryShadowMoveBridge
    (lattice : AdditiveLattice)
    (BinaryWord GolayWord : Set) : Set₁ where
  field
    isGolayWord : BinaryWord → Set
    embedGolayShadowMove : GolayWord → CertifiedMove lattice
    binaryXor : BinaryWord → BinaryWord → BinaryWord
    shadowOfPoint : Point lattice → BinaryWord
    golayWordAsBinary : GolayWord → BinaryWord
    shadowTransportLaw :
      (point : Point lattice) →
      (move : GolayWord) →
      shadowOfPoint (applyMove lattice (embedGolayShadowMove move) point)
      ≡ binaryXor (shadowOfPoint point) (golayWordAsBinary move)
    latticeMembershipPreserved :
      (point : Point lattice) →
      (move : GolayWord) →
      Set

open BinaryShadowMoveBridge public

record LeechMoveStatus : Set where
  constructor leechMoveStatus
  field
    repositoryURL : String
    repositoryAuthor : String
    ambientSingleCoordinateFlipAcceptedAsLeechMove : Bool
    ambientSingleCoordinateFlipAcceptedAsLeechMoveIsFalse :
      ambientSingleCoordinateFlipAcceptedAsLeechMove ≡ false
    certifiedLatticeMoveRequired : Bool
    certifiedLatticeMoveRequiredIsTrue : certifiedLatticeMoveRequired ≡ true
    pathCompositionAvailable : Bool
    pathCompositionAvailableIsTrue : pathCompositionAvailable ≡ true
    constructionAShadowBridgeProvedHere : Bool
    constructionAShadowBridgeProvedHereIsFalse :
      constructionAShadowBridgeProvedHere ≡ false
    minimalVectorGraphImportedHere : Bool
    minimalVectorGraphImportedHereIsFalse :
      minimalVectorGraphImportedHere ≡ false
    reading : String

canonicalLeechMoveStatus : LeechMoveStatus
canonicalLeechMoveStatus =
  leechMoveStatus
    Provenance.ubpRepositoryURL
    Provenance.ubpAuthorName
    false refl
    true refl
    true refl
    false refl
    false refl
    "valid dynamics requires certified lattice displacements; binary-shadow XOR and minimal-vector adjacency remain explicit bridge obligations"

leechValidMoveGenericReceipt : GenericReceipt.GenericReceipt
leechValidMoveGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Leech-valid move and path boundary"
    "DASHI.Foundations.UBP.LeechValidMoveSet"
    "canonicalLeechMoveStatus"
    "certified additive-lattice moves, closure receipts, compositional paths, endpoint/path observations, and a Golay-shadow bridge interface are attached"
    "no ambient bit flip, Construction-A displacement, minimal-vector adjacency, Lyapunov theorem, or physical dynamics claim is promoted without a certificate"
    "agda -i . DASHI/Foundations/UBP/LeechValidMoveSet.agda"

leechValidMoveGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim leechValidMoveGenericReceipt ≡ false
leechValidMoveGenericReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse leechValidMoveGenericReceipt
