{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.SingularBasinValidatedNumericsArtifactExact where

open import Agda.Primitive using (Setω)
open import DASHI.Core.Prelude
import DASHI.Physics.Dynamics.BasinResolutionRobustnessExact as BRR
import DASHI.Physics.Dynamics.ScaledBracketResolutionBridgeExact as SBRB
import DASHI.Physics.Dynamics.YanchukSelectedCrossSectionBracketExact as YB

------------------------------------------------------------------------
-- Validated-numerics promotion boundary for the selected singular-funnel
-- cross-section.
--
-- This mirrors the repository's Maass validated-numerics pattern:
-- frozen bytes and digests are not themselves a theorem.  Promotion occurs
-- only through checkerSound, which must turn accepted payload bytes into the
-- exact endpoint basin proposition consumed by the resolution theorem layer.
------------------------------------------------------------------------

record SelectedEndpointBasinCertificate : Set₁ where
  field
    EndpointPredicate : SBRB.BracketEndpoint → Set
    oppositeEndpoints :
      SBRB.OppositeEndpointPredicateReceipt EndpointPredicate

open SelectedEndpointBasinCertificate public

record SingularBasinValidatedNumericsArtifact
  (Bytes Digest Payload : Set) : Setω where
  field
    sourceCommit : Digest
    cleanWorktreeWitness : Set
    runnerDigest : Digest
    inputDigest : Digest
    outputDigest : Digest
    frozenBytes : Bytes

    selectedBracket :
      YB.AdjacentScaledBracket
    selectedBracketIsCanonical :
      selectedBracket ≡ YB.selectedBracket

    precisionBits : Nat
    intervalPayload : Payload
    parser : Bytes → Payload
    parserAcceptedFrozenOutput :
      parser frozenBytes ≡ intervalPayload

    checker : Payload → Bool
    checkerPassed :
      checker intervalPayload ≡ true

    checkerSound :
      checker intervalPayload ≡ true →
      SelectedEndpointBasinCertificate

open SingularBasinValidatedNumericsArtifact public

validated-endpoint-certificate :
  ∀ {Bytes Digest Payload : Set} →
  (artifact :
    SingularBasinValidatedNumericsArtifact
      Bytes Digest Payload) →
  SelectedEndpointBasinCertificate
validated-endpoint-certificate artifact =
  checkerSound artifact
    (checkerPassed artifact)

validated-selected-boundary-witness :
  ∀ {Bytes Digest Payload : Set} →
  (artifact :
    SingularBasinValidatedNumericsArtifact
      Bytes Digest Payload) →
  BRR.BasinBoundaryResolutionWitness
    SBRB.endpointResolutionGeometry
    (EndpointPredicate
      (validated-endpoint-certificate artifact))
    SBRB.oneGridUnit
validated-selected-boundary-witness artifact =
  SBRB.opposite-adjacent-endpoints-give-boundary-witness
    (oppositeEndpoints
      (validated-endpoint-certificate artifact))

validated-selected-endpoint-not-one-grid-robust :
  ∀ {Bytes Digest Payload : Set} →
  (artifact :
    SingularBasinValidatedNumericsArtifact
      Bytes Digest Payload) →
  ¬ BRR.RobustAt
      SBRB.endpointResolutionGeometry
      (EndpointPredicate
        (validated-endpoint-certificate artifact))
      SBRB.oneGridUnit
      SBRB.lowerEndpoint
validated-selected-endpoint-not-one-grid-robust artifact =
  SBRB.opposite-adjacent-endpoints-refute-one-grid-robustness
    (oppositeEndpoints
      (validated-endpoint-certificate artifact))

------------------------------------------------------------------------
-- Current state boundary.
--
-- The existing RK4 script is a numerical diagnostic and exact bracket
-- generator.  It does not yet instantiate SingularBasinValidatedNumericsArtifact
-- because no interval ODE checker + checkerSound theorem has been supplied.
------------------------------------------------------------------------

record SingularBasinValidationStatus : Set where
  constructor singularBasinValidationStatus
  field
    exactBracketOwned : Bool
    exactBracketOwnedIsTrue :
      exactBracketOwned ≡ true
    rk4SelectedEndpointReceiptPresent : Bool
    rk4SelectedEndpointReceiptPresentIsTrue :
      rk4SelectedEndpointReceiptPresent ≡ true
    intervalODECheckerPresent : Bool
    intervalODECheckerPresentIsFalse :
      intervalODECheckerPresent ≡ false
    checkerSoundToBasinCertificatePresent : Bool
    checkerSoundToBasinCertificatePresentIsFalse :
      checkerSoundToBasinCertificatePresent ≡ false
    analyticGlobalWidthLawPresent : Bool
    analyticGlobalWidthLawPresentIsFalse :
      analyticGlobalWidthLawPresent ≡ false

canonicalSingularBasinValidationStatus :
  SingularBasinValidationStatus
canonicalSingularBasinValidationStatus =
  singularBasinValidationStatus
    true refl
    true refl
    false refl
    false refl
    false refl
