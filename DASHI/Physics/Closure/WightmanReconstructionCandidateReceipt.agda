module DASHI.Physics.Closure.WightmanReconstructionCandidateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NormalisedH0OSPositivity as H0Norm

data OSAxiomStatus : Set where
  osTemperednessGrowthOpen : OSAxiomStatus
  osEuclideanCovarianceLatticeOnly : OSAxiomStatus
  osReflectionPositivityConditional : OSAxiomStatus
  osSymmetryConditionalOnStatisticsSector : OSAxiomStatus

canonicalOSAxiomStatuses :
  List OSAxiomStatus
canonicalOSAxiomStatuses =
  osTemperednessGrowthOpen
  ∷ osEuclideanCovarianceLatticeOnly
  ∷ osReflectionPositivityConditional
  ∷ osSymmetryConditionalOnStatisticsSector
  ∷ []

wightmanCandidateBoundaryStatement : String
wightmanCandidateBoundaryStatement =
  "OS reconstruction is only a candidate route: the carrier has lattice covariance, not full O(4), and reflection positivity is still conditional on the normalized H0 branch."

record WightmanReconstructionCandidateReceipt : Setω where
  field
    normalisedH0Receipt :
      H0Norm.NormalisedH0OSPositivityReceipt

    h0OSPositiveStillOpen :
      H0Norm.h0OSPositiveAfterNormalisation normalisedH0Receipt ≡ false

    osAxiomStatuses :
      List OSAxiomStatus

    osAxiomStatusesAreCanonical :
      osAxiomStatuses ≡ canonicalOSAxiomStatuses

    temperednessProved :
      Bool

    temperednessProvedIsFalse :
      temperednessProved ≡ false

    fullO4CovarianceProved :
      Bool

    fullO4CovarianceProvedIsFalse :
      fullO4CovarianceProved ≡ false

    reflectionPositivityProved :
      Bool

    reflectionPositivityProvedIsFalse :
      reflectionPositivityProved ≡ false

    boseFermiSymmetryProved :
      Bool

    boseFermiSymmetryProvedIsFalse :
      boseFermiSymmetryProved ≡ false

    wightmanOSAxiomStatusRecorded :
      Bool

    wightmanOSAxiomStatusRecordedIsTrue :
      wightmanOSAxiomStatusRecorded ≡ true

    wightmanReconstructionApplied :
      Bool

    wightmanReconstructionAppliedIsFalse :
      wightmanReconstructionApplied ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ wightmanCandidateBoundaryStatement

    receiptBoundary :
      List String

open WightmanReconstructionCandidateReceipt public

canonicalWightmanReconstructionCandidateReceipt :
  WightmanReconstructionCandidateReceipt
canonicalWightmanReconstructionCandidateReceipt =
  record
    { normalisedH0Receipt =
        H0Norm.canonicalNormalisedH0OSPositivityReceipt
    ; h0OSPositiveStillOpen =
        refl
    ; osAxiomStatuses =
        canonicalOSAxiomStatuses
    ; osAxiomStatusesAreCanonical =
        refl
    ; temperednessProved =
        false
    ; temperednessProvedIsFalse =
        refl
    ; fullO4CovarianceProved =
        false
    ; fullO4CovarianceProvedIsFalse =
        refl
    ; reflectionPositivityProved =
        false
    ; reflectionPositivityProvedIsFalse =
        refl
    ; boseFermiSymmetryProved =
        false
    ; boseFermiSymmetryProvedIsFalse =
        refl
    ; wightmanOSAxiomStatusRecorded =
        true
    ; wightmanOSAxiomStatusRecordedIsTrue =
        refl
    ; wightmanReconstructionApplied =
        false
    ; wightmanReconstructionAppliedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; boundaryStatement =
        wightmanCandidateBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; receiptBoundary =
        "The OS axiom status is now itemized for the carrier route"
        ∷ "Full O(4) covariance and reflection positivity are still open"
        ∷ "Wightman reconstruction and Clay Yang-Mills promotion remain false"
        ∷ []
    }

wightmanCandidateDoesNotPromoteClay :
  clayYangMillsPromoted canonicalWightmanReconstructionCandidateReceipt
  ≡
  false
wightmanCandidateDoesNotPromoteClay =
  refl
