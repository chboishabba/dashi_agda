module DASHI.Physics.Closure.RGBanachFixedPointReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Closure.RGOperatorNormReceipt as RGNorm

------------------------------------------------------------------------
-- Banach fixed-point receipt for the carrier RG route.
--
-- This receipt records the conditional theorem shape:
--   alpha1 < 1 and a proved RG contraction imply a unique fixed point H*.
-- The contraction proof, positive spectral gap proof, and Clay promotion
-- remain false.

data RGBanachInput : Set where
  completeSelfAdjointOperatorMetricSpace :
    RGBanachInput

  rgOperatorNormBoundAlphaOne :
    RGBanachInput

  alphaOneStrictlyBelowOne :
    RGBanachInput

canonicalRGBanachInputs :
  List RGBanachInput
canonicalRGBanachInputs =
  completeSelfAdjointOperatorMetricSpace
  ∷ rgOperatorNormBoundAlphaOne
  ∷ alphaOneStrictlyBelowOne
  ∷ []

data RGBanachTarget : Set where
  uniqueRGFixedPointHStar :
    RGBanachTarget

data RGBanachBlocker : Set where
  missingRGOperatorNormEquality :
    RGBanachBlocker

  missingCompleteOperatorSpaceProof :
    RGBanachBlocker

  missingPositiveSpectralGapAtFixedPoint :
    RGBanachBlocker

canonicalRGBanachBlockers :
  List RGBanachBlocker
canonicalRGBanachBlockers =
  missingRGOperatorNormEquality
  ∷ missingCompleteOperatorSpaceProof
  ∷ missingPositiveSpectralGapAtFixedPoint
  ∷ []

banachFixedPointAuthority :
  Authority.CitationAuthorityBoundary
banachFixedPointAuthority =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "Banach fixed-point theorem"
    "Standard contraction mapping theorem on a complete metric space; used only conditionally for the carrier RG map"
    true
    false
    false
    ( "CitationAuthority only"
      ∷ "The theorem is standard, but the carrier RG contraction hypothesis is not proved here"
      ∷ "No Yang-Mills mass-gap promotion follows from this receipt alone"
      ∷ []
    )

banachFixedPointNoArtifact :
  Authority.CitationAuthorityNoArtifact
banachFixedPointNoArtifact =
  Authority.mkCitationAuthorityNoArtifact
    banachFixedPointAuthority
    refl
    refl
    refl

spectralGapLowerBoundFormula : String
spectralGapLowerBoundFormula =
  "Conditional target: gap(H*) >= (1 - alpha1) * epsilon_min > 0, after the RG contraction and positive epsilon_min are proved."

record RGBanachFixedPointReceipt : Setω where
  field
    rgOperatorNormReceipt :
      RGNorm.RGOperatorNormReceipt

    operatorNormEqualityStillOpen :
      RGNorm.operatorNormEqualityProved rgOperatorNormReceipt ≡ false

    alphaOneLessThanOneRecorded :
      RGNorm.alphaOneLessThanOneRecorded rgOperatorNormReceipt ≡ true

    inputs :
      List RGBanachInput

    inputsAreCanonical :
      inputs ≡ canonicalRGBanachInputs

    target :
      RGBanachTarget

    targetIsCanonical :
      target ≡ uniqueRGFixedPointHStar

    banachAuthorityBoundary :
      Authority.CitationAuthorityBoundary

    banachAuthorityNoArtifact :
      Authority.CitationAuthorityNoArtifact

    banachAuthorityAccepted :
      Authority.authorityAccepted banachAuthorityBoundary ≡ true

    uniqueFixedPointConstructed :
      Bool

    uniqueFixedPointConstructedIsFalse :
      uniqueFixedPointConstructed ≡ false

    positiveSpectralGapAtFixedPointProved :
      Bool

    positiveSpectralGapAtFixedPointProvedIsFalse :
      positiveSpectralGapAtFixedPointProved ≡ false

    spectralGapFormulaRecorded :
      Bool

    spectralGapFormulaRecordedIsTrue :
      spectralGapFormulaRecorded ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    blockers :
      List RGBanachBlocker

    blockersAreCanonical :
      blockers ≡ canonicalRGBanachBlockers

    spectralGapFormula :
      String

    spectralGapFormulaIsCanonical :
      spectralGapFormula ≡ spectralGapLowerBoundFormula

    receiptBoundary :
      List String

open RGBanachFixedPointReceipt public

canonicalRGBanachFixedPointReceipt :
  RGBanachFixedPointReceipt
canonicalRGBanachFixedPointReceipt =
  record
    { rgOperatorNormReceipt =
        RGNorm.canonicalRGOperatorNormReceipt
    ; operatorNormEqualityStillOpen =
        refl
    ; alphaOneLessThanOneRecorded =
        refl
    ; inputs =
        canonicalRGBanachInputs
    ; inputsAreCanonical =
        refl
    ; target =
        uniqueRGFixedPointHStar
    ; targetIsCanonical =
        refl
    ; banachAuthorityBoundary =
        banachFixedPointAuthority
    ; banachAuthorityNoArtifact =
        banachFixedPointNoArtifact
    ; banachAuthorityAccepted =
        refl
    ; uniqueFixedPointConstructed =
        false
    ; uniqueFixedPointConstructedIsFalse =
        refl
    ; positiveSpectralGapAtFixedPointProved =
        false
    ; positiveSpectralGapAtFixedPointProvedIsFalse =
        refl
    ; spectralGapFormulaRecorded =
        true
    ; spectralGapFormulaRecordedIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; blockers =
        canonicalRGBanachBlockers
    ; blockersAreCanonical =
        refl
    ; spectralGapFormula =
        spectralGapLowerBoundFormula
    ; spectralGapFormulaIsCanonical =
        refl
    ; receiptBoundary =
        "Banach fixed-point theorem is recorded as CitationAuthority"
        ∷ "The fixed point H* is conditional on the still-missing carrier RG contraction proof"
        ∷ "The positive spectral-gap formula is recorded as a target, not a proof"
        ∷ "Clay Yang-Mills promotion remains false"
        ∷ []
    }

rgBanachFixedPointAuthorityAccepted :
  Authority.authorityAccepted
    (banachAuthorityBoundary canonicalRGBanachFixedPointReceipt)
  ≡
  true
rgBanachFixedPointAuthorityAccepted =
  refl

rgBanachFixedPointStillOpen :
  uniqueFixedPointConstructed canonicalRGBanachFixedPointReceipt ≡ false
rgBanachFixedPointStillOpen =
  refl

rgBanachFixedPointDoesNotPromoteClay :
  clayYangMillsPromoted canonicalRGBanachFixedPointReceipt ≡ false
rgBanachFixedPointDoesNotPromoteClay =
  refl

