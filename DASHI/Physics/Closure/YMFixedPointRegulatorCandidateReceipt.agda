module DASHI.Physics.Closure.YMFixedPointRegulatorCandidateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yang-Mills fixed-point regulator candidate receipt.
--
-- This records an alternative to refining the lattice: keep the three-site
-- spatial carrier geometry fixed, send the depth cutoff d to infinity, and
-- read the UV frequency cutoff alpha1^{-d} as tending to infinity.  The
-- route is NPRG / exact-RG / fixed-point-regulator style candidate
-- bookkeeping only; no Clay promotion is introduced.

data YMFixedPointRegulatorCandidateStatus : Set where
  fixedThreeSiteDepthCutoffRegulatorCandidate :
    YMFixedPointRegulatorCandidateStatus

data YMFixedPointRegulatorLimitComponent : Set where
  fixedThreeSiteSpatialCarrier :
    YMFixedPointRegulatorLimitComponent

  depthCutoffTendsToInfinity :
    YMFixedPointRegulatorLimitComponent

  uvFrequencyCutoffAlphaOnePowerMinusDepthTendsToInfinity :
    YMFixedPointRegulatorLimitComponent

  noSpatialLatticeRefinement :
    YMFixedPointRegulatorLimitComponent

  nprgExactRGFixedPointRegulatorCandidate :
    YMFixedPointRegulatorLimitComponent

canonicalYMFixedPointRegulatorLimitComponents :
  List YMFixedPointRegulatorLimitComponent
canonicalYMFixedPointRegulatorLimitComponents =
  fixedThreeSiteSpatialCarrier
  ∷ depthCutoffTendsToInfinity
  ∷ uvFrequencyCutoffAlphaOnePowerMinusDepthTendsToInfinity
  ∷ noSpatialLatticeRefinement
  ∷ nprgExactRGFixedPointRegulatorCandidate
  ∷ []

data YMFixedPointRegulatorOpenObligation : Set where
  missingExactRGFlowConstructionOnThreeSiteCarrier :
    YMFixedPointRegulatorOpenObligation

  missingFixedPointExistenceAndUniquenessProof :
    YMFixedPointRegulatorOpenObligation

  missingRegulatorRemovalContinuumMeasureProof :
    YMFixedPointRegulatorOpenObligation

  missingYangMillsMassGapTransfer :
    YMFixedPointRegulatorOpenObligation

canonicalYMFixedPointRegulatorOpenObligations :
  List YMFixedPointRegulatorOpenObligation
canonicalYMFixedPointRegulatorOpenObligations =
  missingExactRGFlowConstructionOnThreeSiteCarrier
  ∷ missingFixedPointExistenceAndUniquenessProof
  ∷ missingRegulatorRemovalContinuumMeasureProof
  ∷ missingYangMillsMassGapTransfer
  ∷ []

data YMFixedPointRegulatorPromotion : Set where

ymFixedPointRegulatorPromotionImpossibleHere :
  YMFixedPointRegulatorPromotion →
  ⊥
ymFixedPointRegulatorPromotionImpossibleHere ()

ymFixedPointRegulatorCandidateStatement : String
ymFixedPointRegulatorCandidateStatement =
  "Alternative YM route: fixed three-site spatial carrier, depth cutoff d -> infinity, UV frequency cutoff alpha1^{-d} -> infinity, NPRG/exact-RG fixed-point regulator candidate only; no Clay promotion."

record YMFixedPointRegulatorCandidateReceipt : Setω where
  field
    status :
      YMFixedPointRegulatorCandidateStatus

    statusIsCanonical :
      status ≡ fixedThreeSiteDepthCutoffRegulatorCandidate

    fixedPointRegulatorApproach :
      Bool

    fixedPointRegulatorApproachIsTrue :
      fixedPointRegulatorApproach ≡ true

    continuumLimitFromDepthNotFromRefinement :
      Bool

    continuumLimitFromDepthNotFromRefinementIsTrue :
      continuumLimitFromDepthNotFromRefinement ≡ true

    spatialGeometryFixed3Sites :
      Bool

    spatialGeometryFixed3SitesIsTrue :
      spatialGeometryFixed3Sites ≡ true

    uvCutoffFromDepth :
      Bool

    uvCutoffFromDepthIsTrue :
      uvCutoffFromDepth ≡ true

    ymFixedRegulatorRoute :
      Bool

    ymFixedRegulatorRouteIsTrue :
      ymFixedRegulatorRoute ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    limitComponents :
      List YMFixedPointRegulatorLimitComponent

    limitComponentsAreCanonical :
      limitComponents ≡ canonicalYMFixedPointRegulatorLimitComponents

    openObligations :
      List YMFixedPointRegulatorOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYMFixedPointRegulatorOpenObligations

    statement :
      String

    statementIsCanonical :
      statement ≡ ymFixedPointRegulatorCandidateStatement

    promotionFlags :
      List YMFixedPointRegulatorPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMFixedPointRegulatorCandidateReceipt public

canonicalYMFixedPointRegulatorCandidateReceipt :
  YMFixedPointRegulatorCandidateReceipt
canonicalYMFixedPointRegulatorCandidateReceipt =
  record
    { status =
        fixedThreeSiteDepthCutoffRegulatorCandidate
    ; statusIsCanonical =
        refl
    ; fixedPointRegulatorApproach =
        true
    ; fixedPointRegulatorApproachIsTrue =
        refl
    ; continuumLimitFromDepthNotFromRefinement =
        true
    ; continuumLimitFromDepthNotFromRefinementIsTrue =
        refl
    ; spatialGeometryFixed3Sites =
        true
    ; spatialGeometryFixed3SitesIsTrue =
        refl
    ; uvCutoffFromDepth =
        true
    ; uvCutoffFromDepthIsTrue =
        refl
    ; ymFixedRegulatorRoute =
        true
    ; ymFixedRegulatorRouteIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; limitComponents =
        canonicalYMFixedPointRegulatorLimitComponents
    ; limitComponentsAreCanonical =
        refl
    ; openObligations =
        canonicalYMFixedPointRegulatorOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; statement =
        ymFixedPointRegulatorCandidateStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "This receipt records an alternative to spatial lattice refinement"
        ∷ "The three-site spatial geometry remains fixed"
        ∷ "The continuum candidate is driven by depth cutoff d -> infinity and UV frequency cutoff alpha1^{-d} -> infinity"
        ∷ "The route is NPRG / exact-RG / fixed-point-regulator candidate bookkeeping"
        ∷ "No Clay Yang-Mills, terminal Clay, or mass-gap promotion is introduced"
        ∷ []
    }

ymFixedPointRegulatorApproachRecorded :
  fixedPointRegulatorApproach
    canonicalYMFixedPointRegulatorCandidateReceipt
  ≡ true
ymFixedPointRegulatorApproachRecorded =
  refl

ymFixedPointRegulatorContinuumLimitFromDepth :
  continuumLimitFromDepthNotFromRefinement
    canonicalYMFixedPointRegulatorCandidateReceipt
  ≡ true
ymFixedPointRegulatorContinuumLimitFromDepth =
  refl

ymFixedPointRegulatorCandidateKeepsClayFalse :
  clayYangMillsPromoted canonicalYMFixedPointRegulatorCandidateReceipt
  ≡ false
ymFixedPointRegulatorCandidateKeepsClayFalse =
  refl

ymFixedPointRegulatorCandidateKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYMFixedPointRegulatorCandidateReceipt
  ≡ false
ymFixedPointRegulatorCandidateKeepsTerminalFalse =
  refl
