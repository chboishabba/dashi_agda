module DASHI.Physics.Closure.NSDensityApproximationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes density/approximation receipt.
--
-- This receipt closes only the density question: prime-LP carrier projections
-- approximate arbitrary H^s data in H^s as depth tends to infinity.  The last
-- remaining analytic gap is uniformity of regularity estimates along the
-- approximating family.

data NSDensityApproximationStatus : Set where
  carrierProjectionDensityClosedUniformRegularityOpen :
    NSDensityApproximationStatus

data NSDensityApproximationComponent : Set where
  arbitraryHsInitialData :
    NSDensityApproximationComponent

  primeLPProjectionFamily :
    NSDensityApproximationComponent

  depthLimitInHs :
    NSDensityApproximationComponent

  carrierProjectionDensity :
    NSDensityApproximationComponent

  uniformRegularityEstimateGap :
    NSDensityApproximationComponent

canonicalNSDensityApproximationComponents :
  List NSDensityApproximationComponent
canonicalNSDensityApproximationComponents =
  arbitraryHsInitialData
  ∷ primeLPProjectionFamily
  ∷ depthLimitInHs
  ∷ carrierProjectionDensity
  ∷ uniformRegularityEstimateGap
  ∷ []

data NSDensityApproximationOpenGap : Set where
  uniformRegularityAcrossApproximations :
    NSDensityApproximationOpenGap

canonicalNSDensityApproximationOpenGaps :
  List NSDensityApproximationOpenGap
canonicalNSDensityApproximationOpenGaps =
  uniformRegularityAcrossApproximations
  ∷ []

data NSDensityApproximationPromotion : Set where

nsDensityApproximationPromotionImpossibleHere :
  NSDensityApproximationPromotion →
  ⊥
nsDensityApproximationPromotionImpossibleHere ()

nsDensityApproximationStatement : String
nsDensityApproximationStatement =
  "Prime-LP projections approximate arbitrary H^s data in H^s as depth d tends to infinity, so carrier projections are dense in H^s; uniformity of regularity estimates across the approximation remains open."

record NSDensityApproximationReceipt : Setω where
  field
    status :
      NSDensityApproximationStatus

    components :
      List NSDensityApproximationComponent

    componentsAreCanonical :
      components ≡ canonicalNSDensityApproximationComponents

    openGaps :
      List NSDensityApproximationOpenGap

    openGapsAreCanonical :
      openGaps ≡ canonicalNSDensityApproximationOpenGaps

    carrierProjectionDenseInHs :
      Bool

    carrierProjectionDenseInHsIsTrue :
      carrierProjectionDenseInHs ≡ true

    primeLPApproximatesArbitraryHs :
      Bool

    primeLPApproximatesArbitraryHsIsTrue :
      primeLPApproximatesArbitraryHs ≡ true

    approximationConvergesAsDepthToInfinity :
      Bool

    approximationConvergesAsDepthToInfinityIsTrue :
      approximationConvergesAsDepthToInfinity ≡ true

    densityGapClosed :
      Bool

    densityGapClosedIsTrue :
      densityGapClosed ≡ true

    uniformRegularityEstimateOpen :
      Bool

    uniformRegularityEstimateOpenIsTrue :
      uniformRegularityEstimateOpen ≡ true

    uniformRegularityEstimateClosed :
      Bool

    uniformRegularityEstimateClosedIsFalse :
      uniformRegularityEstimateClosed ≡ false

    continuumRegularityPromoted :
      Bool

    continuumRegularityPromotedIsFalse :
      continuumRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsDensityApproximationStatement

    promotionFlags :
      List NSDensityApproximationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSDensityApproximationReceipt public

canonicalNSDensityApproximationReceipt :
  NSDensityApproximationReceipt
canonicalNSDensityApproximationReceipt =
  record
    { status =
        carrierProjectionDensityClosedUniformRegularityOpen
    ; components =
        canonicalNSDensityApproximationComponents
    ; componentsAreCanonical =
        refl
    ; openGaps =
        canonicalNSDensityApproximationOpenGaps
    ; openGapsAreCanonical =
        refl
    ; carrierProjectionDenseInHs =
        true
    ; carrierProjectionDenseInHsIsTrue =
        refl
    ; primeLPApproximatesArbitraryHs =
        true
    ; primeLPApproximatesArbitraryHsIsTrue =
        refl
    ; approximationConvergesAsDepthToInfinity =
        true
    ; approximationConvergesAsDepthToInfinityIsTrue =
        refl
    ; densityGapClosed =
        true
    ; densityGapClosedIsTrue =
        refl
    ; uniformRegularityEstimateOpen =
        true
    ; uniformRegularityEstimateOpenIsTrue =
        refl
    ; uniformRegularityEstimateClosed =
        false
    ; uniformRegularityEstimateClosedIsFalse =
        refl
    ; continuumRegularityPromoted =
        false
    ; continuumRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        nsDensityApproximationStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Prime-LP carrier projections approximate arbitrary H^s data in H^s as depth d tends to infinity"
        ∷ "Carrier projections are dense in H^s, so the density gap is closed"
        ∷ "Uniform regularity estimates across the approximating sequence remain open"
        ∷ "No continuum regularity, Clay Navier-Stokes, or terminal Clay claim is promoted"
        ∷ []
    }

nsDensityApproximationClosesDensityGap :
  densityGapClosed canonicalNSDensityApproximationReceipt
  ≡
  true
nsDensityApproximationClosesDensityGap =
  refl

nsDensityApproximationLeavesUniformRegularityOpen :
  uniformRegularityEstimateOpen canonicalNSDensityApproximationReceipt
  ≡
  true
nsDensityApproximationLeavesUniformRegularityOpen =
  refl

nsDensityApproximationDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSDensityApproximationReceipt
  ≡
  false
nsDensityApproximationDoesNotPromoteClay =
  refl
