module DASHI.Physics.Closure.UltrametricSobolevUniformBound where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt as ClayTarget
import DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt as NSTower

------------------------------------------------------------------------
-- Ultrametric Sobolev uniform-bound receipt.
--
-- This receipt records the p-adic/ultrametric Sobolev uniformity authority
-- needed by the carrier BKM route.  It is a depth-uniform bound receipt and
-- a BKM-control target, not a proof of continuum Navier-Stokes regularity.

data UltrametricSobolevAuthoritySource : Set where
  taiblesonFourierAnalysisLocalFields :
    UltrametricSobolevAuthoritySource

data CarrierUltrametricSobolevConstant : Set where
  depthIndependentCUM :
    CarrierUltrametricSobolevConstant

data CarrierEnstrophyControlWitness (depth : Nat) : Set where
  finiteDepthEnstrophyControlledByCUM :
    CarrierUltrametricSobolevConstant →
    CarrierEnstrophyControlWitness depth

data CarrierBKMVorticityControlTarget (depth : Nat) : Set where
  bkmVorticityControlTargetFromEnstrophy :
    CarrierEnstrophyControlWitness depth →
    CarrierBKMVorticityControlTarget depth

taiblesonSobolevCitation :
  Authority.CitationAuthorityBoundary
taiblesonSobolevCitation =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "Taibleson p-adic Fourier analysis / ultrametric Sobolev authority"
    "Taibleson, Fourier Analysis on Local Fields"
    true
    false
    false
    ( "CitationAuthority only: records the external p-adic harmonic-analysis source"
      ∷ "Carrier specialization is recorded as a typed target, not a full internal proof of p-adic Sobolev theory"
      ∷ "No machine-readable artifact authority is claimed"
      ∷ []
    )

taiblesonSobolevNoArtifact :
  Authority.CitationAuthorityNoArtifact
taiblesonSobolevNoArtifact =
  Authority.mkCitationAuthorityNoArtifact
    taiblesonSobolevCitation
    refl
    refl
    refl

bkmCriterionCitation :
  Authority.CitationAuthorityBoundary
bkmCriterionCitation =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "Beale-Kato-Majda continuation criterion"
    "Beale, Kato, and Majda, Remarks on the breakdown of smooth solutions for the 3-D Euler equations"
    true
    false
    false
    ( "CitationAuthority only: records the external BKM continuation theorem"
      ∷ "No continuum Navier-Stokes regularity proof is constructed by this receipt"
      ∷ []
    )

bkmCriterionNoArtifact :
  Authority.CitationAuthorityNoArtifact
bkmCriterionNoArtifact =
  Authority.mkCitationAuthorityNoArtifact
    bkmCriterionCitation
    refl
    refl
    refl

record UltrametricSobolevUniformBoundReceipt : Setω where
  field
    authoritySource :
      UltrametricSobolevAuthoritySource

    sobolevAuthority :
      Authority.CitationAuthorityBoundary

    sobolevAuthorityNoArtifact :
      Authority.CitationAuthorityNoArtifact

    bkmAuthority :
      Authority.CitationAuthorityBoundary

    bkmAuthorityNoArtifact :
      Authority.CitationAuthorityNoArtifact

    depthIndependentSobolevConstant :
      CarrierUltrametricSobolevConstant

    ultrametricSobolevUniformBounded :
      Bool

    ultrametricSobolevUniformBoundedIsTrue :
      ultrametricSobolevUniformBounded ≡ true

    sampleDepth :
      Nat

    finiteDepthEnstrophyControl :
      CarrierEnstrophyControlWitness sampleDepth

    carrierBKMControlTarget :
      CarrierBKMVorticityControlTarget sampleDepth

    existingNSTower :
      NSTower.NavierStokesRegularityTowerReceipt

    finiteDepthBKMAvailable :
      Bool

    finiteDepthBKMAvailableIsTrue :
      finiteDepthBKMAvailable ≡ true

    carrierSpecializationFullyFormalizedHere :
      Bool

    carrierSpecializationFullyFormalizedHereIsFalse :
      carrierSpecializationFullyFormalizedHere ≡ false

    continuumBKMRegularityPassageConstructedHere :
      Bool

    continuumBKMRegularityPassageConstructedHereIsFalse :
      continuumBKMRegularityPassageConstructedHere ≡ false

    clayNavierStokesPromotedHere :
      Bool

    clayNavierStokesPromotedHereIsFalse :
      clayNavierStokesPromotedHere ≡ false

    existingClayTarget :
      ClayTarget.CarrierBKMControlTargetReceipt

    existingClayTargetStillKeepsUniformBKMOpen :
      ClayTarget.uniformVorticityLInfinityControlConstructed existingClayTarget
      ≡
      false

    existingClayTargetStillKeepsContinuumBKMOpen :
      ClayTarget.continuumBKMRegularityPassageConstructed existingClayTarget
      ≡
      false

    receiptNotes :
      List String

open UltrametricSobolevUniformBoundReceipt public

canonicalUltrametricSobolevUniformBoundReceipt :
  UltrametricSobolevUniformBoundReceipt
canonicalUltrametricSobolevUniformBoundReceipt =
  record
    { authoritySource =
        taiblesonFourierAnalysisLocalFields
    ; sobolevAuthority =
        taiblesonSobolevCitation
    ; sobolevAuthorityNoArtifact =
        taiblesonSobolevNoArtifact
    ; bkmAuthority =
        bkmCriterionCitation
    ; bkmAuthorityNoArtifact =
        bkmCriterionNoArtifact
    ; depthIndependentSobolevConstant =
        depthIndependentCUM
    ; ultrametricSobolevUniformBounded =
        true
    ; ultrametricSobolevUniformBoundedIsTrue =
        refl
    ; sampleDepth =
        suc zero
    ; finiteDepthEnstrophyControl =
        finiteDepthEnstrophyControlledByCUM depthIndependentCUM
    ; carrierBKMControlTarget =
        bkmVorticityControlTargetFromEnstrophy
          (finiteDepthEnstrophyControlledByCUM depthIndependentCUM)
    ; existingNSTower =
        NSTower.canonicalNavierStokesRegularityTowerReceipt
    ; finiteDepthBKMAvailable =
        NSTower.finiteDepthContinuationConstructed
          (NSTower.finiteDepthBKMContinuationAtEveryDepth
            NSTower.canonicalNavierStokesRegularityTowerReceipt
            (suc zero)
            zero)
    ; finiteDepthBKMAvailableIsTrue =
        NSTower.finiteDepthBKMContinuationConstructedAtDepthZero
          NSTower.canonicalNavierStokesRegularityTowerReceipt
    ; carrierSpecializationFullyFormalizedHere =
        false
    ; carrierSpecializationFullyFormalizedHereIsFalse =
        refl
    ; continuumBKMRegularityPassageConstructedHere =
        false
    ; continuumBKMRegularityPassageConstructedHereIsFalse =
        refl
    ; clayNavierStokesPromotedHere =
        false
    ; clayNavierStokesPromotedHereIsFalse =
        refl
    ; existingClayTarget =
        ClayTarget.canonicalCarrierBKMControlTargetReceipt
    ; existingClayTargetStillKeepsUniformBKMOpen =
        refl
    ; existingClayTargetStillKeepsContinuumBKMOpen =
        refl
    ; receiptNotes =
        "Depth-independent ultrametric Sobolev constant is recorded under Taibleson CitationAuthority"
        ∷ "Finite-depth BKM/enstrophy control is connected to the existing Navier-Stokes tower"
        ∷ "Carrier-specialized p-adic Sobolev proof, continuum BKM passage, and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

canonicalUltrametricSobolevUniformBoundedTrue :
  ultrametricSobolevUniformBounded canonicalUltrametricSobolevUniformBoundReceipt
  ≡
  true
canonicalUltrametricSobolevUniformBoundedTrue =
  refl

ultrametricSobolevDoesNotPromoteContinuumBKM :
  continuumBKMRegularityPassageConstructedHere
    canonicalUltrametricSobolevUniformBoundReceipt
  ≡
  false
ultrametricSobolevDoesNotPromoteContinuumBKM =
  refl

ultrametricSobolevDoesNotPromoteClayNavierStokes :
  clayNavierStokesPromotedHere
    canonicalUltrametricSobolevUniformBoundReceipt
  ≡
  false
ultrametricSobolevDoesNotPromoteClayNavierStokes =
  refl
