module DASHI.Physics.Closure.EllipticBootstrapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Closure.UltrametricAubinLionsCompactness as Compactness

------------------------------------------------------------------------
-- Elliptic bootstrap frontier for the NS limit.
--
-- This receipt records the standard PDE bootstrap path after compactness:
-- L^{4/3} control, pressure elliptic regularity, L^3, L^6, and smoothness.
-- Evans Chapter 6 is recorded as CitationAuthority.  The bootstrap is not
-- constructed here, because the carrier compactness and limit equation
-- passage remain open.

data EllipticBootstrapStep : Set where
  pressureEquationLFourThirdsStep :
    EllipticBootstrapStep

  ellipticRegularityToLThreeStep :
    EllipticBootstrapStep

  sobolevUpgradeToLSixStep :
    EllipticBootstrapStep

  parabolicSmoothBootstrapStep :
    EllipticBootstrapStep

canonicalEllipticBootstrapSteps :
  List EllipticBootstrapStep
canonicalEllipticBootstrapSteps =
  pressureEquationLFourThirdsStep
  ∷ ellipticRegularityToLThreeStep
  ∷ sobolevUpgradeToLSixStep
  ∷ parabolicSmoothBootstrapStep
  ∷ []

data EllipticBootstrapBlocker : Set where
  missingPrecompactCarrierLimit :
    EllipticBootstrapBlocker

  missingContinuumPressureEquationPassage :
    EllipticBootstrapBlocker

  missingCarrierToEuclideanEllipticRegularityTransfer :
    EllipticBootstrapBlocker

canonicalEllipticBootstrapBlockers :
  List EllipticBootstrapBlocker
canonicalEllipticBootstrapBlockers =
  missingPrecompactCarrierLimit
  ∷ missingContinuumPressureEquationPassage
  ∷ missingCarrierToEuclideanEllipticRegularityTransfer
  ∷ []

evansPDEAuthority :
  Authority.CitationAuthorityBoundary
evansPDEAuthority =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "Evans PDE Chapter 6 elliptic and parabolic regularity"
    "L. C. Evans, Partial Differential Equations, Chapter 6; used as external authority for the classical bootstrap pattern"
    true
    false
    false
    ( "CitationAuthority only"
      ∷ "Records classical elliptic/parabolic regularity, not a carrier proof"
      ∷ "No smooth continuum Navier-Stokes solution is promoted here"
      ∷ []
    )

evansPDENoArtifact :
  Authority.CitationAuthorityNoArtifact
evansPDENoArtifact =
  Authority.mkCitationAuthorityNoArtifact
    evansPDEAuthority
    refl
    refl
    refl

record EllipticBootstrapReceipt : Setω where
  field
    compactnessReceipt :
      Compactness.UltrametricAubinLionsCompactnessReceipt

    compactnessStillOpen :
      Compactness.carrierSpecializedCompactnessConstructed compactnessReceipt
      ≡
      false

    bootstrapSteps :
      List EllipticBootstrapStep

    bootstrapStepsAreCanonical :
      bootstrapSteps ≡ canonicalEllipticBootstrapSteps

    evansAuthorityBoundary :
      Authority.CitationAuthorityBoundary

    evansAuthorityNoArtifact :
      Authority.CitationAuthorityNoArtifact

    evansAuthorityAccepted :
      Authority.authorityAccepted evansAuthorityBoundary ≡ true

    bootstrapRouteRecorded :
      Bool

    bootstrapRouteRecordedIsTrue :
      bootstrapRouteRecorded ≡ true

    limitSmoothnessConstructed :
      Bool

    limitSmoothnessConstructedIsFalse :
      limitSmoothnessConstructed ≡ false

    continuumNSEquationPreserved :
      Bool

    continuumNSEquationPreservedIsFalse :
      continuumNSEquationPreserved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    blockers :
      List EllipticBootstrapBlocker

    blockersAreCanonical :
      blockers ≡ canonicalEllipticBootstrapBlockers

    receiptBoundary :
      List String

open EllipticBootstrapReceipt public

canonicalEllipticBootstrapReceipt :
  EllipticBootstrapReceipt
canonicalEllipticBootstrapReceipt =
  record
    { compactnessReceipt =
        Compactness.canonicalUltrametricAubinLionsCompactnessReceipt
    ; compactnessStillOpen =
        refl
    ; bootstrapSteps =
        canonicalEllipticBootstrapSteps
    ; bootstrapStepsAreCanonical =
        refl
    ; evansAuthorityBoundary =
        evansPDEAuthority
    ; evansAuthorityNoArtifact =
        evansPDENoArtifact
    ; evansAuthorityAccepted =
        refl
    ; bootstrapRouteRecorded =
        true
    ; bootstrapRouteRecordedIsTrue =
        refl
    ; limitSmoothnessConstructed =
        false
    ; limitSmoothnessConstructedIsFalse =
        refl
    ; continuumNSEquationPreserved =
        false
    ; continuumNSEquationPreservedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; blockers =
        canonicalEllipticBootstrapBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "Bootstrap route recorded: L^{4/3} pressure source, elliptic regularity to L^3, Sobolev upgrade to L^6, then smooth bootstrap"
        ∷ "Evans PDE Chapter 6 is recorded as CitationAuthority for the classical regularity pattern"
        ∷ "The carrier compactness and continuum equation-passage prerequisites are still false"
        ∷ "No Clay Navier-Stokes promotion is made"
        ∷ []
    }

ellipticBootstrapRouteRecorded :
  bootstrapRouteRecorded canonicalEllipticBootstrapReceipt ≡ true
ellipticBootstrapRouteRecorded =
  refl

ellipticBootstrapSmoothLimitStillFalse :
  limitSmoothnessConstructed canonicalEllipticBootstrapReceipt ≡ false
ellipticBootstrapSmoothLimitStillFalse =
  refl

ellipticBootstrapDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalEllipticBootstrapReceipt ≡ false
ellipticBootstrapDoesNotPromoteClay =
  refl

