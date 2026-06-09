module DASHI.Physics.Closure.NSDynamicVortexStructureReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSLeraySobolevSharpnessReceipt as Sharp

------------------------------------------------------------------------
-- Sprint 15 NS dynamic-vortex structure receipt.
--
-- Sprint 10 killed the static Leray/Sobolev route.  This receipt records
-- the good-route algebra that remains: vorticity energy isolates stretching,
-- strain is the stretching part, exact Beltrami alignment is nonlinear-null
-- after Leray projection, and adjacent-only transfer is absorbable only when
-- the angle defect supplies the missing half derivative.  The dynamic
-- production of that depletion remains open.

data NSDynamicVortexStatus : Set where
  nsDynamicVortexStructureRecorded_noPromotion :
    NSDynamicVortexStatus

data NSDynamicSolvedAlgebra : Set where
  vorticityEnergyIdentityIsolatesStretching :
    NSDynamicSolvedAlgebra

  strainOnlyStretchesVorticity :
    NSDynamicSolvedAlgebra

  exactBeltramiProjectedNonlinearityVanishes :
    NSDynamicSolvedAlgebra

  approximateBeltramiGivesAngleDefect :
    NSDynamicSolvedAlgebra

  adjacentOnlyTransferConditionallyAbsorbs :
    NSDynamicSolvedAlgebra

  pressureIsProjectionGaugeNotDirectDissipation :
    NSDynamicSolvedAlgebra

  h118FallbackDoesNotCloseClay :
    NSDynamicSolvedAlgebra

canonicalNSDynamicSolvedAlgebra :
  List NSDynamicSolvedAlgebra
canonicalNSDynamicSolvedAlgebra =
  vorticityEnergyIdentityIsolatesStretching
  ∷ strainOnlyStretchesVorticity
  ∷ exactBeltramiProjectedNonlinearityVanishes
  ∷ approximateBeltramiGivesAngleDefect
  ∷ adjacentOnlyTransferConditionallyAbsorbs
  ∷ pressureIsProjectionGaugeNotDirectDissipation
  ∷ h118FallbackDoesNotCloseClay
  ∷ []

data NSDynamicOpenLemma : Set where
  openDynamicHalfDerivativeDepletion :
    NSDynamicOpenLemma

  openActualFlowBeltramiProduction :
    NSDynamicOpenLemma

  openPressureInducedStrainVorticityMisalignment :
    NSDynamicOpenLemma

  openCoherentCascadeDepletionAlongFlow :
    NSDynamicOpenLemma

  openSubcriticalVortexStretchingAlongFlow :
    NSDynamicOpenLemma

canonicalNSDynamicOpenLemmas :
  List NSDynamicOpenLemma
canonicalNSDynamicOpenLemmas =
  openDynamicHalfDerivativeDepletion
  ∷ openActualFlowBeltramiProduction
  ∷ openPressureInducedStrainVorticityMisalignment
  ∷ openCoherentCascadeDepletionAlongFlow
  ∷ openSubcriticalVortexStretchingAlongFlow
  ∷ []

data NSDynamicNonClaim : Set where
  beltramiIdentityIsNotDynamicProduction :
    NSDynamicNonClaim

  adjacentOnlyTransferAloneIsNotEnough :
    NSDynamicNonClaim

  pressureDoesNotDirectlyDissipateEnstrophy :
    NSDynamicNonClaim

  h118CarrierControlAloneIsNotClay :
    NSDynamicNonClaim

  noClayPromotion :
    NSDynamicNonClaim

canonicalNSDynamicNonClaims :
  List NSDynamicNonClaim
canonicalNSDynamicNonClaims =
  beltramiIdentityIsNotDynamicProduction
  ∷ adjacentOnlyTransferAloneIsNotEnough
  ∷ pressureDoesNotDirectlyDissipateEnstrophy
  ∷ h118CarrierControlAloneIsNotClay
  ∷ noClayPromotion
  ∷ []

data NSDynamicPromotion : Set where

nsDynamicPromotionImpossibleHere :
  NSDynamicPromotion →
  ⊥
nsDynamicPromotionImpossibleHere ()

missingHalfDerivativeNumerator : Nat
missingHalfDerivativeNumerator =
  1

missingHalfDerivativeDenominator : Nat
missingHalfDerivativeDenominator =
  2

h118FallbackEnstrophyPower : Nat
h118FallbackEnstrophyPower =
  5

angleDefectSmallnessCanonicalStatement : String
angleDefectSmallnessCanonicalStatement =
  "sup_K angleDefect_K(t) * 2^(K/2) <= epsilon * nu / C"

workerCount : Nat
workerCount =
  6

nsDynamicSummary : String
nsDynamicSummary =
  "Sprint 15 NS: solved algebra records vorticity energy, strain-only stretching, Beltrami projection cancellation, angle-defect depletion, conditional adjacent-only absorption, pressure gauge/no-direct-dissipation, and H118 fallback non-closure. Clay requires DynamicHalfDerivativeDepletion along actual NS trajectories."

nsDynamicBoundary : String
nsDynamicBoundary =
  "This receipt records algebraic and conditional depletion surfaces only. It does not prove dynamic half-derivative depletion, vortex alignment along actual flows, pressure-induced strain/vorticity misalignment, subcritical absorption along the flow, pointwise enstrophy control, no blowup, global smoothness, uniqueness, or Clay Navier-Stokes."

record NSDynamicVortexStructureReceipt : Setω where
  field
    status :
      NSDynamicVortexStatus

    statusIsCanonical :
      status ≡ nsDynamicVortexStructureRecorded_noPromotion

    sharpnessReceipt :
      Sharp.NSLeraySobolevSharpnessReceipt

    leraySobolevStaticRouteKilled :
      Sharp.subcriticalAbsorptionImpossibleFromLerayOnlyProved
        sharpnessReceipt
        ≡ true

    previousClayStillFalse :
      Sharp.clayNavierStokesPromoted sharpnessReceipt ≡ false

    solvedAlgebra :
      List NSDynamicSolvedAlgebra

    solvedAlgebraIsCanonical :
      solvedAlgebra ≡ canonicalNSDynamicSolvedAlgebra

    openLemmas :
      List NSDynamicOpenLemma

    openLemmasAreCanonical :
      openLemmas ≡ canonicalNSDynamicOpenLemmas

    nonClaims :
      List NSDynamicNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalNSDynamicNonClaims

    vorticityEnergyIdentitySolved :
      Bool

    vorticityEnergyIdentitySolvedIsTrue :
      vorticityEnergyIdentitySolved ≡ true

    onlyStrainStretchesVorticity :
      Bool

    onlyStrainStretchesVorticityIsTrue :
      onlyStrainStretchesVorticity ≡ true

    exactBeltramiProjectionCancellation :
      Bool

    exactBeltramiProjectionCancellationIsTrue :
      exactBeltramiProjectionCancellation ≡ true

    approximateBeltramiAngleDefect :
      Bool

    approximateBeltramiAngleDefectIsTrue :
      approximateBeltramiAngleDefect ≡ true

    adjacentOnlyConditionalAbsorption :
      Bool

    adjacentOnlyConditionalAbsorptionIsTrue :
      adjacentOnlyConditionalAbsorption ≡ true

    pressureDirectDissipationKilled :
      Bool

    pressureDirectDissipationKilledIsTrue :
      pressureDirectDissipationKilled ≡ true

    h118FallbackNonClosing :
      Bool

    h118FallbackNonClosingIsTrue :
      h118FallbackNonClosing ≡ true

    missingHalfDerivativeNumeratorRecorded :
      Nat

    missingHalfDerivativeNumeratorIs1 :
      missingHalfDerivativeNumeratorRecorded
        ≡ missingHalfDerivativeNumerator

    missingHalfDerivativeDenominatorRecorded :
      Nat

    missingHalfDerivativeDenominatorIs2 :
      missingHalfDerivativeDenominatorRecorded
        ≡ missingHalfDerivativeDenominator

    h118FallbackEnstrophyPowerRecorded :
      Nat

    h118FallbackEnstrophyPowerIs5 :
      h118FallbackEnstrophyPowerRecorded
        ≡ h118FallbackEnstrophyPower

    angleDefectSupHalfDerivativeSmallness :
      Set

    angleDefectSupHalfDerivativeSmallnessProved :
      Bool

    angleDefectSupHalfDerivativeSmallnessProvedIsFalse :
      angleDefectSupHalfDerivativeSmallnessProved ≡ false

    angleDefectSmallnessStatement :
      String

    angleDefectSmallnessStatementIsCanonical :
      angleDefectSmallnessStatement
        ≡ angleDefectSmallnessCanonicalStatement

    angleDefectSupOverKRecorded :
      Bool

    angleDefectSupOverKRecordedIsTrue :
      angleDefectSupOverKRecorded ≡ true

    halfDerivativeWeightRecorded :
      Bool

    halfDerivativeWeightRecordedIsTrue :
      halfDerivativeWeightRecorded ≡ true

    viscosityScaledThresholdRecorded :
      Bool

    viscosityScaledThresholdRecordedIsTrue :
      viscosityScaledThresholdRecorded ≡ true

    dynamicHalfDerivativeDepletion :
      Set

    dynamicHalfDerivativeDepletionProved :
      Bool

    dynamicHalfDerivativeDepletionProvedIsFalse :
      dynamicHalfDerivativeDepletionProved ≡ false

    subcriticalVortexStretchingAlongFlow :
      Set

    subcriticalVortexStretchingAlongFlowProved :
      Bool

    subcriticalVortexStretchingAlongFlowProvedIsFalse :
      subcriticalVortexStretchingAlongFlowProved ≡ false

    pressureInducedStrainVorticityMisalignment :
      Set

    pressureInducedStrainVorticityMisalignmentProved :
      Bool

    pressureInducedStrainVorticityMisalignmentProvedIsFalse :
      pressureInducedStrainVorticityMisalignmentProved ≡ false

    pointwiseEnstrophyControl :
      Set

    pointwiseEnstrophyControlProved :
      Bool

    pointwiseEnstrophyControlProvedIsFalse :
      pointwiseEnstrophyControlProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSDynamicPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSDynamicPromotion →
      ⊥

    summary :
      String

    summaryIsCanonical :
      summary ≡ nsDynamicSummary

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ nsDynamicBoundary

open NSDynamicVortexStructureReceipt public

canonicalNSDynamicVortexStructureReceipt :
  NSDynamicVortexStructureReceipt
canonicalNSDynamicVortexStructureReceipt =
  record
    { status =
        nsDynamicVortexStructureRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; sharpnessReceipt =
        Sharp.canonicalNSLeraySobolevSharpnessReceipt
    ; leraySobolevStaticRouteKilled =
        refl
    ; previousClayStillFalse =
        refl
    ; solvedAlgebra =
        canonicalNSDynamicSolvedAlgebra
    ; solvedAlgebraIsCanonical =
        refl
    ; openLemmas =
        canonicalNSDynamicOpenLemmas
    ; openLemmasAreCanonical =
        refl
    ; nonClaims =
        canonicalNSDynamicNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; vorticityEnergyIdentitySolved =
        true
    ; vorticityEnergyIdentitySolvedIsTrue =
        refl
    ; onlyStrainStretchesVorticity =
        true
    ; onlyStrainStretchesVorticityIsTrue =
        refl
    ; exactBeltramiProjectionCancellation =
        true
    ; exactBeltramiProjectionCancellationIsTrue =
        refl
    ; approximateBeltramiAngleDefect =
        true
    ; approximateBeltramiAngleDefectIsTrue =
        refl
    ; adjacentOnlyConditionalAbsorption =
        true
    ; adjacentOnlyConditionalAbsorptionIsTrue =
        refl
    ; pressureDirectDissipationKilled =
        true
    ; pressureDirectDissipationKilledIsTrue =
        refl
    ; h118FallbackNonClosing =
        true
    ; h118FallbackNonClosingIsTrue =
        refl
    ; missingHalfDerivativeNumeratorRecorded =
        missingHalfDerivativeNumerator
    ; missingHalfDerivativeNumeratorIs1 =
        refl
    ; missingHalfDerivativeDenominatorRecorded =
        missingHalfDerivativeDenominator
    ; missingHalfDerivativeDenominatorIs2 =
        refl
    ; h118FallbackEnstrophyPowerRecorded =
        h118FallbackEnstrophyPower
    ; h118FallbackEnstrophyPowerIs5 =
        refl
    ; angleDefectSupHalfDerivativeSmallness =
        ⊥
    ; angleDefectSupHalfDerivativeSmallnessProved =
        false
    ; angleDefectSupHalfDerivativeSmallnessProvedIsFalse =
        refl
    ; angleDefectSmallnessStatement =
        angleDefectSmallnessCanonicalStatement
    ; angleDefectSmallnessStatementIsCanonical =
        refl
    ; angleDefectSupOverKRecorded =
        true
    ; angleDefectSupOverKRecordedIsTrue =
        refl
    ; halfDerivativeWeightRecorded =
        true
    ; halfDerivativeWeightRecordedIsTrue =
        refl
    ; viscosityScaledThresholdRecorded =
        true
    ; viscosityScaledThresholdRecordedIsTrue =
        refl
    ; dynamicHalfDerivativeDepletion =
        ⊥
    ; dynamicHalfDerivativeDepletionProved =
        false
    ; dynamicHalfDerivativeDepletionProvedIsFalse =
        refl
    ; subcriticalVortexStretchingAlongFlow =
        ⊥
    ; subcriticalVortexStretchingAlongFlowProved =
        false
    ; subcriticalVortexStretchingAlongFlowProvedIsFalse =
        refl
    ; pressureInducedStrainVorticityMisalignment =
        ⊥
    ; pressureInducedStrainVorticityMisalignmentProved =
        false
    ; pressureInducedStrainVorticityMisalignmentProvedIsFalse =
        refl
    ; pointwiseEnstrophyControl =
        ⊥
    ; pointwiseEnstrophyControlProved =
        false
    ; pointwiseEnstrophyControlProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsDynamicPromotionImpossibleHere
    ; summary =
        nsDynamicSummary
    ; summaryIsCanonical =
        refl
    ; boundary =
        nsDynamicBoundary
    ; boundaryIsCanonical =
        refl
    }

nsDynamicVortexStructureKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSDynamicVortexStructureReceipt
    ≡ false
nsDynamicVortexStructureKeepsClayFalse =
  refl
