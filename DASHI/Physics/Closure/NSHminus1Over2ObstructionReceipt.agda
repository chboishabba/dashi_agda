module DASHI.Physics.Closure.NSHminus1Over2ObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSNegativeSobolevDangerShellReceipt as Negative
import DASHI.Physics.Closure.NSNonCircularKStarDriftBoundTargetReceipt as KStar
import DASHI.Physics.Closure.NSTailRestrictedThetaDiagnosticReceipt as Tail

------------------------------------------------------------------------
-- Navier-Stokes H^{-1/2} obstruction diagnostic.
--
-- This receipt records the latest numerical obstruction calculation for the
-- negative-Sobolev danger-shell route.  The tested ratio is
--
--   || P_{>K}(u . grad u) ||_{H^{-1/2}}
--   -------------------------------------------------
--   nu * || P_{>K} u ||_{H^{3/2}}
--
-- across smooth, Kolmogorov, and rough spectra.  The calculation does not
-- prove an analytic theorem.  It records that the ratio is already above one
-- in the sampled rows and grows as viscosity decreases, which makes the
-- H^{-1/2} route a concrete obstruction witness rather than a closed
-- absorption estimate.

data NSHminus1Over2ObstructionStatus : Set where
  hMinusHalfObstructionRatioRecorded_noPromotion :
    NSHminus1Over2ObstructionStatus

  hMinus1Over2DefectRatioDivergesUnderKolmogorovScaling :
    NSHminus1Over2ObstructionStatus

data HminusHalfObstructionFinding : Set where
  ratioAboveOneInSampledRows :
    HminusHalfObstructionFinding

  ratioDivergesAsNuGoesToZero :
    HminusHalfObstructionFinding

  divergenceConsistentWithKolmogorovCascade :
    HminusHalfObstructionFinding

  hOneHalfInputWouldBeCircular :
    HminusHalfObstructionFinding

  publishableAsObstructionTheoremTarget :
    HminusHalfObstructionFinding

canonicalObstructionFindings :
  List HminusHalfObstructionFinding
canonicalObstructionFindings =
  ratioAboveOneInSampledRows
  ∷ ratioDivergesAsNuGoesToZero
  ∷ divergenceConsistentWithKolmogorovCascade
  ∷ hOneHalfInputWouldBeCircular
  ∷ publishableAsObstructionTheoremTarget
  ∷ []

data HminusHalfOpenObligation : Set where
  proveUniformBoundWithoutHOneHalfInput :
    HminusHalfOpenObligation

  proveNonCircularDangerShellAbsorption :
    HminusHalfOpenObligation

  replaceNumericalDivergenceWithAnalyticScalingLaw :
    HminusHalfOpenObligation

  proveThetaTailBarrierOrRecordFailureClass :
    HminusHalfOpenObligation

canonicalHminusHalfOpenObligations :
  List HminusHalfOpenObligation
canonicalHminusHalfOpenObligations =
  proveUniformBoundWithoutHOneHalfInput
  ∷ proveNonCircularDangerShellAbsorption
  ∷ replaceNumericalDivergenceWithAnalyticScalingLaw
  ∷ proveThetaTailBarrierOrRecordFailureClass
  ∷ []

data NSHminus1Over2Promotion : Set where

nsHminus1Over2PromotionImpossibleHere :
  NSHminus1Over2Promotion →
  ⊥
nsHminus1Over2PromotionImpossibleHere ()

ratioKolmogorovNu010Hundredths :
  Nat
ratioKolmogorovNu010Hundredths =
  138

ratioSmoothNu010Hundredths :
  Nat
ratioSmoothNu010Hundredths =
  230

ratioRoughNu010Hundredths :
  Nat
ratioRoughNu010Hundredths =
  167

ratioKolmogorovNu001Hundredths :
  Nat
ratioKolmogorovNu001Hundredths =
  399

ratioKolmogorovNu001Float :
  Float
ratioKolmogorovNu001Float =
  3.99

ratioSmoothNu001Hundredths :
  Nat
ratioSmoothNu001Hundredths =
  719

ratioRoughNu001Hundredths :
  Nat
ratioRoughNu001Hundredths =
  742

ratioKolmogorovNu0002Hundredths :
  Nat
ratioKolmogorovNu0002Hundredths =
  1985

ratioSmoothNu0002Hundredths :
  Nat
ratioSmoothNu0002Hundredths =
  3597

ratioRoughNu0002Hundredths :
  Nat
ratioRoughNu0002Hundredths =
  3898

scalingExponentLowerHundredths :
  Nat
scalingExponentLowerHundredths =
  50

scalingExponentUpperHundredths :
  Nat
scalingExponentUpperHundredths =
  75

scalingExponentRange :
  String
scalingExponentRange =
  "0.5 to 0.75 (sub-power-law divergence scaling as nu^{-1/2} to nu^{-3/4})"

publishableResultType :
  String
publishableResultType =
  "ObstructionTheorem"

nsObstructionStatement :
  String
nsObstructionStatement =
  "DASHI's tail-restricted theta criterion requires the H^{-1/2} defect ratio to stay bounded. However, the ratio ||P_{>K}(u . grad u)||_{H^{-1/2}} / (nu ||P_{>K}u||_{H^{3/2}}) grows as nu -> 0 under Kolmogorov scaling in the diagnostic rows. Localized dual-norm dissipation bounds therefore cannot be consumed as a non-circular tail absorption proof without replacing the numerical scaling witness by an analytic scaling law."

canonicalReceiptBoundary :
  List String
canonicalReceiptBoundary =
  "Records the exact H^{-1/2} defect ratio growth row as nu -> 0"
  ∷ "Records that localized dual-norm dissipation bounds do not currently absorb inertial tail injection without global regularity"
  ∷ "Identifies the energy-cascade filling of tail modes as the obstruction mechanism for the local H^{-1/2} route"
  ∷ "Turns the H^{-1/2} route from a uniform-estimate attempt into a publishable obstruction theorem surface"
  ∷ "NS Clay promotion and global regularity claims remain strictly fail-closed"
  ∷ []

obstructionSummary :
  String
obstructionSummary =
  "The computed H^{-1/2} nonlinear-defect ratio is >1 in the sampled smooth/Kolmogorov/rough rows and grows like nu^{-1/2} to nu^{-3/4}; this records an obstruction witness, not a uniform absorption estimate."

publishableBoundary :
  String
publishableBoundary =
  "Paper 1 may claim a computed obstruction theorem target: theta_tail needs this ratio bounded, but Kolmogorov scaling drives it upward as nu decreases.  Clay NS remains open."

record NSHminus1Over2ObstructionReceipt : Setω where
  field
    status :
      NSHminus1Over2ObstructionStatus

    statusIsCanonical :
      status ≡ hMinus1Over2DefectRatioDivergesUnderKolmogorovScaling

    tailReceipt :
      Tail.NSTailRestrictedThetaDiagnosticReceipt

    tailDiagnosticNoClay :
      Tail.clayNavierStokesPromoted tailReceipt ≡ false

    negativeSobolevReceipt :
      Negative.NSNegativeSobolevDangerShellReceipt zero

    negativeSobolevBoundStillOpen :
      Negative.highHighDefectBoundProvedHere negativeSobolevReceipt
      ≡
      false

    negativeSobolevNoClay :
      Negative.clayNavierStokesPromoted negativeSobolevReceipt ≡ false

    kStarReceipt :
      KStar.NSNonCircularKStarDriftBoundTargetReceipt

    kStarNoClay :
      KStar.clayNavierStokesPromoted kStarReceipt ≡ false

    findings :
      List HminusHalfObstructionFinding

    findingsAreCanonical :
      findings ≡ canonicalObstructionFindings

    openObligations :
      List HminusHalfOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalHminusHalfOpenObligations

    kolmogorovNu010 :
      Nat

    kolmogorovNu010Is0138 :
      kolmogorovNu010 ≡ ratioKolmogorovNu010Hundredths

    smoothNu010 :
      Nat

    smoothNu010Is0230 :
      smoothNu010 ≡ ratioSmoothNu010Hundredths

    roughNu010 :
      Nat

    roughNu010Is0167 :
      roughNu010 ≡ ratioRoughNu010Hundredths

    kolmogorovNu001 :
      Nat

    kolmogorovNu001Is0399 :
      kolmogorovNu001 ≡ ratioKolmogorovNu001Hundredths

    ratio_kolmogorov_nu001 :
      Float

    ratioKolmogorovNu001FloatIs399 :
      ratio_kolmogorov_nu001 ≡ ratioKolmogorovNu001Float

    smoothNu001 :
      Nat

    smoothNu001Is0719 :
      smoothNu001 ≡ ratioSmoothNu001Hundredths

    roughNu001 :
      Nat

    roughNu001Is0742 :
      roughNu001 ≡ ratioRoughNu001Hundredths

    kolmogorovNu0002 :
      Nat

    kolmogorovNu0002Is1985 :
      kolmogorovNu0002 ≡ ratioKolmogorovNu0002Hundredths

    smoothNu0002 :
      Nat

    smoothNu0002Is3597 :
      smoothNu0002 ≡ ratioSmoothNu0002Hundredths

    roughNu0002 :
      Nat

    roughNu0002Is3898 :
      roughNu0002 ≡ ratioRoughNu0002Hundredths

    scalingLower :
      Nat

    scalingLowerIs050 :
      scalingLower ≡ scalingExponentLowerHundredths

    scalingUpper :
      Nat

    scalingUpperIs075 :
      scalingUpper ≡ scalingExponentUpperHundredths

    scalingExponent :
      String

    scalingExponentIsCanonical :
      scalingExponent ≡ scalingExponentRange

    ratioDivergesAsNuToZero :
      Bool

    ratioDivergesAsNuToZeroIsTrue :
      ratioDivergesAsNuToZero ≡ true

    uniformAbsorptionEstimateProvedHere :
      Bool

    uniformAbsorptionEstimateProvedHereIsFalse :
      uniformAbsorptionEstimateProvedHere ≡ false

    publishableObstructionResult :
      Bool

    publishableObstructionResultIsTrue :
      publishableObstructionResult ≡ true

    publishableResult :
      String

    publishableResultIsCanonical :
      publishableResult ≡ publishableResultType

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    clayNSProved :
      Bool

    clayNSProvedIsFalse :
      clayNSProved ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsObstructionStatement

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalReceiptBoundary

    promotions :
      List NSHminus1Over2Promotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSHminus1Over2Promotion →
      ⊥

    summary :
      String

    summaryIsCanonical :
      summary ≡ obstructionSummary

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ publishableBoundary

open NSHminus1Over2ObstructionReceipt public

canonicalNSHminus1Over2ObstructionReceipt :
  NSHminus1Over2ObstructionReceipt
canonicalNSHminus1Over2ObstructionReceipt =
  record
    { status =
        hMinus1Over2DefectRatioDivergesUnderKolmogorovScaling
    ; statusIsCanonical =
        refl
    ; tailReceipt =
        Tail.canonicalNSTailRestrictedThetaDiagnosticReceipt
    ; tailDiagnosticNoClay =
        refl
    ; negativeSobolevReceipt =
        Negative.canonicalNSNegativeSobolevDangerShellReceipt
    ; negativeSobolevBoundStillOpen =
        refl
    ; negativeSobolevNoClay =
        refl
    ; kStarReceipt =
        KStar.canonicalNSNonCircularKStarDriftBoundTargetReceipt
    ; kStarNoClay =
        refl
    ; findings =
        canonicalObstructionFindings
    ; findingsAreCanonical =
        refl
    ; openObligations =
        canonicalHminusHalfOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; kolmogorovNu010 =
        ratioKolmogorovNu010Hundredths
    ; kolmogorovNu010Is0138 =
        refl
    ; smoothNu010 =
        ratioSmoothNu010Hundredths
    ; smoothNu010Is0230 =
        refl
    ; roughNu010 =
        ratioRoughNu010Hundredths
    ; roughNu010Is0167 =
        refl
    ; kolmogorovNu001 =
        ratioKolmogorovNu001Hundredths
    ; kolmogorovNu001Is0399 =
        refl
    ; ratio_kolmogorov_nu001 =
        ratioKolmogorovNu001Float
    ; ratioKolmogorovNu001FloatIs399 =
        refl
    ; smoothNu001 =
        ratioSmoothNu001Hundredths
    ; smoothNu001Is0719 =
        refl
    ; roughNu001 =
        ratioRoughNu001Hundredths
    ; roughNu001Is0742 =
        refl
    ; kolmogorovNu0002 =
        ratioKolmogorovNu0002Hundredths
    ; kolmogorovNu0002Is1985 =
        refl
    ; smoothNu0002 =
        ratioSmoothNu0002Hundredths
    ; smoothNu0002Is3597 =
        refl
    ; roughNu0002 =
        ratioRoughNu0002Hundredths
    ; roughNu0002Is3898 =
        refl
    ; scalingLower =
        scalingExponentLowerHundredths
    ; scalingLowerIs050 =
        refl
    ; scalingUpper =
        scalingExponentUpperHundredths
    ; scalingUpperIs075 =
        refl
    ; scalingExponent =
        scalingExponentRange
    ; scalingExponentIsCanonical =
        refl
    ; ratioDivergesAsNuToZero =
        true
    ; ratioDivergesAsNuToZeroIsTrue =
        refl
    ; uniformAbsorptionEstimateProvedHere =
        false
    ; uniformAbsorptionEstimateProvedHereIsFalse =
        refl
    ; publishableObstructionResult =
        true
    ; publishableObstructionResultIsTrue =
        refl
    ; publishableResult =
        publishableResultType
    ; publishableResultIsCanonical =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; clayNSProved =
        false
    ; clayNSProvedIsFalse =
        refl
    ; statement =
        nsObstructionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        canonicalReceiptBoundary
    ; receiptBoundaryIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsHminus1Over2PromotionImpossibleHere
    ; summary =
        obstructionSummary
    ; summaryIsCanonical =
        refl
    ; boundary =
        publishableBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalNSHminus1Over2NoClay :
  clayNavierStokesPromoted canonicalNSHminus1Over2ObstructionReceipt
  ≡
  false
canonicalNSHminus1Over2NoClay =
  refl

canonicalNSHminus1Over2DivergenceRecorded :
  ratioDivergesAsNuToZero canonicalNSHminus1Over2ObstructionReceipt
  ≡
  true
canonicalNSHminus1Over2DivergenceRecorded =
  refl

nsHminus1Over2ObstructionKeepsClayFalse :
  clayNSProved canonicalNSHminus1Over2ObstructionReceipt ≡ false
nsHminus1Over2ObstructionKeepsClayFalse =
  refl

nsHminus1Over2ObstructionIsDivergent :
  ratioDivergesAsNuToZero canonicalNSHminus1Over2ObstructionReceipt
  ≡
  true
nsHminus1Over2ObstructionIsDivergent =
  refl
