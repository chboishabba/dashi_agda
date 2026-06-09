module DASHI.Physics.Closure.NSCrossLaneLipschitzBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSFlowPreservationBoundReceipt as Flow

------------------------------------------------------------------------
-- Navier-Stokes cross-lane Lipschitz perturbation receipt.
--
-- This receipt records the cross-lane nonlinear forcing schematic
--
--   F_cross(u) = sum_{p != q} Pi_p [ ((Pi_q u) * nabla) (Pi_q u) ]
--
-- or an equivalent cross-lane projection schematic.  The flow-preservation
-- cross-base estimate supplies a summable constant C' in H^{-1}.  The
-- recorded Lipschitz estimate is
--
--   ||F_cross(u)-F_cross(v)||_{H^{-1}} <= C' ||u-v||_{H^{11/8}}.
--
-- For fixed nu > 0, this makes the cross-lane term a Lipschitz
-- perturbation of the per-lane system.  The global boundedness flag remains
-- a candidate requiring nu > C'.  No Clay/global terminal promotion is made.

data NSCrossLaneLipschitzStatus : Set where
  candidate :
    NSCrossLaneLipschitzStatus

  crossLaneForcingSchematicRecorded :
    NSCrossLaneLipschitzStatus

  flowPreservationSuppliesCPrime :
    NSCrossLaneLipschitzStatus

  hMinusOneLipschitzFromH118 :
    NSCrossLaneLipschitzStatus

  summableCrossBaseConstant :
    NSCrossLaneLipschitzStatus

  lipschitzPerturbationOfPerLaneSystem :
    NSCrossLaneLipschitzStatus

  candidateGlobalBoundForNuGreaterThanCPrime :
    NSCrossLaneLipschitzStatus

  noClayOrTerminalPromotionStatus :
    NSCrossLaneLipschitzStatus

canonicalNSCrossLaneLipschitzStatus :
  List NSCrossLaneLipschitzStatus
canonicalNSCrossLaneLipschitzStatus =
  candidate
  ∷ crossLaneForcingSchematicRecorded
  ∷ flowPreservationSuppliesCPrime
  ∷ hMinusOneLipschitzFromH118
  ∷ summableCrossBaseConstant
  ∷ lipschitzPerturbationOfPerLaneSystem
  ∷ candidateGlobalBoundForNuGreaterThanCPrime
  ∷ noClayOrTerminalPromotionStatus
  ∷ []

data CrossLaneForcingSchematic : Set where
  sumPiPOfPiQTransportPiQForPNotQ :
    CrossLaneForcingSchematic

  compatibleCrossLaneProjectionSchematic :
    CrossLaneForcingSchematic

canonicalCrossLaneForcingSchematic :
  CrossLaneForcingSchematic
canonicalCrossLaneForcingSchematic =
  sumPiPOfPiQTransportPiQForPNotQ

data CrossLaneLipschitzConstant : Set where
  cPrimeFromFlowPreservation :
    CrossLaneLipschitzConstant

data LipschitzPerturbationGlobalBound : Set where
  candidateForNuGreaterThanCPrime :
    LipschitzPerturbationGlobalBound

data NSCrossLaneLipschitzPromotion : Set where

nsCrossLaneLipschitzPromotionImpossibleHere :
  NSCrossLaneLipschitzPromotion →
  ⊥
nsCrossLaneLipschitzPromotionImpossibleHere ()

h118SobolevNumerator :
  Nat
h118SobolevNumerator =
  11

h118SobolevDenominator :
  Nat
h118SobolevDenominator =
  8

crossLaneForcingFormula :
  String
crossLaneForcingFormula =
  "F_cross(u) = sum_{p != q} Pi_p[((Pi_q u)*nabla)(Pi_q u)]"

crossLaneFlowPreservationBoundFormula :
  String
crossLaneFlowPreservationBoundFormula =
  "||F_cross(u)||_{H^{-1}} <= C sum cross-base (p^l)/(p^j+q^l) a_j^{1/2} b_l^{1/2}"

crossLaneLipschitzFormula :
  String
crossLaneLipschitzFormula =
  "||F_cross(u)-F_cross(v)||_{H^{-1}} <= C' ||u-v||_{H^{11/8}}"

crossLaneLipschitzBoundFlag :
  String
crossLaneLipschitzBoundFlag =
  "crossLaneLipschitzBound=C' from flowPreservation"

lipschitzPerturbationGlobalBoundFlag :
  String
lipschitzPerturbationGlobalBoundFlag =
  "lipschitzPerturbationGlobalBound=candidate for nu > C'"

nsCrossLaneLipschitzStatement :
  String
nsCrossLaneLipschitzStatement =
  "Candidate receipt: the cross-lane forcing F_cross(u)=sum_{p != q} Pi_p[((Pi_q u)*nabla)(Pi_q u)] is controlled in H^{-1} by the flow-preservation cross-base sums, giving a summable C' for H^s, s > 0, and the H^{11/8} Lipschitz estimate ||F_cross(u)-F_cross(v)||_{H^{-1}} <= C' ||u-v||_{H^{11/8}}.  For fixed nu > 0 it is a Lipschitz perturbation of the per-lane system, with a candidate global bound when nu > C'.  No Clay/global terminal promotion is made."

record NSCrossLaneLipschitzBoundReceipt : Setω where
  field
    flowPreservationReceipt :
      Flow.NSFlowPreservationBoundReceipt

    flowPreservationStatusCanonical :
      Flow.status flowPreservationReceipt
      ≡
      Flow.canonicalNSFlowPreservationBoundStatus

    flowPreservationCrossBaseSumsRecorded :
      Flow.crossBaseSumsBoundRecorded flowPreservationReceipt ≡ true

    flowPreservationSummabilityRecorded :
      Flow.summableForHsWithS>0 flowPreservationReceipt ≡ true

    flowPreservationNoClayPromotion :
      Flow.clayNavierStokesPromoted flowPreservationReceipt ≡ false

    status :
      List NSCrossLaneLipschitzStatus

    statusIsCanonical :
      status ≡ canonicalNSCrossLaneLipschitzStatus

    forcingSchematic :
      CrossLaneForcingSchematic

    forcingSchematicIsCanonical :
      forcingSchematic ≡ canonicalCrossLaneForcingSchematic

    forcingFormula :
      String

    forcingFormulaIsCanonical :
      forcingFormula ≡ crossLaneForcingFormula

    compatibleCrossLaneSchematicAllowed :
      Bool

    compatibleCrossLaneSchematicAllowedIsTrue :
      compatibleCrossLaneSchematicAllowed ≡ true

    hMinusOneForcingBoundRecorded :
      Bool

    hMinusOneForcingBoundRecordedIsTrue :
      hMinusOneForcingBoundRecorded ≡ true

    forcingBoundFormula :
      String

    forcingBoundFormulaIsCanonical :
      forcingBoundFormula ≡ crossLaneFlowPreservationBoundFormula

    crossBaseCoefficientInheritedFromFlowPreservation :
      Bool

    crossBaseCoefficientInheritedFromFlowPreservationIsTrue :
      crossBaseCoefficientInheritedFromFlowPreservation ≡ true

    summableForHsWithSPositive :
      Bool

    summableForHsWithSPositiveIsTrue :
      summableForHsWithSPositive ≡ true

    h118Numerator :
      Nat

    h118NumeratorIs11 :
      h118Numerator ≡ h118SobolevNumerator

    h118Denominator :
      Nat

    h118DenominatorIs8 :
      h118Denominator ≡ h118SobolevDenominator

    lipschitzEstimateRecorded :
      Bool

    lipschitzEstimateRecordedIsTrue :
      lipschitzEstimateRecorded ≡ true

    lipschitzFormula :
      String

    lipschitzFormulaIsCanonical :
      lipschitzFormula ≡ crossLaneLipschitzFormula

    crossLaneLipschitzBound :
      CrossLaneLipschitzConstant

    crossLaneLipschitzBoundIsCPrimeFromFlowPreservation :
      crossLaneLipschitzBound ≡ cPrimeFromFlowPreservation

    crossLaneLipschitzBoundFlagText :
      String

    crossLaneLipschitzBoundFlagTextIsCanonical :
      crossLaneLipschitzBoundFlagText ≡ crossLaneLipschitzBoundFlag

    fixedNuPositiveRecorded :
      Bool

    fixedNuPositiveRecordedIsTrue :
      fixedNuPositiveRecorded ≡ true

    perturbationOfPerLaneSystem :
      Bool

    perturbationOfPerLaneSystemIsTrue :
      perturbationOfPerLaneSystem ≡ true

    lipschitzPerturbationGlobalBound :
      LipschitzPerturbationGlobalBound

    lipschitzPerturbationGlobalBoundIsCandidate :
      lipschitzPerturbationGlobalBound
      ≡
      candidateForNuGreaterThanCPrime

    lipschitzPerturbationGlobalBoundFlagText :
      String

    lipschitzPerturbationGlobalBoundFlagTextIsCanonical :
      lipschitzPerturbationGlobalBoundFlagText
      ≡
      lipschitzPerturbationGlobalBoundFlag

    globalBoundCandidateRequiresNuGreaterThanCPrime :
      Bool

    globalBoundCandidateRequiresNuGreaterThanCPrimeIsTrue :
      globalBoundCandidateRequiresNuGreaterThanCPrime ≡ true

    globalBoundProvedHere :
      Bool

    globalBoundProvedHereIsFalse :
      globalBoundProvedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalTerminalPromotion :
      Bool

    globalTerminalPromotionIsFalse :
      globalTerminalPromotion ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsCrossLaneLipschitzStatement

    promotionFlags :
      List NSCrossLaneLipschitzPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCrossLaneLipschitzBoundReceipt public

canonicalNSCrossLaneLipschitzBoundReceipt :
  NSCrossLaneLipschitzBoundReceipt
canonicalNSCrossLaneLipschitzBoundReceipt =
  record
    { flowPreservationReceipt =
        Flow.canonicalNSFlowPreservationBoundReceipt
    ; flowPreservationStatusCanonical =
        refl
    ; flowPreservationCrossBaseSumsRecorded =
        refl
    ; flowPreservationSummabilityRecorded =
        refl
    ; flowPreservationNoClayPromotion =
        refl
    ; status =
        canonicalNSCrossLaneLipschitzStatus
    ; statusIsCanonical =
        refl
    ; forcingSchematic =
        canonicalCrossLaneForcingSchematic
    ; forcingSchematicIsCanonical =
        refl
    ; forcingFormula =
        crossLaneForcingFormula
    ; forcingFormulaIsCanonical =
        refl
    ; compatibleCrossLaneSchematicAllowed =
        true
    ; compatibleCrossLaneSchematicAllowedIsTrue =
        refl
    ; hMinusOneForcingBoundRecorded =
        true
    ; hMinusOneForcingBoundRecordedIsTrue =
        refl
    ; forcingBoundFormula =
        crossLaneFlowPreservationBoundFormula
    ; forcingBoundFormulaIsCanonical =
        refl
    ; crossBaseCoefficientInheritedFromFlowPreservation =
        true
    ; crossBaseCoefficientInheritedFromFlowPreservationIsTrue =
        refl
    ; summableForHsWithSPositive =
        true
    ; summableForHsWithSPositiveIsTrue =
        refl
    ; h118Numerator =
        11
    ; h118NumeratorIs11 =
        refl
    ; h118Denominator =
        8
    ; h118DenominatorIs8 =
        refl
    ; lipschitzEstimateRecorded =
        true
    ; lipschitzEstimateRecordedIsTrue =
        refl
    ; lipschitzFormula =
        crossLaneLipschitzFormula
    ; lipschitzFormulaIsCanonical =
        refl
    ; crossLaneLipschitzBound =
        cPrimeFromFlowPreservation
    ; crossLaneLipschitzBoundIsCPrimeFromFlowPreservation =
        refl
    ; crossLaneLipschitzBoundFlagText =
        crossLaneLipschitzBoundFlag
    ; crossLaneLipschitzBoundFlagTextIsCanonical =
        refl
    ; fixedNuPositiveRecorded =
        true
    ; fixedNuPositiveRecordedIsTrue =
        refl
    ; perturbationOfPerLaneSystem =
        true
    ; perturbationOfPerLaneSystemIsTrue =
        refl
    ; lipschitzPerturbationGlobalBound =
        candidateForNuGreaterThanCPrime
    ; lipschitzPerturbationGlobalBoundIsCandidate =
        refl
    ; lipschitzPerturbationGlobalBoundFlagText =
        lipschitzPerturbationGlobalBoundFlag
    ; lipschitzPerturbationGlobalBoundFlagTextIsCanonical =
        refl
    ; globalBoundCandidateRequiresNuGreaterThanCPrime =
        true
    ; globalBoundCandidateRequiresNuGreaterThanCPrimeIsTrue =
        refl
    ; globalBoundProvedHere =
        false
    ; globalBoundProvedHereIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalTerminalPromotion =
        false
    ; globalTerminalPromotionIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; statement =
        nsCrossLaneLipschitzStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "F_cross schematic recorded as sum_{p != q} Pi_p[((Pi_q u)*nabla)(Pi_q u)], with compatible cross-lane schematics allowed"
        ∷ "H^{-1} forcing bound inherited from flow-preservation cross-base sums"
        ∷ "crossLaneLipschitzBound=C' from flowPreservation"
        ∷ "H^{11/8} Lipschitz estimate recorded: ||F_cross(u)-F_cross(v)||_{H^{-1}} <= C' ||u-v||_{H^{11/8}}"
        ∷ "The cross-base constant C' is recorded as summable for H^s, s > 0"
        ∷ "For fixed nu > 0, cross-lane forcing is recorded as a Lipschitz perturbation of the per-lane system"
        ∷ "lipschitzPerturbationGlobalBound=candidate for nu > C'"
        ∷ "No Clay Navier-Stokes, global terminal, or terminal theorem promotion is claimed"
        ∷ []
    }

canonicalCrossLaneLipschitzBoundIsFromFlowPreservation :
  crossLaneLipschitzBound canonicalNSCrossLaneLipschitzBoundReceipt
  ≡
  cPrimeFromFlowPreservation
canonicalCrossLaneLipschitzBoundIsFromFlowPreservation =
  refl

canonicalCrossLaneLipschitzEstimateRecorded :
  lipschitzEstimateRecorded canonicalNSCrossLaneLipschitzBoundReceipt
  ≡
  true
canonicalCrossLaneLipschitzEstimateRecorded =
  refl

canonicalCrossLanePerturbationGlobalBoundCandidate :
  lipschitzPerturbationGlobalBound canonicalNSCrossLaneLipschitzBoundReceipt
  ≡
  candidateForNuGreaterThanCPrime
canonicalCrossLanePerturbationGlobalBoundCandidate =
  refl

canonicalCrossLaneGlobalBoundNotProvedHere :
  globalBoundProvedHere canonicalNSCrossLaneLipschitzBoundReceipt
  ≡
  false
canonicalCrossLaneGlobalBoundNotProvedHere =
  refl

canonicalCrossLaneNoClayPromotion :
  clayNavierStokesPromoted canonicalNSCrossLaneLipschitzBoundReceipt
  ≡
  false
canonicalCrossLaneNoClayPromotion =
  refl

canonicalCrossLaneNoGlobalTerminalPromotion :
  globalTerminalPromotion canonicalNSCrossLaneLipschitzBoundReceipt
  ≡
  false
canonicalCrossLaneNoGlobalTerminalPromotion =
  refl

canonicalCrossLaneNoTerminalPromotion :
  terminalClaimPromoted canonicalNSCrossLaneLipschitzBoundReceipt
  ≡
  false
canonicalCrossLaneNoTerminalPromotion =
  refl

nsCrossLaneLipschitzNoPromotion :
  NSCrossLaneLipschitzPromotion →
  ⊥
nsCrossLaneLipschitzNoPromotion =
  nsCrossLaneLipschitzPromotionImpossibleHere
