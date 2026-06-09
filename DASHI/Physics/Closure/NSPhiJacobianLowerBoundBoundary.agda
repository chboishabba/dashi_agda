module DASHI.Physics.Closure.NSPhiJacobianLowerBoundBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSFourierOutputPushforwardBoundary
  as Pushforward
import DASHI.Physics.Closure.NSLeiRenTianFourierOutputCouplingBoundary
  as A4
import DASHI.Physics.Closure.NSLeiRenTianOutputSupportTransferBoundary
  as OutputSupport
import DASHI.Physics.Closure.NSLocalizedWhitneyFramePacketEstimateBoundary
  as WhitneyPackets
import DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary
  as WhitneyCoupling

------------------------------------------------------------------------
-- NS A4 Phi-Jacobian lower-bound boundary.
--
-- Child target of the A4 Sard/Fubini and Whitney-coupling step:
--
--   Phi(theta1,theta2) = normalize(theta1 + theta2)
--
-- should have a quantitative Jacobian lower bound after excluding
-- antipodal / null-output / near-degenerate triads.  The intended analytic
-- role is:
--
--   off-antipodal separation
--     -> derivative formula for normalize(theta1 + theta2)
--     -> rank and lower-bound target on Whitney chart rectangles
--     -> cap-uniform output strip lower bound
--     -> degenerate-triad absorption into lower-order budget.
--
-- This module is intentionally fail-closed.  It records the exact
-- proof-contract structure needed by NSWhitneyCouplingInequalityBoundary.
-- It does not compute the chart derivative, does not prove quantitative
-- constants, does not discharge degenerate-triad absorption, does not prove
-- A4, and does not promote Navier-Stokes Clay.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support anchors.

record ImportedPhiJacobianSupport : Set where
  field
    fourierOutputPhiMap :
      Pushforward.FourierOutputPhiMap
    fourierOutputPhiMapIsCanonical :
      fourierOutputPhiMap ≡ Pushforward.canonicalFourierOutputPhiMap
    antipodalExclusion :
      Pushforward.AntipodalExclusionCarrier
    antipodalExclusionIsCanonical :
      antipodalExclusion ≡ Pushforward.canonicalAntipodalExclusionCarrier
    offAntipodalLipschitzControl :
      Pushforward.OffAntipodalLipschitzControl
    offAntipodalLipschitzControlIsCanonical :
      offAntipodalLipschitzControl
        ≡ Pushforward.canonicalOffAntipodalLipschitzControl
    whitneyCapCover :
      WhitneyPackets.WhitneyAngularCapCover
    whitneyCapCoverIsCanonical :
      whitneyCapCover ≡ WhitneyPackets.canonicalWhitneyAngularCapCover
    annularExclusionControl :
      WhitneyPackets.AnnularExclusionControl
    annularExclusionControlIsCanonical :
      annularExclusionControl
        ≡ WhitneyPackets.canonicalAnnularExclusionControl
    whitneyCouplingGap :
      WhitneyCoupling.SardFubiniGap
    whitneyCouplingGapIsJacobian :
      whitneyCouplingGap
        ≡ WhitneyCoupling.proveJacobianLowerBoundAwayFromDegenerateTriads
    outputRichnessTarget :
      OutputSupport.FourierTriadicOutputDirectionRichness
    outputRichnessTargetIsCanonical :
      outputRichnessTarget
        ≡ OutputSupport.canonicalFourierTriadicOutputDirectionRichness
    parentA4Boundary :
      A4.NSLeiRenTianFourierOutputCouplingBoundary
    parentA4BoundaryIsCanonical :
      parentA4Boundary ≡ A4.canonicalNSLeiRenTianFourierOutputCouplingBoundary

canonicalImportedPhiJacobianSupport :
  ImportedPhiJacobianSupport
canonicalImportedPhiJacobianSupport =
  record
    { fourierOutputPhiMap =
        Pushforward.canonicalFourierOutputPhiMap
    ; fourierOutputPhiMapIsCanonical =
        refl
    ; antipodalExclusion =
        Pushforward.canonicalAntipodalExclusionCarrier
    ; antipodalExclusionIsCanonical =
        refl
    ; offAntipodalLipschitzControl =
        Pushforward.canonicalOffAntipodalLipschitzControl
    ; offAntipodalLipschitzControlIsCanonical =
        refl
    ; whitneyCapCover =
        WhitneyPackets.canonicalWhitneyAngularCapCover
    ; whitneyCapCoverIsCanonical =
        refl
    ; annularExclusionControl =
        WhitneyPackets.canonicalAnnularExclusionControl
    ; annularExclusionControlIsCanonical =
        refl
    ; whitneyCouplingGap =
        WhitneyCoupling.proveJacobianLowerBoundAwayFromDegenerateTriads
    ; whitneyCouplingGapIsJacobian =
        refl
    ; outputRichnessTarget =
        OutputSupport.canonicalFourierTriadicOutputDirectionRichness
    ; outputRichnessTargetIsCanonical =
        refl
    ; parentA4Boundary =
        A4.canonicalNSLeiRenTianFourierOutputCouplingBoundary
    ; parentA4BoundaryIsCanonical =
        refl
    }

------------------------------------------------------------------------
-- Jacobian and degeneracy carriers.

data OffAntipodalSeparationParameter : Set where
  separationEtaForThetaOnePlusThetaTwoNorm :
    Nat →
    Pushforward.AntipodalExclusionCarrier →
    OffAntipodalSeparationParameter

data PhiDerivativeFormulaCarrier : Set where
  dPhiEqualsProjectedDerivativeOverNormalizeSumNorm :
    Pushforward.FourierOutputPhiMap →
    OffAntipodalSeparationParameter →
    PhiDerivativeFormulaCarrier

data PhiChartRankCarrier : Set where
  rankTwoOnRegularWhitneyChartRectangles :
    PhiDerivativeFormulaCarrier →
    WhitneyPackets.WhitneyAngularCapCover →
    PhiChartRankCarrier

data PhiJacobianLowerBoundCarrier : Set where
  jacobianBoundedBelowBySeparationAndCapScale :
    PhiChartRankCarrier →
    OffAntipodalSeparationParameter →
    WhitneyPackets.FrameVariationControl →
    PhiJacobianLowerBoundCarrier

data DegenerateTriadExclusionCarrier : Set where
  excludeAntipodalNullAndRankDropTriads :
    Pushforward.AntipodalExclusionCarrier →
    WhitneyPackets.AnnularExclusionControl →
    PhiChartRankCarrier →
    DegenerateTriadExclusionCarrier

data DegenerateTriadBudgetAbsorptionCarrier : Set where
  degenerateTriadsAbsorbedIntoLowerOrderA4Budget :
    DegenerateTriadExclusionCarrier →
    WhitneyCoupling.WhitneyCouplingErrorTerm →
    DegenerateTriadBudgetAbsorptionCarrier

data WhitneyCapUniformConstantCarrier : Set where
  constantsUniformAcrossBoundedOverlapWhitneyCaps :
    PhiJacobianLowerBoundCarrier →
    WhitneyPackets.PacketOverlapControl →
    WhitneyCapUniformConstantCarrier

data OutputStripWidthRelationCarrier : Set where
  jacobianLowerBoundControlsOutputGreatCircleStripWidth :
    WhitneyCapUniformConstantCarrier →
    OutputSupport.FourierTriadicOutputDirectionRichness →
    OutputStripWidthRelationCarrier

data PhiJacobianLowerBoundTarget : Set where
  regularWhitneyTriadsHaveUniformOutputJacobianLowerBound :
    PhiDerivativeFormulaCarrier →
    PhiChartRankCarrier →
    PhiJacobianLowerBoundCarrier →
    DegenerateTriadExclusionCarrier →
    DegenerateTriadBudgetAbsorptionCarrier →
    WhitneyCapUniformConstantCarrier →
    OutputStripWidthRelationCarrier →
    PhiJacobianLowerBoundTarget

canonicalOffAntipodalSeparationParameter :
  OffAntipodalSeparationParameter
canonicalOffAntipodalSeparationParameter =
  separationEtaForThetaOnePlusThetaTwoNorm
    (suc zero)
    Pushforward.canonicalAntipodalExclusionCarrier

canonicalPhiDerivativeFormulaCarrier :
  PhiDerivativeFormulaCarrier
canonicalPhiDerivativeFormulaCarrier =
  dPhiEqualsProjectedDerivativeOverNormalizeSumNorm
    Pushforward.canonicalFourierOutputPhiMap
    canonicalOffAntipodalSeparationParameter

canonicalPhiChartRankCarrier :
  PhiChartRankCarrier
canonicalPhiChartRankCarrier =
  rankTwoOnRegularWhitneyChartRectangles
    canonicalPhiDerivativeFormulaCarrier
    WhitneyPackets.canonicalWhitneyAngularCapCover

canonicalPhiJacobianLowerBoundCarrier :
  PhiJacobianLowerBoundCarrier
canonicalPhiJacobianLowerBoundCarrier =
  jacobianBoundedBelowBySeparationAndCapScale
    canonicalPhiChartRankCarrier
    canonicalOffAntipodalSeparationParameter
    WhitneyPackets.canonicalFrameVariationControl

canonicalDegenerateTriadExclusionCarrier :
  DegenerateTriadExclusionCarrier
canonicalDegenerateTriadExclusionCarrier =
  excludeAntipodalNullAndRankDropTriads
    Pushforward.canonicalAntipodalExclusionCarrier
    WhitneyPackets.canonicalAnnularExclusionControl
    canonicalPhiChartRankCarrier

canonicalDegenerateTriadBudgetAbsorptionCarrier :
  DegenerateTriadBudgetAbsorptionCarrier
canonicalDegenerateTriadBudgetAbsorptionCarrier =
  degenerateTriadsAbsorbedIntoLowerOrderA4Budget
    canonicalDegenerateTriadExclusionCarrier
    WhitneyCoupling.outputMapJacobianRegularValueLoss

canonicalWhitneyCapUniformConstantCarrier :
  WhitneyCapUniformConstantCarrier
canonicalWhitneyCapUniformConstantCarrier =
  constantsUniformAcrossBoundedOverlapWhitneyCaps
    canonicalPhiJacobianLowerBoundCarrier
    WhitneyPackets.canonicalPacketOverlapControl

canonicalOutputStripWidthRelationCarrier :
  OutputStripWidthRelationCarrier
canonicalOutputStripWidthRelationCarrier =
  jacobianLowerBoundControlsOutputGreatCircleStripWidth
    canonicalWhitneyCapUniformConstantCarrier
    OutputSupport.canonicalFourierTriadicOutputDirectionRichness

canonicalPhiJacobianLowerBoundTarget :
  PhiJacobianLowerBoundTarget
canonicalPhiJacobianLowerBoundTarget =
  regularWhitneyTriadsHaveUniformOutputJacobianLowerBound
    canonicalPhiDerivativeFormulaCarrier
    canonicalPhiChartRankCarrier
    canonicalPhiJacobianLowerBoundCarrier
    canonicalDegenerateTriadExclusionCarrier
    canonicalDegenerateTriadBudgetAbsorptionCarrier
    canonicalWhitneyCapUniformConstantCarrier
    canonicalOutputStripWidthRelationCarrier

------------------------------------------------------------------------
-- Exact proof obligations and blockers.

data PhiJacobianObligation : Set where
  chooseOffAntipodalSeparationParameter :
    PhiJacobianObligation
  computeDerivativeOfNormalizeThetaOnePlusThetaTwoInCharts :
    PhiJacobianObligation
  proveRankTwoAwayFromAntipodalAndRankDropLoci :
    PhiJacobianObligation
  proveQuantitativeJacobianLowerBound :
    PhiJacobianObligation
  makeConstantsUniformAcrossWhitneyCapCover :
    PhiJacobianObligation
  relateCapInputScaleToOutputStripWidth :
    PhiJacobianObligation
  excludeDegenerateTriadsFromSardFubiniSlice :
    PhiJacobianObligation
  absorbDegenerateTriadsIntoLowerOrderA4Budget :
    PhiJacobianObligation
  feedJacobianBoundIntoWhitneyCoupling :
    PhiJacobianObligation

canonicalPhiJacobianObligations :
  List PhiJacobianObligation
canonicalPhiJacobianObligations =
  chooseOffAntipodalSeparationParameter
  ∷ computeDerivativeOfNormalizeThetaOnePlusThetaTwoInCharts
  ∷ proveRankTwoAwayFromAntipodalAndRankDropLoci
  ∷ proveQuantitativeJacobianLowerBound
  ∷ makeConstantsUniformAcrossWhitneyCapCover
  ∷ relateCapInputScaleToOutputStripWidth
  ∷ excludeDegenerateTriadsFromSardFubiniSlice
  ∷ absorbDegenerateTriadsIntoLowerOrderA4Budget
  ∷ feedJacobianBoundIntoWhitneyCoupling
  ∷ []

phiJacobianObligationCount : Nat
phiJacobianObligationCount =
  listLength canonicalPhiJacobianObligations

phiJacobianObligationCountIs9 :
  phiJacobianObligationCount ≡ 9
phiJacobianObligationCountIs9 =
  refl

data PhiJacobianBlocker : Set where
  missingChartDerivativeComputation :
    PhiJacobianBlocker
  missingQuantitativeLowerBound :
    PhiJacobianBlocker
  missingCapUniformConstants :
    PhiJacobianBlocker
  missingDegenerateTriadAbsorptionIntoLowerOrderBudget :
    PhiJacobianBlocker
  missingSardFubiniIntegration :
    PhiJacobianBlocker
  missingA4Promotion :
    PhiJacobianBlocker
  missingClayPromotion :
    PhiJacobianBlocker

canonicalPhiJacobianBlockers :
  List PhiJacobianBlocker
canonicalPhiJacobianBlockers =
  missingChartDerivativeComputation
  ∷ missingQuantitativeLowerBound
  ∷ missingCapUniformConstants
  ∷ missingDegenerateTriadAbsorptionIntoLowerOrderBudget
  ∷ missingSardFubiniIntegration
  ∷ missingA4Promotion
  ∷ missingClayPromotion
  ∷ []

phiJacobianBlockerCount : Nat
phiJacobianBlockerCount =
  listLength canonicalPhiJacobianBlockers

phiJacobianBlockerCountIs7 :
  phiJacobianBlockerCount ≡ 7
phiJacobianBlockerCountIs7 =
  refl

data PhiJacobianStatusRow : Set where
  boundaryRecordedStatus :
    PhiJacobianStatusRow
  derivativeFormulaCarrierRecordedStatus :
    PhiJacobianStatusRow
  offAntipodalSeparationRecordedStatus :
    PhiJacobianStatusRow
  rankLowerBoundTargetRecordedStatus :
    PhiJacobianStatusRow
  degenerateTriadExclusionRecordedStatus :
    PhiJacobianStatusRow
  WhitneyCapAndOutputStripRelationRecordedStatus :
    PhiJacobianStatusRow
  blockersRecordedStatus :
    PhiJacobianStatusRow
  allProofAndPromotionFlagsFalseStatus :
    PhiJacobianStatusRow

canonicalPhiJacobianStatusRows :
  List PhiJacobianStatusRow
canonicalPhiJacobianStatusRows =
  boundaryRecordedStatus
  ∷ derivativeFormulaCarrierRecordedStatus
  ∷ offAntipodalSeparationRecordedStatus
  ∷ rankLowerBoundTargetRecordedStatus
  ∷ degenerateTriadExclusionRecordedStatus
  ∷ WhitneyCapAndOutputStripRelationRecordedStatus
  ∷ blockersRecordedStatus
  ∷ allProofAndPromotionFlagsFalseStatus
  ∷ []

phiJacobianStatusRowCount : Nat
phiJacobianStatusRowCount =
  listLength canonicalPhiJacobianStatusRows

phiJacobianStatusRowCountIs8 :
  phiJacobianStatusRowCount ≡ 8
phiJacobianStatusRowCountIs8 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data PhiJacobianPromotion : Set where

phiJacobianPromotionImpossibleHere :
  PhiJacobianPromotion →
  ⊥
phiJacobianPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSPhiJacobianLowerBoundBoundaryRecorded : Bool
NSPhiJacobianLowerBoundBoundaryRecorded =
  true

PhiDerivativeFormulaRecorded : Bool
PhiDerivativeFormulaRecorded =
  true

offAntipodalSeparationParameterRecorded : Bool
offAntipodalSeparationParameterRecorded =
  true

rankLowerBoundTargetRecorded : Bool
rankLowerBoundTargetRecorded =
  true

degenerateTriadExclusionRecorded : Bool
degenerateTriadExclusionRecorded =
  true

WhitneyCapOutputStripRelationRecorded : Bool
WhitneyCapOutputStripRelationRecorded =
  true

PhiChartDerivativeComputed : Bool
PhiChartDerivativeComputed =
  false

PhiQuantitativeJacobianLowerBoundProved : Bool
PhiQuantitativeJacobianLowerBoundProved =
  false

PhiCapUniformConstantsProved : Bool
PhiCapUniformConstantsProved =
  false

degenerateTriadBudgetAbsorptionProved : Bool
degenerateTriadBudgetAbsorptionProved =
  false

PhiJacobianLowerBoundTheoremProved : Bool
PhiJacobianLowerBoundTheoremProved =
  false

A4SardFubiniStepProved : Bool
A4SardFubiniStepProved =
  false

A4LeiRenTianFourierOutputCouplingProved : Bool
A4LeiRenTianFourierOutputCouplingProved =
  false

fullLocalDefectMonotonicity : Bool
fullLocalDefectMonotonicity =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordsBoundary :
  NSPhiJacobianLowerBoundBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsPhiDerivativeFormula :
  PhiDerivativeFormulaRecorded ≡ true
recordsPhiDerivativeFormula =
  refl

recordsOffAntipodalSeparationParameter :
  offAntipodalSeparationParameterRecorded ≡ true
recordsOffAntipodalSeparationParameter =
  refl

recordsRankLowerBoundTarget :
  rankLowerBoundTargetRecorded ≡ true
recordsRankLowerBoundTarget =
  refl

recordsDegenerateTriadExclusion :
  degenerateTriadExclusionRecorded ≡ true
recordsDegenerateTriadExclusion =
  refl

recordsWhitneyCapOutputStripRelation :
  WhitneyCapOutputStripRelationRecorded ≡ true
recordsWhitneyCapOutputStripRelation =
  refl

keepsPhiChartDerivativeComputedFalse :
  PhiChartDerivativeComputed ≡ false
keepsPhiChartDerivativeComputedFalse =
  refl

keepsPhiQuantitativeJacobianLowerBoundFalse :
  PhiQuantitativeJacobianLowerBoundProved ≡ false
keepsPhiQuantitativeJacobianLowerBoundFalse =
  refl

keepsPhiCapUniformConstantsFalse :
  PhiCapUniformConstantsProved ≡ false
keepsPhiCapUniformConstantsFalse =
  refl

keepsDegenerateTriadBudgetAbsorptionFalse :
  degenerateTriadBudgetAbsorptionProved ≡ false
keepsDegenerateTriadBudgetAbsorptionFalse =
  refl

keepsPhiJacobianLowerBoundTheoremFalse :
  PhiJacobianLowerBoundTheoremProved ≡ false
keepsPhiJacobianLowerBoundTheoremFalse =
  refl

keepsA4SardFubiniStepFalse :
  A4SardFubiniStepProved ≡ false
keepsA4SardFubiniStepFalse =
  refl

keepsA4LeiRenTianFourierOutputCouplingFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4LeiRenTianFourierOutputCouplingFalse =
  refl

keepsFullLocalDefectMonotonicityFalse :
  fullLocalDefectMonotonicity ≡ false
keepsFullLocalDefectMonotonicityFalse =
  refl

keepsFullClayNSSolvedFalse :
  fullClayNSSolved ≡ false
keepsFullClayNSSolvedFalse =
  refl

keepsClayNavierStokesPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayNavierStokesPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- Canonical boundary receipt.

record NSPhiJacobianLowerBoundBoundary : Set where
  field
    importedSupport :
      ImportedPhiJacobianSupport
    derivativeFormula :
      PhiDerivativeFormulaCarrier
    rankCarrier :
      PhiChartRankCarrier
    jacobianLowerBound :
      PhiJacobianLowerBoundCarrier
    degenerateTriadExclusion :
      DegenerateTriadExclusionCarrier
    budgetAbsorption :
      DegenerateTriadBudgetAbsorptionCarrier
    capUniformConstants :
      WhitneyCapUniformConstantCarrier
    outputStripRelation :
      OutputStripWidthRelationCarrier
    target :
      PhiJacobianLowerBoundTarget
    obligations :
      List PhiJacobianObligation
    blockers :
      List PhiJacobianBlocker
    statusRows :
      List PhiJacobianStatusRow
    boundaryRecorded :
      NSPhiJacobianLowerBoundBoundaryRecorded ≡ true
    derivativeRecorded :
      PhiDerivativeFormulaRecorded ≡ true
    separationRecorded :
      offAntipodalSeparationParameterRecorded ≡ true
    rankTargetRecorded :
      rankLowerBoundTargetRecorded ≡ true
    degenerateExclusionRecorded :
      degenerateTriadExclusionRecorded ≡ true
    outputStripRecorded :
      WhitneyCapOutputStripRelationRecorded ≡ true
    derivativeComputationStillFalse :
      PhiChartDerivativeComputed ≡ false
    quantitativeLowerBoundStillFalse :
      PhiQuantitativeJacobianLowerBoundProved ≡ false
    capUniformConstantsStillFalse :
      PhiCapUniformConstantsProved ≡ false
    degenerateBudgetStillFalse :
      degenerateTriadBudgetAbsorptionProved ≡ false
    theoremStillFalse :
      PhiJacobianLowerBoundTheoremProved ≡ false
    A4StillFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    clayStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalStillFalse :
      terminalPromotion ≡ false

canonicalNSPhiJacobianLowerBoundBoundary :
  NSPhiJacobianLowerBoundBoundary
canonicalNSPhiJacobianLowerBoundBoundary =
  record
    { importedSupport =
        canonicalImportedPhiJacobianSupport
    ; derivativeFormula =
        canonicalPhiDerivativeFormulaCarrier
    ; rankCarrier =
        canonicalPhiChartRankCarrier
    ; jacobianLowerBound =
        canonicalPhiJacobianLowerBoundCarrier
    ; degenerateTriadExclusion =
        canonicalDegenerateTriadExclusionCarrier
    ; budgetAbsorption =
        canonicalDegenerateTriadBudgetAbsorptionCarrier
    ; capUniformConstants =
        canonicalWhitneyCapUniformConstantCarrier
    ; outputStripRelation =
        canonicalOutputStripWidthRelationCarrier
    ; target =
        canonicalPhiJacobianLowerBoundTarget
    ; obligations =
        canonicalPhiJacobianObligations
    ; blockers =
        canonicalPhiJacobianBlockers
    ; statusRows =
        canonicalPhiJacobianStatusRows
    ; boundaryRecorded =
        refl
    ; derivativeRecorded =
        refl
    ; separationRecorded =
        refl
    ; rankTargetRecorded =
        refl
    ; degenerateExclusionRecorded =
        refl
    ; outputStripRecorded =
        refl
    ; derivativeComputationStillFalse =
        refl
    ; quantitativeLowerBoundStillFalse =
        refl
    ; capUniformConstantsStillFalse =
        refl
    ; degenerateBudgetStillFalse =
        refl
    ; theoremStillFalse =
        refl
    ; A4StillFalse =
        refl
    ; clayStillFalse =
        refl
    ; terminalStillFalse =
        refl
    }

