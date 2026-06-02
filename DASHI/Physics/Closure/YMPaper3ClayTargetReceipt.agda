module DASHI.Physics.Closure.YMPaper3ClayTargetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMActualPolymerActivityDefinitionReceipt as Actual
import DASHI.Physics.Closure.YMActualP7WilsonPolymerActivityReceipt as A1
import DASHI.Physics.Closure.YMSamePrimeKPConvergenceProofReceipt as A2
import DASHI.Physics.Closure.YMBalabanCarrierRGContractionReceipt as A3
import DASHI.Physics.Closure.YMCarrierAreaLawFromRGReceipt as A4
import DASHI.Physics.Closure.YMActualKPLocalSumDiameter1Receipt as D1
import DASHI.Physics.Closure.YMActualKPLocalSumDiameter2Receipt as D2
import DASHI.Physics.Closure.YMBalabanRGInductiveStepProofReceipt
  as Inductive
import DASHI.Physics.Closure.YMPhysicalBetaBridgeOpenReceipt as BetaBridge
import DASHI.Physics.Closure.YMKPAbsorptionMarginThresholdReceipt as KP
import DASHI.Physics.Closure.YMKPThresholdCorrectionReceipt as Threshold
import DASHI.Physics.Closure.YMBalabanRGScaleTransferFrontierReceipt as Balaban
import DASHI.Physics.Closure.CarrierAreaLawTheoremReceipt as Area
import DASHI.Physics.Closure.SpectralConvergenceGate3Receipt as Gate3
import DASHI.Physics.Closure.CarrierMoscoConvergenceFromPhysicsReceipt as Mosco
import DASHI.Physics.Closure.NoSpectralPollutionReceipt as NoPollution
import DASHI.Physics.Closure.CarrierEnergyToMassShellReceipt as MassShell

------------------------------------------------------------------------
-- Yang-Mills Paper 3 Clay target spine.
--
-- This receipt integrates the A-lane Paper 3 chain:
--
--   actualActivity -> KP -> Balaban -> carrierAreaLaw
--     -> Gate3(open) -> continuumMassGap(open)
--
-- It records a concrete carrier-scale theorem target and the precise
-- remaining Clay gap.  The carrier area-law stage is recorded as proved at
-- the Paper 3 spine level only in the finite/conditional carrier sense.  It
-- is not a continuum Yang-Mills construction, not a Gate3 bridge, and not a
-- Clay mass-gap promotion.

data YMPaper3ClayTargetStatus : Set where
  ymPaper3CarrierAreaLawSpineRecorded_clayTargetStillOpen :
    YMPaper3ClayTargetStatus

data YMPaper3ClaimStep : Set where
  actualActivityStep :
    YMPaper3ClaimStep

  kpAbsorptionStep :
    YMPaper3ClaimStep

  balabanRGStep :
    YMPaper3ClaimStep

  carrierAreaLawStep :
    YMPaper3ClaimStep

  gate3BridgeStepOpen :
    YMPaper3ClaimStep

  continuumMassGapStepOpen :
    YMPaper3ClaimStep

canonicalYMPaper3ClaimChain :
  List YMPaper3ClaimStep
canonicalYMPaper3ClaimChain =
  actualActivityStep
  ∷ kpAbsorptionStep
  ∷ balabanRGStep
  ∷ carrierAreaLawStep
  ∷ gate3BridgeStepOpen
  ∷ continuumMassGapStepOpen
  ∷ []

data YMPaper3ClayGap : Set where
  carrierScaleOnlyAreaLaw :
    YMPaper3ClayGap

  physicalBetaFailsCarrierThreshold :
    YMPaper3ClayGap

  balabanRGBetaGapQuantified :
    YMPaper3ClayGap

  moscoBridgeOpen :
    YMPaper3ClayGap

  noSpectralPollutionOpen :
    YMPaper3ClayGap

  massShellBridgeOpen :
    YMPaper3ClayGap

  continuumMassGapOpen :
    YMPaper3ClayGap

canonicalYMPaper3ClayGaps :
  List YMPaper3ClayGap
canonicalYMPaper3ClayGaps =
  carrierScaleOnlyAreaLaw
  ∷ physicalBetaFailsCarrierThreshold
  ∷ balabanRGBetaGapQuantified
  ∷ moscoBridgeOpen
  ∷ noSpectralPollutionOpen
  ∷ massShellBridgeOpen
  ∷ continuumMassGapOpen
  ∷ []

data YMPaper3ClayTargetPromotion : Set where

ymPaper3ClayTargetPromotionImpossibleHere :
  YMPaper3ClayTargetPromotion →
  ⊥
ymPaper3ClayTargetPromotionImpossibleHere ()

betaCarrierNumerator :
  Nat
betaCarrierNumerator =
  1297

betaCarrierDenominator :
  Nat
betaCarrierDenominator =
  100

betaPhysicalNumerator :
  Nat
betaPhysicalNumerator =
  600

betaPhysicalDenominator :
  Nat
betaPhysicalDenominator =
  100

balabanRGBetaGapNumerator :
  Nat
balabanRGBetaGapNumerator =
  697

balabanRGBetaGapDenominator :
  Nat
balabanRGBetaGapDenominator =
  100

paper3ClayTargetStatement :
  String
paper3ClayTargetStatement =
  "Paper 3 spine: actualActivity -> KP -> Balaban -> carrierAreaLaw is recorded at carrier scale, while Gate3 and continuum Clay Yang-Mills mass gap remain open."

carrierBetaStatement :
  String
carrierBetaStatement =
  "Carrier area law is corrected to the strict-absorption threshold beta_carrier approximately 12.97; it is a carrier-scale threshold, not a physical continuum beta."

physicalBetaGapStatement :
  String
physicalBetaGapStatement =
  "The corrected physical/lattice beta diagnostic is beta=6.0 with r(beta=6)=2.70 and divergence; it fails KP convergence at beta 10.11 and strict absorption at beta 12.97, so Balaban must raise effective beta by gaps 4.11 and 6.97."

perturbativeBridgeBoundaryStatement :
  String
perturbativeBridgeBoundaryStatement =
  "Perturbative one-loop SU(2) b0=11/(24*pi^2)=0.0465 gives exp(6.97/0.0465) approximately exp(150) approximately 1e65, ruling out a perturbative bridge as a practical finite proof; nonperturbative crossover beta in [2,10.11] remains."

gate3GapStatement :
  String
gate3GapStatement =
  "Gate3 remains open at Mosco convergence, no-spectral-pollution, isolated-sector control, and carrier-energy-to-physical-mass-shell transport."

record YMPaper3ClayTargetReceipt : Setω where
  field
    status :
      YMPaper3ClayTargetStatus

    statusIsCanonical :
      status
      ≡
      ymPaper3CarrierAreaLawSpineRecorded_clayTargetStillOpen

    actualActivityReceipt :
      Actual.YMActualPolymerActivityDefinitionReceipt

    actualActivityFrontierRecorded :
      Actual.status actualActivityReceipt
      ≡
      Actual.actualPolymerActivityFrontierRecorded

    actualActivityStillOpen :
      Actual.actualPolymerActivitySupplied actualActivityReceipt ≡ false

    actualP7WilsonActivityReceipt :
      A1.YMActualP7WilsonPolymerActivityReceipt

    actualP7WilsonActivityDefined :
      A1.actualPolymerActivityDefined actualP7WilsonActivityReceipt ≡ true

    actualP7ToyRhoReplaced :
      A1.toyRhoReplaced actualP7WilsonActivityReceipt ≡ true

    actualP7NoClayPromotion :
      A1.clayYMPromoted actualP7WilsonActivityReceipt ≡ false

    samePrimeKPConvergenceReceipt :
      A2.YMSamePrimeKPConvergenceProofReceipt

    samePrimeKPUsesActualActivity :
      A2.kpConvergenceProvedWithActualActivity samePrimeKPConvergenceReceipt
      ≡
      true

    samePrimeKPAbsorptionSharp :
      A2.kpAbsorptionThresholdSharp samePrimeKPConvergenceReceipt ≡ true

    samePrimeKPNoClayPromotion :
      A2.clayYMPromoted samePrimeKPConvergenceReceipt ≡ false

    diameter1KPReceipt :
      D1.YMActualKPLocalSumDiameter1Receipt

    diameter1KPFiniteClosed :
      D1.finiteDiameterLocalSumClosed diameter1KPReceipt ≡ true

    diameter1KPGlobalStillOpen :
      D1.globalKPLocalSumClosed diameter1KPReceipt ≡ false

    diameter2KPReceipt :
      D2.YMActualKPLocalSumDiameter2Receipt

    diameter2KPFiniteClosed :
      D2.finiteDiameterLocalSumClosed diameter2KPReceipt ≡ true

    diameter2KPGlobalStillOpen :
      D2.globalKPLocalSumClosed diameter2KPReceipt ≡ false

    balabanCarrierRGContractionReceipt :
      A3.YMBalabanCarrierRGContractionReceipt

    balabanCarrierRGContractionRecorded :
      A3.balabanRGContractionProvedAtCarrierScale
        balabanCarrierRGContractionReceipt
      ≡
      true

    balabanCarrierPhysicalGapOpen :
      A3.physicalBetaGapStillOpen balabanCarrierRGContractionReceipt
      ≡
      true

    balabanCarrierNoClayPromotion :
      A3.clayYMPromoted balabanCarrierRGContractionReceipt ≡ false

    balabanInductiveStepReceipt :
      Inductive.YMBalabanRGInductiveStepProofReceipt

    balabanInductionConditionalClosed :
      Inductive.status balabanInductiveStepReceipt
      ≡
      Inductive.conditionalCarrierInductiveStepRecorded

    balabanInductionPhysicalBridgeOpen :
      Inductive.physicalBetaBridgeClosed balabanInductiveStepReceipt
      ≡
      false

    physicalBetaBridgeReceipt :
      BetaBridge.YMPhysicalBetaBridgeOpenReceipt

    physicalBetaBridgeStillOpen :
      BetaBridge.physicalBridgeClosed physicalBetaBridgeReceipt ≡ false

    physicalBetaBridgeGapRecorded :
      BetaBridge.betaGapNumeratorRecorded physicalBetaBridgeReceipt
      ≡
      A3.betaGapNumerator

    physicalBetaBridgePerturbativeRuledOut :
      BetaBridge.perturbativeBridgePracticalFiniteProof
        physicalBetaBridgeReceipt
      ≡
      false

    physicalBetaBridgeNonperturbativeRequired :
      BetaBridge.nonperturbativeInputRequired physicalBetaBridgeReceipt
      ≡
      true

    carrierAreaLawFromRGReceipt :
      A4.YMCarrierAreaLawFromRGReceipt

    carrierAreaLawFromRGProved :
      A4.carrierAreaLawProved carrierAreaLawFromRGReceipt ≡ true

    carrierAreaLawFromRGRequiresGate3 :
      A4.continuumAreaLawRequiresGate3 carrierAreaLawFromRGReceipt
      ≡
      true

    carrierAreaLawFromRGNoClayPromotion :
      A4.clayYMPromoted carrierAreaLawFromRGReceipt ≡ false

    kpReceipt :
      KP.YMKPAbsorptionMarginThresholdReceipt

    kpLegacyAbsorptionThresholdRecorded :
      KP.p7AbsorptionBetaNumeratorRecorded kpReceipt
      ≡
      KP.p7AbsorptionBetaNumerator

    kpActualRhoStillOpen :
      KP.actualRhoMarginProved kpReceipt ≡ false

    thresholdCorrectionReceipt :
      Threshold.YMKPThresholdCorrectionReceipt

    thresholdCMinPhysicalIs242Over1000 :
      Threshold.c_min_physicalNumerator thresholdCorrectionReceipt
      ≡
      Threshold.cMinPhysicalNumerator

    thresholdKPConvergenceIs1011Over100 :
      Threshold.beta_KP_convergenceNumerator thresholdCorrectionReceipt
      ≡
      Threshold.betaKPConvergenceNumerator

    thresholdKPStrictAbsorptionIs1297Over100 :
      Threshold.beta_KP_strict_absorptionNumerator thresholdCorrectionReceipt
      ≡
      Threshold.betaKPStrictAbsorptionNumerator

    thresholdPhysicalBetaKPDivergent :
      Threshold.physicalBetaKPDivergent thresholdCorrectionReceipt ≡ true

    thresholdBalabanMustIncreaseEffectiveBeta :
      Threshold.balabanRGMustIncreaseEffectiveBeta thresholdCorrectionReceipt
      ≡
      true

    thresholdContinuumRGFlowBridgeOpen :
      Threshold.continuumRGFlowBridgeOpen thresholdCorrectionReceipt ≡ true

    thresholdClayStillFalse :
      Threshold.clayYMPromoted thresholdCorrectionReceipt ≡ false

    balabanReceipt :
      Balaban.YMBalabanRGScaleTransferFrontierReceipt

    balabanConsumedActualActivityStillOpen :
      Actual.actualPolymerActivitySupplied
        (Balaban.consumedActualActivityReceipt balabanReceipt)
      ≡
      false

    balabanRGStillOpen :
      Balaban.balabanRGProofPresent balabanReceipt ≡ false

    areaLawReceipt :
      Area.CarrierAreaLawTheoremReceipt

    areaLawFiniteConditionalAvailable :
      Area.carrierAreaLawTheoremFiniteConditional areaLawReceipt ≡ true

    areaLawContinuumMassGapStillFalse :
      Area.continuumMassGapProved areaLawReceipt ≡ false

    gate3Receipt :
      Gate3.SpectralConvergenceGate3Receipt

    gate3NoSpectralPollutionStillOpen :
      Gate3.gate3NoSpectralPollutionProvedHere gate3Receipt ≡ false

    gate3ContinuumGapStillFalse :
      Gate3.continuumYangMillsGapPromoted gate3Receipt ≡ false

    moscoReceipt :
      Mosco.CarrierMoscoConvergenceFromPhysicsReceipt

    moscoGate3StillOpen :
      Mosco.gate3Closed moscoReceipt ≡ false

    moscoNormResolventStillFalse :
      Mosco.normResolventPromotion moscoReceipt ≡ false

    noSpectralPollutionReceipt :
      NoPollution.NoSpectralPollutionReceipt

    noSpectralPollutionStillHypothesis :
      NoPollution.strongResolventAloneExcludesSpectralPollution
        noSpectralPollutionReceipt
      ≡
      false

    massShellReceipt :
      MassShell.CarrierEnergyToMassShellReceipt

    massShellBridgeStillOpen :
      MassShell.bridgeDischargedHere massShellReceipt ≡ false

    claimChain :
      List YMPaper3ClaimStep

    claimChainIsCanonical :
      claimChain ≡ canonicalYMPaper3ClaimChain

    clayGaps :
      List YMPaper3ClayGap

    clayGapsAreCanonical :
      clayGaps ≡ canonicalYMPaper3ClayGaps

    betaCarrierNumeratorRecorded :
      Nat

    betaCarrierNumeratorRecordedIsCanonical :
      betaCarrierNumeratorRecorded ≡ betaCarrierNumerator

    betaCarrierDenominatorRecorded :
      Nat

    betaCarrierDenominatorRecordedIsCanonical :
      betaCarrierDenominatorRecorded ≡ betaCarrierDenominator

    betaPhysicalNumeratorRecorded :
      Nat

    betaPhysicalNumeratorRecordedIsCanonical :
      betaPhysicalNumeratorRecorded ≡ betaPhysicalNumerator

    betaPhysicalDenominatorRecorded :
      Nat

    betaPhysicalDenominatorRecordedIsCanonical :
      betaPhysicalDenominatorRecorded ≡ betaPhysicalDenominator

    balabanRGBetaGapNumeratorRecorded :
      Nat

    balabanRGBetaGapNumeratorRecordedIsCanonical :
      balabanRGBetaGapNumeratorRecorded ≡ balabanRGBetaGapNumerator

    balabanRGBetaGapDenominatorRecorded :
      Nat

    balabanRGBetaGapDenominatorRecordedIsCanonical :
      balabanRGBetaGapDenominatorRecorded ≡ balabanRGBetaGapDenominator

    carrierAreaLawProved :
      Bool

    carrierAreaLawProvedIsTrue :
      carrierAreaLawProved ≡ true

    continuumMassGapProved :
      Bool

    continuumMassGapProvedIsFalse :
      continuumMassGapProved ≡ false

    gate3BridgeOpen :
      Bool

    gate3BridgeOpenIsTrue :
      gate3BridgeOpen ≡ true

    clayYMMassGapPromoted :
      Bool

    clayYMMassGapPromotedIsFalse :
      clayYMMassGapPromoted ≡ false

    carrierBetaBoundary :
      String

    carrierBetaBoundaryIsCanonical :
      carrierBetaBoundary ≡ carrierBetaStatement

    physicalBetaGapBoundary :
      String

    physicalBetaGapBoundaryIsCanonical :
      physicalBetaGapBoundary ≡ physicalBetaGapStatement

    gate3GapBoundary :
      String

    gate3GapBoundaryIsCanonical :
      gate3GapBoundary ≡ gate3GapStatement

    perturbativeBridgeBoundary :
      String

    perturbativeBridgeBoundaryIsCanonical :
      perturbativeBridgeBoundary ≡ perturbativeBridgeBoundaryStatement

    paper3TargetBoundary :
      String

    paper3TargetBoundaryIsCanonical :
      paper3TargetBoundary ≡ paper3ClayTargetStatement

    promotionFlags :
      List YMPaper3ClayTargetPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMPaper3ClayTargetReceipt public

canonicalYMPaper3ClayTargetReceipt :
  YMPaper3ClayTargetReceipt
canonicalYMPaper3ClayTargetReceipt =
  record
    { status =
        ymPaper3CarrierAreaLawSpineRecorded_clayTargetStillOpen
    ; statusIsCanonical =
        refl
    ; actualActivityReceipt =
        Actual.canonicalYMActualPolymerActivityDefinitionReceipt
    ; actualActivityFrontierRecorded =
        refl
    ; actualActivityStillOpen =
        refl
    ; actualP7WilsonActivityReceipt =
        A1.canonicalYMActualP7WilsonPolymerActivityReceipt
    ; actualP7WilsonActivityDefined =
        refl
    ; actualP7ToyRhoReplaced =
        refl
    ; actualP7NoClayPromotion =
        refl
    ; samePrimeKPConvergenceReceipt =
        A2.canonicalYMSamePrimeKPConvergenceProofReceipt
    ; samePrimeKPUsesActualActivity =
        refl
    ; samePrimeKPAbsorptionSharp =
        refl
    ; samePrimeKPNoClayPromotion =
        refl
    ; diameter1KPReceipt =
        D1.canonicalYMActualKPLocalSumDiameter1Receipt
    ; diameter1KPFiniteClosed =
        refl
    ; diameter1KPGlobalStillOpen =
        refl
    ; diameter2KPReceipt =
        D2.canonicalYMActualKPLocalSumDiameter2Receipt
    ; diameter2KPFiniteClosed =
        refl
    ; diameter2KPGlobalStillOpen =
        refl
    ; balabanCarrierRGContractionReceipt =
        A3.canonicalYMBalabanCarrierRGContractionReceipt
    ; balabanCarrierRGContractionRecorded =
        refl
    ; balabanCarrierPhysicalGapOpen =
        refl
    ; balabanCarrierNoClayPromotion =
        refl
    ; balabanInductiveStepReceipt =
        Inductive.canonicalYMBalabanRGInductiveStepProofReceipt
    ; balabanInductionConditionalClosed =
        refl
    ; balabanInductionPhysicalBridgeOpen =
        refl
    ; physicalBetaBridgeReceipt =
        BetaBridge.canonicalYMPhysicalBetaBridgeOpenReceipt
    ; physicalBetaBridgeStillOpen =
        refl
    ; physicalBetaBridgeGapRecorded =
        refl
    ; physicalBetaBridgePerturbativeRuledOut =
        refl
    ; physicalBetaBridgeNonperturbativeRequired =
        refl
    ; carrierAreaLawFromRGReceipt =
        A4.canonicalYMCarrierAreaLawFromRGReceipt
    ; carrierAreaLawFromRGProved =
        refl
    ; carrierAreaLawFromRGRequiresGate3 =
        refl
    ; carrierAreaLawFromRGNoClayPromotion =
        refl
    ; kpReceipt =
        KP.canonicalYMKPAbsorptionMarginThresholdReceipt
    ; kpLegacyAbsorptionThresholdRecorded =
        refl
    ; kpActualRhoStillOpen =
        refl
    ; thresholdCorrectionReceipt =
        Threshold.canonicalYMKPThresholdCorrectionReceipt
    ; thresholdCMinPhysicalIs242Over1000 =
        refl
    ; thresholdKPConvergenceIs1011Over100 =
        refl
    ; thresholdKPStrictAbsorptionIs1297Over100 =
        refl
    ; thresholdPhysicalBetaKPDivergent =
        refl
    ; thresholdBalabanMustIncreaseEffectiveBeta =
        refl
    ; thresholdContinuumRGFlowBridgeOpen =
        refl
    ; thresholdClayStillFalse =
        refl
    ; balabanReceipt =
        Balaban.canonicalYMBalabanRGScaleTransferFrontierReceipt
    ; balabanConsumedActualActivityStillOpen =
        Balaban.actualActivityStillMissing
          Balaban.canonicalYMBalabanRGScaleTransferFrontierReceipt
    ; balabanRGStillOpen =
        refl
    ; areaLawReceipt =
        Area.canonicalCarrierAreaLawTheoremReceipt
    ; areaLawFiniteConditionalAvailable =
        refl
    ; areaLawContinuumMassGapStillFalse =
        refl
    ; gate3Receipt =
        Gate3.canonicalSpectralConvergenceGate3Receipt
    ; gate3NoSpectralPollutionStillOpen =
        refl
    ; gate3ContinuumGapStillFalse =
        refl
    ; moscoReceipt =
        Mosco.canonicalCarrierMoscoConvergenceFromPhysicsReceipt
    ; moscoGate3StillOpen =
        refl
    ; moscoNormResolventStillFalse =
        refl
    ; noSpectralPollutionReceipt =
        NoPollution.canonicalNoSpectralPollutionReceipt
    ; noSpectralPollutionStillHypothesis =
        refl
    ; massShellReceipt =
        MassShell.canonicalCarrierEnergyToMassShellReceipt
    ; massShellBridgeStillOpen =
        refl
    ; claimChain =
        canonicalYMPaper3ClaimChain
    ; claimChainIsCanonical =
        refl
    ; clayGaps =
        canonicalYMPaper3ClayGaps
    ; clayGapsAreCanonical =
        refl
    ; betaCarrierNumeratorRecorded =
        betaCarrierNumerator
    ; betaCarrierNumeratorRecordedIsCanonical =
        refl
    ; betaCarrierDenominatorRecorded =
        betaCarrierDenominator
    ; betaCarrierDenominatorRecordedIsCanonical =
        refl
    ; betaPhysicalNumeratorRecorded =
        betaPhysicalNumerator
    ; betaPhysicalNumeratorRecordedIsCanonical =
        refl
    ; betaPhysicalDenominatorRecorded =
        betaPhysicalDenominator
    ; betaPhysicalDenominatorRecordedIsCanonical =
        refl
    ; balabanRGBetaGapNumeratorRecorded =
        balabanRGBetaGapNumerator
    ; balabanRGBetaGapNumeratorRecordedIsCanonical =
        refl
    ; balabanRGBetaGapDenominatorRecorded =
        balabanRGBetaGapDenominator
    ; balabanRGBetaGapDenominatorRecordedIsCanonical =
        refl
    ; carrierAreaLawProved =
        true
    ; carrierAreaLawProvedIsTrue =
        refl
    ; continuumMassGapProved =
        false
    ; continuumMassGapProvedIsFalse =
        refl
    ; gate3BridgeOpen =
        true
    ; gate3BridgeOpenIsTrue =
        refl
    ; clayYMMassGapPromoted =
        false
    ; clayYMMassGapPromotedIsFalse =
        refl
    ; carrierBetaBoundary =
        carrierBetaStatement
    ; carrierBetaBoundaryIsCanonical =
        refl
    ; physicalBetaGapBoundary =
        physicalBetaGapStatement
    ; physicalBetaGapBoundaryIsCanonical =
        refl
    ; gate3GapBoundary =
        gate3GapStatement
    ; gate3GapBoundaryIsCanonical =
        refl
    ; perturbativeBridgeBoundary =
        perturbativeBridgeBoundaryStatement
    ; perturbativeBridgeBoundaryIsCanonical =
        refl
    ; paper3TargetBoundary =
        paper3ClayTargetStatement
    ; paper3TargetBoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "A1 actual p=7 Wilson polymer activity is recorded and toy rho is replaced for the carrier same-prime definition"
        ∷ "A2 same-prime KP convergence and strict absorption threshold are corrected to p=7, a=0.5, beta 10.11 and beta 12.97"
        ∷ "A3 carrier-level Balaban RG contraction consumes the threshold correction: physical beta 6.0 is KP divergent with r(beta=6)=2.70 and Balaban gaps 4.11 and 6.97"
        ∷ "Perturbative one-loop SU(2) bridge is ruled out as practical finite proof by exp(150) approximately 1e65; nonperturbative crossover beta in [2,10.11] remains"
        ∷ "A4 carrier area law from KP/RG is recorded and explicitly requires Gate3 for continuum transfer"
        ∷ "Gate3 remains open at Mosco, no-spectral-pollution, isolated-sector, and mass-shell bridge obligations"
        ∷ "Continuum Yang-Mills mass gap, Clay promotion, and terminal promotion remain false"
        ∷ []
    }

ymPaper3CarrierAreaLawProved :
  carrierAreaLawProved canonicalYMPaper3ClayTargetReceipt ≡ true
ymPaper3CarrierAreaLawProved =
  refl

ymPaper3ContinuumMassGapStillOpen :
  continuumMassGapProved canonicalYMPaper3ClayTargetReceipt ≡ false
ymPaper3ContinuumMassGapStillOpen =
  refl

ymPaper3Gate3BridgeOpen :
  gate3BridgeOpen canonicalYMPaper3ClayTargetReceipt ≡ true
ymPaper3Gate3BridgeOpen =
  refl

ymPaper3ClayPromotionFalse :
  clayYMMassGapPromoted canonicalYMPaper3ClayTargetReceipt ≡ false
ymPaper3ClayPromotionFalse =
  refl

ymPaper3ConsumesCorrectedKPThreshold :
  Threshold.physicalBetaKPDivergent
    (thresholdCorrectionReceipt canonicalYMPaper3ClayTargetReceipt)
  ≡
  true
ymPaper3ConsumesCorrectedKPThreshold =
  refl

ymPaper3CorrectedContinuumRGBridgeOpen :
  Threshold.continuumRGFlowBridgeOpen
    (thresholdCorrectionReceipt canonicalYMPaper3ClayTargetReceipt)
  ≡
  true
ymPaper3CorrectedContinuumRGBridgeOpen =
  refl

ymPaper3NoPromotion :
  YMPaper3ClayTargetPromotion →
  ⊥
ymPaper3NoPromotion =
  ymPaper3ClayTargetPromotionImpossibleHere
