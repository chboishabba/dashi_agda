module DASHI.Physics.Closure.Gate3ScaleGraphBarrierInstantiationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierMoscoConvergenceFromPhysicsReceipt
  as Mosco
import DASHI.Physics.Closure.DangerScaleEdgeConservationReceipt as Edge
import DASHI.Physics.Closure.Gate3NormDictionaryReceipt as Norm
import DASHI.Physics.Closure.Gate3FiniteCutoffFrameLowerBoundProofReceipt
  as FiniteFrame
import DASHI.Physics.Closure.Gate3UniformLowerBoundObstructionReceipt
  as UniformBound
import DASHI.Physics.Closure.Gate3MoscoConstructiveSequenceReceipt
  as ConstructiveMosco
import DASHI.Physics.Closure.Gate3NoSpectralPollutionConditionalProofReceipt
  as ConditionalNoPollution
import DASHI.Physics.Closure.Gate3PAWOTGConcreteConditionReceipt as PAWOTG
import DASHI.Physics.Closure.NoSpectralPollutionReceipt as NSP
import DASHI.Physics.Closure.ScaleGraphBarrierTargetReceipt as Barrier
import DASHI.Physics.Closure.SpectralConvergenceGate3Receipt as Spectral
import DASHI.Physics.Closure.UniversalScaleGraphBarrierTargetReceipt
  as Universal

------------------------------------------------------------------------
-- Gate 3 scale-graph barrier instantiation receipt.
--
-- This receipt specializes the universal scale-graph barrier target to the
-- Gate 3 cutoff/refinement lane.  It records the intended node readings and
-- prerequisite links only.  It does not prove the barrier, does not close
-- Gate 3, and does not promote Clay.

data Gate3ScaleGraphBarrierStatus : Set where
  gate3ScaleGraphBarrierInstantiated_failClosed :
    Gate3ScaleGraphBarrierStatus

data Gate3ScaleNode : Set where
  cutoffLevelN :
    Gate3ScaleNode

data Gate3ScaleQuantity : Set where
  residualUncapturedNormDefect :
    Gate3ScaleQuantity

  productionNewProjectionRefinementError :
    Gate3ScaleQuantity

  absorptionFrameMoscoRecoveryStrength :
    Gate3ScaleQuantity

  qNDefectFrameRatio :
    Gate3ScaleQuantity

canonicalGate3ScaleQuantities :
  List Gate3ScaleQuantity
canonicalGate3ScaleQuantities =
  residualUncapturedNormDefect
  ∷ productionNewProjectionRefinementError
  ∷ absorptionFrameMoscoRecoveryStrength
  ∷ qNDefectFrameRatio
  ∷ []

data Gate3BarrierPrerequisite : Set where
  normDictionaryBindingPrerequisite :
    Gate3BarrierPrerequisite

  finiteCutoffFrameBoundPrerequisite :
    Gate3BarrierPrerequisite

  carrierMoscoRecoveryPrerequisite :
    Gate3BarrierPrerequisite

  noSpectralPollutionPrerequisite :
    Gate3BarrierPrerequisite

  concretePAWOTGSeparationPrerequisite :
    Gate3BarrierPrerequisite

  edgeConservationPrerequisite :
    Gate3BarrierPrerequisite

  universalBarrierComparisonPrerequisite :
    Gate3BarrierPrerequisite

canonicalGate3BarrierPrerequisites :
  List Gate3BarrierPrerequisite
canonicalGate3BarrierPrerequisites =
  normDictionaryBindingPrerequisite
  ∷ finiteCutoffFrameBoundPrerequisite
  ∷ carrierMoscoRecoveryPrerequisite
  ∷ noSpectralPollutionPrerequisite
  ∷ concretePAWOTGSeparationPrerequisite
  ∷ edgeConservationPrerequisite
  ∷ universalBarrierComparisonPrerequisite
  ∷ []

data Gate3BarrierBoundary : Set where
  boundaryNormBindingsStillOpen :
    Gate3BarrierBoundary

  boundaryMoscoRecoveryStillFormalObligation :
    Gate3BarrierBoundary

  boundaryNoSpectralPollutionStillHypothesis :
    Gate3BarrierBoundary

  boundaryGate3EdgeAccountingStillOpen :
    Gate3BarrierBoundary

  boundaryPAWOTGCoherenceStillBlocksClosure :
    Gate3BarrierBoundary

  boundaryClayPromotionBlocked :
    Gate3BarrierBoundary

canonicalGate3BarrierBoundaries :
  List Gate3BarrierBoundary
canonicalGate3BarrierBoundaries =
  boundaryNormBindingsStillOpen
  ∷ boundaryMoscoRecoveryStillFormalObligation
  ∷ boundaryNoSpectralPollutionStillHypothesis
  ∷ boundaryGate3EdgeAccountingStillOpen
  ∷ boundaryPAWOTGCoherenceStillBlocksClosure
  ∷ boundaryClayPromotionBlocked
  ∷ []

data Gate3ScaleGraphBarrierPromotion : Set where

gate3ScaleGraphBarrierPromotionImpossibleHere :
  Gate3ScaleGraphBarrierPromotion →
  ⊥
gate3ScaleGraphBarrierPromotionImpossibleHere ()

gate3BarrierInstantiationStatement : String
gate3BarrierInstantiationStatement =
  "Gate3 instantiates the scale-graph nodes as cutoff levels N: residual R_N is uncaptured norm defect, production P_N is new projection/refinement error, absorption A_N is frame/Mosco recovery strength, and q_N is the defect/frame ratio."

gate3BarrierBoundaryStatement : String
gate3BarrierBoundaryStatement =
  "This receipt links Gate3 to the universal barrier target, norm dictionary, concrete PAWOTG sigma<0.505 condition, Mosco recovery, no-spectral-pollution, and danger-edge accounting prerequisites only; the barrier and Gate3 closure remain unproved."

record Gate3ScaleGraphBarrierInstantiationReceipt : Setω where
  field
    status :
      Gate3ScaleGraphBarrierStatus

    statusIsFailClosed :
      status ≡ gate3ScaleGraphBarrierInstantiated_failClosed

    scaleGraphBarrierReceipt :
      Barrier.ScaleGraphBarrierTargetReceipt

    scaleGraphBarrierStillTarget :
      Barrier.comparisonPrincipleProvedHere scaleGraphBarrierReceipt
      ≡
      false

    scaleGraphBarrierNoClay :
      Barrier.clayPromotion scaleGraphBarrierReceipt ≡ false

    universalBarrierReceipt :
      Universal.UniversalScaleGraphBarrierTargetReceipt

    universalBarrierStillTarget :
      Universal.barrierTheoremProvedHere universalBarrierReceipt ≡ false

    universalBarrierGate3TransferOpen :
      Universal.gate3TransferProved universalBarrierReceipt ≡ false

    edgeConservationReceipt :
      Edge.DangerScaleEdgeConservationReceipt

    edgeConservationStillOpen :
      Edge.edgeConservationProvedHere edgeConservationReceipt ≡ false

    gate3EdgeClosureStillFalse :
      Edge.gate3ClosurePromoted edgeConservationReceipt ≡ false

    normDictionaryReceipt :
      Norm.Gate3NormDictionaryReceipt

    normBindingsStillOpen :
      Norm.normBindingsProved normDictionaryReceipt ≡ false

    finiteCutoffFrameRecorded :
      Norm.finiteCutoffHNFrameBoundANPositiveRecorded
        normDictionaryReceipt
      ≡
      true

    finiteFrameProofReceipt :
      FiniteFrame.Gate3FiniteCutoffFrameLowerBoundProofReceipt

    finiteFrameANPositive :
      FiniteFrame.finiteLowerBoundANPositiveRecorded finiteFrameProofReceipt
      ≡
      true

    finiteFrameNotUniform :
      FiniteFrame.finiteLowerBoundANUniformInN finiteFrameProofReceipt
      ≡
      false

    uniformLowerBoundObstructionReceipt :
      UniformBound.Gate3UniformLowerBoundObstructionReceipt

    uniformLowerBoundStillFalse :
      UniformBound.uniformAOnInfiniteH uniformLowerBoundObstructionReceipt
      ≡
      false

    pawotgCoherenceStillOpen :
      Norm.sig15StableCoherenceProved normDictionaryReceipt ≡ false

    pawotgConcreteConditionReceipt :
      PAWOTG.Gate3PAWOTGConcreteConditionReceipt

    pawotgSigmaCritP3Is505 :
      PAWOTG.sigmaCritP3 pawotgConcreteConditionReceipt
      ≡
      PAWOTG.sigmaCritP3Milli

    pawotgUniformityStillOpen :
      PAWOTG.pawotgUniformityOpen pawotgConcreteConditionReceipt
      ≡
      true

    pawotgNoClayPromotion :
      PAWOTG.clayGate3Promoted pawotgConcreteConditionReceipt
      ≡
      false

    moscoReceipt :
      Mosco.CarrierMoscoConvergenceFromPhysicsReceipt

    moscoRecoveryMotivated :
      Mosco.recoveryUpperBoundMotivated moscoReceipt ≡ true

    moscoRecoveryNotProvedHere :
      Mosco.recoveryUpperBoundProvedHere moscoReceipt ≡ false

    moscoFormalProofRequired :
      Mosco.formalProofRequired moscoReceipt ≡ true

    constructiveMoscoReceipt :
      ConstructiveMosco.Gate3MoscoConstructiveSequenceReceipt

    moscoConditionIStillOpen :
      ConstructiveMosco.moscoConditionIConstructed constructiveMoscoReceipt
      ≡
      false

    moscoPAWOTGStillOpen :
      ConstructiveMosco.pawotgTransferForConditionI constructiveMoscoReceipt
      ≡
      false

    noSpectralPollutionReceipt :
      NSP.NoSpectralPollutionReceipt

    noSpectralPollutionRecordedAsHypothesis :
      NSP.noSpectralPollutionRecordedAsHypothesis
        noSpectralPollutionReceipt
      ≡
      true

    strongResolventAloneStillInsufficient :
      NSP.strongResolventAloneExcludesSpectralPollution
        noSpectralPollutionReceipt
      ≡
      false

    conditionalNoPollutionReceipt :
      ConditionalNoPollution.Gate3NoSpectralPollutionConditionalProofReceipt

    unconditionalNoPollutionStillFalse :
      ConditionalNoPollution.unconditionalNoSpectralPollutionProved
        conditionalNoPollutionReceipt
      ≡
      false

    spectralGate3Receipt :
      Spectral.SpectralConvergenceGate3Receipt

    gate3NoSpectralPollutionRequired :
      Spectral.gate3NoSpectralPollutionRequired spectralGate3Receipt
      ≡
      true

    gate3NoSpectralPollutionProvedHere :
      Spectral.gate3NoSpectralPollutionProvedHere spectralGate3Receipt
      ≡
      true

    nodes :
      Gate3ScaleNode

    nodesAreCutoffLevelsN :
      nodes ≡ cutoffLevelN

    quantities :
      List Gate3ScaleQuantity

    quantitiesAreCanonical :
      quantities ≡ canonicalGate3ScaleQuantities

    prerequisites :
      List Gate3BarrierPrerequisite

    prerequisitesAreCanonical :
      prerequisites ≡ canonicalGate3BarrierPrerequisites

    boundaries :
      List Gate3BarrierBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalGate3BarrierBoundaries

    gate3BarrierInstantiated :
      Bool

    gate3BarrierInstantiatedIsTrue :
      gate3BarrierInstantiated ≡ true

    gate3BarrierProved :
      Bool

    gate3BarrierProvedIsFalse :
      gate3BarrierProved ≡ false

    pawotgBlocks :
      Bool

    pawotgBlocksIsTrue :
      pawotgBlocks ≡ true

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ gate3BarrierInstantiationStatement

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ gate3BarrierBoundaryStatement

    promotions :
      List Gate3ScaleGraphBarrierPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Gate3ScaleGraphBarrierPromotion →
      ⊥

open Gate3ScaleGraphBarrierInstantiationReceipt public

canonicalGate3ScaleGraphBarrierInstantiationReceipt :
  Gate3ScaleGraphBarrierInstantiationReceipt
canonicalGate3ScaleGraphBarrierInstantiationReceipt =
  record
    { status =
        gate3ScaleGraphBarrierInstantiated_failClosed
    ; statusIsFailClosed =
        refl
    ; scaleGraphBarrierReceipt =
        Barrier.canonicalScaleGraphBarrierTargetReceipt
    ; scaleGraphBarrierStillTarget =
        refl
    ; scaleGraphBarrierNoClay =
        refl
    ; universalBarrierReceipt =
        Universal.canonicalUniversalScaleGraphBarrierTargetReceipt
    ; universalBarrierStillTarget =
        refl
    ; universalBarrierGate3TransferOpen =
        refl
    ; edgeConservationReceipt =
        Edge.canonicalDangerScaleEdgeConservationReceipt
    ; edgeConservationStillOpen =
        refl
    ; gate3EdgeClosureStillFalse =
        refl
    ; normDictionaryReceipt =
        Norm.canonicalGate3NormDictionaryReceipt
    ; normBindingsStillOpen =
        refl
    ; finiteCutoffFrameRecorded =
        refl
    ; finiteFrameProofReceipt =
        FiniteFrame.canonicalGate3FiniteCutoffFrameLowerBoundProofReceipt
    ; finiteFrameANPositive =
        refl
    ; finiteFrameNotUniform =
        refl
    ; uniformLowerBoundObstructionReceipt =
        UniformBound.canonicalGate3UniformLowerBoundObstructionReceipt
    ; uniformLowerBoundStillFalse =
        refl
    ; pawotgCoherenceStillOpen =
        refl
    ; pawotgConcreteConditionReceipt =
        PAWOTG.canonicalGate3PAWOTGConcreteConditionReceipt
    ; pawotgSigmaCritP3Is505 =
        refl
    ; pawotgUniformityStillOpen =
        refl
    ; pawotgNoClayPromotion =
        refl
    ; moscoReceipt =
        Mosco.canonicalCarrierMoscoConvergenceFromPhysicsReceipt
    ; moscoRecoveryMotivated =
        refl
    ; moscoRecoveryNotProvedHere =
        refl
    ; moscoFormalProofRequired =
        refl
    ; constructiveMoscoReceipt =
        ConstructiveMosco.canonicalGate3MoscoConstructiveSequenceReceipt
    ; moscoConditionIStillOpen =
        refl
    ; moscoPAWOTGStillOpen =
        refl
    ; noSpectralPollutionReceipt =
        NSP.canonicalNoSpectralPollutionReceipt
    ; noSpectralPollutionRecordedAsHypothesis =
        refl
    ; strongResolventAloneStillInsufficient =
        refl
    ; conditionalNoPollutionReceipt =
        ConditionalNoPollution.canonicalGate3NoSpectralPollutionConditionalProofReceipt
    ; unconditionalNoPollutionStillFalse =
        refl
    ; spectralGate3Receipt =
        Spectral.canonicalSpectralConvergenceGate3Receipt
    ; gate3NoSpectralPollutionRequired =
        refl
    ; gate3NoSpectralPollutionProvedHere =
        refl
    ; nodes =
        cutoffLevelN
    ; nodesAreCutoffLevelsN =
        refl
    ; quantities =
        canonicalGate3ScaleQuantities
    ; quantitiesAreCanonical =
        refl
    ; prerequisites =
        canonicalGate3BarrierPrerequisites
    ; prerequisitesAreCanonical =
        refl
    ; boundaries =
        canonicalGate3BarrierBoundaries
    ; boundariesAreCanonical =
        refl
    ; gate3BarrierInstantiated =
        true
    ; gate3BarrierInstantiatedIsTrue =
        refl
    ; gate3BarrierProved =
        false
    ; gate3BarrierProvedIsFalse =
        refl
    ; pawotgBlocks =
        true
    ; pawotgBlocksIsTrue =
        refl
    ; gate3Closed =
        false
    ; gate3ClosedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; statement =
        gate3BarrierInstantiationStatement
    ; statementIsCanonical =
        refl
    ; boundaryStatement =
        gate3BarrierBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        gate3ScaleGraphBarrierPromotionImpossibleHere
    }

canonicalGate3BarrierInstantiated :
  gate3BarrierInstantiated
    canonicalGate3ScaleGraphBarrierInstantiationReceipt
  ≡
  true
canonicalGate3BarrierInstantiated =
  refl

canonicalGate3BarrierNotProved :
  gate3BarrierProved canonicalGate3ScaleGraphBarrierInstantiationReceipt
  ≡
  false
canonicalGate3BarrierNotProved =
  refl

canonicalGate3PAWOTGBlocks :
  pawotgBlocks canonicalGate3ScaleGraphBarrierInstantiationReceipt ≡ true
canonicalGate3PAWOTGBlocks =
  refl

canonicalGate3NotClosed :
  gate3Closed canonicalGate3ScaleGraphBarrierInstantiationReceipt ≡ false
canonicalGate3NotClosed =
  refl

canonicalGate3NoClayPromotion :
  clayPromotion canonicalGate3ScaleGraphBarrierInstantiationReceipt ≡ false
canonicalGate3NoClayPromotion =
  refl
