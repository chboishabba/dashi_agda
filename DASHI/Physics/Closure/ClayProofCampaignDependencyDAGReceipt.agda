module DASHI.Physics.Closure.ClayProofCampaignDependencyDAGReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayOptimalPathRequisiteLemmaReceipt
  as Optimal
import DASHI.Physics.Closure.Gate3PhaseCompletenessReductionReceipt
  as Gate3Phase
import DASHI.Physics.Closure.MonsterOggPrimeCorrectionReceipt
  as MonsterOgg
import DASHI.Physics.Closure.YMT7RademacherActivityIdentificationReceipt
  as T7Audit

------------------------------------------------------------------------
-- Clay proof campaign dependency DAG receipt.
--
-- This receipt records the larger dependency graph for the next proof
-- campaign round.  Every dependency node is a theorem target or external
-- authority target unless it is explicitly consumed from an existing receipt.
-- It also records the CM arithmetic correction:
--
--   Q(sqrt(-7)) split/inert/ramified table over SSP primes is 5 + 9 + 1.
--   DASHI 7 + 7 + 1 is semantic atom/frame grammar, not that CM table.
--   p71 is split in Q(sqrt(-7)); do not reintroduce p71-as-inert.

data ClayProofCampaignDAGStatus : Set where
  proofCampaignDAGRecorded_workersAssigned_failClosed :
    ClayProofCampaignDAGStatus

data CMSSPPrimeClass : Set where
  cmSplit :
    CMSSPPrimeClass

  cmInert :
    CMSSPPrimeClass

  cmRamified :
    CMSSPPrimeClass

data SSPPrime : Set where
  p2 p3 p5 p7 p11 p13 p17 p19 p23 p29 p31 p41 p47 p59 p71 :
    SSPPrime

cmClassOf : SSPPrime → CMSSPPrimeClass
cmClassOf p2 = cmSplit
cmClassOf p3 = cmInert
cmClassOf p5 = cmInert
cmClassOf p7 = cmRamified
cmClassOf p11 = cmSplit
cmClassOf p13 = cmInert
cmClassOf p17 = cmInert
cmClassOf p19 = cmInert
cmClassOf p23 = cmSplit
cmClassOf p29 = cmSplit
cmClassOf p31 = cmInert
cmClassOf p41 = cmInert
cmClassOf p47 = cmInert
cmClassOf p59 = cmInert
cmClassOf p71 = cmSplit

cmSplitSSPPrimes : List SSPPrime
cmSplitSSPPrimes =
  p2 ∷ p11 ∷ p23 ∷ p29 ∷ p71 ∷ []

cmInertSSPPrimes : List SSPPrime
cmInertSSPPrimes =
  p3 ∷ p5 ∷ p13 ∷ p17 ∷ p19 ∷ p31 ∷ p41 ∷ p47 ∷ p59 ∷ []

cmRamifiedSSPPrimes : List SSPPrime
cmRamifiedSSPPrimes =
  p7 ∷ []

splitCount : Nat
splitCount =
  5

inertCount : Nat
inertCount =
  9

ramifiedCount : Nat
ramifiedCount =
  1

semanticSevenSevenOneAtomGrammarCount : Nat
semanticSevenSevenOneAtomGrammarCount =
  15

data DependencyNode : Set where
  receiptNonPromotionInvariant :
    DependencyNode

  finiteComputationToTheoremBoundary :
    DependencyNode

  externalAuthorityNoFabrication :
    DependencyNode

  t7CoefficientAbsoluteEnvelope :
    DependencyNode

  t7TwiningPhaseCoherence :
    DependencyNode

  t7ActivityIdentification :
    DependencyNode

  polymerMultiplicityCompression :
    DependencyNode

  localPolymerClusterCompatibility :
    DependencyNode

  dashiPolymerTreeGraphBound :
    DependencyNode

  polymerDepthSizeEquivalence :
    DependencyNode

  gaugeOrbitQuotientKPSafe :
    DependencyNode

  wilsonActionToPolymerActivity :
    DependencyNode

  strongCouplingRemainderBound :
    DependencyNode

  balabanBlockVariableCompatibility :
    DependencyNode

  balabanReblockingIdentity :
    DependencyNode

  irrelevantModeContraction :
    DependencyNode

  relevantModeStability :
    DependencyNode

  effectiveBetaMonotoneUnderRG :
    DependencyNode

  betaReachesSafeThreshold :
    DependencyNode

  betaThresholdUniformInLatticeSpacing :
    DependencyNode

  reflectionPositivityUnderBlockSpin :
    DependencyNode

  brstGaugeFixingPhysicalPositivity :
    DependencyNode

  ymInfiniteVolumeTightness :
    DependencyNode

  massGapPreservedInInfiniteVolume :
    DependencyNode

  massGapPreservedInContinuumLimit :
    DependencyNode

  continuumYMNontriviality :
    DependencyNode

  nonFlatPlaquetteCurvature :
    DependencyNode

  fieldStrengthFibreRepresentation :
    DependencyNode

  compactKillingTracePositive :
    DependencyNode

  killingAdInvariance :
    DependencyNode

  covariantExteriorDerivative :
    DependencyNode

  bianchiFromJacobi :
    DependencyNode

  discreteHodgeStar :
    DependencyNode

  discreteVariationIBP :
    DependencyNode

  currentSourceCoupling :
    DependencyNode

  fieldEquationsDoNotImplyMassGap :
    DependencyNode

  cmTableAtomGrammarSeparation :
    DependencyNode

  phaseBlindInertFrameCollapse :
    DependencyNode

  semanticMirrorB7PhaseNecessity :
    DependencyNode

  crossSectorOverlapCriterion :
    DependencyNode

  oneDOrthogonalSectorNoGo :
    DependencyNode

  threeDArchimedeanSectorOverlap :
    DependencyNode

  phaseCompletionStrictlyImprovesFrameBound :
    DependencyNode

  frameBoundFactorisation :
    DependencyNode

  uniformFrameBoundFromFactors :
    DependencyNode

  moscoLiminf :
    DependencyNode

  moscoRecovery :
    DependencyNode

  normResolventConvergence :
    DependencyNode

  noSpectralPollution :
    DependencyNode

  isolatedMassShellPersistence :
    DependencyNode

  physicalSSPHeckeEmbeddingSpread :
    DependencyNode

  candidate256PhysicalCalibration :
    DependencyNode

  waldCoefficientSelection :
    DependencyNode

  stressEnergyConservation :
    DependencyNode

  schwarzschildWeakFieldMatchNode :
    DependencyNode

  hMinusHalfObstructionUniversality :
    DependencyNode

  localTailBoundStrategyFails :
    DependencyNode

  obstructionNotBlowup :
    DependencyNode

  shellEnergyFluxIdentity :
    DependencyNode

  fluxLocality :
    DependencyNode

  dangerShellDissipationDominance :
    DependencyNode

  kStarNoInertialDrift :
    DependencyNode

  h118BoundFromBandPressure :
    DependencyNode

  nsContinuationCriterion :
    DependencyNode

  carrierStructuredDenseInSmoothDivergenceFree :
    DependencyNode

  oggPrimeSupportNotClassPartition :
    DependencyNode

  rademacherDoesNotIdentifyPolymerActivity :
    DependencyNode

  characterCancellationRequiresPhaseLock :
    DependencyNode

  empiricalContactNoClayPromotion :
    DependencyNode

data MissingDAGTarget : DependencyNode → Set where

ymActivityDAG : List DependencyNode
ymActivityDAG =
  t7CoefficientAbsoluteEnvelope
  ∷ t7TwiningPhaseCoherence
  ∷ t7ActivityIdentification
  ∷ polymerMultiplicityCompression
  ∷ polymerDepthSizeEquivalence
  ∷ dashiPolymerTreeGraphBound
  ∷ []

ymBalabanDAG : List DependencyNode
ymBalabanDAG =
  localPolymerClusterCompatibility
  ∷ gaugeOrbitQuotientKPSafe
  ∷ wilsonActionToPolymerActivity
  ∷ strongCouplingRemainderBound
  ∷ balabanBlockVariableCompatibility
  ∷ balabanReblockingIdentity
  ∷ irrelevantModeContraction
  ∷ relevantModeStability
  ∷ effectiveBetaMonotoneUnderRG
  ∷ betaReachesSafeThreshold
  ∷ betaThresholdUniformInLatticeSpacing
  ∷ []

ymOSGeometryDAG : List DependencyNode
ymOSGeometryDAG =
  reflectionPositivityUnderBlockSpin
  ∷ brstGaugeFixingPhysicalPositivity
  ∷ ymInfiniteVolumeTightness
  ∷ massGapPreservedInInfiniteVolume
  ∷ massGapPreservedInContinuumLimit
  ∷ continuumYMNontriviality
  ∷ nonFlatPlaquetteCurvature
  ∷ fieldStrengthFibreRepresentation
  ∷ compactKillingTracePositive
  ∷ killingAdInvariance
  ∷ covariantExteriorDerivative
  ∷ bianchiFromJacobi
  ∷ discreteHodgeStar
  ∷ discreteVariationIBP
  ∷ currentSourceCoupling
  ∷ fieldEquationsDoNotImplyMassGap
  ∷ []

nsDAG : List DependencyNode
nsDAG =
  hMinusHalfObstructionUniversality
  ∷ localTailBoundStrategyFails
  ∷ obstructionNotBlowup
  ∷ shellEnergyFluxIdentity
  ∷ fluxLocality
  ∷ dangerShellDissipationDominance
  ∷ kStarNoInertialDrift
  ∷ h118BoundFromBandPressure
  ∷ nsContinuationCriterion
  ∷ carrierStructuredDenseInSmoothDivergenceFree
  ∷ []

gate3W4GRDAG : List DependencyNode
gate3W4GRDAG =
  cmTableAtomGrammarSeparation
  ∷ phaseBlindInertFrameCollapse
  ∷ semanticMirrorB7PhaseNecessity
  ∷ crossSectorOverlapCriterion
  ∷ oneDOrthogonalSectorNoGo
  ∷ threeDArchimedeanSectorOverlap
  ∷ phaseCompletionStrictlyImprovesFrameBound
  ∷ frameBoundFactorisation
  ∷ uniformFrameBoundFromFactors
  ∷ moscoLiminf
  ∷ moscoRecovery
  ∷ normResolventConvergence
  ∷ noSpectralPollution
  ∷ isolatedMassShellPersistence
  ∷ physicalSSPHeckeEmbeddingSpread
  ∷ candidate256PhysicalCalibration
  ∷ waldCoefficientSelection
  ∷ stressEnergyConservation
  ∷ schwarzschildWeakFieldMatchNode
  ∷ []

governanceDAG : List DependencyNode
governanceDAG =
  receiptNonPromotionInvariant
  ∷ finiteComputationToTheoremBoundary
  ∷ externalAuthorityNoFabrication
  ∷ oggPrimeSupportNotClassPartition
  ∷ rademacherDoesNotIdentifyPolymerActivity
  ∷ characterCancellationRequiresPhaseLock
  ∷ empiricalContactNoClayPromotion
  ∷ []

data CampaignWorker : Set where
  worker1YMActivity :
    CampaignWorker

  worker2YMBalaban :
    CampaignWorker

  worker3YMOSGeometry :
    CampaignWorker

  worker4NavierStokes :
    CampaignWorker

  worker5Gate3W4GR :
    CampaignWorker

  worker6Governance :
    CampaignWorker

canonicalCampaignWorkers : List CampaignWorker
canonicalCampaignWorkers =
  worker1YMActivity
  ∷ worker2YMBalaban
  ∷ worker3YMOSGeometry
  ∷ worker4NavierStokes
  ∷ worker5Gate3W4GR
  ∷ worker6Governance
  ∷ []

data DAGPromotion : Set where

dagPromotionImpossibleHere :
  DAGPromotion →
  ⊥
dagPromotionImpossibleHere ()

cmGuardText : String
cmGuardText =
  "Literal Q(sqrt(-7)) splitting over the SSP primes is 5+9+1: split {2,11,23,29,71}, inert {3,5,13,17,19,31,41,47,59}, ramified {7}.  Semantic 7+7+1 atom/frame grammar is separate; p71 is split, not inert."

dagBoundaryText : String
dagBoundaryText =
  "This DAG records dependency targets and worker assignments only.  No Clay, Gate3, gravity, W4, Schwarzschild, YM, NS, AQFT, empirical, or terminal promotion follows from finite computation, coefficient numerology, experimental contact, toy RG, local plaquette witnesses, or semantic 7+7+1 grammar."

record ClayProofCampaignDependencyDAGReceipt : Setω where
  field
    status :
      ClayProofCampaignDAGStatus

    statusIsCanonical :
      status ≡ proofCampaignDAGRecorded_workersAssigned_failClosed

    optimalPathReceipt :
      Optimal.ClayOptimalPathRequisiteLemmaReceipt

    optimalPathYMStillFalse :
      Optimal.clayYangMillsPromoted optimalPathReceipt ≡ false

    optimalPathNSStillFalse :
      Optimal.clayNavierStokesPromoted optimalPathReceipt ≡ false

    optimalPathGravityStillFalse :
      Optimal.gravityPredictionPromoted optimalPathReceipt ≡ false

    gate3PhaseReceipt :
      Gate3Phase.Gate3PhaseCompletenessReductionReceipt

    gate3PhaseStillOpen :
      Gate3Phase.gate3SpectralGapProved gate3PhaseReceipt ≡ false

    gate3PhaseNeeds3D :
      Gate3Phase.toyModel3DRequiredForCrossSectorOverlap gate3PhaseReceipt
      ≡
      true

    monsterOggReceipt :
      MonsterOgg.MonsterOggPrimeCorrectionReceipt

    monsterOggRejects15Plus179GenusPartition :
      MonsterOgg.fifteenPlus179GenusPartitionClaim monsterOggReceipt ≡ false

    monsterOggKeepsYMFalse :
      MonsterOgg.clayYangMillsPromoted monsterOggReceipt ≡ false

    t7AuditReceipt :
      T7Audit.YMT7RademacherActivityIdentificationReceipt

    t7C0TwoNotJustified :
      T7Audit.c0TwoEffJustifiedByT7Alone t7AuditReceipt ≡ false

    t7ClayYMStillFalse :
      T7Audit.clayYangMillsPromoted t7AuditReceipt ≡ false

    cmSplitPrimes :
      List SSPPrime

    cmSplitPrimesAreCanonical :
      cmSplitPrimes ≡ cmSplitSSPPrimes

    cmInertPrimes :
      List SSPPrime

    cmInertPrimesAreCanonical :
      cmInertPrimes ≡ cmInertSSPPrimes

    cmRamifiedPrimes :
      List SSPPrime

    cmRamifiedPrimesAreCanonical :
      cmRamifiedPrimes ≡ cmRamifiedSSPPrimes

    p71IsSplit :
      cmClassOf p71 ≡ cmSplit

    p71IsNotRecordedAsInert :
      cmClassOf p71 ≡ cmSplit

    splitCountRecorded :
      Nat

    splitCountIs5 :
      splitCountRecorded ≡ splitCount

    inertCountRecorded :
      Nat

    inertCountIs9 :
      inertCountRecorded ≡ inertCount

    ramifiedCountRecorded :
      Nat

    ramifiedCountIs1 :
      ramifiedCountRecorded ≡ ramifiedCount

    semanticAtomGrammarCount :
      Nat

    semanticAtomGrammarCountIs15 :
      semanticAtomGrammarCount ≡ semanticSevenSevenOneAtomGrammarCount

    ymActivityTargets :
      List DependencyNode

    ymActivityTargetsAreCanonical :
      ymActivityTargets ≡ ymActivityDAG

    ymBalabanTargets :
      List DependencyNode

    ymBalabanTargetsAreCanonical :
      ymBalabanTargets ≡ ymBalabanDAG

    ymOSGeometryTargets :
      List DependencyNode

    ymOSGeometryTargetsAreCanonical :
      ymOSGeometryTargets ≡ ymOSGeometryDAG

    nsTargets :
      List DependencyNode

    nsTargetsAreCanonical :
      nsTargets ≡ nsDAG

    gate3W4GRTargets :
      List DependencyNode

    gate3W4GRTargetsAreCanonical :
      gate3W4GRTargets ≡ gate3W4GRDAG

    governanceTargets :
      List DependencyNode

    governanceTargetsAreCanonical :
      governanceTargets ≡ governanceDAG

    workers :
      List CampaignWorker

    workersAreCanonical :
      workers ≡ canonicalCampaignWorkers

    t7PhaseCoherenceTarget :
      Set

    t7PhaseCoherenceTargetIsMissing :
      t7PhaseCoherenceTarget ≡ MissingDAGTarget t7TwiningPhaseCoherence

    polymerTreeGraphTarget :
      Set

    polymerTreeGraphTargetIsMissing :
      polymerTreeGraphTarget ≡ MissingDAGTarget dashiPolymerTreeGraphBound

    balabanReblockingTarget :
      Set

    balabanReblockingTargetIsMissing :
      balabanReblockingTarget ≡ MissingDAGTarget balabanReblockingIdentity

    h118BandTarget :
      Set

    h118BandTargetIsMissing :
      h118BandTarget ≡ MissingDAGTarget h118BoundFromBandPressure

    cmSeparationTarget :
      Set

    cmSeparationTargetIsMissing :
      cmSeparationTarget ≡ MissingDAGTarget cmTableAtomGrammarSeparation

    candidate256Target :
      Set

    candidate256TargetIsMissing :
      candidate256Target ≡ MissingDAGTarget candidate256PhysicalCalibration

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    gravityPredictionPromoted :
      Bool

    gravityPredictionPromotedIsFalse :
      gravityPredictionPromoted ≡ false

    gate3SpectralGapProved :
      Bool

    gate3SpectralGapProvedIsFalse :
      gate3SpectralGapProved ≡ false

    w4PhysicalMassCalibrated :
      Bool

    w4PhysicalMassCalibratedIsFalse :
      w4PhysicalMassCalibrated ≡ false

    schwarzschildWeakFieldMatch :
      Bool

    schwarzschildWeakFieldMatchIsFalse :
      schwarzschildWeakFieldMatch ≡ false

    promotions :
      List DAGPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      DAGPromotion →
      ⊥

    cmGuard :
      String

    cmGuardIsCanonical :
      cmGuard ≡ cmGuardText

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ dagBoundaryText

open ClayProofCampaignDependencyDAGReceipt public

canonicalClayProofCampaignDependencyDAGReceipt :
  ClayProofCampaignDependencyDAGReceipt
canonicalClayProofCampaignDependencyDAGReceipt =
  record
    { status =
        proofCampaignDAGRecorded_workersAssigned_failClosed
    ; statusIsCanonical =
        refl
    ; optimalPathReceipt =
        Optimal.canonicalClayOptimalPathRequisiteLemmaReceipt
    ; optimalPathYMStillFalse =
        refl
    ; optimalPathNSStillFalse =
        refl
    ; optimalPathGravityStillFalse =
        refl
    ; gate3PhaseReceipt =
        Gate3Phase.canonicalGate3PhaseCompletenessReductionReceipt
    ; gate3PhaseStillOpen =
        refl
    ; gate3PhaseNeeds3D =
        refl
    ; monsterOggReceipt =
        MonsterOgg.canonicalMonsterOggPrimeCorrectionReceipt
    ; monsterOggRejects15Plus179GenusPartition =
        refl
    ; monsterOggKeepsYMFalse =
        refl
    ; t7AuditReceipt =
        T7Audit.canonicalYMT7RademacherActivityIdentificationReceipt
    ; t7C0TwoNotJustified =
        refl
    ; t7ClayYMStillFalse =
        refl
    ; cmSplitPrimes =
        cmSplitSSPPrimes
    ; cmSplitPrimesAreCanonical =
        refl
    ; cmInertPrimes =
        cmInertSSPPrimes
    ; cmInertPrimesAreCanonical =
        refl
    ; cmRamifiedPrimes =
        cmRamifiedSSPPrimes
    ; cmRamifiedPrimesAreCanonical =
        refl
    ; p71IsSplit =
        refl
    ; p71IsNotRecordedAsInert =
        refl
    ; splitCountRecorded =
        splitCount
    ; splitCountIs5 =
        refl
    ; inertCountRecorded =
        inertCount
    ; inertCountIs9 =
        refl
    ; ramifiedCountRecorded =
        ramifiedCount
    ; ramifiedCountIs1 =
        refl
    ; semanticAtomGrammarCount =
        semanticSevenSevenOneAtomGrammarCount
    ; semanticAtomGrammarCountIs15 =
        refl
    ; ymActivityTargets =
        ymActivityDAG
    ; ymActivityTargetsAreCanonical =
        refl
    ; ymBalabanTargets =
        ymBalabanDAG
    ; ymBalabanTargetsAreCanonical =
        refl
    ; ymOSGeometryTargets =
        ymOSGeometryDAG
    ; ymOSGeometryTargetsAreCanonical =
        refl
    ; nsTargets =
        nsDAG
    ; nsTargetsAreCanonical =
        refl
    ; gate3W4GRTargets =
        gate3W4GRDAG
    ; gate3W4GRTargetsAreCanonical =
        refl
    ; governanceTargets =
        governanceDAG
    ; governanceTargetsAreCanonical =
        refl
    ; workers =
        canonicalCampaignWorkers
    ; workersAreCanonical =
        refl
    ; t7PhaseCoherenceTarget =
        MissingDAGTarget t7TwiningPhaseCoherence
    ; t7PhaseCoherenceTargetIsMissing =
        refl
    ; polymerTreeGraphTarget =
        MissingDAGTarget dashiPolymerTreeGraphBound
    ; polymerTreeGraphTargetIsMissing =
        refl
    ; balabanReblockingTarget =
        MissingDAGTarget balabanReblockingIdentity
    ; balabanReblockingTargetIsMissing =
        refl
    ; h118BandTarget =
        MissingDAGTarget h118BoundFromBandPressure
    ; h118BandTargetIsMissing =
        refl
    ; cmSeparationTarget =
        MissingDAGTarget cmTableAtomGrammarSeparation
    ; cmSeparationTargetIsMissing =
        refl
    ; candidate256Target =
        MissingDAGTarget candidate256PhysicalCalibration
    ; candidate256TargetIsMissing =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; gravityPredictionPromoted =
        false
    ; gravityPredictionPromotedIsFalse =
        refl
    ; gate3SpectralGapProved =
        false
    ; gate3SpectralGapProvedIsFalse =
        refl
    ; w4PhysicalMassCalibrated =
        false
    ; w4PhysicalMassCalibratedIsFalse =
        refl
    ; schwarzschildWeakFieldMatch =
        false
    ; schwarzschildWeakFieldMatchIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        dagPromotionImpossibleHere
    ; cmGuard =
        cmGuardText
    ; cmGuardIsCanonical =
        refl
    ; boundary =
        dagBoundaryText
    ; boundaryIsCanonical =
        refl
    }

dagKeepsP71Split :
  cmClassOf p71 ≡ cmSplit
dagKeepsP71Split =
  refl

dagKeepsYMFalse :
  clayYangMillsPromoted canonicalClayProofCampaignDependencyDAGReceipt
  ≡
  false
dagKeepsYMFalse =
  refl

dagKeepsNSFalse :
  clayNavierStokesPromoted canonicalClayProofCampaignDependencyDAGReceipt
  ≡
  false
dagKeepsNSFalse =
  refl

dagKeepsGravityFalse :
  gravityPredictionPromoted canonicalClayProofCampaignDependencyDAGReceipt
  ≡
  false
dagKeepsGravityFalse =
  refl
