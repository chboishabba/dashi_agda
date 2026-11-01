module DASHI.Physics.Closure.DevelopmentalGenomicInverseBridge where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BrainConnectomeFMRIObservationQuotient as Brain

------------------------------------------------------------------------
-- Developmental genomic inverse bridge.
--
-- This module records the biologically safer statement:
--
--   DNA -> developmental transition law -> connectome geometry
--       -> processing attractor family
--
-- and the inverse use:
--
--   phenotype / brain residual -> developmental residual
--       -> candidate regulatory/genomic fibre.
--
-- It does not claim that DNA encodes a brain snapshot, a thought, or a
-- one-gene cause for a condition.

data Nucleotide : Set where
  A C G T :
    Nucleotide

data DevelopmentalBridgeStatus : Set where
  developmentalInverseTargetOnlyNoPromotion :
    DevelopmentalBridgeStatus

data DevelopmentalInverseFirstMissing : Set where
  missingGenomeDatasetReceipt :
    DevelopmentalInverseFirstMissing

  missingRegulatoryGraphReceipt :
    DevelopmentalInverseFirstMissing

  missingDevelopmentalDynamicsCalibration :
    DevelopmentalInverseFirstMissing

  missingMorphogenesisDatasetReceipt :
    DevelopmentalInverseFirstMissing

  missingNeuralLineageDifferentiationReceipt :
    DevelopmentalInverseFirstMissing

  missingConnectomeFormationReceipt :
    DevelopmentalInverseFirstMissing

  missingEnvironmentInterventionReceipt :
    DevelopmentalInverseFirstMissing

  missingPhenotypeConditionReceipt :
    DevelopmentalInverseFirstMissing

  missingInverseProjectionBackpropProof :
    DevelopmentalInverseFirstMissing

  missingCandidateGeneRankingValidation :
    DevelopmentalInverseFirstMissing

  missingCalibrationFixtureGroundTruth :
    DevelopmentalInverseFirstMissing

  missingCalibrationFixtureRankingProof :
    DevelopmentalInverseFirstMissing

  missingLayeredResidualCompatibilityProof :
    DevelopmentalInverseFirstMissing

  missingFiberRefinementProof :
    DevelopmentalInverseFirstMissing

  missingLaminarNarrowingReceipt :
    DevelopmentalInverseFirstMissing

  missingSyntheticConstructLibraryReceipt :
    DevelopmentalInverseFirstMissing

  missingSyntheticForwardModelReceipt :
    DevelopmentalInverseFirstMissing

  missingSyntheticPhenotypeMeasurementReceipt :
    DevelopmentalInverseFirstMissing

  missingSyntheticBurdenMeasurementReceipt :
    DevelopmentalInverseFirstMissing

  missingSyntheticCompatibilityPenaltyReceipt :
    DevelopmentalInverseFirstMissing

  missingSyntheticRankingValidation :
    DevelopmentalInverseFirstMissing

  missingNaturalSyntheticScoreBridge :
    DevelopmentalInverseFirstMissing

data CausalShape : Set where
  codingVariantProteinStructure :
    CausalShape

  channelTransporterDysfunction :
    CausalShape

  receptorDeletionPathway :
    CausalShape

  degradationPathwayModulation :
    CausalShape

  regulatoryExpressionTiming :
    CausalShape

  morphogenGradientPatterning :
    CausalShape

  neuralCircuitDevelopment :
    CausalShape

  probabilisticRiskLandscape :
    CausalShape

data CalibrationFixtureName : Set where
  hbbFixture :
    CalibrationFixtureName

  cftrFixture :
    CalibrationFixtureName

  ccr5Delta32Fixture :
    CalibrationFixtureName

  pcsk9Fixture :
    CalibrationFixtureName

  lctEnhancerFixture :
    CalibrationFixtureName

  hoxShhFixture :
    CalibrationFixtureName

  foxp2Fixture :
    CalibrationFixtureName

  apoeFixture :
    CalibrationFixtureName

data CalibrationFixtureQuality : Set where
  cleanDeterministicFixture :
    CalibrationFixtureQuality

  pathwayMechanisticFixture :
    CalibrationFixtureQuality

  developmentalTimeIndexedFixture :
    CalibrationFixtureQuality

  probabilisticRiskFixture :
    CalibrationFixtureQuality

data CRISPRPerturbationClass : Set where
  knockout :
    CRISPRPerturbationClass

  knockdown :
    CRISPRPerturbationClass

  crisprActivation :
    CRISPRPerturbationClass

  baseEdit :
    CRISPRPerturbationClass

  primeEdit :
    CRISPRPerturbationClass

data SyntheticFixtureName : Set where
  gfpReporterFixture :
    SyntheticFixtureName

  rfpCounterfixture :
    SyntheticFixtureName

  metabolicOdorFixture :
    SyntheticFixtureName

  shortPathwayFixture :
    SyntheticFixtureName

  longPathwayCounterfixture :
    SyntheticFixtureName

data SyntheticConstructPartClass : Set where
  promoterPart :
    SyntheticConstructPartClass

  rbsTranslationControlPart :
    SyntheticConstructPartClass

  codingSequencePart :
    SyntheticConstructPartClass

  terminatorPart :
    SyntheticConstructPartClass

  vectorBackbonePart :
    SyntheticConstructPartClass

  hostContextPart :
    SyntheticConstructPartClass

record GenomicCarrier : Setω where
  field
    Genome :
      Set

    Locus :
      Set

    Gene :
      Set

    RegulatoryElement :
      Set

    ChromatinState :
      Set

    EpigeneticMark :
      Set

    baseAt :
      Genome →
      Locus →
      Nucleotide

    codingRegion :
      Genome →
      Gene →
      Set

    regulatoryRegion :
      Genome →
      RegulatoryElement →
      Set

    chromatin :
      Genome →
      Locus →
      ChromatinState

    epigenetic :
      Genome →
      Locus →
      EpigeneticMark

    genomeIsGeneratorNotBlueprint :
      String

open GenomicCarrier public

record RegulatoryStateSpace (Geno : GenomicCarrier) : Setω where
  field
    RegulatoryState :
      Set

    RegulatoryActivation :
      Set

    RegulatoryEdge :
      Set

    RegulatoryWeight :
      Set

    expression :
      RegulatoryState →
      GenomicCarrier.Gene Geno →
      RegulatoryActivation

    regulatoryCoupling :
      RegulatoryEdge →
      RegulatoryWeight

    activationDynamics :
      RegulatoryState →
      RegulatoryState

    regulationLawName :
      String

open RegulatoryStateSpace public

record MorphogenesisLayer
  (Geno : GenomicCarrier)
  (Reg : RegulatoryStateSpace Geno) : Setω where
  field
    MorphogeneticState :
      Set

    CellState :
      Set

    TissueGeometry :
      Set

    SignalingField :
      Set

    morphogenesisStep :
      RegulatoryStateSpace.RegulatoryState Reg →
      MorphogeneticState →
      MorphogeneticState

    tissueGeometry :
      MorphogeneticState →
      TissueGeometry

    signaling :
      MorphogeneticState →
      SignalingField

    morphogenesisLawName :
      String

open MorphogenesisLayer public

record NeuralDifferentiationLayer
  (Geno : GenomicCarrier)
  (Reg : RegulatoryStateSpace Geno)
  (Morph : MorphogenesisLayer Geno Reg) : Setω where
  field
    NeuralLineage :
      Set

    NeuronClass :
      Set

    GliaClass :
      Set

    NeurotransmitterType :
      Set

    ReceptorDistribution :
      Set

    differentiate :
      RegulatoryStateSpace.RegulatoryState Reg →
      MorphogenesisLayer.MorphogeneticState Morph →
      NeuralLineage

    neuronClass :
      NeuralLineage →
      NeuronClass

    gliaClass :
      NeuralLineage →
      GliaClass

    neurotransmitter :
      NeuralLineage →
      NeurotransmitterType

    receptorDistribution :
      NeuralLineage →
      ReceptorDistribution

    dnaSpecifiesConstraintsNotFinalStates :
      String

open NeuralDifferentiationLayer public

record ConnectomeFormationLayer
  (Geno : GenomicCarrier)
  (Reg : RegulatoryStateSpace Geno)
  (Morph : MorphogenesisLayer Geno Reg)
  (Neural : NeuralDifferentiationLayer Geno Reg Morph) : Setω where
  field
    Environment :
      Set

    DevelopmentalTime :
      Set

    DevelopmentalConnectome :
      Set

    PlasticitySignal :
      Set

    connectomeAt :
      DevelopmentalTime →
      DevelopmentalConnectome

    formationStep :
      DevelopmentalConnectome →
      NeuralDifferentiationLayer.NeuralLineage Neural →
      Environment →
      PlasticitySignal →
      DevelopmentalConnectome

    matureConnectome :
      DevelopmentalConnectome →
      Brain.ConnectomeCarrier

    coGeneratedByGenomeAndEnvironment :
      String

open ConnectomeFormationLayer public

record DevelopmentalMDLEnergy
  (Geno : GenomicCarrier)
  (Reg : RegulatoryStateSpace Geno)
  (Morph : MorphogenesisLayer Geno Reg)
  (Neural : NeuralDifferentiationLayer Geno Reg Morph)
  (Conn : ConnectomeFormationLayer Geno Reg Morph Neural) : Setω where
  field
    DevelopmentalState :
      Set

    DevelopmentalCost :
      Set

    _≤dev_ :
      DevelopmentalCost →
      DevelopmentalCost →
      Set

    wiringCost :
      DevelopmentalState →
      DevelopmentalCost

    metabolicCost :
      DevelopmentalState →
      DevelopmentalCost

    predictionEfficiencyCost :
      DevelopmentalState →
      DevelopmentalCost

    robustnessCost :
      DevelopmentalState →
      DevelopmentalCost

    developmentalStabilityCost :
      DevelopmentalState →
      DevelopmentalCost

    deltaDev :
      DevelopmentalState →
      DevelopmentalCost

    developmentalStep :
      DevelopmentalState →
      DevelopmentalState

    developmentalDescentSound :
      (state : DevelopmentalState) →
      deltaDev (developmentalStep state) ≤dev deltaDev state

open DevelopmentalMDLEnergy public

record DevelopmentalForwardSpine : Setω where
  field
    genome :
      GenomicCarrier

    regulation :
      RegulatoryStateSpace genome

    morphogenesis :
      MorphogenesisLayer genome regulation

    neuralDifferentiation :
      NeuralDifferentiationLayer genome regulation morphogenesis

    connectomeFormation :
      ConnectomeFormationLayer
        genome regulation morphogenesis neuralDifferentiation

    developmentalEnergy :
      DevelopmentalMDLEnergy
        genome regulation morphogenesis neuralDifferentiation
        connectomeFormation

    BrainState :
      Set

    ProcessingAttractorFamily :
      Set

    matureBrain :
      Brain.DASHIBrainBridge

    developmentalEndpoint :
      String

    forwardSpineName :
      String

open DevelopmentalForwardSpine public

record PhenotypeConditionSignal : Setω where
  field
    Phenotype :
      Set

    Condition :
      Set

    PhenotypeDelta :
      Set

    structureDelta :
      PhenotypeDelta →
      Set

    functionDelta :
      PhenotypeDelta →
      Set

    metabolismDelta :
      PhenotypeDelta →
      Set

    connectivityDelta :
      PhenotypeDelta →
      Set

    behaviorDelta :
      PhenotypeDelta →
      Set

open PhenotypeConditionSignal public

record DevelopmentalInverseProblem
  (Forward : DevelopmentalForwardSpine)
  (Signal : PhenotypeConditionSignal) : Setω where
  field
    Environment :
      Set

    Intervention :
      Set

    CandidateGenomicPerturbation :
      Set

    CandidateRegulatoryFibre :
      Set

    CandidateScore :
      Set

    _≤score_ :
      CandidateScore →
      CandidateScore →
      Set

    forwardPhenotype :
      GenomicCarrier.Genome (DevelopmentalForwardSpine.genome Forward) →
      Environment →
      Intervention →
      PhenotypeConditionSignal.Phenotype Signal

    inverseProjection :
      PhenotypeConditionSignal.PhenotypeDelta Signal →
      CandidateRegulatoryFibre

    candidatePerturbation :
      CandidateRegulatoryFibre →
      CandidateGenomicPerturbation →
      Set

    phenotypeResidualPenalty :
      CandidateGenomicPerturbation →
      CandidateScore

    mdlPerturbationPenalty :
      CandidateGenomicPerturbation →
      CandidateScore

    pleiotropyPenalty :
      CandidateGenomicPerturbation →
      CandidateScore

    layerConstraintPenalty :
      CandidateGenomicPerturbation →
      CandidateScore

    totalInverseScore :
      CandidateGenomicPerturbation →
      CandidateScore

    ranksBefore :
      CandidateGenomicPerturbation →
      CandidateGenomicPerturbation →
      Set

    rankingSound :
      (left right : CandidateGenomicPerturbation) →
      totalInverseScore left ≤score totalInverseScore right →
      ranksBefore left right

    candidateFibreInterpretation :
      String

open DevelopmentalInverseProblem public

record LayeredPhenotypeResidual
  (Forward : DevelopmentalForwardSpine)
  (Signal : PhenotypeConditionSignal)
  (Inverse : DevelopmentalInverseProblem Forward Signal) : Setω where
  field
    DeltaY :
      PhenotypeConditionSignal.PhenotypeDelta Signal

    DeltaObservation :
      Set

    DeltaNeuronalState :
      Set

    DeltaTransition :
      Set

    DeltaConnectome :
      Set

    DeltaMorphogenesis :
      Set

    DeltaRegulation :
      Set

    observationCompatible :
      DeltaObservation →
      DeltaNeuronalState →
      Set

    transitionCompatible :
      DeltaNeuronalState →
      DeltaTransition →
      Set

    connectomeCompatible :
      DeltaTransition →
      DeltaConnectome →
      Set

    morphogenesisCompatible :
      DeltaConnectome →
      DeltaMorphogenesis →
      Set

    regulationCompatible :
      DeltaMorphogenesis →
      DeltaRegulation →
      Set

    totalDifferentialImageWitness :
      String

open LayeredPhenotypeResidual public

record InverseDevelopmentalObject
  (Forward : DevelopmentalForwardSpine)
  (Signal : PhenotypeConditionSignal)
  (Inverse : DevelopmentalInverseProblem Forward Signal) : Setω where
  field
    Time :
      Set

    forwardModel :
      GenomicCarrier.Genome (DevelopmentalForwardSpine.genome Forward) →
      DevelopmentalInverseProblem.Environment Inverse →
      Time →
      PhenotypeConditionSignal.Phenotype Signal

    layeredResidual :
      LayeredPhenotypeResidual Forward Signal Inverse

    structuralConstraint :
      DevelopmentalInverseProblem.CandidateGenomicPerturbation Inverse →
      DevelopmentalInverseProblem.CandidateScore Inverse

    morphogeneticConstraint :
      DevelopmentalInverseProblem.CandidateGenomicPerturbation Inverse →
      DevelopmentalInverseProblem.CandidateScore Inverse

    channelConstraint :
      DevelopmentalInverseProblem.CandidateGenomicPerturbation Inverse →
      DevelopmentalInverseProblem.CandidateScore Inverse

    metabolicConstraint :
      DevelopmentalInverseProblem.CandidateGenomicPerturbation Inverse →
      DevelopmentalInverseProblem.CandidateScore Inverse

    laminarConstraint :
      DevelopmentalInverseProblem.CandidateGenomicPerturbation Inverse →
      DevelopmentalInverseProblem.CandidateScore Inverse

    inverseScoreFactorsThroughConstraints :
      String

    candidateFiber :
      Set

    MorePhenotypeLayers :
      Set

    SmallerFiber :
      Set →
      Set

    fiberRefines :
      MorePhenotypeLayers →
      SmallerFiber candidateFiber

    CoarseBOLDFiber :
      Set

    LaminarFiber :
      Set

    laminarNarrows :
      LaminarFiber →
      CoarseBOLDFiber →
      Set

    laminarNarrowingInterpretation :
      String

open InverseDevelopmentalObject public

record CalibrationFixture
  (Forward : DevelopmentalForwardSpine)
  (Signal : PhenotypeConditionSignal)
  (Inverse : DevelopmentalInverseProblem Forward Signal) : Setω where
  field
    fixtureName :
      CalibrationFixtureName

    knownCausalPerturbation :
      DevelopmentalInverseProblem.CandidateGenomicPerturbation Inverse

    knownPhenotype :
      PhenotypeConditionSignal.Phenotype Signal

    knownIntermediatePathway :
      Set

    causalDepth :
      Nat

    shape :
      CausalShape

    quality :
      CalibrationFixtureQuality

    candidateFiber :
      DevelopmentalInverseProblem.CandidateRegulatoryFibre Inverse

    fiberIsPointForCoding :
      shape ≡ codingVariantProteinStructure →
      Set

    fiberIsClassForChannel :
      shape ≡ channelTransporterDysfunction →
      Set

    forwardRecoversKnownPhenotype :
      Set

    scoreRanksKnownPerturbation :
      (candidate :
        DevelopmentalInverseProblem.CandidateGenomicPerturbation Inverse) →
      DevelopmentalInverseProblem._≤score_ Inverse
        (DevelopmentalInverseProblem.totalInverseScore Inverse
          knownCausalPerturbation)
        (DevelopmentalInverseProblem.totalInverseScore Inverse candidate)

    criticalDevelopmentalWindow :
      shape ≡ morphogenGradientPatterning →
      Set

    distributionalForwardAdequacy :
      shape ≡ probabilisticRiskLandscape →
      Set

    fixtureIsCalibrationNotDiscovery :
      String

open CalibrationFixture public

record CRISPRPerturbationMDLSurface
  (Forward : DevelopmentalForwardSpine)
  (Signal : PhenotypeConditionSignal)
  (Inverse : DevelopmentalInverseProblem Forward Signal) : Setω where
  field
    perturbationClass :
      DevelopmentalInverseProblem.CandidateGenomicPerturbation Inverse →
      CRISPRPerturbationClass

    perturbationMDLCost :
      CRISPRPerturbationClass →
      DevelopmentalInverseProblem.CandidateScore Inverse

    knockoutNotMoreComplexThanBaseEdit :
      DevelopmentalInverseProblem._≤score_ Inverse
        (perturbationMDLCost knockout)
        (perturbationMDLCost baseEdit)

    baseEditNotMoreComplexThanPrimeEdit :
      DevelopmentalInverseProblem._≤score_ Inverse
        (perturbationMDLCost baseEdit)
        (perturbationMDLCost primeEdit)

    primeEditNotMoreComplexThanActivation :
      DevelopmentalInverseProblem._≤score_ Inverse
        (perturbationMDLCost primeEdit)
        (perturbationMDLCost crisprActivation)

    mdlOrderingIsFixturePolicyNotBiologyLaw :
      String

open CRISPRPerturbationMDLSurface public

record SyntheticConstructCarrier : Setω where
  field
    Construct :
      Set

    Promoter :
      Set

    TranslationControl :
      Set

    CodingSequence :
      Set

    Terminator :
      Set

    VectorBackbone :
      Set

    Host :
      Set

    promoterOf :
      Construct →
      Promoter

    translationControlOf :
      Construct →
      TranslationControl

    codingSequenceOf :
      Construct →
      CodingSequence

    terminatorOf :
      Construct →
      Terminator

    vectorBackboneOf :
      Construct →
      VectorBackbone

    hostOf :
      Construct →
      Host

    partClass :
      SyntheticConstructPartClass →
      Set

    constructInterpretation :
      String

open SyntheticConstructCarrier public

record SyntheticBiologyInverse : Setω where
  field
    constructCarrier :
      SyntheticConstructCarrier

    Environment :
      Set

    Time :
      Set

    Phenotype :
      Set

    PhenotypeDistance :
      Set

    SyntheticScore :
      Set

    Probability :
      Set

    _≤syn_ :
      SyntheticScore →
      SyntheticScore →
      Set

    _<syn_ :
      SyntheticScore →
      SyntheticScore →
      Set

    _>prob_ :
      Probability →
      Probability →
      Set

    F-syn :
      SyntheticConstructCarrier.Construct constructCarrier →
      SyntheticConstructCarrier.Host constructCarrier →
      Environment →
      Time →
      Phenotype

    targetPhenotype :
      Phenotype

    syntheticFiber :
      Set

    phenotypeDistance :
      SyntheticConstructCarrier.Construct constructCarrier →
      PhenotypeDistance

    phenotypeDistanceScore :
      PhenotypeDistance →
      SyntheticScore

    constructMDL :
      SyntheticConstructCarrier.Construct constructCarrier →
      SyntheticScore

    burdenPenalty :
      SyntheticConstructCarrier.Construct constructCarrier →
      SyntheticScore

    compatibilityPenalty :
      SyntheticConstructCarrier.Construct constructCarrier →
      SyntheticScore

    totalSyntheticScore :
      SyntheticConstructCarrier.Construct constructCarrier →
      SyntheticScore

    scoreDecomposes :
      String

    burdenMeasurable :
      String

    pathwayLength :
      SyntheticConstructCarrier.Construct constructCarrier →
      Nat

    SamePhenotype :
      SyntheticConstructCarrier.Construct constructCarrier →
      SyntheticConstructCarrier.Construct constructCarrier →
      Phenotype →
      Set

    shorterPathwayHasNoGreaterMDL :
      (left right :
        SyntheticConstructCarrier.Construct constructCarrier) →
      SamePhenotype left right targetPhenotype →
      Set

    reproducesTargetProbability :
      SyntheticConstructCarrier.Construct constructCarrier →
      Probability

    ranksCorrectly :
      (left right :
        SyntheticConstructCarrier.Construct constructCarrier) →
      totalSyntheticScore left <syn totalSyntheticScore right →
      reproducesTargetProbability left >prob reproducesTargetProbability right

    gfpConstruct :
      SyntheticConstructCarrier.Construct constructCarrier

    greenFluorescenceTarget :
      Phenotype

    gfpCalibrates :
      targetPhenotype ≡ greenFluorescenceTarget →
      (candidate :
        SyntheticConstructCarrier.Construct constructCarrier) →
      totalSyntheticScore gfpConstruct ≤syn totalSyntheticScore candidate

    odorTarget :
      Phenotype

    metabolicOdorRetrosynthesisTarget :
      targetPhenotype ≡ odorTarget →
      Set

    syntheticIsSearchNotNaturalInference :
      String

open SyntheticBiologyInverse public

record SyntheticCalibrationFixture
  (Syn : SyntheticBiologyInverse) : Setω where
  field
    syntheticFixtureName :
      SyntheticFixtureName

    target :
      SyntheticBiologyInverse.Phenotype Syn

    knownConstruct :
      SyntheticConstructCarrier.Construct
        (SyntheticBiologyInverse.constructCarrier Syn)

    counterConstruct :
      SyntheticConstructCarrier.Construct
        (SyntheticBiologyInverse.constructCarrier Syn)

    fixturePassCondition :
      SyntheticBiologyInverse._<syn_ Syn
        (SyntheticBiologyInverse.totalSyntheticScore Syn knownConstruct)
        (SyntheticBiologyInverse.totalSyntheticScore Syn counterConstruct)

    fixtureIsCalibrationNotWetLabValidation :
      String

open SyntheticCalibrationFixture public

record NaturalSyntheticScoreBridge
  (Forward : DevelopmentalForwardSpine)
  (Signal : PhenotypeConditionSignal)
  (Inverse : DevelopmentalInverseProblem Forward Signal)
  (Syn : SyntheticBiologyInverse) : Setω where
  field
    liftNaturalPerturbation :
      DevelopmentalInverseProblem.CandidateGenomicPerturbation Inverse →
      SyntheticConstructCarrier.Construct
        (SyntheticBiologyInverse.constructCarrier Syn)

    naturalScoreAsSyntheticScore :
      DevelopmentalInverseProblem.CandidateGenomicPerturbation Inverse →
      SyntheticBiologyInverse.SyntheticScore Syn

    scoreBridgeCompatible :
      (candidate :
        DevelopmentalInverseProblem.CandidateGenomicPerturbation Inverse) →
      SyntheticBiologyInverse._≤syn_ Syn
        (naturalScoreAsSyntheticScore candidate)
        (SyntheticBiologyInverse.totalSyntheticScore Syn
          (liftNaturalPerturbation candidate))

    sameScoringVocabulary :
      String

    bridgeIsTargetNotTransferOfValidation :
      String

open NaturalSyntheticScoreBridge public

record DevelopmentalCalibrationFixtureSuite
  (Forward : DevelopmentalForwardSpine)
  (Signal : PhenotypeConditionSignal)
  (Inverse : DevelopmentalInverseProblem Forward Signal) : Setω where
  field
    hbb :
      CalibrationFixture Forward Signal Inverse

    cftr :
      CalibrationFixture Forward Signal Inverse

    ccr5Delta32 :
      CalibrationFixture Forward Signal Inverse

    pcsk9 :
      CalibrationFixture Forward Signal Inverse

    lctEnhancer :
      CalibrationFixture Forward Signal Inverse

    hoxShh :
      CalibrationFixture Forward Signal Inverse

    foxp2 :
      CalibrationFixture Forward Signal Inverse

    apoe :
      CalibrationFixture Forward Signal Inverse

    fixtureSuitePurpose :
      String

    hbbMustRankFirstBeforeNovelPrediction :
      String

    probabilisticFixturesUseDistributionalForwardModel :
      String

open DevelopmentalCalibrationFixtureSuite public

record ConditionBackpropagationChain
  (Forward : DevelopmentalForwardSpine)
  (Signal : PhenotypeConditionSignal) : Setω where
  field
    DeltaObservation :
      Set

    DeltaProcessing :
      Set

    DeltaConnectome :
      Set

    DeltaMorphogenesis :
      Set

    DeltaRegulation :
      Set

    DeltaGenome :
      Set

    backpropObservationToProcessing :
      DeltaObservation →
      DeltaProcessing

    backpropProcessingToConnectome :
      DeltaProcessing →
      DeltaConnectome

    backpropConnectomeToMorphogenesis :
      DeltaConnectome →
      DeltaMorphogenesis

    backpropMorphogenesisToRegulation :
      DeltaMorphogenesis →
      DeltaRegulation

    backpropRegulationToGenome :
      DeltaRegulation →
      DeltaGenome

    backpropChainName :
      String

open ConditionBackpropagationChain public

record DevelopmentalGenomicInverseBridgeBoundary : Set where
  field
    status :
      DevelopmentalBridgeStatus

    forwardChain :
      List String

    inverseChain :
      List String

    compactForwardMap :
      String

    matureBrainInterpretation :
      String

    conditionInterpretation :
      String

    methodStatement :
      String

    calibrationFixtureTargets :
      List String

    syntheticConstructFixtureTargets :
      List String

    exactFirstMissing :
      List DevelopmentalInverseFirstMissing

    dnaBlueprintClaim :
      Bool

    dnaBlueprintClaimIsFalse :
      dnaBlueprintClaim ≡ false

    empiricalValidationClosed :
      Bool

    empiricalValidationClosedIsFalse :
      empiricalValidationClosed ≡ false

    allowedClaim :
      List String

    forbiddenClaim :
      List String

open DevelopmentalGenomicInverseBridgeBoundary public

canonicalDevelopmentalGenomicInverseBridgeBoundary :
  DevelopmentalGenomicInverseBridgeBoundary
canonicalDevelopmentalGenomicInverseBridgeBoundary =
  record
    { status =
        developmentalInverseTargetOnlyNoPromotion
    ; forwardChain =
        "genome g"
        ∷ "regulatory activation R_t"
        ∷ "morphogenetic state M_t"
        ∷ "neural lineage / differentiation N_t"
        ∷ "developmental connectome C_t"
        ∷ "mature processing operator T_C"
        ∷ "neuronal state sigma_t"
        ∷ "observable readout O(sigma_t)"
        ∷ []
    ; inverseChain =
        "observed phenotype or brain residual DeltaY"
        ∷ "observation residual DeltaO"
        ∷ "processing residual DeltaT_C"
        ∷ "connectome residual DeltaC"
        ∷ "morphogenesis residual DeltaM"
        ∷ "regulatory residual DeltaR"
        ∷ "candidate genomic perturbation Delta g"
        ∷ []
    ; compactForwardMap =
        "g maps to (C*, T_C, delta_C) through developmental transition constraints"
    ; matureBrainInterpretation =
        "the mature brain is a developmental fixed-point target B* = (C*, T_C, A_C), not a genome-encoded snapshot"
    ; conditionInterpretation =
        "conditions are inverse probes: phenotype differences constrain candidate regulatory/genomic fibres"
    ; methodStatement =
        "phenotype difference -> typed developmental residual -> candidate regulatory fibre -> ranked DNA/search space"
    ; calibrationFixtureTargets =
        "HBB: coding variant to protein structure shallow fixture"
        ∷ "CFTR: channel / transporter dysfunction fixture"
        ∷ "CCR5Delta32: receptor deletion to pathway-entry fixture"
        ∷ "PCSK9: degradation-pathway modulation fixture"
        ∷ "LCT enhancer: regulatory expression-timing fixture"
        ∷ "HOX/SHH: morphogen-gradient / patterning fixture"
        ∷ "FOXP2: neural-circuit developmental fixture"
        ∷ "APOE: probabilistic risk-landscape fixture"
        ∷ []
    ; syntheticConstructFixtureTargets =
        "GFP reporter: synthetic construct point-fibre fixture"
        ∷ "RFP counterfixture: reporter specificity fixture"
        ∷ "metabolic odor: synthetic pathway-retrosynthesis fixture"
        ∷ "short pathway: MDL pathway-length fixture"
        ∷ "long pathway counterfixture: MDL pathway-length negative control"
        ∷ []
    ; exactFirstMissing =
        missingGenomeDatasetReceipt
        ∷ missingRegulatoryGraphReceipt
        ∷ missingDevelopmentalDynamicsCalibration
        ∷ missingMorphogenesisDatasetReceipt
        ∷ missingNeuralLineageDifferentiationReceipt
        ∷ missingConnectomeFormationReceipt
        ∷ missingEnvironmentInterventionReceipt
        ∷ missingPhenotypeConditionReceipt
        ∷ missingInverseProjectionBackpropProof
        ∷ missingCandidateGeneRankingValidation
        ∷ missingCalibrationFixtureGroundTruth
        ∷ missingCalibrationFixtureRankingProof
        ∷ missingLayeredResidualCompatibilityProof
        ∷ missingFiberRefinementProof
        ∷ missingLaminarNarrowingReceipt
        ∷ missingSyntheticConstructLibraryReceipt
        ∷ missingSyntheticForwardModelReceipt
        ∷ missingSyntheticPhenotypeMeasurementReceipt
        ∷ missingSyntheticBurdenMeasurementReceipt
        ∷ missingSyntheticCompatibilityPenaltyReceipt
        ∷ missingSyntheticRankingValidation
        ∷ missingNaturalSyntheticScoreBridge
        ∷ []
    ; dnaBlueprintClaim =
        false
    ; dnaBlueprintClaimIsFalse =
        refl
    ; empiricalValidationClosed =
        false
    ; empiricalValidationClosedIsFalse =
        refl
    ; allowedClaim =
        "DNA may be represented as a generator of admissible developmental constraints"
        ∷ "development can be typed as genome -> regulation -> morphogenesis -> neural differentiation -> connectome -> processing"
        ∷ "known phenotype or brain differences can be represented as inverse probes that shrink genomic/regulatory candidate space"
        ∷ "candidate genes/regulatory elements are ranked by residual, MDL, pleiotropy, and layer-constraint penalties"
        ∷ "named biomedical examples may be staged only as frozen calibration-test targets for inverse-ranking discipline"
        ∷ "synthetic constructs may be staged as design-search calibration fixtures with explicit construct parts and measurable burden targets"
        ∷ []
    ; forbiddenClaim =
        "DNA does not encode a brain snapshot in this bridge"
        ∷ "DNA does not encode thoughts or explicit percepts in this bridge"
        ∷ "no one-gene-causes-condition claim follows from this inverse surface"
        ∷ "calibration fixtures are not validation receipts without ground-truth, ranking, residual-layer, fibre-refinement, and laminar-narrowing receipts"
        ∷ "synthetic fixtures are not wet-lab validation receipts without construct-library, forward-model, phenotype, burden, compatibility, ranking, and natural/synthetic bridge receipts"
        ∷ "no genome-to-connectome, disease-gene, biology, cognition, or perception empirical validation is constructed here"
        ∷ []
    }
