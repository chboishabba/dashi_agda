module DASHI.Physics.Foundations.AtomicGenerationPipelineExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.AtomicFermionShellExact as Atomic
import DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact as Valence

------------------------------------------------------------------------
-- A first-principles element map requires a sequence of typed dependencies.

data AtomicGenerationStage : Set where
  nuclearChargeStage : AtomicGenerationStage
  nuclearStabilityStage : AtomicGenerationStage
  oneParticleRepresentationStage : AtomicGenerationStage
  antisymmetricManyElectronStage : AtomicGenerationStage
  interactingEnergyStage : AtomicGenerationStage
  groundStateSelectionStage : AtomicGenerationStage
  valenceEquivalenceStage : AtomicGenerationStage
  observablePredictionStage : AtomicGenerationStage

data StageStatus : Set where
  stageSupplied : StageStatus
  stageFiniteAnalogue : StageStatus
  stageExternallyOpen : StageStatus

record AtomicGenerationReceipt : Set where
  constructor atomicGenerationReceipt
  field
    stage : AtomicGenerationStage
    status : StageStatus

open AtomicGenerationReceipt public

canonicalAtomicGenerationReceipts : List AtomicGenerationReceipt
canonicalAtomicGenerationReceipts =
  atomicGenerationReceipt nuclearChargeStage stageFiniteAnalogue
  ∷ atomicGenerationReceipt nuclearStabilityStage stageExternallyOpen
  ∷ atomicGenerationReceipt oneParticleRepresentationStage stageSupplied
  ∷ atomicGenerationReceipt antisymmetricManyElectronStage stageFiniteAnalogue
  ∷ atomicGenerationReceipt interactingEnergyStage stageFiniteAnalogue
  ∷ atomicGenerationReceipt groundStateSelectionStage stageFiniteAnalogue
  ∷ atomicGenerationReceipt valenceEquivalenceStage stageFiniteAnalogue
  ∷ atomicGenerationReceipt observablePredictionStage stageExternallyOpen
  ∷ []

------------------------------------------------------------------------
-- Concrete finite pipeline instance.

record FiniteAtomPipeline : Set where
  constructor finiteAtomPipeline
  field
    species : Atomic.AtomicSpecies
    configuration : Atomic.ElectronicConfiguration
    configurationCandidate : Atomic.ConfigurationCandidate
    valencePattern : Valence.ValencePattern

open FiniteAtomPipeline public

canonicalFiniteAtomPipeline : FiniteAtomPipeline
canonicalFiniteAtomPipeline =
  finiteAtomPipeline
    Atomic.argonLikeSpecies
    Atomic.configurationA
    Atomic.compactConfiguration
    Valence.closedValencePattern

canonicalPipelineChargeIsEighteen :
  Atomic.protonNumber (species canonicalFiniteAtomPipeline) ≡ 18
canonicalPipelineChargeIsEighteen = refl

canonicalPipelineConfigurationEnergyIsFour :
  Atomic.totalConfigurationEnergy
    (configurationCandidate canonicalFiniteAtomPipeline)
  ≡
  4
canonicalPipelineConfigurationEnergyIsFour = refl

canonicalPipelineValenceIsNobleLike :
  Valence.valenceClass (valencePattern canonicalFiniteAtomPipeline)
  ≡
  Valence.nobleLikeClass
canonicalPipelineValenceIsNobleLike = refl

------------------------------------------------------------------------
-- A generator can enumerate labelled candidates; derivation requires the
-- operator, interaction, minimisation, and stability receipts.

data GeneratorMode : Set where
  enumerateNuclearCharges : GeneratorMode
  solveDeclaredHamiltonian : GeneratorMode
  predictObservableChemistry : GeneratorMode

generatorAuthority : GeneratorMode → StageStatus
generatorAuthority enumerateNuclearCharges = stageFiniteAnalogue
generatorAuthority solveDeclaredHamiltonian = stageExternallyOpen
generatorAuthority predictObservableChemistry = stageExternallyOpen

enumerationIsNotHamiltonianSolution :
  generatorAuthority enumerateNuclearCharges ≡ stageFiniteAnalogue
  ×
  generatorAuthority solveDeclaredHamiltonian ≡ stageExternallyOpen
enumerationIsNotHamiltonianSolution = refl , refl

record AtomicGenerationBoundary : Set where
  constructor atomicGenerationBoundary
  field
    labelledEnumerationIsFirstPrinciplesElementDerivation : Bool
    labelledEnumerationIsFirstPrinciplesElementDerivationIsFalse :
      labelledEnumerationIsFirstPrinciplesElementDerivation ≡ false

    suppliedOrbitalRepresentationIsDerivedFromKernelAlone : Bool
    suppliedOrbitalRepresentationIsDerivedFromKernelAloneIsFalse :
      suppliedOrbitalRepresentationIsDerivedFromKernelAlone ≡ false

    finiteInteractionScorePredictsQuantitativeChemistry : Bool
    finiteInteractionScorePredictsQuantitativeChemistryIsFalse :
      finiteInteractionScorePredictsQuantitativeChemistry ≡ false

    oneElementExampleProvesUniversalityAcrossProtonNumber : Bool
    oneElementExampleProvesUniversalityAcrossProtonNumberIsFalse :
      oneElementExampleProvesUniversalityAcrossProtonNumber ≡ false

open AtomicGenerationBoundary public

canonicalAtomicGenerationBoundary : AtomicGenerationBoundary
canonicalAtomicGenerationBoundary =
  atomicGenerationBoundary false refl false refl false refl false refl
