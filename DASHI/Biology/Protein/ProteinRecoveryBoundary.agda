module DASHI.Biology.Protein.ProteinRecoveryBoundary where

open import DASHI.Biology.Protein.TranslationContext
open import DASHI.Biology.Protein.ProteinConformationAttractor
open import DASHI.Biology.Protein.ProteinDiameterLocalityControl
open import DASHI.Biology.Protein.ProteinFunctionProjection
open import DASHI.Biology.Protein.PrionAmyloidIntegrationBoundary

record ProteinRecoveryBoundary : Set₁ where
  field
    translationContext : TranslationContext
    translationSystem  : TranslationSystem translationContext
    conformationSystem : ProteinConformationSystem
    profileGeometry    : ProteinProfileGeometry
    localityControl    : ProteinLocalityControl profileGeometry
    functionSystem     : ProteinFunctionSystem
    prionBoundary      : PrionAmyloidIntegrationBoundary

    MolecularToSequence : Set
    SequenceToConformationalEnsemble : Set
    ConformationToProfile : Set
    ProfileToContextualFunction : Set
    MisfoldingToTemplatingCompatibility : Set

    molecularToSequenceWitness : MolecularToSequence
    sequenceToEnsembleWitness  : SequenceToConformationalEnsemble
    conformationToProfileWitness : ConformationToProfile
    profileToFunctionWitness   : ProfileToContextualFunction
    misfoldingCompatibilityWitness : MisfoldingToTemplatingCompatibility

record ProteinRecoveryWitness
  (P : ProteinRecoveryBoundary) : Set₁ where
  field
    SequenceRecovered : Set
    ConformationalEnsembleRecovered : Set
    LocalityProfileRecovered : Set
    ContextualFunctionRecovered : Set

    sequenceWitness : SequenceRecovered
    conformationWitness : ConformationalEnsembleRecovered
    localityWitness : LocalityProfileRecovered
    functionWitness : ContextualFunctionRecovered

record ProteinOpenObligations
  (P : ProteinRecoveryBoundary) : Set₁ where
  field
    transcriptionAndReadingFrame : Set
    molecularDynamicsToAttractor : Set
    chaperoneAndModificationControl : Set
    profileToMechanismValidation : Set
    templatingCompatibilityAndClearance : Set
    experimentalPropertyAuthority : Set

proteinRecoveryAvailable :
  {P : ProteinRecoveryBoundary} →
  ProteinRecoveryWitness P → ProteinRecoveryWitness P
proteinRecoveryAvailable witness = witness
