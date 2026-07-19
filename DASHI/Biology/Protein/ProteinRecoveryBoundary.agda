module DASHI.Biology.Protein.ProteinRecoveryBoundary where

import DASHI.Biology.Protein.TranslationContext as Translation
import DASHI.Biology.Protein.ProteinConformationAttractor as Conformation
import DASHI.Biology.Protein.ProteinDiameterLocalityControl as Geometry
import DASHI.Biology.Protein.ProteinFunctionProjection as Function
import DASHI.Biology.Protein.PrionAmyloidIntegrationBoundary as Prion

record ProteinRecoveryBoundary : Set₁ where
  field
    translationContext : Translation.TranslationContext
    translationSystem  : Translation.TranslationSystem translationContext
    conformationSystem : Conformation.ProteinConformationSystem
    profileGeometry    : Geometry.ProteinProfileGeometry
    localityControl    : Geometry.ProteinLocalityControl profileGeometry
    functionSystem     : Function.ProteinFunctionSystem
    prionBoundary      : Prion.PrionAmyloidIntegrationBoundary

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
