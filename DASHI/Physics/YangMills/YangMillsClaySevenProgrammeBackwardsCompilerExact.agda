module DASHI.Physics.YangMills.YangMillsClaySevenProgrammeBackwardsCompilerExact where

------------------------------------------------------------------------
-- ROUND65: SEVEN-PROGRAMME BACKWARDS COMPILER TO THE LITERAL CLAY TYPE
--
-- This is a stronger compression of the Round64 ten-master graph.  It is not
-- obtained by merely conjoining proposition fields: the seven programmes are
-- the mathematically distinct mechanisms that remain after reusing existing
-- exact/source-owned closures.
--
-- P1  literal weak-coupling SU(2) RG step on the physical Wilson carrier;
-- P2  cutoff-uniform physical transfer/spectral theorem;
-- P3  strong OS-compatible same-family continuum RG convergence;
-- P4  same-family local fields / OPE / stress tensor;
-- P5  same-limit interacting fourth-cumulant survival;
-- P6  same-limit physical exponential clustering;
-- P7  compact-simple-group promotion of the complete construction.
--
-- The endpoint is the literal in-repo ClayYangMillsSolution.  In particular,
-- P4--P6 consume the SAME ContinuumSchwingerFamily produced by P3, so unrelated
-- subsequential limits cannot be spliced into one claimed theory.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay

record SevenProgrammeTypes : Set₁ where
  field
    LiteralSU2WeakCouplingRGStep : Set
    CutoffUniformPhysicalSpectralTheorem : Set
    StrongOSCompatibleContinuumRGConvergence : Set
    ContinuumLocalFieldOPEStressTensor : Set
    SameLimitInteractionSurvival : Set
    SameLimitPhysicalExponentialClustering : Set
    CompactSimpleGroupPromotion : Set

open SevenProgrammeTypes public

record SevenProgrammeWitnesses (types : SevenProgrammeTypes) : Set₁ where
  field
    literalSU2WeakCouplingRGStep : LiteralSU2WeakCouplingRGStep types
    cutoffUniformPhysicalSpectralTheorem :
      CutoffUniformPhysicalSpectralTheorem types
    strongOSCompatibleContinuumRGConvergence :
      StrongOSCompatibleContinuumRGConvergence types
    continuumLocalFieldOPEStressTensor : ContinuumLocalFieldOPEStressTensor types
    sameLimitInteractionSurvival : SameLimitInteractionSurvival types
    sameLimitPhysicalExponentialClustering :
      SameLimitPhysicalExponentialClustering types
    compactSimpleGroupPromotion : CompactSimpleGroupPromotion types

open SevenProgrammeWitnesses public

record SevenProgrammeBackwardsGraph (types : SevenProgrammeTypes) : Set₁ where
  field
    RenormalizedLatticeFamily : Set
    UniformSpectralTheory : Set
    ContinuumSchwingerFamily : Set
    CompleteSingleGroupContinuumYM : Set
    AllCompactSimpleContinuumYM : Set

    clayVocabulary : Clay.ClayProblemVocabulary

    compileRenormalizedLatticeFamily :
      LiteralSU2WeakCouplingRGStep types →
      RenormalizedLatticeFamily

    compileUniformSpectralTheory :
      RenormalizedLatticeFamily →
      CutoffUniformPhysicalSpectralTheorem types →
      UniformSpectralTheory

    compileContinuumSchwingerFamily :
      UniformSpectralTheory →
      StrongOSCompatibleContinuumRGConvergence types →
      ContinuumSchwingerFamily

    compileCompleteSingleGroupContinuumYM :
      ContinuumSchwingerFamily →
      ContinuumLocalFieldOPEStressTensor types →
      SameLimitInteractionSurvival types →
      SameLimitPhysicalExponentialClustering types →
      CompleteSingleGroupContinuumYM

    compileAllCompactSimpleContinuumYM :
      CompleteSingleGroupContinuumYM →
      CompactSimpleGroupPromotion types →
      AllCompactSimpleContinuumYM

    identifyLiteralClaySolution :
      AllCompactSimpleContinuumYM →
      Clay.ClayYangMillsSolution clayVocabulary

open SevenProgrammeBackwardsGraph public

renormalizedLatticeFromSeven :
  ∀ {types}
    (graph : SevenProgrammeBackwardsGraph types) →
    SevenProgrammeWitnesses types →
  RenormalizedLatticeFamily graph
renormalizedLatticeFromSeven graph witnesses =
  compileRenormalizedLatticeFamily graph
    (literalSU2WeakCouplingRGStep witnesses)

uniformSpectralTheoryFromSeven :
  ∀ {types}
    (graph : SevenProgrammeBackwardsGraph types) →
    (witnesses : SevenProgrammeWitnesses types) →
  UniformSpectralTheory graph
uniformSpectralTheoryFromSeven graph witnesses =
  compileUniformSpectralTheory graph
    (renormalizedLatticeFromSeven graph witnesses)
    (cutoffUniformPhysicalSpectralTheorem witnesses)

continuumSchwingerFromSeven :
  ∀ {types}
    (graph : SevenProgrammeBackwardsGraph types) →
    (witnesses : SevenProgrammeWitnesses types) →
  ContinuumSchwingerFamily graph
continuumSchwingerFromSeven graph witnesses =
  compileContinuumSchwingerFamily graph
    (uniformSpectralTheoryFromSeven graph witnesses)
    (strongOSCompatibleContinuumRGConvergence witnesses)

completeSingleGroupFromSeven :
  ∀ {types}
    (graph : SevenProgrammeBackwardsGraph types) →
    (witnesses : SevenProgrammeWitnesses types) →
  CompleteSingleGroupContinuumYM graph
completeSingleGroupFromSeven graph witnesses =
  compileCompleteSingleGroupContinuumYM graph
    (continuumSchwingerFromSeven graph witnesses)
    (continuumLocalFieldOPEStressTensor witnesses)
    (sameLimitInteractionSurvival witnesses)
    (sameLimitPhysicalExponentialClustering witnesses)

allCompactSimpleFromSeven :
  ∀ {types}
    (graph : SevenProgrammeBackwardsGraph types) →
    (witnesses : SevenProgrammeWitnesses types) →
  AllCompactSimpleContinuumYM graph
allCompactSimpleFromSeven graph witnesses =
  compileAllCompactSimpleContinuumYM graph
    (completeSingleGroupFromSeven graph witnesses)
    (compactSimpleGroupPromotion witnesses)

claySolutionFromSevenProgrammes :
  ∀ {types}
    (graph : SevenProgrammeBackwardsGraph types) →
    (witnesses : SevenProgrammeWitnesses types) →
  Clay.ClayYangMillsSolution (clayVocabulary graph)
claySolutionFromSevenProgrammes graph witnesses =
  identifyLiteralClaySolution graph
    (allCompactSimpleFromSeven graph witnesses)

sevenProgrammeCount : Nat
sevenProgrammeCount = 1 + 1 + 1 + 1 + 1 + 1 + 1

sevenProgrammeCountExact : sevenProgrammeCount ≡ 7
sevenProgrammeCountExact = refl

sevenProgrammeBackwardsCompilerLevel : ProofLevel
sevenProgrammeBackwardsCompilerLevel = machineChecked

sevenProgrammeConcretePhysicalInstantiationLevel : ProofLevel
sevenProgrammeConcretePhysicalInstantiationLevel = conditional
