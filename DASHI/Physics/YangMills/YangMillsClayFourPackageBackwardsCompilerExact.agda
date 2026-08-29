module DASHI.Physics.YangMills.YangMillsClayFourPackageBackwardsCompilerExact where

------------------------------------------------------------------------
-- ROUND65: CONDITIONAL FOUR-PACKAGE COLLAPSE
--
-- The seven-programme graph is the current honest cutset.  This file encodes
-- the highest-alpha stronger possibility without pretending it is already
-- proved: if ONE unified continuum RG theorem simultaneously constructs the
-- continuum limit, local/OPE/stress data, interacting survival and physical
-- clustering on that same limit, then the literal Clay graph has four research
-- packages rather than seven.
--
-- F1 literal weak-coupling RG construction
-- F2 cutoff-uniform physical spectral theorem
-- F3 unified continuum RG completion
-- F4 compact-simple-group promotion
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay

record FourPackageTypes : Set₁ where
  field
    LiteralWeakCouplingRGConstruction : Set
    CutoffUniformPhysicalSpectralTheorem : Set
    UnifiedContinuumRGCompletion : Set
    CompactSimpleGroupPromotion : Set

open FourPackageTypes public

record FourPackageWitnesses (types : FourPackageTypes) : Set₁ where
  field
    literalWeakCouplingRGConstruction :
      LiteralWeakCouplingRGConstruction types
    cutoffUniformPhysicalSpectralTheorem :
      CutoffUniformPhysicalSpectralTheorem types
    unifiedContinuumRGCompletion : UnifiedContinuumRGCompletion types
    compactSimpleGroupPromotion : CompactSimpleGroupPromotion types

open FourPackageWitnesses public

record FourPackageBackwardsGraph (types : FourPackageTypes) : Set₁ where
  field
    RenormalizedLatticeFamily : Set
    UniformSpectralTheory : Set
    CompleteSingleGroupContinuumYM : Set
    AllCompactSimpleContinuumYM : Set

    clayVocabulary : Clay.ClayProblemVocabulary

    compileRenormalizedLatticeFamily :
      LiteralWeakCouplingRGConstruction types → RenormalizedLatticeFamily

    compileUniformSpectralTheory :
      RenormalizedLatticeFamily →
      CutoffUniformPhysicalSpectralTheorem types →
      UniformSpectralTheory

    -- F3 deliberately jumps from the uniform lattice/spectral family to the
    -- COMPLETE same-group continuum theory.  Therefore a future inhabitant of
    -- this field must own all continuum/OPE/nontriviality/clustering data on one
    -- carrier; those requirements cannot be discharged on unrelated limits.
    compileUnifiedContinuumRGCompletion :
      UniformSpectralTheory →
      UnifiedContinuumRGCompletion types →
      CompleteSingleGroupContinuumYM

    compileAllCompactSimpleContinuumYM :
      CompleteSingleGroupContinuumYM →
      CompactSimpleGroupPromotion types →
      AllCompactSimpleContinuumYM

    identifyLiteralClaySolution :
      AllCompactSimpleContinuumYM →
      Clay.ClayYangMillsSolution clayVocabulary

open FourPackageBackwardsGraph public

renormalizedLatticeFromFour :
  ∀ {types}
    (graph : FourPackageBackwardsGraph types) →
    FourPackageWitnesses types →
  RenormalizedLatticeFamily graph
renormalizedLatticeFromFour graph witnesses =
  compileRenormalizedLatticeFamily graph
    (literalWeakCouplingRGConstruction witnesses)

uniformSpectralTheoryFromFour :
  ∀ {types}
    (graph : FourPackageBackwardsGraph types) →
    (witnesses : FourPackageWitnesses types) →
  UniformSpectralTheory graph
uniformSpectralTheoryFromFour graph witnesses =
  compileUniformSpectralTheory graph
    (renormalizedLatticeFromFour graph witnesses)
    (cutoffUniformPhysicalSpectralTheorem witnesses)

completeSingleGroupFromFour :
  ∀ {types}
    (graph : FourPackageBackwardsGraph types) →
    (witnesses : FourPackageWitnesses types) →
  CompleteSingleGroupContinuumYM graph
completeSingleGroupFromFour graph witnesses =
  compileUnifiedContinuumRGCompletion graph
    (uniformSpectralTheoryFromFour graph witnesses)
    (unifiedContinuumRGCompletion witnesses)

allCompactSimpleFromFour :
  ∀ {types}
    (graph : FourPackageBackwardsGraph types) →
    (witnesses : FourPackageWitnesses types) →
  AllCompactSimpleContinuumYM graph
allCompactSimpleFromFour graph witnesses =
  compileAllCompactSimpleContinuumYM graph
    (completeSingleGroupFromFour graph witnesses)
    (compactSimpleGroupPromotion witnesses)

claySolutionFromFourPackages :
  ∀ {types}
    (graph : FourPackageBackwardsGraph types) →
    (witnesses : FourPackageWitnesses types) →
  Clay.ClayYangMillsSolution (clayVocabulary graph)
claySolutionFromFourPackages graph witnesses =
  identifyLiteralClaySolution graph
    (allCompactSimpleFromFour graph witnesses)

fourPackageCount : Nat
fourPackageCount = 1 + 1 + 1 + 1

fourPackageCountExact : fourPackageCount ≡ 4
fourPackageCountExact = refl

fourPackageBackwardsCompilerLevel : ProofLevel
fourPackageBackwardsCompilerLevel = machineChecked

-- The count four is conditional on constructing a single theorem strong enough
-- to inhabit UnifiedContinuumRGCompletion.  Until then the seven-programme graph
-- remains the authoritative honest cutset.
fourPackagePhysicalCollapseLevel : ProofLevel
fourPackagePhysicalCollapseLevel = conditional
