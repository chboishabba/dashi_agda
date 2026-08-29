module DASHI.Physics.YangMills.YangMillsClaySixPackageElevenLeafBackwardsCompilerExact where

------------------------------------------------------------------------
-- ROUND66: SIX THEOREM PACKAGES / ELEVEN SOURCE-SIDE LEAVES
--
-- This compiler is deliberately finer than the Round65 four-package bet and
-- sharper than the seven-programme graph.  It records the smallest current
-- source-side cutset without pretending that standard semigroup consequences
-- are new Yang--Mills estimates.
--
-- P1 literal weak-coupling RG construction:
--   L1 signed five-block G2;
--   L2 literal Wilson/FP/Haar Ward scalar;
--   L3 regular one-loop matching remainder;
--   L4 literal CMP119/122 carrier + transfer intertwiner.
--
-- P2 cutoff-uniform physical spectral control:
--   L5 terminal/reference physical gap;
--   L6 cutoff-uniform Feshbach/Schur loss budget;
--   L7 transfer-gap -> observable clustering on the same Hilbert carrier.
--
-- P3 unified continuum RG:
--   L8 one polymer/Schwinger norm contraction + uniform Cauchy closure.
--
-- P4 local continuum fields:
--   L9 composite flow / OPE / stress Ward construction.
--
-- P5 interaction survival:
--   L10 strict finite-scale fourth-cumulant margin.
--
-- P6 compact-simple continuation:
--   L11 group-parametric continuation of the complete estimate stack.
--
-- L7 is kept in the eleven-leaf diagnostic for carrier accountability.  A
-- separate Round66 theorem proves that, after the actual transfer-semigroup
-- representation and common spectral floor are identified, its inequality is
-- a Cauchy--Schwarz/semigroup consequence rather than a new physical estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay

record ElevenLeafTypes : Set₁ where
  field
    SignedFiveBlockG2 : Set
    LiteralWilsonFPHaarWardScalar : Set
    RegularOneLoopMatchingRemainder : Set
    LiteralCMP119122CarrierAndTransfer : Set

    PhysicalTerminalReferenceGap : Set
    CutoffUniformFeshbachLossBudget : Set
    TransferGapObservableClustering : Set

    UnifiedPolymerSchwingerContinuum : Set
    CompositeOPEStressWard : Set
    FiniteScaleFourthCumulantMargin : Set
    CompactSimpleParametricContinuation : Set

open ElevenLeafTypes public

record ElevenLeafWitnesses (types : ElevenLeafTypes) : Set₁ where
  field
    l1 : SignedFiveBlockG2 types
    l2 : LiteralWilsonFPHaarWardScalar types
    l3 : RegularOneLoopMatchingRemainder types
    l4 : LiteralCMP119122CarrierAndTransfer types
    l5 : PhysicalTerminalReferenceGap types
    l6 : CutoffUniformFeshbachLossBudget types
    l7 : TransferGapObservableClustering types
    l8 : UnifiedPolymerSchwingerContinuum types
    l9 : CompositeOPEStressWard types
    l10 : FiniteScaleFourthCumulantMargin types
    l11 : CompactSimpleParametricContinuation types

open ElevenLeafWitnesses public

record SixPackageBackwardsGraph (types : ElevenLeafTypes) : Set₁ where
  field
    LiteralRenormalizedLatticeFamily : Set
    UniformSpectralClusteredLatticeFamily : Set
    ContinuumSchwingerFamily : Set
    CompleteSingleGroupContinuumYM : Set
    AllCompactSimpleContinuumYM : Set

    clayVocabulary : Clay.ClayProblemVocabulary

    compileLiteralRG :
      SignedFiveBlockG2 types →
      LiteralWilsonFPHaarWardScalar types →
      RegularOneLoopMatchingRemainder types →
      LiteralCMP119122CarrierAndTransfer types →
      LiteralRenormalizedLatticeFamily

    compileUniformSpectralClusteredLattice :
      LiteralRenormalizedLatticeFamily →
      PhysicalTerminalReferenceGap types →
      CutoffUniformFeshbachLossBudget types →
      TransferGapObservableClustering types →
      UniformSpectralClusteredLatticeFamily

    compileUnifiedContinuum :
      UniformSpectralClusteredLatticeFamily →
      UnifiedPolymerSchwingerContinuum types →
      ContinuumSchwingerFamily

    compileCompleteSingleGroup :
      ContinuumSchwingerFamily →
      CompositeOPEStressWard types →
      FiniteScaleFourthCumulantMargin types →
      CompleteSingleGroupContinuumYM

    compileAllCompactSimple :
      CompleteSingleGroupContinuumYM →
      CompactSimpleParametricContinuation types →
      AllCompactSimpleContinuumYM

    identifyLiteralClaySolution :
      AllCompactSimpleContinuumYM →
      Clay.ClayYangMillsSolution clayVocabulary

open SixPackageBackwardsGraph public

literalLatticeFromEleven :
  ∀ {types}
    (graph : SixPackageBackwardsGraph types) →
    ElevenLeafWitnesses types →
  LiteralRenormalizedLatticeFamily graph
literalLatticeFromEleven graph witnesses =
  compileLiteralRG graph
    (l1 witnesses) (l2 witnesses) (l3 witnesses) (l4 witnesses)

spectralClusteredLatticeFromEleven :
  ∀ {types}
    (graph : SixPackageBackwardsGraph types) →
    (witnesses : ElevenLeafWitnesses types) →
  UniformSpectralClusteredLatticeFamily graph
spectralClusteredLatticeFromEleven graph witnesses =
  compileUniformSpectralClusteredLattice graph
    (literalLatticeFromEleven graph witnesses)
    (l5 witnesses) (l6 witnesses) (l7 witnesses)

continuumFromEleven :
  ∀ {types}
    (graph : SixPackageBackwardsGraph types) →
    (witnesses : ElevenLeafWitnesses types) →
  ContinuumSchwingerFamily graph
continuumFromEleven graph witnesses =
  compileUnifiedContinuum graph
    (spectralClusteredLatticeFromEleven graph witnesses)
    (l8 witnesses)

singleGroupFromEleven :
  ∀ {types}
    (graph : SixPackageBackwardsGraph types) →
    (witnesses : ElevenLeafWitnesses types) →
  CompleteSingleGroupContinuumYM graph
singleGroupFromEleven graph witnesses =
  compileCompleteSingleGroup graph
    (continuumFromEleven graph witnesses)
    (l9 witnesses) (l10 witnesses)

allGroupsFromEleven :
  ∀ {types}
    (graph : SixPackageBackwardsGraph types) →
    (witnesses : ElevenLeafWitnesses types) →
  AllCompactSimpleContinuumYM graph
allGroupsFromEleven graph witnesses =
  compileAllCompactSimple graph
    (singleGroupFromEleven graph witnesses)
    (l11 witnesses)

claySolutionFromElevenLeaves :
  ∀ {types}
    (graph : SixPackageBackwardsGraph types) →
    (witnesses : ElevenLeafWitnesses types) →
  Clay.ClayYangMillsSolution (clayVocabulary graph)
claySolutionFromElevenLeaves graph witnesses =
  identifyLiteralClaySolution graph (allGroupsFromEleven graph witnesses)

sixPackageCount : Nat
sixPackageCount = 1 + 1 + 1 + 1 + 1 + 1

sixPackageCountExact : sixPackageCount ≡ 6
sixPackageCountExact = refl

elevenLeafCount : Nat
elevenLeafCount = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1

elevenLeafCountExact : elevenLeafCount ≡ 11
elevenLeafCountExact = refl

sixPackageElevenLeafCompilerLevel : ProofLevel
sixPackageElevenLeafCompilerLevel = machineChecked

sixPackageElevenLeafPhysicalInstantiationLevel : ProofLevel
sixPackageElevenLeafPhysicalInstantiationLevel = conditional
