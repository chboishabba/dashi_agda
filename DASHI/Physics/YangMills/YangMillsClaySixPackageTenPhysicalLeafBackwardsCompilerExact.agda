module DASHI.Physics.YangMills.YangMillsClaySixPackageTenPhysicalLeafBackwardsCompilerExact where

------------------------------------------------------------------------
-- ROUND66: SIX PACKAGES / TEN GENUINELY NEW PHYSICAL LEAVES
--
-- The eleven-leaf diagnostic remains useful, but transfer-gap -> observable
-- clustering is standard semigroup/Cauchy--Schwarz once the SAME physical
-- transfer representation is identified.  Therefore it is not counted as an
-- independent Yang--Mills analytic producer here.
--
-- The ten physical leaves are:
--   1 signed five-block G2;
--   2 literal Wilson/FP/Haar Ward scalar;
--   3 regular one-loop matching remainder;
--   4 literal CMP119/122 carrier + transfer/observable representation;
--   5 terminal/reference physical gap;
--   6 cutoff-uniform Feshbach/Schur loss budget;
--   7 unified polymer/Schwinger continuum contraction;
--   8 composite/OPE/stress Ward construction;
--   9 strict finite-scale fourth-cumulant margin;
--  10 compact-simple parametric continuation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay

record TenPhysicalLeafTypes : Set₁ where
  field
    SignedFiveBlockG2 : Set
    LiteralWilsonFPHaarWardScalar : Set
    RegularOneLoopMatchingRemainder : Set
    LiteralCMP119122TransferObservableCarrier : Set
    PhysicalTerminalReferenceGap : Set
    CutoffUniformFeshbachLossBudget : Set
    UnifiedPolymerSchwingerContinuum : Set
    CompositeOPEStressWard : Set
    FiniteScaleFourthCumulantMargin : Set
    CompactSimpleParametricContinuation : Set

open TenPhysicalLeafTypes public

record TenPhysicalLeafWitnesses (types : TenPhysicalLeafTypes) : Set₁ where
  field
    l1 : SignedFiveBlockG2 types
    l2 : LiteralWilsonFPHaarWardScalar types
    l3 : RegularOneLoopMatchingRemainder types
    l4 : LiteralCMP119122TransferObservableCarrier types
    l5 : PhysicalTerminalReferenceGap types
    l6 : CutoffUniformFeshbachLossBudget types
    l7 : UnifiedPolymerSchwingerContinuum types
    l8 : CompositeOPEStressWard types
    l9 : FiniteScaleFourthCumulantMargin types
    l10 : CompactSimpleParametricContinuation types

open TenPhysicalLeafWitnesses public

record SixPackageTenLeafGraph (types : TenPhysicalLeafTypes) : Set₁ where
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
      LiteralCMP119122TransferObservableCarrier types →
      LiteralRenormalizedLatticeFamily

    -- Observable clustering is compiled here from the same transfer carrier and
    -- spectral witnesses; it is not accepted as an eleventh physical input.
    compileUniformSpectralClusteredLattice :
      LiteralRenormalizedLatticeFamily →
      LiteralCMP119122TransferObservableCarrier types →
      PhysicalTerminalReferenceGap types →
      CutoffUniformFeshbachLossBudget types →
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

open SixPackageTenLeafGraph public

literalLattice :
  ∀ {types} (graph : SixPackageTenLeafGraph types) →
  TenPhysicalLeafWitnesses types → LiteralRenormalizedLatticeFamily graph
literalLattice graph witnesses =
  compileLiteralRG graph
    (l1 witnesses) (l2 witnesses) (l3 witnesses) (l4 witnesses)

spectralClusteredLattice :
  ∀ {types} (graph : SixPackageTenLeafGraph types) →
  (witnesses : TenPhysicalLeafWitnesses types) →
  UniformSpectralClusteredLatticeFamily graph
spectralClusteredLattice graph witnesses =
  compileUniformSpectralClusteredLattice graph
    (literalLattice graph witnesses)
    (l4 witnesses) (l5 witnesses) (l6 witnesses)

continuum :
  ∀ {types} (graph : SixPackageTenLeafGraph types) →
  (witnesses : TenPhysicalLeafWitnesses types) →
  ContinuumSchwingerFamily graph
continuum graph witnesses =
  compileUnifiedContinuum graph
    (spectralClusteredLattice graph witnesses) (l7 witnesses)

singleGroup :
  ∀ {types} (graph : SixPackageTenLeafGraph types) →
  (witnesses : TenPhysicalLeafWitnesses types) →
  CompleteSingleGroupContinuumYM graph
singleGroup graph witnesses =
  compileCompleteSingleGroup graph
    (continuum graph witnesses) (l8 witnesses) (l9 witnesses)

allGroups :
  ∀ {types} (graph : SixPackageTenLeafGraph types) →
  (witnesses : TenPhysicalLeafWitnesses types) →
  AllCompactSimpleContinuumYM graph
allGroups graph witnesses =
  compileAllCompactSimple graph
    (singleGroup graph witnesses) (l10 witnesses)

claySolutionFromTenPhysicalLeaves :
  ∀ {types} (graph : SixPackageTenLeafGraph types) →
  (witnesses : TenPhysicalLeafWitnesses types) →
  Clay.ClayYangMillsSolution (clayVocabulary graph)
claySolutionFromTenPhysicalLeaves graph witnesses =
  identifyLiteralClaySolution graph (allGroups graph witnesses)

tenPhysicalLeafCount : Nat
tenPhysicalLeafCount = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1

tenPhysicalLeafCountExact : tenPhysicalLeafCount ≡ 10
tenPhysicalLeafCountExact = refl

sixPackageCount : Nat
sixPackageCount = 1 + 1 + 1 + 1 + 1 + 1

sixPackageCountExact : sixPackageCount ≡ 6
sixPackageCountExact = refl

sixPackageTenPhysicalLeafCompilerLevel : ProofLevel
sixPackageTenPhysicalLeafCompilerLevel = machineChecked

sixPackageTenPhysicalLeafInstantiationLevel : ProofLevel
sixPackageTenPhysicalLeafInstantiationLevel = conditional
