module DASHI.Physics.YangMills.YangMillsClayTenMasterBackwardsCompilerExact where

------------------------------------------------------------------------
-- ROUND64: TEN-MASTER BACKWARDS COMPILER TO THE LITERAL CLAY TYPE
--
-- Round63 was intentionally aggressive, but its thirteen fields were still
-- implementation-shaped and its endpoint was an abstract Set named
-- SU2ClayConclusion.  The literal repository contract is stronger: it requires
-- local gauge-invariant curvature operators, short-distance AF/OPE/stress-
-- tensor data, and a construction for every compact simple gauge group.
--
-- Round64 therefore makes the final target exactly
--
--   ClayYangMillsSolution vocabulary
--
-- and exposes ten MASTER analytic producers.  Several Round63 leaves now live
-- only inside proof decompositions:
--
--   2 G2 leaves                 -> 1 signed G2 master theorem
--   2 transfer-naturality leaves-> 1 physical transfer intertwiner theorem
--   2 gap leaves                -> 1 cutoff-uniform physical gap theorem
--   3 continuum leaves          -> 1 strong same-family convergence theorem
--
-- while two literal Clay obligations absent from Round63 become explicit:
--
--   local operators/OPE/stress tensor;
--   all compact-simple-group uniformization.
--
-- No master proposition is postulated here.  This file is the backwards proof
-- compiler: future work replaces fields by concrete theorem types and then
-- constructs their witnesses.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay

------------------------------------------------------------------------
-- 1. The ten mathematical producer proposition TYPES.
------------------------------------------------------------------------

record TenMasterProducerTypes : Set₁ where
  field
    -- M1. One signed selected-region G2 absorption theorem.
    SignedSelectedRegionG2Absorption : Set

    -- M2. Literal Wilson + reduced FP ghost + Haar one-loop coefficient.
    LiteralWilsonGhostHaarOneLoopCoefficient : Set

    -- M3. Whole-good-class nonlinear one-step RG stability, uniform in the
    -- physical cutoff/volume parameters required downstream.
    UniformNonlinearOneStepRGStability : Set

    -- M4. Literal physical transfer equation B T_n = T_{n+1} B.
    LiteralOSCompatibleTransferNaturality : Set

    -- M5. Positive gap in physical units uniformly along the cutoff family.
    CutoffUniformPhysicalTransferGap : Set

    -- M6. Strong same-family continuum Schwinger convergence, chosen strong
    -- enough to own tightness, uniqueness and cutoff independence rather than
    -- asking for those as unrelated leaves.
    StrongContinuumSchwingerConvergence : Set

    -- M7. Same-family gauge-invariant local curvature operators, quantitative
    -- OPE/short-distance AF matching, local conserved stress tensor and T00/H
    -- identification.
    ContinuumLocalOperatorOPEStressTensor : Set

    -- M8. Strict same-limit interacting/non-Gaussian witness.
    SameLimitFourthCumulantLowerBound : Set

    -- M9. Same-limit exponential clustering in physical units.
    SameLimitPhysicalExponentialClustering : Set

    -- M10. Promotion of the complete construction through every compact simple
    -- gauge group with all group-dependent analytic constants exposed.
    CompactSimpleGroupUniformization : Set

open TenMasterProducerTypes public

record TenMasterProducers (types : TenMasterProducerTypes) : Set₁ where
  field
    signedSelectedRegionG2Absorption :
      SignedSelectedRegionG2Absorption types
    literalWilsonGhostHaarOneLoopCoefficient :
      LiteralWilsonGhostHaarOneLoopCoefficient types
    uniformNonlinearOneStepRGStability :
      UniformNonlinearOneStepRGStability types
    literalOSCompatibleTransferNaturality :
      LiteralOSCompatibleTransferNaturality types
    cutoffUniformPhysicalTransferGap :
      CutoffUniformPhysicalTransferGap types
    strongContinuumSchwingerConvergence :
      StrongContinuumSchwingerConvergence types
    continuumLocalOperatorOPEStressTensor :
      ContinuumLocalOperatorOPEStressTensor types
    sameLimitFourthCumulantLowerBound :
      SameLimitFourthCumulantLowerBound types
    sameLimitPhysicalExponentialClustering :
      SameLimitPhysicalExponentialClustering types
    compactSimpleGroupUniformization :
      CompactSimpleGroupUniformization types

open TenMasterProducers public

------------------------------------------------------------------------
-- 2. The physical theorem graph.
--
-- The stage carriers are shared so same-limit requirements cannot be satisfied
-- on unrelated subsequences or on an operator family detached from the theory
-- used to prove clustering/nontriviality.
------------------------------------------------------------------------

record TenMasterBackwardsGraph (types : TenMasterProducerTypes) : Set₁ where
  field
    RenormalizedLatticeFamily : Set
    UniformTransferTheory : Set
    ContinuumSchwingerFamily : Set
    SingleGroupCompleteContinuumYM : Set
    AllCompactSimpleContinuumYM : Set

    clayVocabulary : Clay.ClayProblemVocabulary

    -- M1+M2+M3 construct the actual scale-uniform renormalized lattice family.
    compileRenormalizedLatticeFamily :
      SignedSelectedRegionG2Absorption types →
      LiteralWilsonGhostHaarOneLoopCoefficient types →
      UniformNonlinearOneStepRGStability types →
      RenormalizedLatticeFamily

    -- M4+M5 construct the transfer theory with physical-unit gap information.
    compileUniformTransferTheory :
      RenormalizedLatticeFamily →
      LiteralOSCompatibleTransferNaturality types →
      CutoffUniformPhysicalTransferGap types →
      UniformTransferTheory

    -- M6 produces ONE continuum family.  Tightness/subsequence extraction and
    -- uniqueness are downstream consequences/ingredients of this stronger
    -- theorem, not independent final producers.
    compileContinuumSchwingerFamily :
      UniformTransferTheory →
      StrongContinuumSchwingerConvergence types →
      ContinuumSchwingerFamily

    -- M7+M8+M9 must all concern that SAME continuum family.
    compileSingleGroupCompleteContinuumYM :
      ContinuumSchwingerFamily →
      ContinuumLocalOperatorOPEStressTensor types →
      SameLimitFourthCumulantLowerBound types →
      SameLimitPhysicalExponentialClustering types →
      SingleGroupCompleteContinuumYM

    -- M10 is not a relabelling of SU(2).  It transports/proves the complete
    -- analytic construction for every compact simple group.
    compileAllCompactSimpleContinuumYM :
      SingleGroupCompleteContinuumYM →
      CompactSimpleGroupUniformization types →
      AllCompactSimpleContinuumYM

    -- No physical theorem remains after this arrow: it is only the exact
    -- identification/assembly of the completed all-group construction with the
    -- literal Clay vocabulary already declared in-repo.
    identifyLiteralClaySolution :
      AllCompactSimpleContinuumYM →
      Clay.ClayYangMillsSolution clayVocabulary

open TenMasterBackwardsGraph public

------------------------------------------------------------------------
-- 3. The complete backwards-compiled proof term.
------------------------------------------------------------------------

renormalizedLatticeFromTenMasters :
  ∀ {types}
    (graph : TenMasterBackwardsGraph types) →
    TenMasterProducers types →
  RenormalizedLatticeFamily graph
renormalizedLatticeFromTenMasters graph producers =
  compileRenormalizedLatticeFamily graph
    (signedSelectedRegionG2Absorption producers)
    (literalWilsonGhostHaarOneLoopCoefficient producers)
    (uniformNonlinearOneStepRGStability producers)

uniformTransferFromTenMasters :
  ∀ {types}
    (graph : TenMasterBackwardsGraph types) →
    (producers : TenMasterProducers types) →
  UniformTransferTheory graph
uniformTransferFromTenMasters graph producers =
  compileUniformTransferTheory graph
    (renormalizedLatticeFromTenMasters graph producers)
    (literalOSCompatibleTransferNaturality producers)
    (cutoffUniformPhysicalTransferGap producers)

continuumSchwingerFromTenMasters :
  ∀ {types}
    (graph : TenMasterBackwardsGraph types) →
    (producers : TenMasterProducers types) →
  ContinuumSchwingerFamily graph
continuumSchwingerFromTenMasters graph producers =
  compileContinuumSchwingerFamily graph
    (uniformTransferFromTenMasters graph producers)
    (strongContinuumSchwingerConvergence producers)

singleGroupCompleteFromTenMasters :
  ∀ {types}
    (graph : TenMasterBackwardsGraph types) →
    (producers : TenMasterProducers types) →
  SingleGroupCompleteContinuumYM graph
singleGroupCompleteFromTenMasters graph producers =
  compileSingleGroupCompleteContinuumYM graph
    (continuumSchwingerFromTenMasters graph producers)
    (continuumLocalOperatorOPEStressTensor producers)
    (sameLimitFourthCumulantLowerBound producers)
    (sameLimitPhysicalExponentialClustering producers)

allCompactSimpleFromTenMasters :
  ∀ {types}
    (graph : TenMasterBackwardsGraph types) →
    (producers : TenMasterProducers types) →
  AllCompactSimpleContinuumYM graph
allCompactSimpleFromTenMasters graph producers =
  compileAllCompactSimpleContinuumYM graph
    (singleGroupCompleteFromTenMasters graph producers)
    (compactSimpleGroupUniformization producers)

claySolutionFromTenMasters :
  ∀ {types}
    (graph : TenMasterBackwardsGraph types) →
    (producers : TenMasterProducers types) →
  Clay.ClayYangMillsSolution (clayVocabulary graph)
claySolutionFromTenMasters graph producers =
  identifyLiteralClaySolution graph
    (allCompactSimpleFromTenMasters graph producers)

------------------------------------------------------------------------
-- 4. Executable count.  This count is a theorem-architecture diagnostic, not
-- a claim that each master theorem is small.
------------------------------------------------------------------------

tenMasterCount : Nat
tenMasterCount = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1

tenMasterCountExact : tenMasterCount ≡ 10
tenMasterCountExact = refl

tenMasterBackwardsCompilerLevel : ProofLevel
tenMasterBackwardsCompilerLevel = machineChecked

-- Concrete instantiation on the literal physical carriers remains conditional
-- until each master producer is actually proved.
tenMasterConcretePhysicalInstantiationLevel : ProofLevel
tenMasterConcretePhysicalInstantiationLevel = conditional
