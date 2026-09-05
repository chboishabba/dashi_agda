module DASHI.Physics.QuantumVacuum.PerfectConductorTETMGenerationCompletenessBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SineNaturalMultiplePiZeroBidiExact as Sine

------------------------------------------------------------------------
-- PERFECT-CONDUCTOR TE/TM: GENERATION != COMPLETENESS
--
-- Forward lane:
--   (polarisation, n, transverse label) -> candidate physical mode.
--
-- Reverse lane:
--   every physical finite-energy plate mode has such coordinates, with the
--   zero sector counted correctly and no duplicate TE/TM representation away
--   from the exceptional sector.
--
-- The forward lane can use the internally owned n*pi sine-zero theorem.
-- Nothing in forward generation proves reverse completeness.
------------------------------------------------------------------------

data Polarisation : Set where
  TE TM : Polarisation

record GeneratedPlateMode : Set₁ where
  field
    TransverseLabel : Set
    transverse : TransverseLabel
    longitudinalIndex : Nat
    polarisation : Polarisation

    LongitudinalArgument : Set
    longitudinalArgument : LongitudinalArgument
    indexedEndpointZero : Set

    PhysicalModeCandidate : Set
    candidate : PhysicalModeCandidate

    boundaryConditionsSatisfied : Set
    sourceFreeWaveEquationSatisfied : Set
    sameIndexAsLongitudinalArgument : Set
    reading : String

open GeneratedPlateMode public

record ForwardPlateModeGenerator : Set₁ where
  field
    TransverseLabel : Set
    Candidate : Set
    generate : Polarisation → Nat → TransverseLabel → Candidate

    indexedSineZeroOwnerUsed : Set
    boundaryTraceCompiler : Set
    waveEquationCompiler : Set
    reading : String

open ForwardPlateModeGenerator public

record PhysicalModeCompleteness
    (G : ForwardPlateModeGenerator) : Set₁ where
  field
    PhysicalMode : Set
    represents : Candidate G → PhysicalMode → Set

    everyPhysicalModeGenerated :
      (m : PhysicalMode) →
      Σ (Candidate G) (λ c → represents c m)

    ZeroSector : PhysicalMode → Set
    teTmUniqueAwayFromZeroSector : Set
    zeroSectorCountingCorrect : Set
    transverseLabelsComplete : Set
    longitudinalIndicesComplete : Set
    finiteEnergyDomainMatches : Set
    reading : String

open PhysicalModeCompleteness public

record ReverseCompletenessObligations : Set where
  field
    physicalModeDomainFixed : Set
    finiteEnergyOrHilbertDomainFixed : Set
    transverseBasisComplete : Set
    longitudinalBasisComplete : Set
    teTmSpanning : Set
    teTmIndependenceAwayFromZero : Set
    zeroSectorQuotientOrCounting : Set
    sameBoundaryProblemAsGenerator : Set

open ReverseCompletenessObligations public

data ForwardGenerationAutomaticallyProvesCompleteness : Set where

data CandidateBoundarySatisfactionAutomaticallyProvesSpanning : Set where

forwardDoesNotProveCompleteness :
  ForwardGenerationAutomaticallyProvesCompleteness → ⊥
forwardDoesNotProveCompleteness ()

boundarySatisfactionDoesNotProveSpanning :
  CandidateBoundarySatisfactionAutomaticallyProvesSpanning → ⊥
boundarySatisfactionDoesNotProveSpanning ()

record BidiStatus : Set where
  field
    indexedSineZerosOwnedForward : Bool
    forwardModeGenerationInterfaceOwned : Bool
    reverseCompletenessInterfaceOwned : Bool
    reverseCompletenessClosed : Bool

    indexedSineZerosOwnedForwardIsTrue : indexedSineZerosOwnedForward ≡ true
    forwardModeGenerationInterfaceOwnedIsTrue : forwardModeGenerationInterfaceOwned ≡ true
    reverseCompletenessInterfaceOwnedIsTrue : reverseCompletenessInterfaceOwned ≡ true
    reverseCompletenessClosedIsFalse : reverseCompletenessClosed ≡ false

open BidiStatus public

canonicalBidiStatus : BidiStatus
canonicalBidiStatus = record
  { indexedSineZerosOwnedForward = true
  ; forwardModeGenerationInterfaceOwned = true
  ; reverseCompletenessInterfaceOwned = true
  ; reverseCompletenessClosed = false
  ; indexedSineZerosOwnedForwardIsTrue = refl
  ; forwardModeGenerationInterfaceOwnedIsTrue = refl
  ; reverseCompletenessInterfaceOwnedIsTrue = refl
  ; reverseCompletenessClosedIsFalse = refl
  }
