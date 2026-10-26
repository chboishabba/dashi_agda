module DASHI.Biology.SignedSSPWeaveSemanticCoreReplayExact where

------------------------------------------------------------------------
-- GENERIC SEMANTIC-CORE REPLAY FOR THE SIGNED SSP WEAVE LANGUAGE
--
-- The instruction language itself determines two components of the rich state:
--   * the full fifteen-lane signed valuation;
--   * the invariant-unit count.
--
-- This module reconstructs those components for arbitrary programs.  It does
-- not invent address369, zero-approach residuals, or description-length data;
-- those are not determined by WeaveInstruction alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

natEq : Nat → Nat → Bool
natEq zero zero = true
natEq zero (suc n) = false
natEq (suc n) zero = false
natEq (suc n) (suc m) = natEq n m

samePrime : Signed.SSPPrime → Signed.SSPPrime → Bool
samePrime p q = natEq (Signed.sspComplexityRank p) (Signed.sspComplexityRank q)

incrementMultiplicity : Signed.SignedMultiplicity → Signed.SignedMultiplicity
incrementMultiplicity Signed.zeroMultiplicity = Signed.positiveMultiplicity 1
incrementMultiplicity (Signed.positiveMultiplicity n) = Signed.positiveMultiplicity (suc n)
incrementMultiplicity (Signed.negativeMultiplicity zero) = Signed.positiveMultiplicity 1
incrementMultiplicity (Signed.negativeMultiplicity (suc zero)) = Signed.zeroMultiplicity
incrementMultiplicity (Signed.negativeMultiplicity (suc (suc n))) =
  Signed.negativeMultiplicity (suc n)

decrementMultiplicity : Signed.SignedMultiplicity → Signed.SignedMultiplicity
decrementMultiplicity Signed.zeroMultiplicity = Signed.negativeMultiplicity 1
decrementMultiplicity (Signed.negativeMultiplicity n) = Signed.negativeMultiplicity (suc n)
decrementMultiplicity (Signed.positiveMultiplicity zero) = Signed.negativeMultiplicity 1
decrementMultiplicity (Signed.positiveMultiplicity (suc zero)) = Signed.zeroMultiplicity
decrementMultiplicity (Signed.positiveMultiplicity (suc (suc n))) =
  Signed.positiveMultiplicity (suc n)

incrementPrime : Signed.SSPPrime → Signed.SSPValuation → Signed.SSPValuation
incrementPrime target valuation query with samePrime target query
... | true = incrementMultiplicity (valuation query)
... | false = valuation query

decrementPrime : Signed.SSPPrime → Signed.SSPValuation → Signed.SSPValuation
decrementPrime target valuation query with samePrime target query
... | true = decrementMultiplicity (valuation query)
... | false = valuation query

record SignedSemanticCore : Set where
  constructor signed-semantic-core
  field
    valuation : Signed.SSPValuation
    invariantUnits : Nat

open SignedSemanticCore public

zeroSemanticCore : SignedSemanticCore
zeroSemanticCore = signed-semantic-core Signed.zeroValuation 0

applyInstructionCore : Signed.WeaveInstruction → SignedSemanticCore → SignedSemanticCore
applyInstructionCore Signed.buildSixByNineFibre core = core
applyInstructionCore Signed.removeInvariantMode core = core
applyInstructionCore (Signed.introducePrime prime)
  (signed-semantic-core valuation units) =
  signed-semantic-core (incrementPrime prime valuation) units
applyInstructionCore (Signed.introduceInversePrime prime)
  (signed-semantic-core valuation units) =
  signed-semantic-core (decrementPrime prime valuation) units
applyInstructionCore Signed.introduceInvariantUnit
  (signed-semantic-core valuation units) =
  signed-semantic-core valuation (suc units)
applyInstructionCore Signed.refineAt369 core = core

executeSemanticCore :
  List Signed.WeaveInstruction → SignedSemanticCore → SignedSemanticCore
executeSemanticCore [] core = core
executeSemanticCore (instruction ∷ rest) core =
  executeSemanticCore rest (applyInstructionCore instruction core)

canonicalVirtualSemanticCore : SignedSemanticCore
canonicalVirtualSemanticCore =
  executeSemanticCore Signed.canonicalVirtualFiftyThreeProgram zeroSemanticCore

canonicalGeometrySemanticCore : SignedSemanticCore
canonicalGeometrySemanticCore =
  executeSemanticCore Signed.canonicalGeometricFiftyThreeProgram zeroSemanticCore

canonicalVirtualValuationPointwise :
  (prime : Signed.SSPPrime) →
  valuation canonicalVirtualSemanticCore prime
  ≡ Signed.virtualFiftyThreeValuation prime
canonicalVirtualValuationPointwise Signed.ssp2 = refl
canonicalVirtualValuationPointwise Signed.ssp3 = refl
canonicalVirtualValuationPointwise Signed.ssp5 = refl
canonicalVirtualValuationPointwise Signed.ssp7 = refl
canonicalVirtualValuationPointwise Signed.ssp11 = refl
canonicalVirtualValuationPointwise Signed.ssp13 = refl
canonicalVirtualValuationPointwise Signed.ssp17 = refl
canonicalVirtualValuationPointwise Signed.ssp19 = refl
canonicalVirtualValuationPointwise Signed.ssp23 = refl
canonicalVirtualValuationPointwise Signed.ssp29 = refl
canonicalVirtualValuationPointwise Signed.ssp31 = refl
canonicalVirtualValuationPointwise Signed.ssp41 = refl
canonicalVirtualValuationPointwise Signed.ssp47 = refl
canonicalVirtualValuationPointwise Signed.ssp59 = refl
canonicalVirtualValuationPointwise Signed.ssp71 = refl

canonicalVirtualInvariantUnitsExact :
  invariantUnits canonicalVirtualSemanticCore ≡ 1
canonicalVirtualInvariantUnitsExact = refl

canonicalGeometryValuationPointwise :
  (prime : Signed.SSPPrime) →
  valuation canonicalGeometrySemanticCore prime ≡ Signed.zeroValuation prime
canonicalGeometryValuationPointwise Signed.ssp2 = refl
canonicalGeometryValuationPointwise Signed.ssp3 = refl
canonicalGeometryValuationPointwise Signed.ssp5 = refl
canonicalGeometryValuationPointwise Signed.ssp7 = refl
canonicalGeometryValuationPointwise Signed.ssp11 = refl
canonicalGeometryValuationPointwise Signed.ssp13 = refl
canonicalGeometryValuationPointwise Signed.ssp17 = refl
canonicalGeometryValuationPointwise Signed.ssp19 = refl
canonicalGeometryValuationPointwise Signed.ssp23 = refl
canonicalGeometryValuationPointwise Signed.ssp29 = refl
canonicalGeometryValuationPointwise Signed.ssp31 = refl
canonicalGeometryValuationPointwise Signed.ssp41 = refl
canonicalGeometryValuationPointwise Signed.ssp47 = refl
canonicalGeometryValuationPointwise Signed.ssp59 = refl
canonicalGeometryValuationPointwise Signed.ssp71 = refl

canonicalGeometryInvariantUnitsExact :
  invariantUnits canonicalGeometrySemanticCore ≡ 0
canonicalGeometryInvariantUnitsExact = refl

record SignedSemanticCoreReplayBoundary : Set where
  constructor signed-semantic-core-replay-boundary
  field
    allFifteenPrimeIdentitiesDistinguished : Bool
    arbitraryProgramValuationReplayConstructed : Bool
    arbitraryProgramInvariantUnitReplayConstructed : Bool
    canonicalVirtualValuationRecoveredPointwise : Bool
    canonicalGeometryValuationRecoveredPointwise : Bool
    addressRecoveredFromInstructionsAlone : Bool
    zeroResidualRecoveredFromInstructionsAlone : Bool
    descriptionLengthsRecoveredFromInstructionsAlone : Bool

canonicalSignedSemanticCoreReplayBoundary : SignedSemanticCoreReplayBoundary
canonicalSignedSemanticCoreReplayBoundary =
  signed-semantic-core-replay-boundary
    true true true true true
    false false false
