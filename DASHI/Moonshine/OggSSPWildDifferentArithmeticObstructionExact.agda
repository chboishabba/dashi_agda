module DASHI.Moonshine.OggSSPWildDifferentArithmeticObstructionExact where

------------------------------------------------------------------------
-- WILD DIFFERENT / MONSTER GAP: EXACT OBSTRUCTION AND ATTRIBUTION
--
-- SOURCE DIVISION
-- Duncan--Swisher: arithmetic p>3; continuation 36,18 at p=2,3.
-- Kobin--Zureick-Brown: wild stacky canonical data in characteristics 2,3.
--
-- DASHI cross-module comparison ONLY:
--   raw coefficients (14,7) and Monster continuation gaps (10,2)
--   satisfy 14 = 10 + 4 and 7 = 2 + 5.
-- This rules out the *identity observable* as the missing correction.
-- It does not rule out all wild-stack contributions, does not assert that
-- subtracting 4/5 is geometrically meaningful, and does not promote sector
-- counts to arithmetic multiplicities.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact as Candidate
import DASHI.Moonshine.OggSSPSmallCharacteristicWildDifferentNoGoExact as Different
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

rawDifferent : Candidate.SmallCharacteristicPrime -> Nat
rawDifferent Candidate.primeTwo   = Different.p2WildDifferentCoefficient
rawDifferent Candidate.primeThree = Different.p3WildDifferentCoefficient

arithmeticGap : Candidate.SmallCharacteristicPrime -> Nat
arithmeticGap Candidate.primeTwo   = Candidate.wildGeometricSectorCount Candidate.primeTwo
arithmeticGap Candidate.primeThree = Candidate.wildGeometricSectorCount Candidate.primeThree

unpaidOffset : Candidate.SmallCharacteristicPrime -> Nat
unpaidOffset Candidate.primeTwo   = 4
unpaidOffset Candidate.primeThree = 5

-- Genuine arithmetic equalities rather than "false" status fields.
rawDifferentSplits :
  (p : Candidate.SmallCharacteristicPrime) ->
  rawDifferent p ≡ arithmeticGap p + unpaidOffset p
rawDifferentSplits Candidate.primeTwo   = refl
rawDifferentSplits Candidate.primeThree = refl

rawDifferentNotGap :
  (p : Candidate.SmallCharacteristicPrime) ->
  rawDifferent p ≡ arithmeticGap p -> ⊥
rawDifferentNotGap Candidate.primeTwo ()
rawDifferentNotGap Candidate.primeThree ()

-- Rejects a uniform raw-different=correction hypothesis by a pointwise
-- contradiction, without pretending the *entire* wild-stack mechanism fails.
record RawDifferentIdentityMechanism : Set where
  field
    explains :
      (p : Candidate.SmallCharacteristicPrime) ->
      rawDifferent p ≡ arithmeticGap p

noRawDifferentIdentityMechanism :
  RawDifferentIdentityMechanism -> ⊥
noRawDifferentIdentityMechanism mechanism =
  rawDifferentNotGap Candidate.primeTwo
    (RawDifferentIdentityMechanism.explains mechanism Candidate.primeTwo)

-- This is a bookkeeping identity.  A SOURCE theorem must identify an actual
-- q-expansion/integral-lattice observable and prove it transports to Monster
-- valuation before any correction mechanism can be promoted.
record ArithmeticWildStackMechanism : Set₁ where
  field
    ArithmeticObservable : Set
    sourceObservable :
      Candidate.SmallCharacteristicPrime -> ArithmeticObservable
    valuationContribution :
      ArithmeticObservable -> Nat
    contributionExact :
      (p : Candidate.SmallCharacteristicPrime) ->
      valuationContribution (sourceObservable p) ≡ arithmeticGap p
    -- Separate, uninhabited by this module: direct source provenance that
    -- establishes *why* that observable enters the Monster valuation.
    sourceRecognition :
      Set

-- Whether sourceRecognition is inhabited is intentionally not asserted.
data NumericalMatchProvesWildStackCause : Set where

numericalMatchDoesNotProveWildStackCause :
  NumericalMatchProvesWildStackCause -> ⊥
numericalMatchDoesNotProveWildStackCause ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record WildDifferentArithmeticObstructionBoundary : Set where
  constructor wild-different-arithmetic-obstruction-boundary
  field
    literalP2Split : Bool
    literalP3Split : Bool
    rawIdentityMechanismRuledOut : Bool
    correctionObservableIdentifiedInSource : Bool
    sourceRecognitionPaid : Bool
    geometryToMonsterCausalityProved : Bool

canonicalWildDifferentArithmeticObstructionBoundary :
  WildDifferentArithmeticObstructionBoundary
canonicalWildDifferentArithmeticObstructionBoundary =
  wild-different-arithmetic-obstruction-boundary
    true true true false false false
