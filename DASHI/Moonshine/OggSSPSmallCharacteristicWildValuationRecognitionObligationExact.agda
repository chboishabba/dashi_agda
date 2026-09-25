module DASHI.Moonshine.OggSSPSmallCharacteristicWildValuationRecognitionObligationExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC WILD VALUATION RECOGNITION OBLIGATION
--
-- This is the exact theorem interface still missing after the classical
-- carrier/moduli work.
--
-- A valid proof must NOT merely supply the known numbers 10 and 2.  It must
-- construct a small-characteristic arithmetic observable whose valuation
-- decomposes into:
--
--   Duncan--Swisher continuation + geometry-derived correction
--
-- and prove that the correction descends from the relevant stack/marked-moduli
-- structure.
--
-- p=2 geometry:
--   orientation doublet x loop-reversal quotient of supersingular inertia.
--
-- p=3 geometry:
--   Deligne--Rapoport branch/node/branch local incidence object.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact as Wild
import DASHI.Moonshine.OggSSPP2OrientedInertiaModuliProblemExact as P2Geometry
import DASHI.Moonshine.OggSSPP3DeligneRapoportStratumCodeExact as P3Geometry
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Domain-separated arithmetic observables.
------------------------------------------------------------------------

data SmallPrime : Set where
  p2 p3 : SmallPrime

laneOf : SmallPrime -> Lane.MonsterPrimeLane
laneOf p2 = Lane.p2
laneOf p3 = Lane.p3

baseline : SmallPrime -> Nat
baseline p2 = Exponent.duncanSwisherExceptionalRHS Lane.p2
baseline p3 = Exponent.duncanSwisherExceptionalRHS Lane.p3

monsterExponent : SmallPrime -> Nat
monsterExponent p =
  Exponent.monsterOrderExponent (laneOf p)

requiredCorrection : SmallPrime -> Nat
requiredCorrection p2 = 10
requiredCorrection p3 = 2

------------------------------------------------------------------------
-- 2. A valuation witness is richer than a Nat equality.
------------------------------------------------------------------------

record WildValuationWitness (p : SmallPrime) : Set₁ where
  field
    ArithmeticObject : Set
    arithmeticObject : ArithmeticObject

    IntegralModel : Set
    integralModel : IntegralModel

    ExpansionData : Set
    expansionData : ExpansionData

    valuation :
      IntegralModel ->
      ExpansionData ->
      Nat

    totalValuation :
      valuation integralModel expansionData
      ≡ monsterExponent p

    tameContinuationContribution :
      Nat

    tameContinuationExact :
      tameContinuationContribution
      ≡ baseline p

    GeometryWitness : Set
    geometryWitness : GeometryWitness

    stackCorrection :
      GeometryWitness ->
      Nat

    correctionContribution :
      Nat

    correctionContributionExact :
      correctionContribution
      ≡ stackCorrection geometryWitness

    valuationSplits :
      valuation integralModel expansionData
      ≡ tameContinuationContribution + correctionContribution

    correctionHasArithmeticDerivation : Bool
    correctionHasArithmeticDerivationIsTrue :
      correctionHasArithmeticDerivation ≡ true

    correctionUsesMarkedGeometry : Bool
    correctionUsesMarkedGeometryIsTrue :
      correctionUsesMarkedGeometry ≡ true

    correctionIsNotInsertedAsTargetConstant : Bool
    correctionIsNotInsertedAsTargetConstantIsTrue :
      correctionIsNotInsertedAsTargetConstant ≡ true

open WildValuationWitness public

------------------------------------------------------------------------
-- 3. Prime-specific geometry obligations.
------------------------------------------------------------------------

record P2WildValuationRecognition : Set₁ where
  field
    witness :
      WildValuationWitness p2

    p2GeometryBoundary :
      P2Geometry.P2OrientedInertiaModuliProblemBoundary

    correctionMatchesTen :
      correctionContribution witness ≡ 10

    geometryIsOrientedInertia :
      correctionUsesMarkedGeometry witness ≡ true

    gamma04TenPointShortcutUsed : Bool
    gamma04TenPointShortcutUsedIsFalse :
      gamma04TenPointShortcutUsed ≡ false

open P2WildValuationRecognition public

record P3WildValuationRecognition : Set₁ where
  field
    witness :
      WildValuationWitness p3

    p3GeometryBoundary :
      P3Geometry.P3DeligneRapoportStratumCodeBoundary

    correctionMatchesTwo :
      correctionContribution witness ≡ 2

    geometryIsLocalStrata :
      correctionUsesMarkedGeometry witness ≡ true

    f9CoordinateUsedAsFormalParameter : Bool
    f9CoordinateUsedAsFormalParameterIsFalse :
      f9CoordinateUsedAsFormalParameter ≡ false

open P3WildValuationRecognition public

------------------------------------------------------------------------
-- 4. Full recognition requires both primes.
------------------------------------------------------------------------

record SmallCharacteristicWildValuationRecognition : Set₁ where
  field
    p2Recognition :
      P2WildValuationRecognition

    p3Recognition :
      P3WildValuationRecognition

    sameMechanismFamily :
      Bool

    sameMechanismFamilyIsTrue :
      sameMechanismFamily ≡ true

    externalArithmeticRecognitionPaid :
      Bool

    externalArithmeticRecognitionPaidIsTrue :
      externalArithmeticRecognitionPaid ≡ true

open SmallCharacteristicWildValuationRecognition public

------------------------------------------------------------------------
-- 5. Known numerical identities are insufficient.
------------------------------------------------------------------------

data ExactGapEqualityCreatesWitness : Set where
data SectorCountCreatesValuationMap : Set where
data WildDifferentNoGoEliminatesAllWildMechanisms : Set where
data ClassicalCarrierRecognitionCreatesMonsterArithmetic : Set where

exactGapEqualityDoesNotCreateWitness :
  ExactGapEqualityCreatesWitness -> ⊥
exactGapEqualityDoesNotCreateWitness ()

sectorCountDoesNotCreateValuationMap :
  SectorCountCreatesValuationMap -> ⊥
sectorCountDoesNotCreateValuationMap ()

wildDifferentNoGoDoesNotEliminateAllWildMechanisms :
  WildDifferentNoGoEliminatesAllWildMechanisms -> ⊥
wildDifferentNoGoDoesNotEliminateAllWildMechanisms ()

classicalCarrierRecognitionDoesNotCreateMonsterArithmetic :
  ClassicalCarrierRecognitionCreatesMonsterArithmetic -> ⊥
classicalCarrierRecognitionDoesNotCreateMonsterArithmetic ()

------------------------------------------------------------------------
-- 6. Frontier receipt.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record WildValuationRecognitionBoundary : Set where
  constructor wild-valuation-recognition-boundary
  field
    p2ExactGapKnown : Bool
    p3ExactGapKnown : Bool
    p2ClassicalGeometryKnown : Bool
    p3ClassicalGeometryKnown : Bool
    rawWildDifferentRejected : Bool
    arithmeticObjectStillRequired : Bool
    integralModelStillRequired : Bool
    expansionValuationStillRequired : Bool
    geometryToCorrectionDerivationStillRequired : Bool
    p2RecognitionInhabited : Bool
    p3RecognitionInhabited : Bool
    fullRecognitionInhabited : Bool

canonicalWildValuationRecognitionBoundary :
  WildValuationRecognitionBoundary
canonicalWildValuationRecognitionBoundary =
  wild-valuation-recognition-boundary
    true true true true true
    true true true true
    false false false
