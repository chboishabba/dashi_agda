module DASHI.Moonshine.JackDanielsNaturalMonsterRecognitionMaxCutExact where

------------------------------------------------------------------------
-- JACK DANIEL'S NATURAL-RECOGNITION MAX-CUT
--
-- Current repository state already pays two different things which should no
-- longer be conflated:
--
--   (1) a representation/arithmetic Fricke-closure predicate on the complete
--       twenty-prime control universe;
--   (2) the exact published Monster order.
--
-- This owner first compares those objects directly, without consulting the
-- external Ogg label or MonsterPrimeLane.  It then makes the stronger research
-- target proof-relevant: actual prime-element occurrence, Fricke-class/local
-- recognition, and finally a supersingular -> Monster/McKay-Thompson map.
--
-- The finite support comparison is repository reconstruction.  The stronger
-- recognition records below are TARGET TYPES: support/cardinality does not
-- manufacture their inhabitants.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_%_)
open import Data.Empty using (⊥)

import DASHI.Moonshine.AllPrimeRepresentationFrickeClosureExact as Closure
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.MonsterBinaryTernaryInformationDepthExact as Monster

------------------------------------------------------------------------
-- 1. Finite actual-order support, independent of the external Ogg column.
------------------------------------------------------------------------

monsterOrderRemainder : Closure.PrimeCandidateUnder72 → Nat
monsterOrderRemainder Closure.spinorPrime2 = Monster.monsterOrderExact % 2
monsterOrderRemainder (Closure.oddPrime Matrix.prime3) = Monster.monsterOrderExact % 3
monsterOrderRemainder (Closure.oddPrime Matrix.prime5) = Monster.monsterOrderExact % 5
monsterOrderRemainder (Closure.oddPrime Matrix.prime7) = Monster.monsterOrderExact % 7
monsterOrderRemainder (Closure.oddPrime Matrix.prime11) = Monster.monsterOrderExact % 11
monsterOrderRemainder (Closure.oddPrime Matrix.prime13) = Monster.monsterOrderExact % 13
monsterOrderRemainder (Closure.oddPrime Matrix.prime17) = Monster.monsterOrderExact % 17
monsterOrderRemainder (Closure.oddPrime Matrix.prime19) = Monster.monsterOrderExact % 19
monsterOrderRemainder (Closure.oddPrime Matrix.prime23) = Monster.monsterOrderExact % 23
monsterOrderRemainder (Closure.oddPrime Matrix.prime29) = Monster.monsterOrderExact % 29
monsterOrderRemainder (Closure.oddPrime Matrix.prime31) = Monster.monsterOrderExact % 31
monsterOrderRemainder (Closure.oddPrime Matrix.prime37) = Monster.monsterOrderExact % 37
monsterOrderRemainder (Closure.oddPrime Matrix.prime41) = Monster.monsterOrderExact % 41
monsterOrderRemainder (Closure.oddPrime Matrix.prime43) = Monster.monsterOrderExact % 43
monsterOrderRemainder (Closure.oddPrime Matrix.prime47) = Monster.monsterOrderExact % 47
monsterOrderRemainder (Closure.oddPrime Matrix.prime53) = Monster.monsterOrderExact % 53
monsterOrderRemainder (Closure.oddPrime Matrix.prime59) = Monster.monsterOrderExact % 59
monsterOrderRemainder (Closure.oddPrime Matrix.prime61) = Monster.monsterOrderExact % 61
monsterOrderRemainder (Closure.oddPrime Matrix.prime67) = Monster.monsterOrderExact % 67
monsterOrderRemainder (Closure.oddPrime Matrix.prime71) = Monster.monsterOrderExact % 71

isZero : Nat → Bool
isZero zero = true
isZero (suc _) = false

actualMonsterOrderSupport : Closure.PrimeCandidateUnder72 → Bool
actualMonsterOrderSupport p = isZero (monsterOrderRemainder p)

representationFrickeClosureMatchesActualMonsterSupport :
  (p : Closure.PrimeCandidateUnder72) →
  Closure.representationArithmeticFrickeClosed p ≡ actualMonsterOrderSupport p
representationFrickeClosureMatchesActualMonsterSupport Closure.spinorPrime2 = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime3) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime5) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime7) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime11) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime13) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime17) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime19) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime23) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime29) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime31) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime37) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime41) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime43) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime47) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime53) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime59) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime61) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime67) = refl
representationFrickeClosureMatchesActualMonsterSupport (Closure.oddPrime Matrix.prime71) = refl

prime37ActualRemainder : monsterOrderRemainder (Closure.oddPrime Matrix.prime37) ≡ 21
prime37ActualRemainder = refl
prime43ActualRemainder : monsterOrderRemainder (Closure.oddPrime Matrix.prime43) ≡ 13
prime43ActualRemainder = refl
prime53ActualRemainder : monsterOrderRemainder (Closure.oddPrime Matrix.prime53) ≡ 36
prime53ActualRemainder = refl
prime61ActualRemainder : monsterOrderRemainder (Closure.oddPrime Matrix.prime61) ≡ 47
prime61ActualRemainder = refl
prime67ActualRemainder : monsterOrderRemainder (Closure.oddPrime Matrix.prime67) ≡ 14
prime67ActualRemainder = refl

------------------------------------------------------------------------
-- 2. Stronger Monster-side targets.
--
-- Cauchy occurrence is intentionally represented separately from the much
-- stronger Jack-Daniels recognition object.  A finite-order divisibility fact
-- can justify searching for an order-p element; it does not select the Fricke
-- class, centralizer, p-local structure, action on V^natural, or supersingular
-- correspondence.
------------------------------------------------------------------------

record MonsterPrimeElementOccurrence (p : Nat) : Set₁ where
  constructor monster-prime-element-occurrence
  field
    MonsterCarrier : Set
    element : MonsterCarrier
    elementOrder : MonsterCarrier → Nat
    elementHasPrimeOrder : elementOrder element ≡ p
    actualMonsterIdentification : Set

record FrickeMonsterLocalRecognition (p : Nat) : Set₁ where
  constructor fricke-monster-local-recognition
  field
    occurrence : MonsterPrimeElementOccurrence p
    ConjugacyClass : Set
    Centralizer : Set
    LocalNormalizer : Set
    McKayThompsonDatum : Set
    HauptmodulDatum : Set

    elementInDistinguishedClass : Set
    centralizerIsSameElementCentralizer : Set
    localNormalizerIsSameCyclicSubgroupNormalizer : Set
    mcKayThompsonUsesSameElement : Set
    frickeGroupIsGamma0PlusP : Set
    hauptmodulIsSameMcKayThompsonFunction : Set

record SupersingularMonsterRecognition (p : Nat) : Set₁ where
  constructor supersingular-monster-recognition
  field
    localRecognition : FrickeMonsterLocalRecognition p
    SupersingularJ : Set
    ModularDatum : Set
    MonsterDatum : Set

    supersingularToModular : SupersingularJ → ModularDatum
    modularToMonster : ModularDatum → MonsterDatum
    monsterDatumReadsLocalRecognition : Set

    samePrime : Set
    exceptionalJValuesHandled : Set
    correspondenceRecoversSupersingularLocus : Set
    correspondenceRespectsMonsterActionStructure : Set

------------------------------------------------------------------------
-- 3. Wrong-type firewalls.
------------------------------------------------------------------------

data DivisibilityCreatesDistinguishedFrickeClass : Set where
data FiniteSupportEqualityCreatesSupersingularMonsterMap : Set where
data CarrierCardinalityCreatesGroupAction : Set where

divisibilityDoesNotSelectFrickeClass :
  DivisibilityCreatesDistinguishedFrickeClass → ⊥
divisibilityDoesNotSelectFrickeClass ()

finiteSupportDoesNotCreateNaturalMap :
  FiniteSupportEqualityCreatesSupersingularMonsterMap → ⊥
finiteSupportDoesNotCreateNaturalMap ()

cardinalityDoesNotCreateGroupAction : CarrierCardinalityCreatesGroupAction → ⊥
cardinalityDoesNotCreateGroupAction ()

------------------------------------------------------------------------
-- 4. Machine-readable status.
------------------------------------------------------------------------

record JackDanielsNaturalRecognitionBoundary : Set where
  constructor jack-daniels-natural-recognition-boundary
  field
    finiteRepresentationFrickeVsActualMonsterSupportPaid : Bool
    externalOggLabelUsedInFiniteComparison : Bool
    MonsterPrimeLaneUsedInFiniteComparison : Bool
    orderPElementOccurrenceSeparatedFromSupport : Bool
    distinguishedFrickeClassRecognitionPaid : Bool
    supersingularToMonsterNaturalMapPaid : Bool
    groupStructureVisibleInCorrespondencePaid : Bool
    nextResidual : String

canonicalJackDanielsNaturalRecognitionBoundary : JackDanielsNaturalRecognitionBoundary
canonicalJackDanielsNaturalRecognitionBoundary =
  jack-daniels-natural-recognition-boundary
    true false false true false false false
    "Finite closure equals literal Monster-order support on all twenty controls without the Ogg label. The remaining Jack Daniel's theorem is natural recognition: inhabit a same-prime Monster element/class/local-action object and then a supersingular/modular -> McKay-Thompson/Monster correspondence. Mere divisibility or Cauchy occurrence is not charged as the conceptual endpoint."
