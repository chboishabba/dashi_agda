module DASHI.Moonshine.DuncanSwisherSmallCharacteristicFormulaExtensionObligationExact where

------------------------------------------------------------------------
-- DUNCAN--SWISHER SMALL-CHARACTERISTIC FORMULA EXTENSION OBLIGATION
--
-- Proof audit of Duncan--Swisher:
--
--   * Proposition 3.1 partial fractions / lower bounds are prime-generic on
--     the Ogg/genus-zero lane.  Stronger bounds are even available for 2,3.
--
--   * Proposition 4.1 includes every prime with Gamma0(p) genus zero.
--
--   * Proposition 4.2 explicitly includes p in {2,3,5}.
--
--   * Therefore the standard modular-function RHS is already well-defined and
--     computed at p=2,3.
--
--   * That RHS equals 36 and 18, while the Monster exponents are 46 and 20.
--
-- Hence the small-prime problem is NOT merely to repair an intermediate
-- sharpness proof.  Any true extension of Theorem 1.1 must add a genuinely new
-- small-characteristic contribution Delta_p:
--
--     v_p(|M|) = V_p^DS + Delta_p,
--
--     Delta_2 = 10,
--     Delta_3 =  2.
--
-- This file makes the extension obligation typed and fail-closed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.DuncanSwisherDworkPrimeGenericCoefficientFamilyExact as Generic
import DASHI.Moonshine.DuncanSwisherSmallCharacteristicReplacementPaymentExact as Sharpness
import DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact as Wild
import DASHI.Moonshine.OggSSPP2OrientedInertiaModuliProblemExact as P2Geometry
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3Geometry
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Standard Duncan--Swisher small-prime RHS.
------------------------------------------------------------------------

data SmallPrime : Set where
  p2 p3 : SmallPrime

primeLane : SmallPrime -> Lane.MonsterPrimeLane
primeLane p2 = Lane.p2
primeLane p3 = Lane.p3

standardDuncanSwisherRHS : SmallPrime -> Nat
standardDuncanSwisherRHS p =
  Exponent.duncanSwisherExceptionalRHS (primeLane p)

monsterExponent : SmallPrime -> Nat
monsterExponent p =
  Exponent.monsterOrderExponent (primeLane p)

requiredCorrection : SmallPrime -> Nat
requiredCorrection p2 = 10
requiredCorrection p3 = 2

p2StandardRHSIsThirtySix :
  standardDuncanSwisherRHS p2 ≡ 36
p2StandardRHSIsThirtySix = refl

p3StandardRHSIsEighteen :
  standardDuncanSwisherRHS p3 ≡ 18
p3StandardRHSIsEighteen = refl

p2MonsterExponentIsFortySix :
  monsterExponent p2 ≡ 46
p2MonsterExponentIsFortySix = refl

p3MonsterExponentIsTwenty :
  monsterExponent p3 ≡ 20
p3MonsterExponentIsTwenty = refl

p2ExtendedArithmeticIdentity :
  monsterExponent p2
  ≡ standardDuncanSwisherRHS p2 + requiredCorrection p2
p2ExtendedArithmeticIdentity =
  Exponent.p2ExceptionalGap

p3ExtendedArithmeticIdentity :
  monsterExponent p3
  ≡ standardDuncanSwisherRHS p3 + requiredCorrection p3
p3ExtendedArithmeticIdentity =
  Exponent.p3ExceptionalGap

------------------------------------------------------------------------
-- 2. Existing analytic repairs are not sufficient.
------------------------------------------------------------------------

data A1SharpnessImpliesMonsterFormulaAtP2 : Set where
data A1SharpnessImpliesMonsterFormulaAtP3 : Set where
data StrongerProposition31BoundsCreateMissingTerm : Set where
data ExistingThreeTermRHSCanEqualMonsterWithoutExtension : Set where

a1SharpnessAloneDoesNotCloseP2MonsterFormula :
  A1SharpnessImpliesMonsterFormulaAtP2 -> ⊥
a1SharpnessAloneDoesNotCloseP2MonsterFormula ()

a1SharpnessAloneDoesNotCloseP3MonsterFormula :
  A1SharpnessImpliesMonsterFormulaAtP3 -> ⊥
a1SharpnessAloneDoesNotCloseP3MonsterFormula ()

strongerBoundsDoNotByThemselvesCreateMissingTerm :
  StrongerProposition31BoundsCreateMissingTerm -> ⊥
strongerBoundsDoNotByThemselvesCreateMissingTerm ()

existingThreeTermRHSNeedsExtensionAtSmallPrimes :
  ExistingThreeTermRHSCanEqualMonsterWithoutExtension -> ⊥
existingThreeTermRHSNeedsExtensionAtSmallPrimes ()

------------------------------------------------------------------------
-- 3. Exact replacement theorem interface.
--
-- A valid correction observable must be born in the modular/arithmetic layer;
-- an equality of finite carrier counts is not enough.  The observable may use
-- the classically grounded p2/p3 local geometry, but it must produce a theorem
-- that its valuation contribution is exactly Delta_p.
------------------------------------------------------------------------

record SmallPrimeCorrectionObservable
    (p : SmallPrime) : Set₁ where
  field
    Observable : Set
    observable : Observable

    correctionDepth :
      Observable -> Nat

    correctionDepthIsRequiredGap :
      correctionDepth observable ≡ requiredCorrection p

    derivedFromModularOrPadicData :
      Bool
    derivedFromModularOrPadicDataIsTrue :
      derivedFromModularOrPadicData ≡ true

    notDefinedAsCarrierCardinality :
      Bool
    notDefinedAsCarrierCardinalityIsTrue :
      notDefinedAsCarrierCardinality ≡ true

open SmallPrimeCorrectionObservable public

extendedFormulaFromCorrectionObservable :
  (p : SmallPrime) ->
  (C : SmallPrimeCorrectionObservable p) ->
  monsterExponent p
  ≡ standardDuncanSwisherRHS p + correctionDepth C (observable C)
extendedFormulaFromCorrectionObservable p2 C =
  trans
    p2ExtendedArithmeticIdentity
    (cong (standardDuncanSwisherRHS p2 +_) (sym (correctionDepthIsRequiredGap C)))
extendedFormulaFromCorrectionObservable p3 C =
  trans
    p3ExtendedArithmeticIdentity
    (cong (standardDuncanSwisherRHS p3 +_) (sym (correctionDepthIsRequiredGap C)))

------------------------------------------------------------------------
-- 4. Geometry is a candidate DOMAIN for the observable, not its proof.
------------------------------------------------------------------------

p2GeometryBoundary :
  P2Geometry.P2OrientedInertiaModuliProblemBoundary
p2GeometryBoundary =
  P2Geometry.canonicalP2OrientedInertiaModuliProblemBoundary

p3GeometryBoundary :
  P3Geometry.P3DeligneRapoportLocalStrataBoundary
p3GeometryBoundary =
  P3Geometry.canonicalP3DeligneRapoportLocalStrataBoundary

data P2GeometryAlreadyIsCorrectionObservable : Set where
data P3GeometryAlreadyIsCorrectionObservable : Set where
data SectorCountIsPadicValuationByDefinition : Set where

p2GeometryDoesNotAutomaticallySupplyCorrectionObservable :
  P2GeometryAlreadyIsCorrectionObservable -> ⊥
p2GeometryDoesNotAutomaticallySupplyCorrectionObservable ()

p3GeometryDoesNotAutomaticallySupplyCorrectionObservable :
  P3GeometryAlreadyIsCorrectionObservable -> ⊥
p3GeometryDoesNotAutomaticallySupplyCorrectionObservable ()

sectorCountIsNotPadicValuationByDefinition :
  SectorCountIsPadicValuationByDefinition -> ⊥
sectorCountIsNotPadicValuationByDefinition ()

------------------------------------------------------------------------
-- 5. Live frontier.
------------------------------------------------------------------------

data P2CorrectionObservableInhabited : Set where
data P3CorrectionObservableInhabited : Set where

p2CorrectionObservableStillOpen :
  P2CorrectionObservableInhabited -> ⊥
p2CorrectionObservableStillOpen ()

p3CorrectionObservableStillOpen :
  P3CorrectionObservableInhabited -> ⊥
p3CorrectionObservableStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record SmallCharacteristicFormulaExtensionBoundary : Set where
  constructor small-characteristic-formula-extension-boundary
  field
    proposition31PrimeGenericFactored : Bool
    proposition41IncludesSmallPrimes : Bool
    proposition42IncludesTwoThreeFive : Bool
    standardP2RHSComputedThirtySix : Bool
    standardP3RHSComputedEighteen : Bool
    p2MonsterExponentFortySix : Bool
    p3MonsterExponentTwenty : Bool
    p2MissingTermTenExact : Bool
    p3MissingTermTwoExact : Bool
    a1SharpnessAloneSufficient : Bool
    existingThreeTermFormulaSufficientAtSmallPrimes : Bool
    p2CorrectionObservablePaid : Bool
    p3CorrectionObservablePaid : Bool

canonicalSmallCharacteristicFormulaExtensionBoundary :
  SmallCharacteristicFormulaExtensionBoundary
canonicalSmallCharacteristicFormulaExtensionBoundary =
  small-characteristic-formula-extension-boundary
    true true true true true true true true true
    false false false false
