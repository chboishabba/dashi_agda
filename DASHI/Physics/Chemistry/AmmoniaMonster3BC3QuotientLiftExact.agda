module DASHI.Physics.Chemistry.AmmoniaMonster3BC3QuotientLiftExact where

open import DASHI.Core.Prelude

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Monster3B
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Actual
import DASHI.Moonshine.Base369Monster3BActualSectorRecognitionBidiExact as Base369
import DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact as NH3

------------------------------------------------------------------------
-- Exact common C3 quotient.
--
-- This upgrades the earlier three-label round trip to the algebraic statement
-- actually justified by the common data: NH3 electronic C3 phases and the
-- Monster-3B central phases are two presentations of the same abstract C3
-- phase coordinate.  The theorem is deliberately quotient-level: it does not
-- map NH3 electronic states to Monster states.
------------------------------------------------------------------------

nh3ToCommon : NH3.ElectronicC3Phase → C3.C3Phase
nh3ToCommon NH3.invariant = C3.phase0
nh3ToCommon NH3.zeta = C3.phase1
nh3ToCommon NH3.zetaSquared = C3.phase2

commonToNH3 : C3.C3Phase → NH3.ElectronicC3Phase
commonToNH3 C3.phase0 = NH3.invariant
commonToNH3 C3.phase1 = NH3.zeta
commonToNH3 C3.phase2 = NH3.zetaSquared

monsterToCommon : Monster3B.CentralPhase3 → C3.C3Phase
monsterToCommon Monster3B.phaseOne = C3.phase0
monsterToCommon Monster3B.phaseZeta = C3.phase1
monsterToCommon Monster3B.phaseZetaSquared = C3.phase2

commonToMonster : C3.C3Phase → Monster3B.CentralPhase3
commonToMonster C3.phase0 = Monster3B.phaseOne
commonToMonster C3.phase1 = Monster3B.phaseZeta
commonToMonster C3.phase2 = Monster3B.phaseZetaSquared

nh3CommonRoundTrip :
  (p : NH3.ElectronicC3Phase) → commonToNH3 (nh3ToCommon p) ≡ p
nh3CommonRoundTrip NH3.invariant = refl
nh3CommonRoundTrip NH3.zeta = refl
nh3CommonRoundTrip NH3.zetaSquared = refl

commonNH3RoundTrip :
  (p : C3.C3Phase) → nh3ToCommon (commonToNH3 p) ≡ p
commonNH3RoundTrip C3.phase0 = refl
commonNH3RoundTrip C3.phase1 = refl
commonNH3RoundTrip C3.phase2 = refl

monsterCommonRoundTrip :
  (p : Monster3B.CentralPhase3) → commonToMonster (monsterToCommon p) ≡ p
monsterCommonRoundTrip Monster3B.phaseOne = refl
monsterCommonRoundTrip Monster3B.phaseZeta = refl
monsterCommonRoundTrip Monster3B.phaseZetaSquared = refl

commonMonsterRoundTrip :
  (p : C3.C3Phase) → monsterToCommon (commonToMonster p) ≡ p
commonMonsterRoundTrip C3.phase0 = refl
commonMonsterRoundTrip C3.phase1 = refl
commonMonsterRoundTrip C3.phase2 = refl

nh3ToMonster : NH3.ElectronicC3Phase → Monster3B.CentralPhase3
nh3ToMonster p = commonToMonster (nh3ToCommon p)

monsterToNH3 : Monster3B.CentralPhase3 → NH3.ElectronicC3Phase
monsterToNH3 p = commonToNH3 (monsterToCommon p)

nh3MonsterRoundTrip :
  (p : NH3.ElectronicC3Phase) → monsterToNH3 (nh3ToMonster p) ≡ p
nh3MonsterRoundTrip NH3.invariant = refl
nh3MonsterRoundTrip NH3.zeta = refl
nh3MonsterRoundTrip NH3.zetaSquared = refl

monsterNH3RoundTrip :
  (p : Monster3B.CentralPhase3) → nh3ToMonster (monsterToNH3 p) ≡ p
monsterNH3RoundTrip Monster3B.phaseOne = refl
monsterNH3RoundTrip Monster3B.phaseZeta = refl
monsterNH3RoundTrip Monster3B.phaseZetaSquared = refl

------------------------------------------------------------------------
-- Group law and inversion transported through the common quotient.
------------------------------------------------------------------------

multiplyNH3 :
  NH3.ElectronicC3Phase → NH3.ElectronicC3Phase → NH3.ElectronicC3Phase
multiplyNH3 a b = commonToNH3 (C3.multiplyPhase (nh3ToCommon a) (nh3ToCommon b))

multiplyMonster :
  Monster3B.CentralPhase3 → Monster3B.CentralPhase3 → Monster3B.CentralPhase3
multiplyMonster a b =
  commonToMonster (C3.multiplyPhase (monsterToCommon a) (monsterToCommon b))

inverseNH3 : NH3.ElectronicC3Phase → NH3.ElectronicC3Phase
inverseNH3 p = commonToNH3 (C3.conjugatePhase (nh3ToCommon p))

nh3MonsterMultiplicationIntertwines :
  (a b : NH3.ElectronicC3Phase) →
  nh3ToMonster (multiplyNH3 a b)
  ≡ multiplyMonster (nh3ToMonster a) (nh3ToMonster b)
nh3MonsterMultiplicationIntertwines NH3.invariant NH3.invariant = refl
nh3MonsterMultiplicationIntertwines NH3.invariant NH3.zeta = refl
nh3MonsterMultiplicationIntertwines NH3.invariant NH3.zetaSquared = refl
nh3MonsterMultiplicationIntertwines NH3.zeta NH3.invariant = refl
nh3MonsterMultiplicationIntertwines NH3.zeta NH3.zeta = refl
nh3MonsterMultiplicationIntertwines NH3.zeta NH3.zetaSquared = refl
nh3MonsterMultiplicationIntertwines NH3.zetaSquared NH3.invariant = refl
nh3MonsterMultiplicationIntertwines NH3.zetaSquared NH3.zeta = refl
nh3MonsterMultiplicationIntertwines NH3.zetaSquared NH3.zetaSquared = refl

nh3MonsterInversionIntertwines :
  (p : NH3.ElectronicC3Phase) →
  nh3ToMonster (inverseNH3 p) ≡ Monster3B.invertPhase (nh3ToMonster p)
nh3MonsterInversionIntertwines NH3.invariant = refl
nh3MonsterInversionIntertwines NH3.zeta = refl
nh3MonsterInversionIntertwines NH3.zetaSquared = refl

------------------------------------------------------------------------
-- Character/Fourier compatibility.
------------------------------------------------------------------------

monsterFourierRow : Monster3B.CentralPhase3 → Fourier.FourierRow
monsterFourierRow Monster3B.phaseOne = Fourier.chi0
monsterFourierRow Monster3B.phaseZeta = Fourier.chi1
monsterFourierRow Monster3B.phaseZetaSquared = Fourier.chi2

nh3MonsterFourierRowsIntertwine :
  (p : NH3.ElectronicC3Phase) →
  monsterFourierRow (nh3ToMonster p) ≡ NH3.phaseFourierRow p
nh3MonsterFourierRowsIntertwine NH3.invariant = refl
nh3MonsterFourierRowsIntertwine NH3.zeta = refl
nh3MonsterFourierRowsIntertwine NH3.zetaSquared = refl

------------------------------------------------------------------------
-- Exact lift target into the already-owned literal Monster/Base369 sector.
------------------------------------------------------------------------

record NH3ToActualMonsterZetaLift (NH3State ActualSector : Set) : Set₁ where
  constructor nh3ToActualMonsterZetaLift
  field
    recognition : Actual.ActualZetaSectorRecognition ActualSector
    nh3Phase : NH3State → NH3.ElectronicC3Phase
    toActualZeta : NH3State → ActualSector
    fromActualZeta : ActualSector → NH3State
    fromAfterTo : (s : NH3State) → fromActualZeta (toActualZeta s) ≡ s
    toAfterFrom : (s : ActualSector) → toActualZeta (fromActualZeta s) ≡ s
    allNH3StatesAreZetaSector : (s : NH3State) → nh3Phase s ≡ NH3.zeta
    physicalSameObjectAuthority : Set

open NH3ToActualMonsterZetaLift public

liftRecognitionToBase369 :
  ∀ {NH3State ActualSector} →
  NH3ToActualMonsterZetaLift NH3State ActualSector →
  Base369.ActualBase369SectorRecognition ActualSector
liftRecognitionToBase369 lift =
  Base369.composeActualRecognitionWithBase369 (recognition lift)

record C3QuotientRepresentationIntertwiner : Set where
  constructor c3QuotientRepresentationIntertwiner
  field
    forward : NH3.ElectronicC3Phase → Monster3B.CentralPhase3
    backward : Monster3B.CentralPhase3 → NH3.ElectronicC3Phase
    forwardBackward : (m : Monster3B.CentralPhase3) → forward (backward m) ≡ m
    backwardForward : (n : NH3.ElectronicC3Phase) → backward (forward n) ≡ n
    multiplicationLaw :
      (a b : NH3.ElectronicC3Phase) →
      forward (multiplyNH3 a b) ≡ multiplyMonster (forward a) (forward b)
    inversionLaw :
      (a : NH3.ElectronicC3Phase) →
      forward (inverseNH3 a) ≡ Monster3B.invertPhase (forward a)
    FourierLaw :
      (a : NH3.ElectronicC3Phase) →
      monsterFourierRow (forward a) ≡ NH3.phaseFourierRow a
    scope : String

open C3QuotientRepresentationIntertwiner public

canonicalC3QuotientRepresentationIntertwiner : C3QuotientRepresentationIntertwiner
canonicalC3QuotientRepresentationIntertwiner =
  c3QuotientRepresentationIntertwiner
    nh3ToMonster
    monsterToNH3
    monsterNH3RoundTrip
    nh3MonsterRoundTrip
    nh3MonsterMultiplicationIntertwines
    nh3MonsterInversionIntertwines
    nh3MonsterFourierRowsIntertwine
    "exact C3 quotient representation isomorphism preserving product, inversion and Fourier rows; does not by itself lift NH3 states into the literal Monster zeta sector"

record C3QuotientLiftBoundary : Set where
  constructor c3QuotientLiftBoundary
  field
    phaseBijectionPaid : Bool
    phaseBijectionPaidIsTrue : phaseBijectionPaid ≡ true
    c3GroupLawIntertwiningPaid : Bool
    c3GroupLawIntertwiningPaidIsTrue : c3GroupLawIntertwiningPaid ≡ true
    conjugationInversionIntertwiningPaid : Bool
    conjugationInversionIntertwiningPaidIsTrue :
      conjugationInversionIntertwiningPaid ≡ true
    fourierCharacterIntertwiningPaid : Bool
    fourierCharacterIntertwiningPaidIsTrue :
      fourierCharacterIntertwiningPaid ≡ true
    literalMonsterBase369LiftTargetExists : Bool
    literalMonsterBase369LiftTargetExistsIsTrue :
      literalMonsterBase369LiftTargetExists ≡ true
    actualNH3StateToMonsterSectorLiftPaid : Bool
    actualNH3StateToMonsterSectorLiftPaidIsFalse :
      actualNH3StateToMonsterSectorLiftPaid ≡ false
    nontrivialPhysicalMonsterActionOnNH3Paid : Bool
    nontrivialPhysicalMonsterActionOnNH3PaidIsFalse :
      nontrivialPhysicalMonsterActionOnNH3Paid ≡ false
    quotientIntertwinerCreatesStateIntertwiner : Bool
    quotientIntertwinerCreatesStateIntertwinerIsFalse :
      quotientIntertwinerCreatesStateIntertwiner ≡ false
    missingPayment : String

open C3QuotientLiftBoundary public

canonicalC3QuotientLiftBoundary : C3QuotientLiftBoundary
canonicalC3QuotientLiftBoundary =
  c3QuotientLiftBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "construct a proof-relevant same-object map from a nontrivial NH3 electronic/vibronic state carrier into an ActualZetaSectorRecognition carrier, with physical authority and action equivariance beyond the shared C3 quotient"
