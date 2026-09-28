module DASHI.Moonshine.OggSSPSmallCharacteristicBadLevelIgusaCorrectionCutsetExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC BAD-LEVEL IGUSA / ROOT-STACK CORRECTION CUTSET
--
-- SOURCE SCOPE
--
-- Kobin--Zureick-Brown's explicit ethereal-form multiplicity theorem is stated
-- for level N with p NOT dividing N.  Their Section 8.2 identifies level
-- divisible by the characteristic as future work and suggests the Igusa tower
--
--     Ig(p^n) -> X(1)
--
-- as a natural ramified cover.  They also point out that Ig(p) is the moduli
-- problem of (p-1)-st roots of the Hasse invariant and explicitly say they do
-- not realize the connection to their wild root-stack description in detail.
--
-- DUNCAN--SWISHER INTERSECTION
--
-- The exceptional small-prime formula uses Hauptmodul data at levels p and p^2.
-- Thus the decisive correction problem lies precisely in the bad-level regime
-- omitted by the current wild-stack modular-form multiplicity theorem.
--
-- REQUIRED PAYMENT
--
-- Build one source-independent exceptional analytic object from the p-power
-- Igusa tower / bad-level integral modular geometry, compare it to the sourced
-- wild root-stack local model, and prove that its divisor/q-expansion valuation
-- contributes the missing 10 at p=2 and 2 at p=3.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicCorrectedValuationPaymentExact as Payment
import DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulDivisorCutsetExact as Divisor
import DASHI.Moonshine.OggSSPSmallCharacteristicJointCorrectionCutsetExact as Joint
import DASHI.Moonshine.OggSSPSmallCharacteristicWildLayerSectorProductCandidateExact as LayerSector
import DASHI.Moonshine.OggSSPSmallCharacteristicEtherealMultiplicityTransferExact as Ethereal
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Level profile.
------------------------------------------------------------------------

data BadLevelPrime : Set where
  pTwo pThree : BadLevelPrime

primeNat : BadLevelPrime -> Nat
primeNat pTwo = 2
primeNat pThree = 3

data RelevantPowerLevel : Set where
  firstPrimeLevel :
    RelevantPowerLevel
  primeSquareLevel :
    RelevantPowerLevel

levelExponent : RelevantPowerLevel -> Nat
levelExponent firstPrimeLevel = 1
levelExponent primeSquareLevel = 2

------------------------------------------------------------------------
-- 2. Scope mismatch with the currently sourced ethereal multiplicity theorem.
------------------------------------------------------------------------

data ExistingEtherealTheoremCoversLevelDivisibleByP : Set where
data ExistingWildRootStackPaperRealizesIgusaComparison : Set where
data LevelPrimeToPTheoremCanBeAppliedToPLevelTerm : Set where
data LevelPrimeToPTheoremCanBeAppliedToPSquaredTerm : Set where

existingEtherealTheoremDoesNotCoverBadLevel :
  ExistingEtherealTheoremCoversLevelDivisibleByP -> ⊥
existingEtherealTheoremDoesNotCoverBadLevel ()

rootStackPaperLeavesIgusaComparisonOpen :
  ExistingWildRootStackPaperRealizesIgusaComparison -> ⊥
rootStackPaperLeavesIgusaComparisonOpen ()

primeToPTheoremDoesNotClosePLevel :
  LevelPrimeToPTheoremCanBeAppliedToPLevelTerm -> ⊥
primeToPTheoremDoesNotClosePLevel ()

primeToPTheoremDoesNotClosePSquaredLevel :
  LevelPrimeToPTheoremCanBeAppliedToPSquaredTerm -> ⊥
primeToPTheoremDoesNotClosePSquaredLevel ()

------------------------------------------------------------------------
-- 3. Typed bad-level geometry target.
------------------------------------------------------------------------

data BadLevelGeometryKind : Set where
  igusaPrimeLevel :
    BadLevelGeometryKind
  igusaPrimeSquareLevel :
    BadLevelGeometryKind
  wildRootStackLocalModel :
    BadLevelGeometryKind

record BadLevelIgusaRootStackComparison
    (p : BadLevelPrime) : Set₁ where
  field
    IgusaPrimeLevelObject : Set
    IgusaPrimeSquareObject : Set
    WildLocalObject : Set

    igusaP :
      IgusaPrimeLevelObject
    igusaP2 :
      IgusaPrimeSquareObject
    wildLocal :
      WildLocalObject

    primeLevelMapsToX1 :
      Bool
    primeLevelMapsToX1IsTrue :
      primeLevelMapsToX1 ≡ true

    primeSquareMapsToX1 :
      Bool
    primeSquareMapsToX1IsTrue :
      primeSquareMapsToX1 ≡ true

    comparisonUsesWildRamificationData :
      Bool
    comparisonUsesWildRamificationDataIsTrue :
      comparisonUsesWildRamificationData ≡ true

    comparisonWithRootStackConstructed :
      Bool
    comparisonWithRootStackConstructedIsTrue :
      comparisonWithRootStackConstructed ≡ true

open BadLevelIgusaRootStackComparison public

------------------------------------------------------------------------
-- 4. Corrected bad-level Hauptmodul authority.
--
-- This is deliberately stronger than a count or a stack equivalence: it must
-- reach the actual valuation/divisor surface consumed by the Monster formula.
------------------------------------------------------------------------

record BadLevelIgusaCorrectionAuthority
    (p : BadLevelPrime) : Set₁ where
  field
    comparison :
      BadLevelIgusaRootStackComparison p

    ExceptionalBadLevelObject : Set
    exceptionalObject :
      ExceptionalBadLevelObject

    exceptionalValuation :
      ExceptionalBadLevelObject -> Nat

    requiredCorrection :
      Nat

    valuationIsRequiredCorrection :
      exceptionalValuation exceptionalObject
      ≡ requiredCorrection

    objectDerivedFromIgusaPAndP2Data :
      Bool
    objectDerivedFromIgusaPAndP2DataIsTrue :
      objectDerivedFromIgusaPAndP2Data ≡ true

    correctedHauptmodulDivisorOwned :
      Bool
    correctedHauptmodulDivisorOwnedIsTrue :
      correctedHauptmodulDivisorOwned ≡ true

    correctedQExpansionOwned :
      Bool
    correctedQExpansionOwnedIsTrue :
      correctedQExpansionOwned ≡ true

    sameObjectRefinesSupersingularSide :
      Bool
    sameObjectRefinesSupersingularSideIsTrue :
      sameObjectRefinesSupersingularSide ≡ true

    proofIndependentOfMonsterTarget :
      Bool
    proofIndependentOfMonsterTargetIsTrue :
      proofIndependentOfMonsterTarget ≡ true

open BadLevelIgusaCorrectionAuthority public

------------------------------------------------------------------------
-- 5. Prime-specific target values are obligations, not definitions.
------------------------------------------------------------------------

p2TargetCorrection : Nat
p2TargetCorrection = 10

p3TargetCorrection : Nat
p3TargetCorrection = 2

record P2IgusaCorrectionAuthority : Set₁ where
  field
    authority :
      BadLevelIgusaCorrectionAuthority pTwo

    targetIsTen :
      requiredCorrection authority ≡ p2TargetCorrection

record P3IgusaCorrectionAuthority : Set₁ where
  field
    authority :
      BadLevelIgusaCorrectionAuthority pThree

    targetIsTwo :
      requiredCorrection authority ≡ p3TargetCorrection

------------------------------------------------------------------------
-- 6. Existing candidate surfaces remain inputs, not proofs.
------------------------------------------------------------------------

candidatePayment :
  Payment.CandidateSmallPrimeCorrectionPayment
candidatePayment =
  Payment.canonicalCandidateSmallPrimeCorrectionPayment

etherealBoundary :
  Ethereal.EtherealMultiplicityTransferBoundary
etherealBoundary =
  Ethereal.canonicalEtherealMultiplicityTransferBoundary

layerSectorBoundary :
  LayerSector.WildLayerSectorProductBoundary
layerSectorBoundary =
  LayerSector.canonicalWildLayerSectorProductBoundary

data IgusaTowerExistsThereforeCorrectionTenTwo : Set where
data HasseRootDescriptionCreatesHauptmodulCorrection : Set where
data RootStackComparisonAloneCreatesValuationAuthority : Set where
data SectorProductDefinesIgusaCorrection : Set where

igusaExistenceDoesNotCreateCorrection :
  IgusaTowerExistsThereforeCorrectionTenTwo -> ⊥
igusaExistenceDoesNotCreateCorrection ()

hasseRootDoesNotCreateHauptmodulCorrection :
  HasseRootDescriptionCreatesHauptmodulCorrection -> ⊥
hasseRootDoesNotCreateHauptmodulCorrection ()

rootStackComparisonDoesNotCreateValuationAuthority :
  RootStackComparisonAloneCreatesValuationAuthority -> ⊥
rootStackComparisonDoesNotCreateValuationAuthority ()

sectorProductDoesNotDefineIgusaCorrection :
  SectorProductDefinesIgusaCorrection -> ⊥
sectorProductDoesNotDefineIgusaCorrection ()

------------------------------------------------------------------------
-- 7. Live boundary.
------------------------------------------------------------------------

data P2BadLevelIgusaAuthorityInhabited : Set where
data P3BadLevelIgusaAuthorityInhabited : Set where

p2BadLevelIgusaAuthorityStillOpen :
  P2BadLevelIgusaAuthorityInhabited -> ⊥
p2BadLevelIgusaAuthorityStillOpen ()

p3BadLevelIgusaAuthorityStillOpen :
  P3BadLevelIgusaAuthorityInhabited -> ⊥
p3BadLevelIgusaAuthorityStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record BadLevelIgusaCorrectionCutsetBoundary : Set where
  constructor bad-level-igusa-correction-cutset-boundary
  field
    duncanSwisherUsesPLevelTerm : Bool
    duncanSwisherUsesPSquaredLevelTerm : Bool
    sourcedEtherealMultiplicityRequiresLevelPrimeToP : Bool
    sourcedPaperMarksBadLevelAsFutureWork : Bool
    sourcedPaperSuggestsIgusaTower : Bool
    igusaPAsHasseRootModuliProblemSourced : Bool
    igusaRootStackComparisonAlreadyInSource : Bool
    badLevelComparisonInterfaceSpecified : Bool
    correctedValuationAuthoritySpecified : Bool
    p2AuthorityInhabited : Bool
    p3AuthorityInhabited : Bool
    finiteSectorCountPromotedToBadLevelValuation : Bool

canonicalBadLevelIgusaCorrectionCutsetBoundary :
  BadLevelIgusaCorrectionCutsetBoundary
canonicalBadLevelIgusaCorrectionCutsetBoundary =
  bad-level-igusa-correction-cutset-boundary
    true true true true true true false true true false false false
