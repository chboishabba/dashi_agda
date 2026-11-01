module DASHI.Physics.Closure.MonstrousMoonshineSSPBoundaryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Closure.SupersingularPrimeLaneBridge as SSP

------------------------------------------------------------------------
-- Monstrous Moonshine / supersingular-prime boundary receipt.
--
-- This receipt hardens the Moonshine/SSP lane to an arithmetic-only claim:
-- the Ogg supersingular-prime set and the tracked Monster-prime lane have the
-- same 15-prime structural profile.  It does not assert physical moonshine,
-- does not construct a Monster/VOA theorem, and does not promote any CKM, YM,
-- NS, SM, Clay, or terminal closure claim.

data MonstrousMoonshineSSPBoundaryStatus : Set where
  arithmeticOnlyOggMonsterPrimeCompatibilityNoPhysicalPromotion :
    MonstrousMoonshineSSPBoundaryStatus

data MonstrousMoonshineSSPPromotionAuthorityToken : Set where

data PhysicalMoonshineAuthorityToken : Set where

data CKMYMNSSMClayTerminalAuthorityToken : Set where

data MonstrousMoonshineSSPBoundaryEntry : Set where
  boundaryOggSetRecordedAsArithmeticInput :
    MonstrousMoonshineSSPBoundaryEntry

  boundaryMonsterPrimeLaneRecordedAsStructuralInput :
    MonstrousMoonshineSSPBoundaryEntry

  boundaryCompatibilityIsPrimeSetShapeOnly :
    MonstrousMoonshineSSPBoundaryEntry

  boundaryNoPhysicalMoonshineClaim :
    MonstrousMoonshineSSPBoundaryEntry

  boundaryNoCKMPromotion :
    MonstrousMoonshineSSPBoundaryEntry

  boundaryNoYMPromotion :
    MonstrousMoonshineSSPBoundaryEntry

  boundaryNoNSPromotion :
    MonstrousMoonshineSSPBoundaryEntry

  boundaryNoSMPromotion :
    MonstrousMoonshineSSPBoundaryEntry

  boundaryNoClayPromotion :
    MonstrousMoonshineSSPBoundaryEntry

  boundaryNoTerminalPromotion :
    MonstrousMoonshineSSPBoundaryEntry

canonicalMonstrousMoonshineSSPBoundaryEntries :
  List MonstrousMoonshineSSPBoundaryEntry
canonicalMonstrousMoonshineSSPBoundaryEntries =
  boundaryOggSetRecordedAsArithmeticInput
  ∷ boundaryMonsterPrimeLaneRecordedAsStructuralInput
  ∷ boundaryCompatibilityIsPrimeSetShapeOnly
  ∷ boundaryNoPhysicalMoonshineClaim
  ∷ boundaryNoCKMPromotion
  ∷ boundaryNoYMPromotion
  ∷ boundaryNoNSPromotion
  ∷ boundaryNoSMPromotion
  ∷ boundaryNoClayPromotion
  ∷ boundaryNoTerminalPromotion
  ∷ []

monstrousMoonshineSSPBoundaryStatement : String
monstrousMoonshineSSPBoundaryStatement =
  "Monstrous Moonshine / SSP compatibility is recorded only as arithmetic Ogg-set and Monster-prime structural compatibility; physical Moonshine, CKM, YM, NS, SM, Clay, and terminal promotions remain fail-closed."

record OggSetMonsterPrimeStructuralCompatibility : Setω where
  field
    oggPrimeSetNats :
      List Nat

    oggPrimeSetNatsAreCanonical :
      oggPrimeSetNats ≡ SSP.canonicalSupersingularPrimeLaneNats

    monsterPrimeLaneSet :
      List Lane.MonsterPrimeLane

    monsterPrimeLaneSetIsCanonical :
      monsterPrimeLaneSet ≡ Lane.canonicalMonsterPrimeLane

    monsterPrimeLaneNats :
      List Nat

    monsterPrimeLaneNatsAreCanonical :
      monsterPrimeLaneNats ≡ Lane.canonicalMonsterPrimeLaneNats

    arithmeticSetCompatible :
      Bool

    arithmeticSetCompatibleIsTrue :
      arithmeticSetCompatible ≡ true

    compatibilityScope :
      String

open OggSetMonsterPrimeStructuralCompatibility public

canonicalOggSetMonsterPrimeStructuralCompatibility :
  OggSetMonsterPrimeStructuralCompatibility
canonicalOggSetMonsterPrimeStructuralCompatibility =
  record
    { oggPrimeSetNats =
        SSP.canonicalSupersingularPrimeLaneNats
    ; oggPrimeSetNatsAreCanonical =
        refl
    ; monsterPrimeLaneSet =
        Lane.canonicalMonsterPrimeLane
    ; monsterPrimeLaneSetIsCanonical =
        refl
    ; monsterPrimeLaneNats =
        Lane.canonicalMonsterPrimeLaneNats
    ; monsterPrimeLaneNatsAreCanonical =
        refl
    ; arithmeticSetCompatible =
        true
    ; arithmeticSetCompatibleIsTrue =
        refl
    ; compatibilityScope =
        "Set-level compatibility only: the 15 Ogg supersingular primes match the tracked Monster-prime lane profile."
    }

record MonstrousMoonshineSSPBoundaryReceipt : Setω where
  field
    status :
      MonstrousMoonshineSSPBoundaryStatus

    supersingularPrimeLaneBridge :
      SSP.SupersingularPrimeLaneBridgeReceipt

    structuralCompatibility :
      OggSetMonsterPrimeStructuralCompatibility

    boundaryEntries :
      List MonstrousMoonshineSSPBoundaryEntry

    boundaryEntriesAreCanonical :
      boundaryEntries ≡ canonicalMonstrousMoonshineSSPBoundaryEntries

    arithmeticOnly :
      Bool

    arithmeticOnlyIsTrue :
      arithmeticOnly ≡ true

    oggSetMonsterPrimeStructuralCompatibilityOnly :
      Bool

    oggSetMonsterPrimeStructuralCompatibilityOnlyIsTrue :
      oggSetMonsterPrimeStructuralCompatibilityOnly ≡ true

    physicalMoonshinePromoted :
      Bool

    physicalMoonshinePromotedIsFalse :
      physicalMoonshinePromoted ≡ false

    ckmPromoted :
      Bool

    ckmPromotedIsFalse :
      ckmPromoted ≡ false

    ymPromoted :
      Bool

    ymPromotedIsFalse :
      ymPromoted ≡ false

    nsPromoted :
      Bool

    nsPromotedIsFalse :
      nsPromoted ≡ false

    smPromoted :
      Bool

    smPromotedIsFalse :
      smPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalPromoted :
      Bool

    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    noMoonshinePromotionWithoutAuthority :
      MonstrousMoonshineSSPPromotionAuthorityToken → ⊥

    noPhysicalMoonshineWithoutAuthority :
      PhysicalMoonshineAuthorityToken → ⊥

    noCKMYMNSSMClayTerminalPromotionWithoutAuthority :
      CKMYMNSSMClayTerminalAuthorityToken → ⊥

    statement :
      String

    statementIsCanonical :
      statement ≡ monstrousMoonshineSSPBoundaryStatement

    receiptBoundary :
      List String

open MonstrousMoonshineSSPBoundaryReceipt public

canonicalMonstrousMoonshineSSPBoundaryReceipt :
  MonstrousMoonshineSSPBoundaryReceipt
canonicalMonstrousMoonshineSSPBoundaryReceipt =
  record
    { status =
        arithmeticOnlyOggMonsterPrimeCompatibilityNoPhysicalPromotion
    ; supersingularPrimeLaneBridge =
        SSP.canonicalSupersingularPrimeLaneBridgeReceipt
    ; structuralCompatibility =
        canonicalOggSetMonsterPrimeStructuralCompatibility
    ; boundaryEntries =
        canonicalMonstrousMoonshineSSPBoundaryEntries
    ; boundaryEntriesAreCanonical =
        refl
    ; arithmeticOnly =
        true
    ; arithmeticOnlyIsTrue =
        refl
    ; oggSetMonsterPrimeStructuralCompatibilityOnly =
        true
    ; oggSetMonsterPrimeStructuralCompatibilityOnlyIsTrue =
        refl
    ; physicalMoonshinePromoted =
        false
    ; physicalMoonshinePromotedIsFalse =
        refl
    ; ckmPromoted =
        false
    ; ckmPromotedIsFalse =
        refl
    ; ymPromoted =
        false
    ; ymPromotedIsFalse =
        refl
    ; nsPromoted =
        false
    ; nsPromotedIsFalse =
        refl
    ; smPromoted =
        false
    ; smPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; terminalPromoted =
        false
    ; terminalPromotedIsFalse =
        refl
    ; noMoonshinePromotionWithoutAuthority =
        λ ()
    ; noPhysicalMoonshineWithoutAuthority =
        λ ()
    ; noCKMYMNSSMClayTerminalPromotionWithoutAuthority =
        λ ()
    ; statement =
        monstrousMoonshineSSPBoundaryStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Ogg supersingular-prime data is consumed as an arithmetic set boundary."
        ∷ "Monster-prime lane data is consumed as structural prime-lane data."
        ∷ "The only positive claim is set/profile compatibility between those arithmetic carriers."
        ∷ "No physical Moonshine, CKM, YM, NS, SM, Clay, or terminal promotion is issued."
        ∷ []
    }

monstrousMoonshineSSPBoundaryArithmeticOnly :
  arithmeticOnly canonicalMonstrousMoonshineSSPBoundaryReceipt ≡ true
monstrousMoonshineSSPBoundaryArithmeticOnly =
  refl

monstrousMoonshineSSPBoundaryNoPhysicalMoonshine :
  physicalMoonshinePromoted canonicalMonstrousMoonshineSSPBoundaryReceipt
  ≡ false
monstrousMoonshineSSPBoundaryNoPhysicalMoonshine =
  refl

monstrousMoonshineSSPBoundaryNoTerminalPromotion :
  terminalPromoted canonicalMonstrousMoonshineSSPBoundaryReceipt ≡ false
monstrousMoonshineSSPBoundaryNoTerminalPromotion =
  refl
