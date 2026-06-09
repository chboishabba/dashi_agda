module DASHI.Physics.Closure.IsospinSplittingFromP3LaneReceipt where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _-_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import MonsterOntos using (SSP; p3; toNat)

------------------------------------------------------------------------
-- Gate 7 p3 isospin-splitting receipt.
--
-- This is a concrete diagnostic receipt only.  It records the p3 finite
-- lane F9/F3 with Frobenius group Z/2 and the discriminant diagnostic
-- 3^2 - 3 = 6.  The target delta is m_d - m_u about 2.5 MeV, recorded as
-- an external target, not derived from the DASHI carrier.

data P3IsospinSplittingBlocker : Set where
  missingPhysicalUnitCalibrationForP3Delta :
    P3IsospinSplittingBlocker

  missingQuarkMassSchemeAuthorityForDelta :
    P3IsospinSplittingBlocker

  missingCarrierToQuarkMassDerivation :
    P3IsospinSplittingBlocker

canonicalP3IsospinSplittingBlockers :
  List P3IsospinSplittingBlocker
canonicalP3IsospinSplittingBlockers =
  missingPhysicalUnitCalibrationForP3Delta
  ∷ missingQuarkMassSchemeAuthorityForDelta
  ∷ missingCarrierToQuarkMassDerivation
  ∷ []

data P3PhysicalIsospinMassDerived : Set where

p3PhysicalIsospinMassDerivedIsFalse :
  P3PhysicalIsospinMassDerived →
  ⊥
p3PhysicalIsospinMassDerivedIsFalse ()

record IsospinSplittingFromP3LaneReceipt : Set where
  field
    lane :
      SSP

    laneIsP3 :
      lane ≡ p3

    baseFieldCardinality :
      Nat

    baseFieldCardinalityIsF3 :
      baseFieldCardinality ≡ 3

    extensionFieldCardinality :
      Nat

    extensionFieldCardinalityIsF9 :
      extensionFieldCardinality ≡ 9

    extensionLabel :
      String

    frobeniusGroupLabel :
      String

    frobeniusOrder :
      Nat

    frobeniusOrderIsZ2 :
      frobeniusOrder ≡ 2

    discriminantDiagnostic :
      Nat

    discriminantDiagnosticIsThreeSquaredMinusThree :
      discriminantDiagnostic ≡ (3 * 3) - 3

    discriminantDiagnosticIsSix :
      discriminantDiagnostic ≡ 6

    targetDeltaMeVTenths :
      Nat

    targetDeltaMeVTenthsIsAboutTwoPointFiveMeV :
      targetDeltaMeVTenths ≡ 25

    targetDeltaLabel :
      String

    derivedPhysicalMass :
      Bool

    derivedPhysicalMassIsFalse :
      derivedPhysicalMass ≡ false

    blockers :
      List P3IsospinSplittingBlocker

    blockersAreCanonical :
      blockers ≡ canonicalP3IsospinSplittingBlockers

    receiptBoundary :
      List String

open IsospinSplittingFromP3LaneReceipt public

canonicalIsospinSplittingFromP3LaneReceipt :
  IsospinSplittingFromP3LaneReceipt
canonicalIsospinSplittingFromP3LaneReceipt =
  record
    { lane =
        p3
    ; laneIsP3 =
        refl
    ; baseFieldCardinality =
        toNat p3
    ; baseFieldCardinalityIsF3 =
        refl
    ; extensionFieldCardinality =
        9
    ; extensionFieldCardinalityIsF9 =
        refl
    ; extensionLabel =
        "F9/F3"
    ; frobeniusGroupLabel =
        "Frobenius group Z/2"
    ; frobeniusOrder =
        2
    ; frobeniusOrderIsZ2 =
        refl
    ; discriminantDiagnostic =
        6
    ; discriminantDiagnosticIsThreeSquaredMinusThree =
        refl
    ; discriminantDiagnosticIsSix =
        refl
    ; targetDeltaMeVTenths =
        25
    ; targetDeltaMeVTenthsIsAboutTwoPointFiveMeV =
        refl
    ; targetDeltaLabel =
        "target m_d - m_u about 2.5 MeV; comparison target only, not derived"
    ; derivedPhysicalMass =
        false
    ; derivedPhysicalMassIsFalse =
        refl
    ; blockers =
        canonicalP3IsospinSplittingBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "p3 lane records F9/F3 with Frobenius Z/2"
        ∷ "discriminant diagnostic is 3^2 - 3 = 6"
        ∷ "target delta=m_d-m_u is about 2.5 MeV, recorded only as an external target"
        ∷ "no physical quark mass or mass splitting is derived by this receipt"
        ∷ []
    }

p3IsospinSplittingReceiptDerivedPhysicalMassFalse :
  derivedPhysicalMass canonicalIsospinSplittingFromP3LaneReceipt ≡ false
p3IsospinSplittingReceiptDerivedPhysicalMassFalse =
  refl

p3IsospinSplittingNoPhysicalMassDerivation :
  P3PhysicalIsospinMassDerived →
  ⊥
p3IsospinSplittingNoPhysicalMassDerivation =
  p3PhysicalIsospinMassDerivedIsFalse
