module DASHI.Physics.Closure.StrangeMassFromP5LaneReceipt where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _-_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import MonsterOntos using (SSP; p5; toNat)

------------------------------------------------------------------------
-- Gate 7 p5 strange-mass receipt.
--
-- This is a concrete diagnostic receipt only.  It records the p5 finite
-- lane F25/F5 with Frobenius group Z/2 and the discriminant diagnostic
-- 5^2 - 5 = 20.  The target strange mass is about 93.5 MeV, recorded as
-- an external target, not derived from the DASHI carrier.

data P5StrangeMassBlocker : Set where
  missingPhysicalUnitCalibrationForP5Mass :
    P5StrangeMassBlocker

  missingStrangeMassSchemeAuthority :
    P5StrangeMassBlocker

  missingCarrierToStrangeMassDerivation :
    P5StrangeMassBlocker

canonicalP5StrangeMassBlockers :
  List P5StrangeMassBlocker
canonicalP5StrangeMassBlockers =
  missingPhysicalUnitCalibrationForP5Mass
  ∷ missingStrangeMassSchemeAuthority
  ∷ missingCarrierToStrangeMassDerivation
  ∷ []

data P5PhysicalStrangeMassDerived : Set where

p5PhysicalStrangeMassDerivedIsFalse :
  P5PhysicalStrangeMassDerived →
  ⊥
p5PhysicalStrangeMassDerivedIsFalse ()

record StrangeMassFromP5LaneReceipt : Set where
  field
    lane :
      SSP

    laneIsP5 :
      lane ≡ p5

    baseFieldCardinality :
      Nat

    baseFieldCardinalityIsF5 :
      baseFieldCardinality ≡ 5

    extensionFieldCardinality :
      Nat

    extensionFieldCardinalityIsF25 :
      extensionFieldCardinality ≡ 25

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

    discriminantDiagnosticIsFiveSquaredMinusFive :
      discriminantDiagnostic ≡ (5 * 5) - 5

    discriminantDiagnosticIsTwenty :
      discriminantDiagnostic ≡ 20

    targetStrangeMassMeVTenths :
      Nat

    targetStrangeMassMeVTenthsIsAboutNinetyThreePointFiveMeV :
      targetStrangeMassMeVTenths ≡ 935

    targetStrangeMassLabel :
      String

    derivedPhysicalMass :
      Bool

    derivedPhysicalMassIsFalse :
      derivedPhysicalMass ≡ false

    blockers :
      List P5StrangeMassBlocker

    blockersAreCanonical :
      blockers ≡ canonicalP5StrangeMassBlockers

    receiptBoundary :
      List String

open StrangeMassFromP5LaneReceipt public

canonicalStrangeMassFromP5LaneReceipt :
  StrangeMassFromP5LaneReceipt
canonicalStrangeMassFromP5LaneReceipt =
  record
    { lane =
        p5
    ; laneIsP5 =
        refl
    ; baseFieldCardinality =
        toNat p5
    ; baseFieldCardinalityIsF5 =
        refl
    ; extensionFieldCardinality =
        25
    ; extensionFieldCardinalityIsF25 =
        refl
    ; extensionLabel =
        "F25/F5"
    ; frobeniusGroupLabel =
        "Frobenius group Z/2"
    ; frobeniusOrder =
        2
    ; frobeniusOrderIsZ2 =
        refl
    ; discriminantDiagnostic =
        20
    ; discriminantDiagnosticIsFiveSquaredMinusFive =
        refl
    ; discriminantDiagnosticIsTwenty =
        refl
    ; targetStrangeMassMeVTenths =
        935
    ; targetStrangeMassMeVTenthsIsAboutNinetyThreePointFiveMeV =
        refl
    ; targetStrangeMassLabel =
        "target m_s about 93.5 MeV; comparison target only, not derived"
    ; derivedPhysicalMass =
        false
    ; derivedPhysicalMassIsFalse =
        refl
    ; blockers =
        canonicalP5StrangeMassBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "p5 lane records F25/F5 with Frobenius Z/2"
        ∷ "discriminant diagnostic is 5^2 - 5 = 20"
        ∷ "target m_s is about 93.5 MeV, recorded only as an external target"
        ∷ "no physical strange-quark mass is derived by this receipt"
        ∷ []
    }

p5StrangeMassReceiptDerivedPhysicalMassFalse :
  derivedPhysicalMass canonicalStrangeMassFromP5LaneReceipt ≡ false
p5StrangeMassReceiptDerivedPhysicalMassFalse =
  refl

p5StrangeMassNoPhysicalMassDerivation :
  P5PhysicalStrangeMassDerived →
  ⊥
p5StrangeMassNoPhysicalMassDerivation =
  p5PhysicalStrangeMassDerivedIsFalse
