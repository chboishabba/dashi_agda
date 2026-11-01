module DASHI.Physics.QFT.TrialitySymmetryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Triality / CRT diagnostic receipt.
--
-- The finite CM unit orders are 4, 6, and 2.  Their lcm is 12, so Z/12
-- records a diagonal carrier-level CRT action by reduction modulo 4, 6, and
-- 2.  This is only a finite candidate diagnostic: it does not produce a
-- transitive triality among the unequal CM unit groups, does not construct
-- full SU3 from Z/12, and does not promote an exact Standard Model match.

data TrialityCMLane : Set where
  p2CMUnitLane :
    TrialityCMLane

  p3CMUnitLane :
    TrialityCMLane

  p5CMUnitLane :
    TrialityCMLane

canonicalTrialityCMLanes :
  List TrialityCMLane
canonicalTrialityCMLanes =
  p2CMUnitLane
  ∷ p3CMUnitLane
  ∷ p5CMUnitLane
  ∷ []

cmUnitOrder :
  TrialityCMLane →
  Nat
cmUnitOrder p2CMUnitLane =
  4
cmUnitOrder p3CMUnitLane =
  6
cmUnitOrder p5CMUnitLane =
  2

canonicalCMUnitOrders :
  List Nat
canonicalCMUnitOrders =
  4 ∷ 6 ∷ 2 ∷ []

data Z12ReductionComponent : Set where
  reduceMod4ToP2CMUnits :
    Z12ReductionComponent

  reduceMod6ToP3CMUnits :
    Z12ReductionComponent

  reduceMod2ToP5CMUnits :
    Z12ReductionComponent

canonicalZ12ReductionComponents :
  List Z12ReductionComponent
canonicalZ12ReductionComponents =
  reduceMod4ToP2CMUnits
  ∷ reduceMod6ToP3CMUnits
  ∷ reduceMod2ToP5CMUnits
  ∷ []

data TrialityDiagnosticBlocker : Set where
  unequalCMUnitGroupsBlockTransitiveTriality :
    TrialityDiagnosticBlocker

  diagonalCRTActionIsFiniteCarrierActionOnly :
    TrialityDiagnosticBlocker

  z12IsNotFullSU3 :
    TrialityDiagnosticBlocker

  exactSMMatchNotConstructed :
    TrialityDiagnosticBlocker

canonicalTrialityDiagnosticBlockers :
  List TrialityDiagnosticBlocker
canonicalTrialityDiagnosticBlockers =
  unequalCMUnitGroupsBlockTransitiveTriality
  ∷ diagonalCRTActionIsFiniteCarrierActionOnly
  ∷ z12IsNotFullSU3
  ∷ exactSMMatchNotConstructed
  ∷ []

z12CRTActionLabel : String
z12CRTActionLabel =
  "Z/12 acts diagonally by reduction modulo 4, 6, and 2 on the CM unit lanes"

carrierDiagonalCRTLabel : String
carrierDiagonalCRTLabel =
  "The diagonal CRT action is carrier-derived from the lcm-12 finite CM unit orders"

nonTransitiveTrialityLabel : String
nonTransitiveTrialityLabel =
  "No transitive triality is derived among unequal CM unit groups of orders 4, 6, and 2"

finiteSU3CandidateBoundaryLabel : String
finiteSU3CandidateBoundaryLabel =
  "Z/12 is recorded only as a finite candidate that may embed in SU3, not as full SU3"

exactSMFalseBoundaryLabel : String
exactSMFalseBoundaryLabel =
  "The triality/CRT diagnostic does not construct an exact Standard Model match"

record TrialitySymmetryReceipt : Setω where
  field
    cmLanes :
      List TrialityCMLane

    cmLanesAreCanonical :
      cmLanes ≡ canonicalTrialityCMLanes

    p2CMUnitOrder :
      Nat

    p2CMUnitOrderIsFour :
      p2CMUnitOrder ≡ 4

    p3CMUnitOrder :
      Nat

    p3CMUnitOrderIsSix :
      p3CMUnitOrder ≡ 6

    p5CMUnitOrder :
      Nat

    p5CMUnitOrderIsTwo :
      p5CMUnitOrder ≡ 2

    cmUnitOrders :
      List Nat

    cmUnitOrdersAreCanonical :
      cmUnitOrders ≡ canonicalCMUnitOrders

    cmUnitOrderFunctionP2 :
      cmUnitOrder p2CMUnitLane ≡ p2CMUnitOrder

    cmUnitOrderFunctionP3 :
      cmUnitOrder p3CMUnitLane ≡ p3CMUnitOrder

    cmUnitOrderFunctionP5 :
      cmUnitOrder p5CMUnitLane ≡ p5CMUnitOrder

    cmUnitOrderLCM :
      Nat

    cmUnitOrderLCMIsTwelve :
      cmUnitOrderLCM ≡ 12

    z12ReductionComponents :
      List Z12ReductionComponent

    z12ReductionComponentsAreCanonical :
      z12ReductionComponents ≡ canonicalZ12ReductionComponents

    z12ReducesToP2Modulo :
      Nat

    z12ReducesToP2ModuloIsFour :
      z12ReducesToP2Modulo ≡ 4

    z12ReducesToP3Modulo :
      Nat

    z12ReducesToP3ModuloIsSix :
      z12ReducesToP3Modulo ≡ 6

    z12ReducesToP5Modulo :
      Nat

    z12ReducesToP5ModuloIsTwo :
      z12ReducesToP5Modulo ≡ 2

    z12ReductionActionLabel :
      String

    z12ReductionActionLabelIsCanonical :
      z12ReductionActionLabel ≡ z12CRTActionLabel

    z12ReductionActionRecorded :
      Bool

    z12ReductionActionRecordedIsTrue :
      z12ReductionActionRecorded ≡ true

    carrierDerivedDiagonalCRTAction :
      Bool

    carrierDerivedDiagonalCRTActionIsTrue :
      carrierDerivedDiagonalCRTAction ≡ true

    carrierDerivedDiagonalCRTActionBoundary :
      String

    carrierDerivedDiagonalCRTActionBoundaryIsCanonical :
      carrierDerivedDiagonalCRTActionBoundary ≡ carrierDiagonalCRTLabel

    carrierTrialityDerived :
      Bool

    carrierTrialityDerivedIsFalse :
      carrierTrialityDerived ≡ false

    transitiveTrialityAmongCMUnitGroups :
      Bool

    transitiveTrialityAmongCMUnitGroupsIsFalse :
      transitiveTrialityAmongCMUnitGroups ≡ false

    nonTransitiveTrialityBoundary :
      String

    nonTransitiveTrialityBoundaryIsCanonical :
      nonTransitiveTrialityBoundary ≡ nonTransitiveTrialityLabel

    z12EmbedsInSU3AsFiniteCandidate :
      Bool

    z12EmbedsInSU3AsFiniteCandidateIsTrue :
      z12EmbedsInSU3AsFiniteCandidate ≡ true

    fullSU3FromZ12 :
      Bool

    fullSU3FromZ12IsFalse :
      fullSU3FromZ12 ≡ false

    su3Boundary :
      String

    su3BoundaryIsCanonical :
      su3Boundary ≡ finiteSU3CandidateBoundaryLabel

    exactSMFromTrialityCRT :
      Bool

    exactSMFromTrialityCRTIsFalse :
      exactSMFromTrialityCRT ≡ false

    exactSMBoundary :
      String

    exactSMBoundaryIsCanonical :
      exactSMBoundary ≡ exactSMFalseBoundaryLabel

    blockers :
      List TrialityDiagnosticBlocker

    blockersAreCanonical :
      blockers ≡ canonicalTrialityDiagnosticBlockers

    diagnosticBoundary :
      List String

open TrialitySymmetryReceipt public

canonicalTrialitySymmetryReceipt :
  TrialitySymmetryReceipt
canonicalTrialitySymmetryReceipt =
  record
    { cmLanes =
        canonicalTrialityCMLanes
    ; cmLanesAreCanonical =
        refl
    ; p2CMUnitOrder =
        4
    ; p2CMUnitOrderIsFour =
        refl
    ; p3CMUnitOrder =
        6
    ; p3CMUnitOrderIsSix =
        refl
    ; p5CMUnitOrder =
        2
    ; p5CMUnitOrderIsTwo =
        refl
    ; cmUnitOrders =
        canonicalCMUnitOrders
    ; cmUnitOrdersAreCanonical =
        refl
    ; cmUnitOrderFunctionP2 =
        refl
    ; cmUnitOrderFunctionP3 =
        refl
    ; cmUnitOrderFunctionP5 =
        refl
    ; cmUnitOrderLCM =
        12
    ; cmUnitOrderLCMIsTwelve =
        refl
    ; z12ReductionComponents =
        canonicalZ12ReductionComponents
    ; z12ReductionComponentsAreCanonical =
        refl
    ; z12ReducesToP2Modulo =
        4
    ; z12ReducesToP2ModuloIsFour =
        refl
    ; z12ReducesToP3Modulo =
        6
    ; z12ReducesToP3ModuloIsSix =
        refl
    ; z12ReducesToP5Modulo =
        2
    ; z12ReducesToP5ModuloIsTwo =
        refl
    ; z12ReductionActionLabel =
        z12CRTActionLabel
    ; z12ReductionActionLabelIsCanonical =
        refl
    ; z12ReductionActionRecorded =
        true
    ; z12ReductionActionRecordedIsTrue =
        refl
    ; carrierDerivedDiagonalCRTAction =
        true
    ; carrierDerivedDiagonalCRTActionIsTrue =
        refl
    ; carrierDerivedDiagonalCRTActionBoundary =
        carrierDiagonalCRTLabel
    ; carrierDerivedDiagonalCRTActionBoundaryIsCanonical =
        refl
    ; carrierTrialityDerived =
        false
    ; carrierTrialityDerivedIsFalse =
        refl
    ; transitiveTrialityAmongCMUnitGroups =
        false
    ; transitiveTrialityAmongCMUnitGroupsIsFalse =
        refl
    ; nonTransitiveTrialityBoundary =
        nonTransitiveTrialityLabel
    ; nonTransitiveTrialityBoundaryIsCanonical =
        refl
    ; z12EmbedsInSU3AsFiniteCandidate =
        true
    ; z12EmbedsInSU3AsFiniteCandidateIsTrue =
        refl
    ; fullSU3FromZ12 =
        false
    ; fullSU3FromZ12IsFalse =
        refl
    ; su3Boundary =
        finiteSU3CandidateBoundaryLabel
    ; su3BoundaryIsCanonical =
        refl
    ; exactSMFromTrialityCRT =
        false
    ; exactSMFromTrialityCRTIsFalse =
        refl
    ; exactSMBoundary =
        exactSMFalseBoundaryLabel
    ; exactSMBoundaryIsCanonical =
        refl
    ; blockers =
        canonicalTrialityDiagnosticBlockers
    ; blockersAreCanonical =
        refl
    ; diagnosticBoundary =
        "CM unit orders are recorded as 4, 6, and 2 for the p2, p3, and p5 lanes"
        ∷ "The lcm is recorded as 12, so the finite carrier action is the diagonal Z/12 reduction modulo 4, 6, and 2"
        ∷ "This diagonal CRT action is not a transitive triality among the unequal CM unit groups"
        ∷ "Z/12 is retained as an SU3 finite-candidate embedding surface only; full SU3 from Z/12 remains false"
        ∷ "Exact Standard Model reconstruction from this triality/CRT diagnostic remains false"
        ∷ []
    }

trialityReceiptRecordsZ12Reduction :
  z12ReductionActionRecorded canonicalTrialitySymmetryReceipt ≡ true
trialityReceiptRecordsZ12Reduction =
  refl

trialityReceiptRejectsCarrierTrialityDerivation :
  carrierTrialityDerived canonicalTrialitySymmetryReceipt ≡ false
trialityReceiptRejectsCarrierTrialityDerivation =
  refl

trialityReceiptKeepsFiniteSU3Candidate :
  z12EmbedsInSU3AsFiniteCandidate canonicalTrialitySymmetryReceipt ≡ true
trialityReceiptKeepsFiniteSU3Candidate =
  refl

trialityReceiptRejectsFullSU3FromZ12 :
  fullSU3FromZ12 canonicalTrialitySymmetryReceipt ≡ false
trialityReceiptRejectsFullSU3FromZ12 =
  refl

trialityReceiptKeepsExactSMFalse :
  exactSMFromTrialityCRT canonicalTrialitySymmetryReceipt ≡ false
trialityReceiptKeepsExactSMFalse =
  refl
