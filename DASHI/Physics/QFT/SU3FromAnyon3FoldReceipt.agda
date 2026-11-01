module DASHI.Physics.QFT.SU3FromAnyon3FoldReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- SU3 from anyonic three-fold prime-lane receipt.
--
-- This receipt records a narrow candidate surface: three anyonic prime-lane
-- sectors carry a Z/3 braided structure, which is suggestive of the three
-- Wilson-line sectors of SU(3)_1 Chern-Simons theory.  It deliberately stops
-- at conditional/candidate status.  It does not construct the full continuous
-- SU3_c gauge group from Chern-Simons data, and it does not promote either an
-- exact SU3_c result or an exact G_DHR ~= G_SM result.

data AnyonicPrimeLaneSector : Set where
  anyonicPrimeLaneSector0 :
    AnyonicPrimeLaneSector

  anyonicPrimeLaneSector1 :
    AnyonicPrimeLaneSector

  anyonicPrimeLaneSector2 :
    AnyonicPrimeLaneSector

canonicalAnyonicPrimeLaneSectors :
  List AnyonicPrimeLaneSector
canonicalAnyonicPrimeLaneSectors =
  anyonicPrimeLaneSector0
  ∷ anyonicPrimeLaneSector1
  ∷ anyonicPrimeLaneSector2
  ∷ []

data Z3BraidedCharge : Set where
  z3Charge0 :
    Z3BraidedCharge

  z3Charge1 :
    Z3BraidedCharge

  z3Charge2 :
    Z3BraidedCharge

canonicalZ3BraidedCharges :
  List Z3BraidedCharge
canonicalZ3BraidedCharges =
  z3Charge0
  ∷ z3Charge1
  ∷ z3Charge2
  ∷ []

z3BraidedChargeCardinality :
  Nat
z3BraidedChargeCardinality =
  3

data SU3CSFromAnyonicPrimeLanesStatus : Set where
  conditional/candidate :
    SU3CSFromAnyonicPrimeLanesStatus

data SU3FullGaugeGroupFromCSStatus : Set where
  false/open :
    SU3FullGaugeGroupFromCSStatus

data SU3ChernSimonsLevel1WilsonLineSector : Set where
  trivialWilsonLine :
    SU3ChernSimonsLevel1WilsonLineSector

  fundamentalWilsonLine :
    SU3ChernSimonsLevel1WilsonLineSector

  antiFundamentalWilsonLine :
    SU3ChernSimonsLevel1WilsonLineSector

canonicalSU3ChernSimonsLevel1WilsonLineSectors :
  List SU3ChernSimonsLevel1WilsonLineSector
canonicalSU3ChernSimonsLevel1WilsonLineSectors =
  trivialWilsonLine
  ∷ fundamentalWilsonLine
  ∷ antiFundamentalWilsonLine
  ∷ []

su3ChernSimonsLevel1CandidateLabel :
  String
su3ChernSimonsLevel1CandidateLabel =
  "Three Z/3 anyonic prime-lane sectors are recorded as a candidate relation to SU(3)_1 Chern-Simons Wilson lines"

conditionalCandidateBoundaryLabel :
  String
conditionalCandidateBoundaryLabel =
  "SU3 Chern-Simons from anyonic prime lanes is conditional/candidate only"

fullGaugeGroupOpenBoundaryLabel :
  String
fullGaugeGroupOpenBoundaryLabel =
  "Full continuous SU3_c gauge group from Chern-Simons data is false/open here"

exactSU3cFalseBoundaryLabel :
  String
exactSU3cFalseBoundaryLabel =
  "Exact SU3_c is false in this receipt"

exactGDHREqualsGSMFalseBoundaryLabel :
  String
exactGDHREqualsGSMFalseBoundaryLabel =
  "Exact G_DHR ~= G_SM is false in this receipt"

record SU3FromAnyon3FoldReceipt : Setω where
  field
    anyonicPrimeLaneSectors :
      List AnyonicPrimeLaneSector

    anyonicPrimeLaneSectorsAreCanonical :
      anyonicPrimeLaneSectors ≡ canonicalAnyonicPrimeLaneSectors

    anyonicPrimeLaneSectorCount :
      Nat

    anyonicPrimeLaneSectorCountIsThree :
      anyonicPrimeLaneSectorCount ≡ 3

    z3BraidedStructure :
      List Z3BraidedCharge

    z3BraidedStructureIsCanonical :
      z3BraidedStructure ≡ canonicalZ3BraidedCharges

    z3BraidedStructureCardinality :
      Nat

    z3BraidedStructureCardinalityIsThree :
      z3BraidedStructureCardinality ≡ z3BraidedChargeCardinality

    su3ChernSimonsLevel1WilsonLineSectors :
      List SU3ChernSimonsLevel1WilsonLineSector

    su3ChernSimonsLevel1WilsonLineSectorsAreCanonical :
      su3ChernSimonsLevel1WilsonLineSectors
      ≡
      canonicalSU3ChernSimonsLevel1WilsonLineSectors

    su3ChernSimonsLevel1Candidate :
      Bool

    su3ChernSimonsLevel1CandidateIsTrue :
      su3ChernSimonsLevel1Candidate ≡ true

    su3ChernSimonsLevel1CandidateBoundary :
      String

    su3ChernSimonsLevel1CandidateBoundaryIsCanonical :
      su3ChernSimonsLevel1CandidateBoundary
      ≡
      su3ChernSimonsLevel1CandidateLabel

    su3CSFromAnyonicPrimeLanes :
      SU3CSFromAnyonicPrimeLanesStatus

    su3CSFromAnyonicPrimeLanesIsConditionalCandidate :
      su3CSFromAnyonicPrimeLanes ≡ conditional/candidate

    su3CSFromAnyonicPrimeLanesBoundary :
      String

    su3CSFromAnyonicPrimeLanesBoundaryIsCanonical :
      su3CSFromAnyonicPrimeLanesBoundary
      ≡
      conditionalCandidateBoundaryLabel

    su3FullGaugeGroupFromCS :
      SU3FullGaugeGroupFromCSStatus

    su3FullGaugeGroupFromCSIsFalseOpen :
      su3FullGaugeGroupFromCS ≡ false/open

    su3FullGaugeGroupFromCSBoundary :
      String

    su3FullGaugeGroupFromCSBoundaryIsCanonical :
      su3FullGaugeGroupFromCSBoundary
      ≡
      fullGaugeGroupOpenBoundaryLabel

    exactSU3c :
      Bool

    exactSU3cIsFalse :
      exactSU3c ≡ false

    exactSU3cBoundary :
      String

    exactSU3cBoundaryIsCanonical :
      exactSU3cBoundary ≡ exactSU3cFalseBoundaryLabel

    exactGDHREqualsGSM :
      Bool

    exactGDHREqualsGSMIsFalse :
      exactGDHREqualsGSM ≡ false

    exactGDHREqualsGSMBoundary :
      String

    exactGDHREqualsGSMBoundaryIsCanonical :
      exactGDHREqualsGSMBoundary ≡ exactGDHREqualsGSMFalseBoundaryLabel

    receiptBoundary :
      List String

open SU3FromAnyon3FoldReceipt public

canonicalSU3FromAnyon3FoldReceipt :
  SU3FromAnyon3FoldReceipt
canonicalSU3FromAnyon3FoldReceipt =
  record
    { anyonicPrimeLaneSectors =
        canonicalAnyonicPrimeLaneSectors
    ; anyonicPrimeLaneSectorsAreCanonical =
        refl
    ; anyonicPrimeLaneSectorCount =
        3
    ; anyonicPrimeLaneSectorCountIsThree =
        refl
    ; z3BraidedStructure =
        canonicalZ3BraidedCharges
    ; z3BraidedStructureIsCanonical =
        refl
    ; z3BraidedStructureCardinality =
        z3BraidedChargeCardinality
    ; z3BraidedStructureCardinalityIsThree =
        refl
    ; su3ChernSimonsLevel1WilsonLineSectors =
        canonicalSU3ChernSimonsLevel1WilsonLineSectors
    ; su3ChernSimonsLevel1WilsonLineSectorsAreCanonical =
        refl
    ; su3ChernSimonsLevel1Candidate =
        true
    ; su3ChernSimonsLevel1CandidateIsTrue =
        refl
    ; su3ChernSimonsLevel1CandidateBoundary =
        su3ChernSimonsLevel1CandidateLabel
    ; su3ChernSimonsLevel1CandidateBoundaryIsCanonical =
        refl
    ; su3CSFromAnyonicPrimeLanes =
        conditional/candidate
    ; su3CSFromAnyonicPrimeLanesIsConditionalCandidate =
        refl
    ; su3CSFromAnyonicPrimeLanesBoundary =
        conditionalCandidateBoundaryLabel
    ; su3CSFromAnyonicPrimeLanesBoundaryIsCanonical =
        refl
    ; su3FullGaugeGroupFromCS =
        false/open
    ; su3FullGaugeGroupFromCSIsFalseOpen =
        refl
    ; su3FullGaugeGroupFromCSBoundary =
        fullGaugeGroupOpenBoundaryLabel
    ; su3FullGaugeGroupFromCSBoundaryIsCanonical =
        refl
    ; exactSU3c =
        false
    ; exactSU3cIsFalse =
        refl
    ; exactSU3cBoundary =
        exactSU3cFalseBoundaryLabel
    ; exactSU3cBoundaryIsCanonical =
        refl
    ; exactGDHREqualsGSM =
        false
    ; exactGDHREqualsGSMIsFalse =
        refl
    ; exactGDHREqualsGSMBoundary =
        exactGDHREqualsGSMFalseBoundaryLabel
    ; exactGDHREqualsGSMBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        "Three anyonic prime-lane sectors are recorded"
        ∷ "The three sectors carry the canonical Z/3 braided charge structure"
        ∷ "The Z/3 braided structure is only a candidate relation to the three SU(3)_1 Chern-Simons Wilson-line sectors"
        ∷ "su3ChernSimonsLevel1Candidate=true and su3CSFromAnyonicPrimeLanes=conditional/candidate"
        ∷ "su3FullGaugeGroupFromCS=false/open; exact SU3_c and exact G_DHR ~= G_SM remain false"
        ∷ []
    }

su3FromAnyon3FoldChernSimonsLevel1CandidateIsTrue :
  su3ChernSimonsLevel1Candidate canonicalSU3FromAnyon3FoldReceipt
  ≡
  true
su3FromAnyon3FoldChernSimonsLevel1CandidateIsTrue =
  refl

su3FromAnyon3FoldCSStatusIsConditionalCandidate :
  su3CSFromAnyonicPrimeLanes canonicalSU3FromAnyon3FoldReceipt
  ≡
  conditional/candidate
su3FromAnyon3FoldCSStatusIsConditionalCandidate =
  refl

su3FromAnyon3FoldFullGaugeGroupFromCSIsFalseOpen :
  su3FullGaugeGroupFromCS canonicalSU3FromAnyon3FoldReceipt
  ≡
  false/open
su3FromAnyon3FoldFullGaugeGroupFromCSIsFalseOpen =
  refl

su3FromAnyon3FoldExactSU3cIsFalse :
  exactSU3c canonicalSU3FromAnyon3FoldReceipt
  ≡
  false
su3FromAnyon3FoldExactSU3cIsFalse =
  refl

su3FromAnyon3FoldExactGDHREqualsGSMIsFalse :
  exactGDHREqualsGSM canonicalSU3FromAnyon3FoldReceipt
  ≡
  false
su3FromAnyon3FoldExactGDHREqualsGSMIsFalse =
  refl
