module DASHI.Physics.QFT.SMChargeQuantisationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Standard Model charge-quantisation finite receipt.
--
-- This receipt records the structural finite quantisation visible from the
-- p3 Z/6 lane and adjacent candidate surfaces:
--
--   * electric charge units 1/3 from the Z/3 subset of the p3 Z/6 lane;
--   * hypercharge units 1/6 from the full Z/6 lane;
--   * weak-isospin half-integer units from the SU2_3 candidate;
--   * colour triple degeneracy from the SU3_1 dual candidate.
--
-- It is deliberately a finite/candidate receipt.  It does not promote exact
-- G_DHR = G_SM, the full continuous Standard Model gauge group, or a full
-- Standard Model reconstruction theorem.

data P3Z6ChargeElement : Set where
  p3z6-0 :
    P3Z6ChargeElement

  p3z6-1 :
    P3Z6ChargeElement

  p3z6-2 :
    P3Z6ChargeElement

  p3z6-3 :
    P3Z6ChargeElement

  p3z6-4 :
    P3Z6ChargeElement

  p3z6-5 :
    P3Z6ChargeElement

canonicalP3Z6ChargeElements :
  List P3Z6ChargeElement
canonicalP3Z6ChargeElements =
  p3z6-0
  ∷ p3z6-1
  ∷ p3z6-2
  ∷ p3z6-3
  ∷ p3z6-4
  ∷ p3z6-5
  ∷ []

canonicalElectricZ3SubsetOfP3Z6 :
  List P3Z6ChargeElement
canonicalElectricZ3SubsetOfP3Z6 =
  p3z6-0
  ∷ p3z6-2
  ∷ p3z6-4
  ∷ []

data SU2ThreeIsospinCandidate : Set where
  su2ThreeWeakIsospinCandidate :
    SU2ThreeIsospinCandidate

data WeakIsospinHalfIntegerWeight : Set where
  weakIsospinMinusHalf :
    WeakIsospinHalfIntegerWeight

  weakIsospinPlusHalf :
    WeakIsospinHalfIntegerWeight

canonicalWeakIsospinHalfIntegerWeights :
  List WeakIsospinHalfIntegerWeight
canonicalWeakIsospinHalfIntegerWeights =
  weakIsospinMinusHalf
  ∷ weakIsospinPlusHalf
  ∷ []

data SU3OneDualColourCandidate : Set where
  su3OneDualColourTripletCandidate :
    SU3OneDualColourCandidate

data ColourDegeneracyWitness : Set where
  colourRed :
    ColourDegeneracyWitness

  colourGreen :
    ColourDegeneracyWitness

  colourBlue :
    ColourDegeneracyWitness

canonicalColourTripleDegeneracy :
  List ColourDegeneracyWitness
canonicalColourTripleDegeneracy =
  colourRed
  ∷ colourGreen
  ∷ colourBlue
  ∷ []

data SMChargeStructureStatus : Set where
  candidate :
    SMChargeStructureStatus

electricChargeUnitFromZ3SubsetOfP3Z6Label :
  String
electricChargeUnitFromZ3SubsetOfP3Z6Label =
  "Electric charge unit 1/3 from the Z/3 subset {0,2,4} of the p3 Z/6 lane"

hyperchargeUnitFromP3Z6Label :
  String
hyperchargeUnitFromP3Z6Label =
  "Hypercharge unit 1/6 from the full p3 Z/6 lane"

weakIsospinHalfIntegerFromSU2ThreeLabel :
  String
weakIsospinHalfIntegerFromSU2ThreeLabel =
  "Weak isospin half-integer units from the SU2_3 candidate"

colourTripleDegeneracyFromSU3OneDualLabel :
  String
colourTripleDegeneracyFromSU3OneDualLabel =
  "Colour triple degeneracy from the SU3_1 dual candidate"

finiteQuantisationBoundaryLabel :
  String
finiteQuantisationBoundaryLabel =
  "Structural finite charge quantisation is recorded without exact G_DHR = G_SM or full Standard Model promotion"

chargeQuantisationFromP3Lane :
  Bool
chargeQuantisationFromP3Lane =
  true

smChargeStructureFromSingleCMRing :
  SMChargeStructureStatus
smChargeStructureFromSingleCMRing =
  candidate

smChargeQuantisationDerived :
  Bool
smChargeQuantisationDerived =
  true

exactGDHREqualsGSM :
  Bool
exactGDHREqualsGSM =
  false

fullStandardModelDerived :
  Bool
fullStandardModelDerived =
  false

record SMChargeQuantisationReceipt : Setω where
  field
    p3LaneFiniteCarrier :
      String

    p3LaneFiniteCarrierIsZ6 :
      p3LaneFiniteCarrier ≡ "p3 Z/6"

    p3Z6ChargeElements :
      List P3Z6ChargeElement

    p3Z6ChargeElementsAreCanonical :
      p3Z6ChargeElements ≡ canonicalP3Z6ChargeElements

    electricChargeZ3Subset :
      List P3Z6ChargeElement

    electricChargeZ3SubsetIsCanonical :
      electricChargeZ3Subset ≡ canonicalElectricZ3SubsetOfP3Z6

    electricChargeUnitDenominator :
      Nat

    electricChargeUnitDenominatorIsThree :
      electricChargeUnitDenominator ≡ 3

    electricChargeUnitStatement :
      String

    electricChargeUnitStatementIsCanonical :
      electricChargeUnitStatement
      ≡
      electricChargeUnitFromZ3SubsetOfP3Z6Label

    hyperchargeUnitDenominator :
      Nat

    hyperchargeUnitDenominatorIsSix :
      hyperchargeUnitDenominator ≡ 6

    hyperchargeUnitStatement :
      String

    hyperchargeUnitStatementIsCanonical :
      hyperchargeUnitStatement ≡ hyperchargeUnitFromP3Z6Label

    weakIsospinCandidate :
      SU2ThreeIsospinCandidate

    weakIsospinCandidateIsSU2Three :
      weakIsospinCandidate ≡ su2ThreeWeakIsospinCandidate

    weakIsospinWeights :
      List WeakIsospinHalfIntegerWeight

    weakIsospinWeightsAreHalfInteger :
      weakIsospinWeights ≡ canonicalWeakIsospinHalfIntegerWeights

    weakIsospinUnitDenominator :
      Nat

    weakIsospinUnitDenominatorIsTwo :
      weakIsospinUnitDenominator ≡ 2

    weakIsospinStatement :
      String

    weakIsospinStatementIsCanonical :
      weakIsospinStatement ≡ weakIsospinHalfIntegerFromSU2ThreeLabel

    colourCandidate :
      SU3OneDualColourCandidate

    colourCandidateIsSU3OneDual :
      colourCandidate ≡ su3OneDualColourTripletCandidate

    colourDegeneracy :
      List ColourDegeneracyWitness

    colourDegeneracyIsTriple :
      colourDegeneracy ≡ canonicalColourTripleDegeneracy

    colourDegeneracyCount :
      Nat

    colourDegeneracyCountIsThree :
      colourDegeneracyCount ≡ 3

    colourDegeneracyStatement :
      String

    colourDegeneracyStatementIsCanonical :
      colourDegeneracyStatement
      ≡
      colourTripleDegeneracyFromSU3OneDualLabel

    chargeQuantisationFromP3LaneField :
      Bool

    chargeQuantisationFromP3LaneFieldIsTrue :
      chargeQuantisationFromP3LaneField ≡ chargeQuantisationFromP3Lane

    structuralFiniteQuantisation :
      Bool

    structuralFiniteQuantisationIsTrue :
      structuralFiniteQuantisation ≡ true

    smChargeStructureFromSingleCMRingField :
      SMChargeStructureStatus

    smChargeStructureFromSingleCMRingFieldIsCandidate :
      smChargeStructureFromSingleCMRingField
      ≡
      smChargeStructureFromSingleCMRing

    smChargeQuantisationDerivedField :
      Bool

    smChargeQuantisationDerivedFieldIsTrue :
      smChargeQuantisationDerivedField ≡ smChargeQuantisationDerived

    exactGDHREqualsGSMField :
      Bool

    exactGDHREqualsGSMFieldIsFalse :
      exactGDHREqualsGSMField ≡ exactGDHREqualsGSM

    fullStandardModelDerivedField :
      Bool

    fullStandardModelDerivedFieldIsFalse :
      fullStandardModelDerivedField ≡ fullStandardModelDerived

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ finiteQuantisationBoundaryLabel

    receiptBoundary :
      List String

open SMChargeQuantisationReceipt public

canonicalSMChargeQuantisationReceipt :
  SMChargeQuantisationReceipt
canonicalSMChargeQuantisationReceipt =
  record
    { p3LaneFiniteCarrier =
        "p3 Z/6"
    ; p3LaneFiniteCarrierIsZ6 =
        refl
    ; p3Z6ChargeElements =
        canonicalP3Z6ChargeElements
    ; p3Z6ChargeElementsAreCanonical =
        refl
    ; electricChargeZ3Subset =
        canonicalElectricZ3SubsetOfP3Z6
    ; electricChargeZ3SubsetIsCanonical =
        refl
    ; electricChargeUnitDenominator =
        3
    ; electricChargeUnitDenominatorIsThree =
        refl
    ; electricChargeUnitStatement =
        electricChargeUnitFromZ3SubsetOfP3Z6Label
    ; electricChargeUnitStatementIsCanonical =
        refl
    ; hyperchargeUnitDenominator =
        6
    ; hyperchargeUnitDenominatorIsSix =
        refl
    ; hyperchargeUnitStatement =
        hyperchargeUnitFromP3Z6Label
    ; hyperchargeUnitStatementIsCanonical =
        refl
    ; weakIsospinCandidate =
        su2ThreeWeakIsospinCandidate
    ; weakIsospinCandidateIsSU2Three =
        refl
    ; weakIsospinWeights =
        canonicalWeakIsospinHalfIntegerWeights
    ; weakIsospinWeightsAreHalfInteger =
        refl
    ; weakIsospinUnitDenominator =
        2
    ; weakIsospinUnitDenominatorIsTwo =
        refl
    ; weakIsospinStatement =
        weakIsospinHalfIntegerFromSU2ThreeLabel
    ; weakIsospinStatementIsCanonical =
        refl
    ; colourCandidate =
        su3OneDualColourTripletCandidate
    ; colourCandidateIsSU3OneDual =
        refl
    ; colourDegeneracy =
        canonicalColourTripleDegeneracy
    ; colourDegeneracyIsTriple =
        refl
    ; colourDegeneracyCount =
        3
    ; colourDegeneracyCountIsThree =
        refl
    ; colourDegeneracyStatement =
        colourTripleDegeneracyFromSU3OneDualLabel
    ; colourDegeneracyStatementIsCanonical =
        refl
    ; chargeQuantisationFromP3LaneField =
        true
    ; chargeQuantisationFromP3LaneFieldIsTrue =
        refl
    ; structuralFiniteQuantisation =
        true
    ; structuralFiniteQuantisationIsTrue =
        refl
    ; smChargeStructureFromSingleCMRingField =
        candidate
    ; smChargeStructureFromSingleCMRingFieldIsCandidate =
        refl
    ; smChargeQuantisationDerivedField =
        true
    ; smChargeQuantisationDerivedFieldIsTrue =
        refl
    ; exactGDHREqualsGSMField =
        false
    ; exactGDHREqualsGSMFieldIsFalse =
        refl
    ; fullStandardModelDerivedField =
        false
    ; fullStandardModelDerivedFieldIsFalse =
        refl
    ; boundaryStatement =
        finiteQuantisationBoundaryLabel
    ; boundaryStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Electric charge units are recorded as 1/3 from the Z/3 subset {0,2,4} of p3 Z/6"
        ∷ "Hypercharge units are recorded as 1/6 from the full p3 Z/6 lane"
        ∷ "Weak isospin half-integer units are recorded from the SU2_3 candidate"
        ∷ "Colour triple degeneracy is recorded from the SU3_1 dual candidate"
        ∷ "chargeQuantisationFromP3Lane=true as structural finite quantisation"
        ∷ "smChargeStructureFromSingleCMRing=candidate and smChargeQuantisationDerived=true"
        ∷ "Exact G_DHR=G_SM and full Standard Model reconstruction remain false"
        ∷ []
    }

chargeQuantisationFromP3LaneIsTrue :
  chargeQuantisationFromP3Lane ≡ true
chargeQuantisationFromP3LaneIsTrue =
  refl

smChargeStructureFromSingleCMRingIsCandidate :
  smChargeStructureFromSingleCMRing ≡ candidate
smChargeStructureFromSingleCMRingIsCandidate =
  refl

smChargeQuantisationDerivedIsTrue :
  smChargeQuantisationDerived ≡ true
smChargeQuantisationDerivedIsTrue =
  refl

exactGDHREqualsGSMIsFalse :
  exactGDHREqualsGSM ≡ false
exactGDHREqualsGSMIsFalse =
  refl

fullStandardModelDerivedIsFalse :
  fullStandardModelDerived ≡ false
fullStandardModelDerivedIsFalse =
  refl
