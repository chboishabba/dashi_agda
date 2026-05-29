module DASHI.Physics.QFT.ChargeNormalisationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; 0ℤ; _+_)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Charge normalisation receipt.
--
-- The finite Z/6 carrier explains the hypercharge quantisation unit 1/6.
-- It does not by itself derive the exact Standard Model assignment, exact
-- U(1)_Y normalisation, or anomaly cancellation.  Those are recorded here
-- as a separate Standard Model per-generation ledger with signed-sixth
-- hypercharges and Weyl multiplicities.

data FiniteHyperchargeCarrier : Set where
  p3Z6Carrier :
    FiniteHyperchargeCarrier

data SMWeylMultiplet : Set where
  qL :
    SMWeylMultiplet

  uC :
    SMWeylMultiplet

  dC :
    SMWeylMultiplet

  leptonL :
    SMWeylMultiplet

  eC :
    SMWeylMultiplet

  nuC :
    SMWeylMultiplet

sixthZero :
  ℤ
sixthZero =
  + 0

sixthPlusOne :
  ℤ
sixthPlusOne =
  + 1

sixthPlusTwo :
  ℤ
sixthPlusTwo =
  + 2

sixthPlusSix :
  ℤ
sixthPlusSix =
  + 6

sixthMinusThree :
  ℤ
sixthMinusThree =
  -[1+ 2 ]

sixthMinusFour :
  ℤ
sixthMinusFour =
  -[1+ 3 ]

smSignedSixthHypercharge :
  SMWeylMultiplet →
  ℤ
smSignedSixthHypercharge qL =
  sixthPlusOne
smSignedSixthHypercharge uC =
  sixthMinusFour
smSignedSixthHypercharge dC =
  sixthPlusTwo
smSignedSixthHypercharge leptonL =
  sixthMinusThree
smSignedSixthHypercharge eC =
  sixthPlusSix
smSignedSixthHypercharge nuC =
  sixthZero

smWeylMultiplicity :
  SMWeylMultiplet →
  Nat
smWeylMultiplicity qL =
  6
smWeylMultiplicity uC =
  3
smWeylMultiplicity dC =
  3
smWeylMultiplicity leptonL =
  2
smWeylMultiplicity eC =
  1
smWeylMultiplicity nuC =
  1

smCubicAnomalyNumeratorOver216 :
  SMWeylMultiplet →
  ℤ
smCubicAnomalyNumeratorOver216 qL =
  + 6
smCubicAnomalyNumeratorOver216 uC =
  -[1+ 191 ]
smCubicAnomalyNumeratorOver216 dC =
  + 24
smCubicAnomalyNumeratorOver216 leptonL =
  -[1+ 53 ]
smCubicAnomalyNumeratorOver216 eC =
  + 216
smCubicAnomalyNumeratorOver216 nuC =
  + 0

record SMHyperchargeLedgerEntry : Set where
  field
    multiplet :
      SMWeylMultiplet

    displayName :
      String

    signedSixths :
      ℤ

    signedSixthsAreStandard :
      signedSixths ≡ smSignedSixthHypercharge multiplet

    weylMultiplicity :
      Nat

    weylMultiplicityIsStandard :
      weylMultiplicity ≡ smWeylMultiplicity multiplet

    cubicNumeratorOver216 :
      ℤ

    cubicNumeratorOver216IsStandard :
      cubicNumeratorOver216
      ≡
      smCubicAnomalyNumeratorOver216 multiplet

open SMHyperchargeLedgerEntry public

qLHyperchargeLedgerEntry :
  SMHyperchargeLedgerEntry
qLHyperchargeLedgerEntry =
  record
    { multiplet =
        qL
    ; displayName =
        "Q_L: 3 colours x 2 weak components, Y=1/6"
    ; signedSixths =
        sixthPlusOne
    ; signedSixthsAreStandard =
        refl
    ; weylMultiplicity =
        6
    ; weylMultiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        + 6
    ; cubicNumeratorOver216IsStandard =
        refl
    }

uCHyperchargeLedgerEntry :
  SMHyperchargeLedgerEntry
uCHyperchargeLedgerEntry =
  record
    { multiplet =
        uC
    ; displayName =
        "u^c: 3 colours, left-handed conjugate of u_R, Y=-4/6"
    ; signedSixths =
        sixthMinusFour
    ; signedSixthsAreStandard =
        refl
    ; weylMultiplicity =
        3
    ; weylMultiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        -[1+ 191 ]
    ; cubicNumeratorOver216IsStandard =
        refl
    }

dCHyperchargeLedgerEntry :
  SMHyperchargeLedgerEntry
dCHyperchargeLedgerEntry =
  record
    { multiplet =
        dC
    ; displayName =
        "d^c: 3 colours, left-handed conjugate of d_R, Y=2/6"
    ; signedSixths =
        sixthPlusTwo
    ; signedSixthsAreStandard =
        refl
    ; weylMultiplicity =
        3
    ; weylMultiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        + 24
    ; cubicNumeratorOver216IsStandard =
        refl
    }

leptonLHyperchargeLedgerEntry :
  SMHyperchargeLedgerEntry
leptonLHyperchargeLedgerEntry =
  record
    { multiplet =
        leptonL
    ; displayName =
        "L_L: 2 weak components, Y=-3/6"
    ; signedSixths =
        sixthMinusThree
    ; signedSixthsAreStandard =
        refl
    ; weylMultiplicity =
        2
    ; weylMultiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        -[1+ 53 ]
    ; cubicNumeratorOver216IsStandard =
        refl
    }

eCHyperchargeLedgerEntry :
  SMHyperchargeLedgerEntry
eCHyperchargeLedgerEntry =
  record
    { multiplet =
        eC
    ; displayName =
        "e^c: left-handed conjugate of e_R, Y=6/6"
    ; signedSixths =
        sixthPlusSix
    ; signedSixthsAreStandard =
        refl
    ; weylMultiplicity =
        1
    ; weylMultiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        + 216
    ; cubicNumeratorOver216IsStandard =
        refl
    }

nuCHyperchargeLedgerEntry :
  SMHyperchargeLedgerEntry
nuCHyperchargeLedgerEntry =
  record
    { multiplet =
        nuC
    ; displayName =
        "nu^c optional sterile conjugate, Y=0/6"
    ; signedSixths =
        sixthZero
    ; signedSixthsAreStandard =
        refl
    ; weylMultiplicity =
        1
    ; weylMultiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        + 0
    ; cubicNumeratorOver216IsStandard =
        refl
    }

canonicalSMHyperchargeLedger :
  List SMHyperchargeLedgerEntry
canonicalSMHyperchargeLedger =
  qLHyperchargeLedgerEntry
  ∷ uCHyperchargeLedgerEntry
  ∷ dCHyperchargeLedgerEntry
  ∷ leptonLHyperchargeLedgerEntry
  ∷ eCHyperchargeLedgerEntry
  ∷ nuCHyperchargeLedgerEntry
  ∷ []

standardGenerationCubicAnomalyNumeratorOver216 :
  ℤ
standardGenerationCubicAnomalyNumeratorOver216 =
  smCubicAnomalyNumeratorOver216 qL
  + smCubicAnomalyNumeratorOver216 uC
  + smCubicAnomalyNumeratorOver216 dC
  + smCubicAnomalyNumeratorOver216 leptonL
  + smCubicAnomalyNumeratorOver216 eC
  + smCubicAnomalyNumeratorOver216 nuC

finiteZ6CarrierBoundaryLabel :
  String
finiteZ6CarrierBoundaryLabel =
  "Finite Z/6 derives the hypercharge unit 1/6 only; exact normalisation and anomaly cancellation are separate checks"

standardCubicAnomalyCancellationLabel :
  String
standardCubicAnomalyCancellationLabel =
  "Per-generation SM signed-sixth cubic numerator over 216 sums to zero: 6 - 192 + 24 - 54 + 216 + 0 = 0"

record ChargeNormalisationReceipt : Setω where
  field
    finiteCarrier :
      FiniteHyperchargeCarrier

    finiteCarrierIsP3Z6 :
      finiteCarrier ≡ p3Z6Carrier

    carrierOrder :
      Nat

    carrierOrderIsSix :
      carrierOrder ≡ 6

    hyperchargeUnitDenominator :
      Nat

    hyperchargeUnitDenominatorIsSix :
      hyperchargeUnitDenominator ≡ 6

    carrierDerivesHyperchargeUnit :
      Bool

    carrierDerivesHyperchargeUnitIsTrue :
      carrierDerivesHyperchargeUnit ≡ true

    carrierDerivesExactNormalisation :
      Bool

    carrierDerivesExactNormalisationIsFalse :
      carrierDerivesExactNormalisation ≡ false

    carrierDerivesExactAssignment :
      Bool

    carrierDerivesExactAssignmentIsFalse :
      carrierDerivesExactAssignment ≡ false

    carrierDerivesAnomalyCancellation :
      Bool

    carrierDerivesAnomalyCancellationIsFalse :
      carrierDerivesAnomalyCancellation ≡ false

    smHyperchargeLedger :
      List SMHyperchargeLedgerEntry

    smHyperchargeLedgerIsCanonical :
      smHyperchargeLedger ≡ canonicalSMHyperchargeLedger

    cubicAnomalyCommonDenominator :
      Nat

    cubicAnomalyCommonDenominatorIs216 :
      cubicAnomalyCommonDenominator ≡ 216

    cubicAnomalyNumerator :
      ℤ

    cubicAnomalyNumeratorIsStandardSum :
      cubicAnomalyNumerator
      ≡
      standardGenerationCubicAnomalyNumeratorOver216

    cubicAnomalyNumeratorIsZero :
      cubicAnomalyNumerator ≡ 0ℤ

    separateAnomalyCheckPerformed :
      Bool

    separateAnomalyCheckPerformedIsTrue :
      separateAnomalyCheckPerformed ≡ true

    exactU1YNormalisationPromoted :
      Bool

    exactU1YNormalisationPromotedIsFalse :
      exactU1YNormalisationPromoted ≡ false

    exactSMChargeAssignmentPromoted :
      Bool

    exactSMChargeAssignmentPromotedIsFalse :
      exactSMChargeAssignmentPromoted ≡ false

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ finiteZ6CarrierBoundaryLabel

    anomalyStatement :
      String

    anomalyStatementIsCanonical :
      anomalyStatement ≡ standardCubicAnomalyCancellationLabel

    auditTrail :
      List String

open ChargeNormalisationReceipt public

canonicalChargeNormalisationReceipt :
  ChargeNormalisationReceipt
canonicalChargeNormalisationReceipt =
  record
    { finiteCarrier =
        p3Z6Carrier
    ; finiteCarrierIsP3Z6 =
        refl
    ; carrierOrder =
        6
    ; carrierOrderIsSix =
        refl
    ; hyperchargeUnitDenominator =
        6
    ; hyperchargeUnitDenominatorIsSix =
        refl
    ; carrierDerivesHyperchargeUnit =
        true
    ; carrierDerivesHyperchargeUnitIsTrue =
        refl
    ; carrierDerivesExactNormalisation =
        false
    ; carrierDerivesExactNormalisationIsFalse =
        refl
    ; carrierDerivesExactAssignment =
        false
    ; carrierDerivesExactAssignmentIsFalse =
        refl
    ; carrierDerivesAnomalyCancellation =
        false
    ; carrierDerivesAnomalyCancellationIsFalse =
        refl
    ; smHyperchargeLedger =
        canonicalSMHyperchargeLedger
    ; smHyperchargeLedgerIsCanonical =
        refl
    ; cubicAnomalyCommonDenominator =
        216
    ; cubicAnomalyCommonDenominatorIs216 =
        refl
    ; cubicAnomalyNumerator =
        standardGenerationCubicAnomalyNumeratorOver216
    ; cubicAnomalyNumeratorIsStandardSum =
        refl
    ; cubicAnomalyNumeratorIsZero =
        refl
    ; separateAnomalyCheckPerformed =
        true
    ; separateAnomalyCheckPerformedIsTrue =
        refl
    ; exactU1YNormalisationPromoted =
        false
    ; exactU1YNormalisationPromotedIsFalse =
        refl
    ; exactSMChargeAssignmentPromoted =
        false
    ; exactSMChargeAssignmentPromotedIsFalse =
        refl
    ; boundaryStatement =
        finiteZ6CarrierBoundaryLabel
    ; boundaryStatementIsCanonical =
        refl
    ; anomalyStatement =
        standardCubicAnomalyCancellationLabel
    ; anomalyStatementIsCanonical =
        refl
    ; auditTrail =
        "Finite Z/6 supplies hypercharge denominator 6"
        ∷ "The carrier does not promote exact U1_Y normalisation"
        ∷ "The carrier does not derive the exact SM hypercharge assignment"
        ∷ "Cubic anomaly cancellation is checked separately on the SM per-generation signed-sixth ledger"
        ∷ "Common-denominator numerator is 6 - 192 + 24 - 54 + 216 + 0 = 0 over 216"
        ∷ []
    }

chargeNormalisationCarrierDerivesUnit :
  carrierDerivesHyperchargeUnit canonicalChargeNormalisationReceipt
  ≡
  true
chargeNormalisationCarrierDerivesUnit =
  refl

chargeNormalisationCarrierExactNormalisationFalse :
  carrierDerivesExactNormalisation canonicalChargeNormalisationReceipt
  ≡
  false
chargeNormalisationCarrierExactNormalisationFalse =
  refl

chargeNormalisationCarrierExactAssignmentFalse :
  carrierDerivesExactAssignment canonicalChargeNormalisationReceipt
  ≡
  false
chargeNormalisationCarrierExactAssignmentFalse =
  refl

chargeNormalisationCarrierAnomalyCancellationFalse :
  carrierDerivesAnomalyCancellation canonicalChargeNormalisationReceipt
  ≡
  false
chargeNormalisationCarrierAnomalyCancellationFalse =
  refl

chargeNormalisationStandardCubicNumeratorZero :
  cubicAnomalyNumerator canonicalChargeNormalisationReceipt
  ≡
  0ℤ
chargeNormalisationStandardCubicNumeratorZero =
  refl

chargeNormalisationSeparateAnomalyCheckPerformed :
  separateAnomalyCheckPerformed canonicalChargeNormalisationReceipt
  ≡
  true
chargeNormalisationSeparateAnomalyCheckPerformed =
  refl

chargeNormalisationExactU1YNormalisationPromotedFalse :
  exactU1YNormalisationPromoted canonicalChargeNormalisationReceipt
  ≡
  false
chargeNormalisationExactU1YNormalisationPromotedFalse =
  refl

chargeNormalisationExactSMChargeAssignmentPromotedFalse :
  exactSMChargeAssignmentPromoted canonicalChargeNormalisationReceipt
  ≡
  false
chargeNormalisationExactSMChargeAssignmentPromotedFalse =
  refl
