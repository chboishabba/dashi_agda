module DASHI.Physics.QFT.HyperchargeNormalisationAnomalyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; 0ℤ; _+_)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Hypercharge normalisation and anomaly receipt.
--
-- Convention: all matter is represented by left-handed Weyl fermions.
-- Hypercharges are recorded as signed sixths:
--
--   Q_L   :  +1/6, multiplicity 6 = 3 colours x 2 weak components
--   u^c   :  -2/3, multiplicity 3 = 3 anti-colours
--   d^c   :  +1/3, multiplicity 3 = 3 anti-colours
--   L_L   :  -1/2, multiplicity 2 = 2 weak components
--   e^c   :  +1,   multiplicity 1
--   nu^c  :   0,   optional sterile conjugate
--
-- With this left-handed convention, the Standard Model anomaly sums vanish:
--
--   U(1)_Y^3 numerator over 216:
--     6 - 192 + 24 - 54 + 216 + 0 = 0
--
--   gravitational-U(1)_Y numerator over 6:
--     6 - 12 + 6 - 6 + 6 + 0 = 0
--
--   SU(2)^2-U(1)_Y numerator over 6:
--     3 - 3 = 0
--
--   SU(3)^2-U(1)_Y numerator over 6:
--     2 - 4 + 2 = 0
--
-- The carrier Z/6 explains the unit 1/6.  This receipt does not claim
-- that the carrier derives the exact assignment, continuous U(1)_Y, anomaly
-- cancellation, the Standard Model, or G_DHR ~= G_SM.

data LeftHandedWeylMultiplet : Set where
  qL :
    LeftHandedWeylMultiplet

  uC :
    LeftHandedWeylMultiplet

  dC :
    LeftHandedWeylMultiplet

  leptonL :
    LeftHandedWeylMultiplet

  eC :
    LeftHandedWeylMultiplet

  nuC :
    LeftHandedWeylMultiplet

canonicalLeftHandedWeylMultiplets :
  List LeftHandedWeylMultiplet
canonicalLeftHandedWeylMultiplets =
  qL
  ∷ uC
  ∷ dC
  ∷ leptonL
  ∷ eC
  ∷ nuC
  ∷ []

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

signedSixthHypercharge :
  LeftHandedWeylMultiplet →
  ℤ
signedSixthHypercharge qL =
  sixthPlusOne
signedSixthHypercharge uC =
  sixthMinusFour
signedSixthHypercharge dC =
  sixthPlusTwo
signedSixthHypercharge leptonL =
  sixthMinusThree
signedSixthHypercharge eC =
  sixthPlusSix
signedSixthHypercharge nuC =
  sixthZero

weylMultiplicity :
  LeftHandedWeylMultiplet →
  Nat
weylMultiplicity qL =
  6
weylMultiplicity uC =
  3
weylMultiplicity dC =
  3
weylMultiplicity leptonL =
  2
weylMultiplicity eC =
  1
weylMultiplicity nuC =
  1

cubicContributionNumeratorOver216 :
  LeftHandedWeylMultiplet →
  ℤ
cubicContributionNumeratorOver216 qL =
  + 6
cubicContributionNumeratorOver216 uC =
  -[1+ 191 ]
cubicContributionNumeratorOver216 dC =
  + 24
cubicContributionNumeratorOver216 leptonL =
  -[1+ 53 ]
cubicContributionNumeratorOver216 eC =
  + 216
cubicContributionNumeratorOver216 nuC =
  + 0

gravitationalContributionNumeratorOver6 :
  LeftHandedWeylMultiplet →
  ℤ
gravitationalContributionNumeratorOver6 qL =
  + 6
gravitationalContributionNumeratorOver6 uC =
  -[1+ 11 ]
gravitationalContributionNumeratorOver6 dC =
  + 6
gravitationalContributionNumeratorOver6 leptonL =
  -[1+ 5 ]
gravitationalContributionNumeratorOver6 eC =
  + 6
gravitationalContributionNumeratorOver6 nuC =
  + 0

record HyperchargeLedgerEntry : Set where
  field
    multiplet :
      LeftHandedWeylMultiplet

    displayName :
      String

    signedSixths :
      ℤ

    signedSixthsAreStandard :
      signedSixths ≡ signedSixthHypercharge multiplet

    multiplicity :
      Nat

    multiplicityIsStandard :
      multiplicity ≡ weylMultiplicity multiplet

    cubicNumeratorOver216 :
      ℤ

    cubicNumeratorOver216IsStandard :
      cubicNumeratorOver216
      ≡
      cubicContributionNumeratorOver216 multiplet

    gravitationalNumeratorOver6 :
      ℤ

    gravitationalNumeratorOver6IsStandard :
      gravitationalNumeratorOver6
      ≡
      gravitationalContributionNumeratorOver6 multiplet

open HyperchargeLedgerEntry public

qLHyperchargeLedgerEntry :
  HyperchargeLedgerEntry
qLHyperchargeLedgerEntry =
  record
    { multiplet =
        qL
    ; displayName =
        "Q_L: Y=+1/6, multiplicity 6"
    ; signedSixths =
        sixthPlusOne
    ; signedSixthsAreStandard =
        refl
    ; multiplicity =
        6
    ; multiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        + 6
    ; cubicNumeratorOver216IsStandard =
        refl
    ; gravitationalNumeratorOver6 =
        + 6
    ; gravitationalNumeratorOver6IsStandard =
        refl
    }

uCHyperchargeLedgerEntry :
  HyperchargeLedgerEntry
uCHyperchargeLedgerEntry =
  record
    { multiplet =
        uC
    ; displayName =
        "u^c: Y=-2/3=-4/6, multiplicity 3"
    ; signedSixths =
        sixthMinusFour
    ; signedSixthsAreStandard =
        refl
    ; multiplicity =
        3
    ; multiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        -[1+ 191 ]
    ; cubicNumeratorOver216IsStandard =
        refl
    ; gravitationalNumeratorOver6 =
        -[1+ 11 ]
    ; gravitationalNumeratorOver6IsStandard =
        refl
    }

dCHyperchargeLedgerEntry :
  HyperchargeLedgerEntry
dCHyperchargeLedgerEntry =
  record
    { multiplet =
        dC
    ; displayName =
        "d^c: Y=+1/3=+2/6, multiplicity 3"
    ; signedSixths =
        sixthPlusTwo
    ; signedSixthsAreStandard =
        refl
    ; multiplicity =
        3
    ; multiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        + 24
    ; cubicNumeratorOver216IsStandard =
        refl
    ; gravitationalNumeratorOver6 =
        + 6
    ; gravitationalNumeratorOver6IsStandard =
        refl
    }

leptonLHyperchargeLedgerEntry :
  HyperchargeLedgerEntry
leptonLHyperchargeLedgerEntry =
  record
    { multiplet =
        leptonL
    ; displayName =
        "L_L: Y=-1/2=-3/6, multiplicity 2"
    ; signedSixths =
        sixthMinusThree
    ; signedSixthsAreStandard =
        refl
    ; multiplicity =
        2
    ; multiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        -[1+ 53 ]
    ; cubicNumeratorOver216IsStandard =
        refl
    ; gravitationalNumeratorOver6 =
        -[1+ 5 ]
    ; gravitationalNumeratorOver6IsStandard =
        refl
    }

eCHyperchargeLedgerEntry :
  HyperchargeLedgerEntry
eCHyperchargeLedgerEntry =
  record
    { multiplet =
        eC
    ; displayName =
        "e^c: Y=+1=+6/6, multiplicity 1"
    ; signedSixths =
        sixthPlusSix
    ; signedSixthsAreStandard =
        refl
    ; multiplicity =
        1
    ; multiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        + 216
    ; cubicNumeratorOver216IsStandard =
        refl
    ; gravitationalNumeratorOver6 =
        + 6
    ; gravitationalNumeratorOver6IsStandard =
        refl
    }

nuCHyperchargeLedgerEntry :
  HyperchargeLedgerEntry
nuCHyperchargeLedgerEntry =
  record
    { multiplet =
        nuC
    ; displayName =
        "nu^c: optional sterile conjugate, Y=0"
    ; signedSixths =
        sixthZero
    ; signedSixthsAreStandard =
        refl
    ; multiplicity =
        1
    ; multiplicityIsStandard =
        refl
    ; cubicNumeratorOver216 =
        + 0
    ; cubicNumeratorOver216IsStandard =
        refl
    ; gravitationalNumeratorOver6 =
        + 0
    ; gravitationalNumeratorOver6IsStandard =
        refl
    }

canonicalHyperchargeLedger :
  List HyperchargeLedgerEntry
canonicalHyperchargeLedger =
  qLHyperchargeLedgerEntry
  ∷ uCHyperchargeLedgerEntry
  ∷ dCHyperchargeLedgerEntry
  ∷ leptonLHyperchargeLedgerEntry
  ∷ eCHyperchargeLedgerEntry
  ∷ nuCHyperchargeLedgerEntry
  ∷ []

cubicAnomalyNumeratorOver216 :
  ℤ
cubicAnomalyNumeratorOver216 =
  cubicContributionNumeratorOver216 qL
  + cubicContributionNumeratorOver216 uC
  + cubicContributionNumeratorOver216 dC
  + cubicContributionNumeratorOver216 leptonL
  + cubicContributionNumeratorOver216 eC
  + cubicContributionNumeratorOver216 nuC

gravitationalAnomalyNumeratorOver6 :
  ℤ
gravitationalAnomalyNumeratorOver6 =
  gravitationalContributionNumeratorOver6 qL
  + gravitationalContributionNumeratorOver6 uC
  + gravitationalContributionNumeratorOver6 dC
  + gravitationalContributionNumeratorOver6 leptonL
  + gravitationalContributionNumeratorOver6 eC
  + gravitationalContributionNumeratorOver6 nuC

su2MixedAnomalyNumeratorOver6 :
  ℤ
su2MixedAnomalyNumeratorOver6 =
  + 3 + -[1+ 2 ]

su3MixedAnomalyNumeratorOver6 :
  ℤ
su3MixedAnomalyNumeratorOver6 =
  + 2 + -[1+ 3 ] + + 2

cubicAnomalyCancellationStatement :
  String
cubicAnomalyCancellationStatement =
  "U(1)_Y^3 numerator over 216: 6 - 192 + 24 - 54 + 216 + 0 = 0"

gravitationalAnomalyCancellationStatement :
  String
gravitationalAnomalyCancellationStatement =
  "gravitational-U(1)_Y numerator over 6: 6 - 12 + 6 - 6 + 6 + 0 = 0"

su2MixedAnomalyCancellationStatement :
  String
su2MixedAnomalyCancellationStatement =
  "SU(2)^2-U(1)_Y numerator over 6: three Q_L colours minus one L_L doublet contribution, 3 - 3 = 0"

su3MixedAnomalyCancellationStatement :
  String
su3MixedAnomalyCancellationStatement =
  "SU(3)^2-U(1)_Y numerator over 6: two Q_L weak components plus u^c plus d^c, 2 - 4 + 2 = 0"

carrierZ6BoundaryStatement :
  String
carrierZ6BoundaryStatement =
  "The p3 Z/6 carrier explains the hypercharge unit 1/6 only; exact assignments, continuous U(1)_Y, anomaly cancellation, SM reconstruction, and G_DHR ~= G_SM are not promoted"

record HyperchargeNormalisationAnomalyReceipt : Setω where
  field
    leftHandedConvention :
      String

    leftHandedConventionIsCanonical :
      leftHandedConvention
      ≡
      "Left-handed Weyl convention with conjugates u^c, d^c, e^c, and optional nu^c"

    hyperchargeUnitDenominator :
      Nat

    hyperchargeUnitDenominatorIsSix :
      hyperchargeUnitDenominator ≡ 6

    carrierFiniteGroup :
      String

    carrierFiniteGroupIsZ6 :
      carrierFiniteGroup ≡ "p3 Z/6"

    carrierExplainsUnitOneSixth :
      Bool

    carrierExplainsUnitOneSixthIsTrue :
      carrierExplainsUnitOneSixth ≡ true

    hyperchargeLedger :
      List HyperchargeLedgerEntry

    hyperchargeLedgerIsCanonical :
      hyperchargeLedger ≡ canonicalHyperchargeLedger

    cubicCommonDenominator :
      Nat

    cubicCommonDenominatorIs216 :
      cubicCommonDenominator ≡ 216

    cubicNumerator :
      ℤ

    cubicNumeratorIsStandardSum :
      cubicNumerator ≡ cubicAnomalyNumeratorOver216

    cubicNumeratorIsZero :
      cubicNumerator ≡ 0ℤ

    gravitationalCommonDenominator :
      Nat

    gravitationalCommonDenominatorIsSix :
      gravitationalCommonDenominator ≡ 6

    gravitationalNumerator :
      ℤ

    gravitationalNumeratorIsStandardSum :
      gravitationalNumerator ≡ gravitationalAnomalyNumeratorOver6

    gravitationalNumeratorIsZero :
      gravitationalNumerator ≡ 0ℤ

    su2MixedNumerator :
      ℤ

    su2MixedNumeratorIsStandardSum :
      su2MixedNumerator ≡ su2MixedAnomalyNumeratorOver6

    su2MixedNumeratorIsZero :
      su2MixedNumerator ≡ 0ℤ

    su3MixedNumerator :
      ℤ

    su3MixedNumeratorIsStandardSum :
      su3MixedNumerator ≡ su3MixedAnomalyNumeratorOver6

    su3MixedNumeratorIsZero :
      su3MixedNumerator ≡ 0ℤ

    cubicAnomalyCancels :
      Bool

    cubicAnomalyCancelsIsTrue :
      cubicAnomalyCancels ≡ true

    gravitationalAnomalyCancels :
      Bool

    gravitationalAnomalyCancelsIsTrue :
      gravitationalAnomalyCancels ≡ true

    su2MixedAnomalyCancels :
      Bool

    su2MixedAnomalyCancelsIsTrue :
      su2MixedAnomalyCancels ≡ true

    su3MixedAnomalyCancels :
      Bool

    su3MixedAnomalyCancelsIsTrue :
      su3MixedAnomalyCancels ≡ true

    carrierDerivesExactAssignment :
      Bool

    carrierDerivesExactAssignmentIsFalse :
      carrierDerivesExactAssignment ≡ false

    carrierDerivesContinuousU1Y :
      Bool

    carrierDerivesContinuousU1YIsFalse :
      carrierDerivesContinuousU1Y ≡ false

    exactU1YPromoted :
      Bool

    exactU1YPromotedIsFalse :
      exactU1YPromoted ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    exactGDHREqualsGSMPromoted :
      Bool

    exactGDHREqualsGSMPromotedIsFalse :
      exactGDHREqualsGSMPromoted ≡ false

    cubicStatement :
      String

    cubicStatementIsCanonical :
      cubicStatement ≡ cubicAnomalyCancellationStatement

    gravitationalStatement :
      String

    gravitationalStatementIsCanonical :
      gravitationalStatement ≡ gravitationalAnomalyCancellationStatement

    su2Statement :
      String

    su2StatementIsCanonical :
      su2Statement ≡ su2MixedAnomalyCancellationStatement

    su3Statement :
      String

    su3StatementIsCanonical :
      su3Statement ≡ su3MixedAnomalyCancellationStatement

    carrierBoundary :
      String

    carrierBoundaryIsCanonical :
      carrierBoundary ≡ carrierZ6BoundaryStatement

    auditTrail :
      List String

open HyperchargeNormalisationAnomalyReceipt public

canonicalHyperchargeNormalisationAnomalyReceipt :
  HyperchargeNormalisationAnomalyReceipt
canonicalHyperchargeNormalisationAnomalyReceipt =
  record
    { leftHandedConvention =
        "Left-handed Weyl convention with conjugates u^c, d^c, e^c, and optional nu^c"
    ; leftHandedConventionIsCanonical =
        refl
    ; hyperchargeUnitDenominator =
        6
    ; hyperchargeUnitDenominatorIsSix =
        refl
    ; carrierFiniteGroup =
        "p3 Z/6"
    ; carrierFiniteGroupIsZ6 =
        refl
    ; carrierExplainsUnitOneSixth =
        true
    ; carrierExplainsUnitOneSixthIsTrue =
        refl
    ; hyperchargeLedger =
        canonicalHyperchargeLedger
    ; hyperchargeLedgerIsCanonical =
        refl
    ; cubicCommonDenominator =
        216
    ; cubicCommonDenominatorIs216 =
        refl
    ; cubicNumerator =
        cubicAnomalyNumeratorOver216
    ; cubicNumeratorIsStandardSum =
        refl
    ; cubicNumeratorIsZero =
        refl
    ; gravitationalCommonDenominator =
        6
    ; gravitationalCommonDenominatorIsSix =
        refl
    ; gravitationalNumerator =
        gravitationalAnomalyNumeratorOver6
    ; gravitationalNumeratorIsStandardSum =
        refl
    ; gravitationalNumeratorIsZero =
        refl
    ; su2MixedNumerator =
        su2MixedAnomalyNumeratorOver6
    ; su2MixedNumeratorIsStandardSum =
        refl
    ; su2MixedNumeratorIsZero =
        refl
    ; su3MixedNumerator =
        su3MixedAnomalyNumeratorOver6
    ; su3MixedNumeratorIsStandardSum =
        refl
    ; su3MixedNumeratorIsZero =
        refl
    ; cubicAnomalyCancels =
        true
    ; cubicAnomalyCancelsIsTrue =
        refl
    ; gravitationalAnomalyCancels =
        true
    ; gravitationalAnomalyCancelsIsTrue =
        refl
    ; su2MixedAnomalyCancels =
        true
    ; su2MixedAnomalyCancelsIsTrue =
        refl
    ; su3MixedAnomalyCancels =
        true
    ; su3MixedAnomalyCancelsIsTrue =
        refl
    ; carrierDerivesExactAssignment =
        false
    ; carrierDerivesExactAssignmentIsFalse =
        refl
    ; carrierDerivesContinuousU1Y =
        false
    ; carrierDerivesContinuousU1YIsFalse =
        refl
    ; exactU1YPromoted =
        false
    ; exactU1YPromotedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; exactGDHREqualsGSMPromoted =
        false
    ; exactGDHREqualsGSMPromotedIsFalse =
        refl
    ; cubicStatement =
        cubicAnomalyCancellationStatement
    ; cubicStatementIsCanonical =
        refl
    ; gravitationalStatement =
        gravitationalAnomalyCancellationStatement
    ; gravitationalStatementIsCanonical =
        refl
    ; su2Statement =
        su2MixedAnomalyCancellationStatement
    ; su2StatementIsCanonical =
        refl
    ; su3Statement =
        su3MixedAnomalyCancellationStatement
    ; su3StatementIsCanonical =
        refl
    ; carrierBoundary =
        carrierZ6BoundaryStatement
    ; carrierBoundaryIsCanonical =
        refl
    ; auditTrail =
        "SM anomaly cancellation is computed in the left-handed Weyl convention"
        ∷ "The cubic numerator over 216 vanishes: 6 - 192 + 24 - 54 + 216 + 0 = 0"
        ∷ "The gravitational-U1 numerator over 6 vanishes: 6 - 12 + 6 - 6 + 6 + 0 = 0"
        ∷ "The SU2^2-U1 mixed anomaly vanishes: 3 - 3 = 0"
        ∷ "The SU3^2-U1 mixed anomaly vanishes: 2 - 4 + 2 = 0"
        ∷ "The carrier Z/6 explains the unit only; exact U1Y, SM, and GDHR promotions remain false"
        ∷ []
    }

hyperchargeAnomalyCarrierExplainsUnit :
  carrierExplainsUnitOneSixth canonicalHyperchargeNormalisationAnomalyReceipt
  ≡
  true
hyperchargeAnomalyCarrierExplainsUnit =
  refl

hyperchargeAnomalyCubicNumeratorZero :
  cubicNumerator canonicalHyperchargeNormalisationAnomalyReceipt
  ≡
  0ℤ
hyperchargeAnomalyCubicNumeratorZero =
  refl

hyperchargeAnomalyGravitationalNumeratorZero :
  gravitationalNumerator canonicalHyperchargeNormalisationAnomalyReceipt
  ≡
  0ℤ
hyperchargeAnomalyGravitationalNumeratorZero =
  refl

hyperchargeAnomalySU2MixedNumeratorZero :
  su2MixedNumerator canonicalHyperchargeNormalisationAnomalyReceipt
  ≡
  0ℤ
hyperchargeAnomalySU2MixedNumeratorZero =
  refl

hyperchargeAnomalySU3MixedNumeratorZero :
  su3MixedNumerator canonicalHyperchargeNormalisationAnomalyReceipt
  ≡
  0ℤ
hyperchargeAnomalySU3MixedNumeratorZero =
  refl

hyperchargeAnomalyExactAssignmentFalse :
  carrierDerivesExactAssignment canonicalHyperchargeNormalisationAnomalyReceipt
  ≡
  false
hyperchargeAnomalyExactAssignmentFalse =
  refl

hyperchargeAnomalyContinuousU1YFalse :
  carrierDerivesContinuousU1Y canonicalHyperchargeNormalisationAnomalyReceipt
  ≡
  false
hyperchargeAnomalyContinuousU1YFalse =
  refl

hyperchargeAnomalyExactU1YPromotedFalse :
  exactU1YPromoted canonicalHyperchargeNormalisationAnomalyReceipt
  ≡
  false
hyperchargeAnomalyExactU1YPromotedFalse =
  refl

hyperchargeAnomalyExactStandardModelPromotedFalse :
  exactStandardModelPromoted canonicalHyperchargeNormalisationAnomalyReceipt
  ≡
  false
hyperchargeAnomalyExactStandardModelPromotedFalse =
  refl

hyperchargeAnomalyExactGDHREqualsGSMPromotedFalse :
  exactGDHREqualsGSMPromoted canonicalHyperchargeNormalisationAnomalyReceipt
  ≡
  false
hyperchargeAnomalyExactGDHREqualsGSMPromotedFalse =
  refl
