module DASHI.Promotion.StandardModelFiniteAnomalyHyperchargeCheck where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (ℤ; 0ℤ)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.AnomalyCancellationVerificationReceipt as Verify
import DASHI.Physics.Closure.U1YChargeAssignmentTableReceipt as U1YTable
import DASHI.Physics.QFT.HyperchargeNormalisationAnomalyReceipt as HAnomaly
import DASHI.Promotion.StandardModelFiniteRepresentationNarrowing as Narrow

------------------------------------------------------------------------
-- Finite Standard Model anomaly and hypercharge check.
--
-- This module is a finite one-generation check surface.  It narrows the SM
-- lane to the concrete all-left-handed Weyl multiplets and their signed-sixth
-- hypercharges, then records the four standard anomaly balance rows.
--
-- It is deliberately not a broad Standard Model promotion: continuous gauge
-- construction, PDG authority, Yukawa/CKM/PMNS data, empirical observables,
-- DHR exactness, and terminal unification remain false/open.

data FiniteSMAnomalyMultiplet : Set where
  finiteQL :
    FiniteSMAnomalyMultiplet

  finiteUC :
    FiniteSMAnomalyMultiplet

  finiteDC :
    FiniteSMAnomalyMultiplet

  finiteLL :
    FiniteSMAnomalyMultiplet

  finiteEC :
    FiniteSMAnomalyMultiplet

  finiteNuC :
    FiniteSMAnomalyMultiplet

finiteMultipletLabel :
  FiniteSMAnomalyMultiplet →
  String
finiteMultipletLabel finiteQL =
  "Q_L"
finiteMultipletLabel finiteUC =
  "u^c"
finiteMultipletLabel finiteDC =
  "d^c"
finiteMultipletLabel finiteLL =
  "L_L"
finiteMultipletLabel finiteEC =
  "e^c"
finiteMultipletLabel finiteNuC =
  "nu^c"

finiteMultipletSource :
  FiniteSMAnomalyMultiplet →
  HAnomaly.LeftHandedWeylMultiplet
finiteMultipletSource finiteQL =
  HAnomaly.qL
finiteMultipletSource finiteUC =
  HAnomaly.uC
finiteMultipletSource finiteDC =
  HAnomaly.dC
finiteMultipletSource finiteLL =
  HAnomaly.leptonL
finiteMultipletSource finiteEC =
  HAnomaly.eC
finiteMultipletSource finiteNuC =
  HAnomaly.nuC

record FiniteSMHyperchargeMultipletRow : Set where
  field
    multiplet :
      FiniteSMAnomalyMultiplet

    sourceMultiplet :
      HAnomaly.LeftHandedWeylMultiplet

    sourceMultipletIsCanonical :
      sourceMultiplet ≡ finiteMultipletSource multiplet

    displayLabel :
      String

    displayLabelIsCanonical :
      displayLabel ≡ finiteMultipletLabel multiplet

    signedSixths :
      ℤ

    signedSixthsAreCanonical :
      signedSixths ≡ HAnomaly.signedSixthHypercharge sourceMultiplet

    weylMultiplicity :
      Nat

    weylMultiplicityIsCanonical :
      weylMultiplicity ≡ HAnomaly.weylMultiplicity sourceMultiplet

    cubicNumeratorOver216 :
      ℤ

    cubicNumeratorOver216IsCanonical :
      cubicNumeratorOver216
      ≡
      HAnomaly.cubicContributionNumeratorOver216 sourceMultiplet

    gravitationalNumeratorOver6 :
      ℤ

    gravitationalNumeratorOver6IsCanonical :
      gravitationalNumeratorOver6
      ≡
      HAnomaly.gravitationalContributionNumeratorOver6 sourceMultiplet

    rowIsFiniteOneGenerationOnly :
      Bool

    rowIsFiniteOneGenerationOnlyIsTrue :
      rowIsFiniteOneGenerationOnly ≡ true

open FiniteSMHyperchargeMultipletRow public

qLFiniteSMHyperchargeMultipletRow :
  FiniteSMHyperchargeMultipletRow
qLFiniteSMHyperchargeMultipletRow =
  record
    { multiplet = finiteQL
    ; sourceMultiplet = HAnomaly.qL
    ; sourceMultipletIsCanonical = refl
    ; displayLabel = "Q_L"
    ; displayLabelIsCanonical = refl
    ; signedSixths = HAnomaly.sixthPlusOne
    ; signedSixthsAreCanonical = refl
    ; weylMultiplicity = 6
    ; weylMultiplicityIsCanonical = refl
    ; cubicNumeratorOver216 = HAnomaly.cubicContributionNumeratorOver216 HAnomaly.qL
    ; cubicNumeratorOver216IsCanonical = refl
    ; gravitationalNumeratorOver6 =
        HAnomaly.gravitationalContributionNumeratorOver6 HAnomaly.qL
    ; gravitationalNumeratorOver6IsCanonical = refl
    ; rowIsFiniteOneGenerationOnly = true
    ; rowIsFiniteOneGenerationOnlyIsTrue = refl
    }

uCFiniteSMHyperchargeMultipletRow :
  FiniteSMHyperchargeMultipletRow
uCFiniteSMHyperchargeMultipletRow =
  record
    { multiplet = finiteUC
    ; sourceMultiplet = HAnomaly.uC
    ; sourceMultipletIsCanonical = refl
    ; displayLabel = "u^c"
    ; displayLabelIsCanonical = refl
    ; signedSixths = HAnomaly.sixthMinusFour
    ; signedSixthsAreCanonical = refl
    ; weylMultiplicity = 3
    ; weylMultiplicityIsCanonical = refl
    ; cubicNumeratorOver216 = HAnomaly.cubicContributionNumeratorOver216 HAnomaly.uC
    ; cubicNumeratorOver216IsCanonical = refl
    ; gravitationalNumeratorOver6 =
        HAnomaly.gravitationalContributionNumeratorOver6 HAnomaly.uC
    ; gravitationalNumeratorOver6IsCanonical = refl
    ; rowIsFiniteOneGenerationOnly = true
    ; rowIsFiniteOneGenerationOnlyIsTrue = refl
    }

dCFiniteSMHyperchargeMultipletRow :
  FiniteSMHyperchargeMultipletRow
dCFiniteSMHyperchargeMultipletRow =
  record
    { multiplet = finiteDC
    ; sourceMultiplet = HAnomaly.dC
    ; sourceMultipletIsCanonical = refl
    ; displayLabel = "d^c"
    ; displayLabelIsCanonical = refl
    ; signedSixths = HAnomaly.sixthPlusTwo
    ; signedSixthsAreCanonical = refl
    ; weylMultiplicity = 3
    ; weylMultiplicityIsCanonical = refl
    ; cubicNumeratorOver216 = HAnomaly.cubicContributionNumeratorOver216 HAnomaly.dC
    ; cubicNumeratorOver216IsCanonical = refl
    ; gravitationalNumeratorOver6 =
        HAnomaly.gravitationalContributionNumeratorOver6 HAnomaly.dC
    ; gravitationalNumeratorOver6IsCanonical = refl
    ; rowIsFiniteOneGenerationOnly = true
    ; rowIsFiniteOneGenerationOnlyIsTrue = refl
    }

lLFiniteSMHyperchargeMultipletRow :
  FiniteSMHyperchargeMultipletRow
lLFiniteSMHyperchargeMultipletRow =
  record
    { multiplet = finiteLL
    ; sourceMultiplet = HAnomaly.leptonL
    ; sourceMultipletIsCanonical = refl
    ; displayLabel = "L_L"
    ; displayLabelIsCanonical = refl
    ; signedSixths = HAnomaly.sixthMinusThree
    ; signedSixthsAreCanonical = refl
    ; weylMultiplicity = 2
    ; weylMultiplicityIsCanonical = refl
    ; cubicNumeratorOver216 =
        HAnomaly.cubicContributionNumeratorOver216 HAnomaly.leptonL
    ; cubicNumeratorOver216IsCanonical = refl
    ; gravitationalNumeratorOver6 =
        HAnomaly.gravitationalContributionNumeratorOver6 HAnomaly.leptonL
    ; gravitationalNumeratorOver6IsCanonical = refl
    ; rowIsFiniteOneGenerationOnly = true
    ; rowIsFiniteOneGenerationOnlyIsTrue = refl
    }

eCFiniteSMHyperchargeMultipletRow :
  FiniteSMHyperchargeMultipletRow
eCFiniteSMHyperchargeMultipletRow =
  record
    { multiplet = finiteEC
    ; sourceMultiplet = HAnomaly.eC
    ; sourceMultipletIsCanonical = refl
    ; displayLabel = "e^c"
    ; displayLabelIsCanonical = refl
    ; signedSixths = HAnomaly.sixthPlusSix
    ; signedSixthsAreCanonical = refl
    ; weylMultiplicity = 1
    ; weylMultiplicityIsCanonical = refl
    ; cubicNumeratorOver216 = HAnomaly.cubicContributionNumeratorOver216 HAnomaly.eC
    ; cubicNumeratorOver216IsCanonical = refl
    ; gravitationalNumeratorOver6 =
        HAnomaly.gravitationalContributionNumeratorOver6 HAnomaly.eC
    ; gravitationalNumeratorOver6IsCanonical = refl
    ; rowIsFiniteOneGenerationOnly = true
    ; rowIsFiniteOneGenerationOnlyIsTrue = refl
    }

nuCFiniteSMHyperchargeMultipletRow :
  FiniteSMHyperchargeMultipletRow
nuCFiniteSMHyperchargeMultipletRow =
  record
    { multiplet = finiteNuC
    ; sourceMultiplet = HAnomaly.nuC
    ; sourceMultipletIsCanonical = refl
    ; displayLabel = "nu^c"
    ; displayLabelIsCanonical = refl
    ; signedSixths = HAnomaly.sixthZero
    ; signedSixthsAreCanonical = refl
    ; weylMultiplicity = 1
    ; weylMultiplicityIsCanonical = refl
    ; cubicNumeratorOver216 =
        HAnomaly.cubicContributionNumeratorOver216 HAnomaly.nuC
    ; cubicNumeratorOver216IsCanonical = refl
    ; gravitationalNumeratorOver6 =
        HAnomaly.gravitationalContributionNumeratorOver6 HAnomaly.nuC
    ; gravitationalNumeratorOver6IsCanonical = refl
    ; rowIsFiniteOneGenerationOnly = true
    ; rowIsFiniteOneGenerationOnlyIsTrue = refl
    }

canonicalFiniteSMHyperchargeMultipletRows :
  List FiniteSMHyperchargeMultipletRow
canonicalFiniteSMHyperchargeMultipletRows =
  qLFiniteSMHyperchargeMultipletRow
  ∷ uCFiniteSMHyperchargeMultipletRow
  ∷ dCFiniteSMHyperchargeMultipletRow
  ∷ lLFiniteSMHyperchargeMultipletRow
  ∷ eCFiniteSMHyperchargeMultipletRow
  ∷ nuCFiniteSMHyperchargeMultipletRow
  ∷ []

data FiniteSMAnomalyBalanceKind : Set where
  balanceU1YCubed :
    FiniteSMAnomalyBalanceKind

  balanceGravitationalU1Y :
    FiniteSMAnomalyBalanceKind

  balanceSU2SquaredU1Y :
    FiniteSMAnomalyBalanceKind

  balanceSU3SquaredU1Y :
    FiniteSMAnomalyBalanceKind

balanceLabel :
  FiniteSMAnomalyBalanceKind →
  String
balanceLabel balanceU1YCubed =
  "U1Y^3"
balanceLabel balanceGravitationalU1Y =
  "grav^2-U1Y"
balanceLabel balanceSU2SquaredU1Y =
  "SU2^2-U1Y"
balanceLabel balanceSU3SquaredU1Y =
  "SU3^2-U1Y"

balanceDenominator :
  FiniteSMAnomalyBalanceKind →
  Nat
balanceDenominator balanceU1YCubed =
  216
balanceDenominator balanceGravitationalU1Y =
  6
balanceDenominator balanceSU2SquaredU1Y =
  6
balanceDenominator balanceSU3SquaredU1Y =
  6

balanceNumerator :
  FiniteSMAnomalyBalanceKind →
  ℤ
balanceNumerator balanceU1YCubed =
  HAnomaly.cubicAnomalyNumeratorOver216
balanceNumerator balanceGravitationalU1Y =
  HAnomaly.gravitationalAnomalyNumeratorOver6
balanceNumerator balanceSU2SquaredU1Y =
  HAnomaly.su2MixedAnomalyNumeratorOver6
balanceNumerator balanceSU3SquaredU1Y =
  HAnomaly.su3MixedAnomalyNumeratorOver6

record FiniteSMAnomalyBalanceRow : Set where
  field
    balanceKind :
      FiniteSMAnomalyBalanceKind

    label :
      String

    labelIsCanonical :
      label ≡ balanceLabel balanceKind

    commonDenominator :
      Nat

    commonDenominatorIsCanonical :
      commonDenominator ≡ balanceDenominator balanceKind

    numerator :
      ℤ

    numeratorIsCanonical :
      numerator ≡ balanceNumerator balanceKind

    numeratorIsZero :
      numerator ≡ 0ℤ

    inheritedFromFiniteHyperchargeLedger :
      Bool

    inheritedFromFiniteHyperchargeLedgerIsTrue :
      inheritedFromFiniteHyperchargeLedger ≡ true

    promotedAsPhysicalSMTheorem :
      Bool

    promotedAsPhysicalSMTheoremIsFalse :
      promotedAsPhysicalSMTheorem ≡ false

open FiniteSMAnomalyBalanceRow public

u1YCubedFiniteSMAnomalyBalanceRow :
  FiniteSMAnomalyBalanceRow
u1YCubedFiniteSMAnomalyBalanceRow =
  record
    { balanceKind = balanceU1YCubed
    ; label = "U1Y^3"
    ; labelIsCanonical = refl
    ; commonDenominator = 216
    ; commonDenominatorIsCanonical = refl
    ; numerator = HAnomaly.cubicAnomalyNumeratorOver216
    ; numeratorIsCanonical = refl
    ; numeratorIsZero = refl
    ; inheritedFromFiniteHyperchargeLedger = true
    ; inheritedFromFiniteHyperchargeLedgerIsTrue = refl
    ; promotedAsPhysicalSMTheorem = false
    ; promotedAsPhysicalSMTheoremIsFalse = refl
    }

gravitationalFiniteSMAnomalyBalanceRow :
  FiniteSMAnomalyBalanceRow
gravitationalFiniteSMAnomalyBalanceRow =
  record
    { balanceKind = balanceGravitationalU1Y
    ; label = "grav^2-U1Y"
    ; labelIsCanonical = refl
    ; commonDenominator = 6
    ; commonDenominatorIsCanonical = refl
    ; numerator = HAnomaly.gravitationalAnomalyNumeratorOver6
    ; numeratorIsCanonical = refl
    ; numeratorIsZero = refl
    ; inheritedFromFiniteHyperchargeLedger = true
    ; inheritedFromFiniteHyperchargeLedgerIsTrue = refl
    ; promotedAsPhysicalSMTheorem = false
    ; promotedAsPhysicalSMTheoremIsFalse = refl
    }

su2FiniteSMAnomalyBalanceRow :
  FiniteSMAnomalyBalanceRow
su2FiniteSMAnomalyBalanceRow =
  record
    { balanceKind = balanceSU2SquaredU1Y
    ; label = "SU2^2-U1Y"
    ; labelIsCanonical = refl
    ; commonDenominator = 6
    ; commonDenominatorIsCanonical = refl
    ; numerator = HAnomaly.su2MixedAnomalyNumeratorOver6
    ; numeratorIsCanonical = refl
    ; numeratorIsZero = refl
    ; inheritedFromFiniteHyperchargeLedger = true
    ; inheritedFromFiniteHyperchargeLedgerIsTrue = refl
    ; promotedAsPhysicalSMTheorem = false
    ; promotedAsPhysicalSMTheoremIsFalse = refl
    }

su3FiniteSMAnomalyBalanceRow :
  FiniteSMAnomalyBalanceRow
su3FiniteSMAnomalyBalanceRow =
  record
    { balanceKind = balanceSU3SquaredU1Y
    ; label = "SU3^2-U1Y"
    ; labelIsCanonical = refl
    ; commonDenominator = 6
    ; commonDenominatorIsCanonical = refl
    ; numerator = HAnomaly.su3MixedAnomalyNumeratorOver6
    ; numeratorIsCanonical = refl
    ; numeratorIsZero = refl
    ; inheritedFromFiniteHyperchargeLedger = true
    ; inheritedFromFiniteHyperchargeLedgerIsTrue = refl
    ; promotedAsPhysicalSMTheorem = false
    ; promotedAsPhysicalSMTheoremIsFalse = refl
    }

canonicalFiniteSMAnomalyBalanceRows :
  List FiniteSMAnomalyBalanceRow
canonicalFiniteSMAnomalyBalanceRows =
  u1YCubedFiniteSMAnomalyBalanceRow
  ∷ gravitationalFiniteSMAnomalyBalanceRow
  ∷ su2FiniteSMAnomalyBalanceRow
  ∷ su3FiniteSMAnomalyBalanceRow
  ∷ []

data FiniteSMBroadPromotionGuard : Set where
  continuousGaugeGroupGuard :
    FiniteSMBroadPromotionGuard

  physicalIrrepTheoremGuard :
    FiniteSMBroadPromotionGuard

  pdgAuthorityGuard :
    FiniteSMBroadPromotionGuard

  yukawaCKMPMNSGuard :
    FiniteSMBroadPromotionGuard

  empiricalObservableGuard :
    FiniteSMBroadPromotionGuard

  exactDHRSMGuard :
    FiniteSMBroadPromotionGuard

  terminalUnificationGuard :
    FiniteSMBroadPromotionGuard

canonicalFiniteSMBroadPromotionGuards :
  List FiniteSMBroadPromotionGuard
canonicalFiniteSMBroadPromotionGuards =
  continuousGaugeGroupGuard
  ∷ physicalIrrepTheoremGuard
  ∷ pdgAuthorityGuard
  ∷ yukawaCKMPMNSGuard
  ∷ empiricalObservableGuard
  ∷ exactDHRSMGuard
  ∷ terminalUnificationGuard
  ∷ []

listCount :
  {A : Set} →
  List A →
  Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

record FiniteSMAnomalyHyperchargeCheckReceipt : Setω where
  field
    finiteRepresentationNarrowingReceipt :
      Narrow.StandardModelFiniteRepresentationNarrowingReceipt

    finiteRepresentationNarrowingReceiptSelectedCanonical :
      Bool

    finiteRepresentationNarrowingReceiptSelectedCanonicalIsTrue :
      finiteRepresentationNarrowingReceiptSelectedCanonical ≡ true

    hyperchargeNormalisationAnomalyReceipt :
      HAnomaly.HyperchargeNormalisationAnomalyReceipt

    hyperchargeLedgerIsCanonical :
      HAnomaly.hyperchargeLedger hyperchargeNormalisationAnomalyReceipt
      ≡
      HAnomaly.canonicalHyperchargeLedger

    anomalyVerificationReceipt :
      Verify.AnomalyCancellationVerificationReceipt

    anomalyVerificationReceiptSelectedCanonical :
      Bool

    anomalyVerificationReceiptSelectedCanonicalIsTrue :
      anomalyVerificationReceiptSelectedCanonical ≡ true

    physicalChargeAssignmentTableReceipt :
      U1YTable.U1YChargeAssignmentTableReceipt

    physicalChargeTableHasSixRows :
      U1YTable.physicalTable physicalChargeAssignmentTableReceipt
      ≡
      U1YTable.canonicalPhysicalHyperchargeTable

    physicalChargeTableTotalWeylCount :
      U1YTable.totalWeylCount physicalChargeAssignmentTableReceipt
      ≡
      48

    finiteHyperchargeMultipletRows :
      List FiniteSMHyperchargeMultipletRow

    finiteHyperchargeMultipletRowsAreCanonical :
      finiteHyperchargeMultipletRows
      ≡
      canonicalFiniteSMHyperchargeMultipletRows

    finiteHyperchargeMultipletRowCount :
      Nat

    finiteHyperchargeMultipletRowCountIsSix :
      finiteHyperchargeMultipletRowCount ≡ 6

    oneGenerationTargetCount :
      Nat

    oneGenerationTargetCountIsFive :
      oneGenerationTargetCount ≡ 5

    physicalHyperchargeTableRowCount :
      Nat

    physicalHyperchargeTableRowCountIsSix :
      physicalHyperchargeTableRowCount ≡ 6

    anomalyBalanceRows :
      List FiniteSMAnomalyBalanceRow

    anomalyBalanceRowsAreCanonical :
      anomalyBalanceRows ≡ canonicalFiniteSMAnomalyBalanceRows

    anomalyBalanceRowCount :
      Nat

    anomalyBalanceRowCountIsFour :
      anomalyBalanceRowCount ≡ 4

    anomalyNumeratorZeroCount :
      Nat

    anomalyNumeratorZeroCountIsFour :
      anomalyNumeratorZeroCount ≡ 4

    cubicNumeratorIsZero :
      HAnomaly.cubicNumerator hyperchargeNormalisationAnomalyReceipt ≡ 0ℤ

    gravitationalNumeratorIsZero :
      HAnomaly.gravitationalNumerator hyperchargeNormalisationAnomalyReceipt
      ≡
      0ℤ

    su2MixedNumeratorIsZero :
      HAnomaly.su2MixedNumerator hyperchargeNormalisationAnomalyReceipt
      ≡
      0ℤ

    su3MixedNumeratorIsZero :
      HAnomaly.su3MixedNumerator hyperchargeNormalisationAnomalyReceipt
      ≡
      0ℤ

    finiteAnomalyBalanceChecked :
      Bool

    finiteAnomalyBalanceCheckedIsTrue :
      finiteAnomalyBalanceChecked ≡ true

    finiteHyperchargeRowsChecked :
      Bool

    finiteHyperchargeRowsCheckedIsTrue :
      finiteHyperchargeRowsChecked ≡ true

    broadPromotionGuards :
      List FiniteSMBroadPromotionGuard

    broadPromotionGuardsAreCanonical :
      broadPromotionGuards ≡ canonicalFiniteSMBroadPromotionGuards

    broadPromotionGuardCount :
      Nat

    broadPromotionGuardCountIsSeven :
      broadPromotionGuardCount ≡ 7

    continuousStandardModelPromoted :
      Bool

    continuousStandardModelPromotedIsFalse :
      continuousStandardModelPromoted ≡ false

    exactPhysicalIrrepPromoted :
      Bool

    exactPhysicalIrrepPromotedIsFalse :
      exactPhysicalIrrepPromoted ≡ false

    broadStandardModelPromoted :
      Bool

    broadStandardModelPromotedIsFalse :
      broadStandardModelPromoted ≡ false

    terminalUnificationPromoted :
      Bool

    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

    receiptBoundary :
      List String

open FiniteSMAnomalyHyperchargeCheckReceipt public

canonicalFiniteSMAnomalyHyperchargeCheckReceipt :
  FiniteSMAnomalyHyperchargeCheckReceipt
canonicalFiniteSMAnomalyHyperchargeCheckReceipt =
  record
    { finiteRepresentationNarrowingReceipt =
        Narrow.canonicalStandardModelFiniteRepresentationNarrowingReceipt
    ; finiteRepresentationNarrowingReceiptSelectedCanonical =
        true
    ; finiteRepresentationNarrowingReceiptSelectedCanonicalIsTrue =
        refl
    ; hyperchargeNormalisationAnomalyReceipt =
        HAnomaly.canonicalHyperchargeNormalisationAnomalyReceipt
    ; hyperchargeLedgerIsCanonical =
        refl
    ; anomalyVerificationReceipt =
        Verify.canonicalAnomalyCancellationVerificationReceipt
    ; anomalyVerificationReceiptSelectedCanonical =
        true
    ; anomalyVerificationReceiptSelectedCanonicalIsTrue =
        refl
    ; physicalChargeAssignmentTableReceipt =
        U1YTable.canonicalU1YChargeAssignmentTableReceipt
    ; physicalChargeTableHasSixRows =
        refl
    ; physicalChargeTableTotalWeylCount =
        refl
    ; finiteHyperchargeMultipletRows =
        canonicalFiniteSMHyperchargeMultipletRows
    ; finiteHyperchargeMultipletRowsAreCanonical =
        refl
    ; finiteHyperchargeMultipletRowCount =
        listCount canonicalFiniteSMHyperchargeMultipletRows
    ; finiteHyperchargeMultipletRowCountIsSix =
        refl
    ; oneGenerationTargetCount =
        Narrow.oneGenerationRepresentationTargetCount
          Narrow.canonicalStandardModelFiniteRepresentationNarrowingReceipt
    ; oneGenerationTargetCountIsFive =
        refl
    ; physicalHyperchargeTableRowCount =
        listCount U1YTable.canonicalPhysicalHyperchargeTable
    ; physicalHyperchargeTableRowCountIsSix =
        refl
    ; anomalyBalanceRows =
        canonicalFiniteSMAnomalyBalanceRows
    ; anomalyBalanceRowsAreCanonical =
        refl
    ; anomalyBalanceRowCount =
        listCount canonicalFiniteSMAnomalyBalanceRows
    ; anomalyBalanceRowCountIsFour =
        refl
    ; anomalyNumeratorZeroCount =
        4
    ; anomalyNumeratorZeroCountIsFour =
        refl
    ; cubicNumeratorIsZero =
        refl
    ; gravitationalNumeratorIsZero =
        refl
    ; su2MixedNumeratorIsZero =
        refl
    ; su3MixedNumeratorIsZero =
        refl
    ; finiteAnomalyBalanceChecked =
        true
    ; finiteAnomalyBalanceCheckedIsTrue =
        refl
    ; finiteHyperchargeRowsChecked =
        true
    ; finiteHyperchargeRowsCheckedIsTrue =
        refl
    ; broadPromotionGuards =
        canonicalFiniteSMBroadPromotionGuards
    ; broadPromotionGuardsAreCanonical =
        refl
    ; broadPromotionGuardCount =
        listCount canonicalFiniteSMBroadPromotionGuards
    ; broadPromotionGuardCountIsSeven =
        refl
    ; continuousStandardModelPromoted =
        false
    ; continuousStandardModelPromotedIsFalse =
        refl
    ; exactPhysicalIrrepPromoted =
        false
    ; exactPhysicalIrrepPromotedIsFalse =
        refl
    ; broadStandardModelPromoted =
        false
    ; broadStandardModelPromotedIsFalse =
        refl
    ; terminalUnificationPromoted =
        false
    ; terminalUnificationPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Finite check: six all-left-handed Weyl multiplet rows are tied to signed-sixth hypercharge data"
        ∷ "Finite check: four anomaly numerators are zero using the canonical hypercharge anomaly receipt"
        ∷ "Finite check consumes the five-row one-generation representation target narrowing but does not promote physical irreps"
        ∷ "Continuous gauge groups, empirical authority, Yukawa/CKM/PMNS data, exact DHR-SM, and terminal unification remain false"
        ∷ []
    }

finiteSMHyperchargeMultipletRowCountIsSix :
  finiteHyperchargeMultipletRowCount
    canonicalFiniteSMAnomalyHyperchargeCheckReceipt
  ≡
  6
finiteSMHyperchargeMultipletRowCountIsSix =
  refl

finiteSMAnomalyBalanceRowCountIsFour :
  anomalyBalanceRowCount canonicalFiniteSMAnomalyHyperchargeCheckReceipt
  ≡
  4
finiteSMAnomalyBalanceRowCountIsFour =
  refl

finiteSMAnomalyNumeratorZeroCountIsFour :
  anomalyNumeratorZeroCount canonicalFiniteSMAnomalyHyperchargeCheckReceipt
  ≡
  4
finiteSMAnomalyNumeratorZeroCountIsFour =
  refl

finiteSMCheckDoesNotPromoteBroadSM :
  broadStandardModelPromoted canonicalFiniteSMAnomalyHyperchargeCheckReceipt
  ≡
  false
finiteSMCheckDoesNotPromoteBroadSM =
  refl

finiteSMCheckDoesNotPromoteTerminalUnification :
  terminalUnificationPromoted canonicalFiniteSMAnomalyHyperchargeCheckReceipt
  ≡
  false
finiteSMCheckDoesNotPromoteTerminalUnification =
  refl
