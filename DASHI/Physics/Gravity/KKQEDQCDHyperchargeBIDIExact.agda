module DASHI.Physics.Gravity.KKQEDQCDHyperchargeBIDIExact where

------------------------------------------------------------------------
-- SAME-CONSUMER HYPERCHARGE NORMALISATION: QED x QCD x HIGGS
--
-- Canonical U1YChargeAssignmentTableReceipt stores Y(Q_L)=1/6,
-- Y(L_L)=-1/2, Y(e_R)=-1 and so Q_EM=T3+Y.
--
-- Old Higgs boundary Q_EM=T3+Y/2 used doubled hypercharge without
-- actually doubling this canonical table. This file prevents regression
-- and exhibits the explicit wrong-charge witness.
--
-- Classical Standard Model prior art; not a new EW unification theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer.Base as Z using (ℤ; +_; -[1+_]; _+_)

import DASHI.Physics.Closure.U1YChargeAssignmentTableReceipt as U1Y
import DASHI.Physics.Closure.HiggsElectroweakBoundary as Higgs
import DASHI.Physics.Closure.AnomalyCancellationVerificationReceipt as Anomaly

-- The repository's charged-table sixths are Y itself, NOT 2*Y.
-- Use the all-physical right-handed table here, not the conjugate
-- Weyl anomaly table (where right-handed signs reverse).

halfPlusInSixths : ℤ
halfPlusInSixths = + 3

halfMinusInSixths : ℤ
halfMinusInSixths = -[1+ 2 ]

upChargeInSixths : ℤ
upChargeInSixths =
  Z._+_ halfPlusInSixths (U1Y.physicalSignedSixths U1Y.qL)

downChargeInSixths : ℤ
downChargeInSixths =
  Z._+_ halfMinusInSixths (U1Y.physicalSignedSixths U1Y.qL)

electronChargeInSixths : ℤ
electronChargeInSixths =
  Z._+_ halfMinusInSixths
    (U1Y.physicalSignedSixths U1Y.leptonL)

neutrinoChargeInSixths : ℤ
neutrinoChargeInSixths =
  Z._+_ halfPlusInSixths
    (U1Y.physicalSignedSixths U1Y.leptonL)

rightUpChargeInSixths : ℤ
rightUpChargeInSixths = U1Y.physicalSignedSixths U1Y.uR

rightDownChargeInSixths : ℤ
rightDownChargeInSixths = U1Y.physicalSignedSixths U1Y.dR

rightElectronChargeInSixths : ℤ
rightElectronChargeInSixths = U1Y.physicalSignedSixths U1Y.eR

upChargeExactlyTwoThirds : upChargeInSixths ≡ + 4
upChargeExactlyTwoThirds = refl

downChargeExactlyMinusThird : downChargeInSixths ≡ -[1+ 1 ]
downChargeExactlyMinusThird = refl

electronChargeExactlyMinusOne :
  electronChargeInSixths ≡ -[1+ 5 ]
electronChargeExactlyMinusOne = refl

neutrinoChargeExactlyZero : neutrinoChargeInSixths ≡ + 0
neutrinoChargeExactlyZero = refl

rightAndLeftUpChargeMatch :
  upChargeInSixths ≡ rightUpChargeInSixths
rightAndLeftUpChargeMatch = refl

rightAndLeftDownChargeMatch :
  downChargeInSixths ≡ rightDownChargeInSixths
rightAndLeftDownChargeMatch = refl

rightAndLeftElectronChargeMatch :
  electronChargeInSixths ≡ rightElectronChargeInSixths
rightAndLeftElectronChargeMatch = refl

-- Wrong original convention, without doubling the source table:
-- up = +1/2+(1/6)/2 = 7/12, desired up = 8/12.
legacyUpChargeNumeratorInTwelfths : ℤ
legacyUpChargeNumeratorInTwelfths =
  Z._+_ (+ 6) (U1Y.physicalSignedSixths U1Y.qL)

desiredUpChargeNumeratorInTwelfths : ℤ
desiredUpChargeNumeratorInTwelfths = + 8

wrongNormalisationChangesPhysicalUpCharge :
  legacyUpChargeNumeratorInTwelfths
  ≡ desiredUpChargeNumeratorInTwelfths → ⊥
wrongNormalisationChangesPhysicalUpCharge ()

-- Owning Higgs boundary NOW uses source-table convention.
higgsAndHyperchargeNormalisationAgree :
  Higgs.emGeneratorLabel Higgs.canonicalHiggsElectroweakBoundaryReceipt
    ≡ "Q_EM = T3 + Y"
higgsAndHyperchargeNormalisationAgree = refl

-- Reuse rather than regenerate anomaly equations; cancellation of
-- tabulated Weyl charges does not derive the corresponding 5D fields.
conditionalAnomalyReceiptStillNoFullSM :
  Anomaly.exactStandardModelPromoted
    Anomaly.canonicalAnomalyCancellationVerificationReceipt
    ≡ false
conditionalAnomalyReceiptStillNoFullSM =
  Anomaly.anomalyVerificationStandardModelPromotionFalse
