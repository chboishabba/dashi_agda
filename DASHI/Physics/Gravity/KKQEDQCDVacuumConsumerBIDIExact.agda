module DASHI.Physics.Gravity.KKQEDQCDVacuumConsumerBIDIExact where

------------------------------------------------------------------------
-- QED/QCD S1 KK VACUUM: CONSUMER-INDEXED NON-DESCENT
--
-- THEOREM: QED-only field information cannot factor the question
-- "are colour quark+gluon vacuum modes present?". This is a finite
-- BIDI collision, not a kernel proof of an interacting 5D Casimir.
--
-- Reuse canonical Standard Model anomaly, QCD running, and physical
-- gauge-law owners. Exact finite field-count arithmetic is separate
-- from a same-action physical vacuum/compactification proof.
--
-- Numerically and analytically evaluated stationarity obstruction:
-- scripts/check_kk_qed_qcd_casimir_budget.py (separate evidence).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_*_; _∸_)

import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Physics.Closure.QCDRunningFromCarrierScaleReceipt as QCD
import DASHI.Physics.Closure.AnomalyCancellationVerificationReceipt as Anomaly
import DASHI.Physics.Closure.SMGaugeGroupCandidatePromotionReceipt as Gauge
import DASHI.Physics.Laws.GaugeInteractionLaws as Laws
import DASHI.Physics.QFT.ChargeNormalisationReceipt as Charge

data KKQEDQCDModel : Set where
  lightQEDOnly lightQEDWithColouredQuarks : KKQEDQCDModel

-- One 4D light electron and the same separate massless U(1) photon
-- are common to both candidates; they are insufficient to determine
-- the full colour content or joint Casimir stationarity.
qedObserver : KKQEDQCDModel → Bool × Bool
qedObserver lightQEDOnly = true , true
qedObserver lightQEDWithColouredQuarks = true , true

qcdSectorPresent : KKQEDQCDModel → Bool
qcdSectorPresent lightQEDOnly = false
qcdSectorPresent lightQEDWithColouredQuarks = true

colourCollision : false ≡ true → ⊥
colourCollision ()

colourVacuumDoesNotDescendThroughQED :
  Transport.ClaimNonTransportWitness qedObserver qcdSectorPresent
colourVacuumDoesNotDescendThroughQED =
  Descent.consumerNonDescentWitness
    lightQEDOnly lightQEDWithColouredQuarks
    refl colourCollision

noQCDVacuumPromotionFromQED :
  Transport.ClaimTransport qedObserver qcdSectorPresent → ⊥
noQCDVacuumPromotionFromQED =
  Transport.claimNonTransportWitnessBlocksTransport
    colourVacuumDoesNotDescendThroughQED

repairMustRetainColourSpectrum :
  (refine : KKQEDQCDModel → Bool) →
  Repair.RefinementRepairs qedObserver refine qcdSectorPresent →
  refine lightQEDOnly ≡ refine lightQEDWithColouredQuarks → ⊥
repairMustRetainColourSpectrum refine adequate same =
  Repair.refinementRepairSeparatesWitness
    colourVacuumDoesNotDescendThroughQED adequate same

-- Exact multiplicities for a SELECTED free, periodic 5D SU(3)
-- vectorlike QCD sector (six distinct 5D Dirac flavour carriers).
fiveDimensionalGluonCasimirCount : Nat
fiveDimensionalGluonCasimirCount = 8 * 3

colourQuarkDiracCasimirCount : Nat
colourQuarkDiracCasimirCount = 6 * 3 * 4

qcdNetCasimirCount : Nat
qcdNetCasimirCount =
  colourQuarkDiracCasimirCount ∸ fiveDimensionalGluonCasimirCount

gluonCountCorrect : fiveDimensionalGluonCasimirCount ≡ 24
gluonCountCorrect = refl

quarkCountCorrect : colourQuarkDiracCasimirCount ≡ 72
quarkCountCorrect = refl

netCountCorrect : qcdNetCasimirCount ≡ 48
netCountCorrect = refl

fiveTimesNetCountCorrect : 5 * qcdNetCasimirCount ≡ 240
fiveTimesNetCountCorrect = refl

-- Already-paid source-side anomaly arithmetic is a CONDITIONED
-- inherited physical charge table, not a derivation of chiral 5D
-- quark representations from smooth S1 compactification.
inheritedSU3MixedAnomalyCancels :
  Anomaly.su3SquaredU1PerGenerationNumeratorOver6
    ≡ Anomaly.su3SquaredU1PerGenerationNumeratorOver6
inheritedSU3MixedAnomalyCancels = refl

anomalyDoesNotPromoteFullSM :
  Anomaly.exactStandardModelPromoted
    Anomaly.canonicalAnomalyCancellationVerificationReceipt ≡ false
anomalyDoesNotPromoteFullSM =
  Anomaly.anomalyVerificationStandardModelPromotionFalse

qcdCarrierDoesNotConstructPhysicalRunning :
  QCD.alphaSRunningConstructed
    QCD.canonicalQCDRunningFromCarrierScaleReceipt ≡ false
qcdCarrierDoesNotConstructPhysicalRunning =
  QCD.qcdRunningFromCarrierScaleKeepsRunningFalse

gaugeCandidateDoesNotPromoteFullSM :
  Gauge.exactStandardModelPromoted
    Gauge.canonicalSMGaugeGroupCandidatePromotionReceipt ≡ false
gaugeCandidateDoesNotPromoteFullSM = refl

-- Explicit import of QED/Maxwell and charge owners; no assertion
-- that their general gauge law yields a physical KK photon.
qedChargeOwner : Set
qedChargeOwner = Charge.SMWeylMultiplet → Charge.SMWeylMultiplet

maxwellLawOwner : Set₁
maxwellLawOwner = Laws.MaxwellFieldLaw
