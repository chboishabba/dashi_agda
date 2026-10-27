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
open import Data.Integer.Base using (0ℤ)

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

fortySevenUnitsOnlyCover235 : 47 * 5 ≡ 235
fortySevenUnitsOnlyCover235 = refl

fortyEightUnitsCover240 : 48 * 5 ≡ 240
fortyEightUnitsCover240 = refl

-- Already-paid source-side anomaly arithmetic is a CONDITIONED
-- inherited physical charge table, not a derivation of chiral 5D
-- quark representations from smooth S1 compactification.
inheritedSU3MixedAnomalyCancels :
  Anomaly.su3SquaredU1PerGenerationNumeratorOver6 ≡ 0ℤ
inheritedSU3MixedAnomalyCancels =
  Anomaly.anomalyVerificationSU3MixedZero

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


------------------------------------------------------------------------
-- 2026-10-24 strongest selected QED+QCD+SU3^3 finite BIDI collision.
--
-- Source-side numeric predicate attribution:
--   scripts/check_kk_light_qed_dirac_same_action.py
--   scripts/check_kk_e6_trinification_joint_radion_wilson.py
-- For the SELECTED one-loop spectra, both can be retuned to a
-- stationary positive-curvature RADION at theta_EM=0, but only the
-- QED-only toy has POSITIVE electromagnetic Wilson curvature.
--
-- These constructors label SOURCE-WRITTEN finite candidate outcomes;
-- they do not kernel-prove the continuum one-loop determinants.
------------------------------------------------------------------------

data RadionWilsonCandidate : Set where
  priorLightQEDOnly : RadionWilsonCandidate
  selectedQEDQCDWithTwoExtraMasslessSU3 : RadionWilsonCandidate

radionStationarityOnly : RadionWilsonCandidate → Bool
radionStationarityOnly priorLightQEDOnly = true
radionStationarityOnly selectedQEDQCDWithTwoExtraMasslessSU3 = true

emWilsonLocalStability : RadionWilsonCandidate → Bool
emWilsonLocalStability priorLightQEDOnly = true
emWilsonLocalStability selectedQEDQCDWithTwoExtraMasslessSU3 = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

radionPassCannotDetermineWilsonPass :
  Transport.ClaimNonTransportWitness
    radionStationarityOnly emWilsonLocalStability
radionPassCannotDetermineWilsonPass =
  Descent.consumerNonDescentWitness
    priorLightQEDOnly selectedQEDQCDWithTwoExtraMasslessSU3
    refl trueNotFalse

noSteelmanWilsonPromotionFromRadionOnly :
  Transport.ClaimTransport
    radionStationarityOnly emWilsonLocalStability → ⊥
noSteelmanWilsonPromotionFromRadionOnly =
  Transport.claimNonTransportWitnessBlocksTransport
    radionPassCannotDetermineWilsonPass

repairMustTrackWilsonHessian :
  (refine : RadionWilsonCandidate → Bool) →
  Repair.RefinementRepairs
    radionStationarityOnly refine emWilsonLocalStability →
  refine priorLightQEDOnly
    ≡ refine selectedQEDQCDWithTwoExtraMasslessSU3 → ⊥
repairMustTrackWilsonHessian refine adequate same =
  Repair.refinementRepairSeparatesWitness
    radionPassCannotDetermineWilsonPass adequate same


------------------------------------------------------------------------
-- LATER global holonomy cut: local Hessian ≠ chosen Wilson global min.
-- These truth labels are SELECTED PYTHON CONSUMER TEST outcomes, not
-- Agda proofs of a continuum one-loop determinant.
--
-- The paired six-flavour QCD multiplet has positive radion and local
-- EM/SU3 Wilson Hessians but a strictly LOWER SU3 centre phase;
-- adding TWO split heavy vectorlike colour fundamental hyper-like
-- multiplets (for 8 total fundamental Dirac flavours) repairs the
-- fixed-radius theta_EM=0 global colour phase in a Fourier tail proof.
--
-- Original SUSY field-content authority is EXTERNAL; the local
-- WittenIndexSUSYBoundarySurface remains targets-only, and neither
-- these arithmetic identities nor finite witnesses claim supercharge,
-- parity anomaly, soft breaking action or experimental validation.
------------------------------------------------------------------------

data SelectedQCDHolonomyCandidate : Set where
  sixPairedQCDFlavours : SelectedQCDHolonomyCandidate
  eightFlavoursWithTwoSplitExotics : SelectedQCDHolonomyCandidate

localRadionEMAndColourHessianPositive :
  SelectedQCDHolonomyCandidate → Bool
localRadionEMAndColourHessianPositive sixPairedQCDFlavours = true
localRadionEMAndColourHessianPositive eightFlavoursWithTwoSplitExotics = true

identityColourHolonomyGlobalAtChosenRadiusAndEMZero :
  SelectedQCDHolonomyCandidate → Bool
identityColourHolonomyGlobalAtChosenRadiusAndEMZero
  sixPairedQCDFlavours = false
identityColourHolonomyGlobalAtChosenRadiusAndEMZero
  eightFlavoursWithTwoSplitExotics = true

localHessianDoesNotDetermineGlobalColourVacuum :
  Transport.ClaimNonTransportWitness
    localRadionEMAndColourHessianPositive
    identityColourHolonomyGlobalAtChosenRadiusAndEMZero
localHessianDoesNotDetermineGlobalColourVacuum =
  Descent.consumerNonDescentWitness
    sixPairedQCDFlavours eightFlavoursWithTwoSplitExotics
    refl trueNotFalse

noGlobalHolonomyPromotionFromLocalHessian :
  Transport.ClaimTransport
    localRadionEMAndColourHessianPositive
    identityColourHolonomyGlobalAtChosenRadiusAndEMZero → ⊥
noGlobalHolonomyPromotionFromLocalHessian =
  Transport.claimNonTransportWitnessBlocksTransport
    localHessianDoesNotDetermineGlobalColourVacuum

fiveDimensionalVectorMultipletFreeCount : 3 + 1 ≡ 4
fiveDimensionalVectorMultipletFreeCount = refl

fiveDimensionalHypermultipletFreeCount : 2 * 2 ≡ 4
fiveDimensionalHypermultipletFreeCount = refl

eightFundamentalFlavoursEvenNumber : 6 + 2 ≡ 8
eightFundamentalFlavoursEvenNumber = refl

eightFundamentalFlavoursPairedScalarUnits : 8 * 3 * 4 ≡ 96
eightFundamentalFlavoursPairedScalarUnits = refl

-- Neither counting identity constructs 5D supersymmetry nor determines
-- the mixed SU3/U1 Chern-Simons quantization or chiral SM zero modes.
