{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.Zhang2025EMGravityQuantitativeSourceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import DASHI.Physics.ExoticGravity.Zhang2025EMGravitySourceClaimExact as Zhang

------------------------------------------------------------------------
-- Published NUMBERS are not all estimators of the same physical observable.
-- A 2024 vacuum-balance measurement is not a Zhang 2025 ON/OFF experiment.
------------------------------------------------------------------------

data SourceStudy : Set where
  zhangXu2025Toroid : SourceStudy
  zhangPatent2025Sphere : SourceStudy
  pais2019GravitationalWaveProposal : SourceStudy
  tajmar2024SteadyVacuumBalance : SourceStudy
  tajmar2026ThreeAmpereDCToroid : SourceStudy

data EvidenceKind : Set where
  reportedNominalInput : EvidenceKind
  assumedWaveformPrediction : EvidenceKind
  authorNoiseScreening : EvidenceKind
  instrumentalResolution : EvidenceKind
  independentlyMeasuredPairedOutcome : EvidenceKind

data PhysicalConsumer : Set where
  experimentSourceMetadata : PhysicalConsumer
  ordinaryEMForceComparator : PhysicalConsumer
  independentRegimeSensitivity : PhysicalConsumer
  sameApparatusAnomaly : PhysicalConsumer
  gravitationalFreeFallMetric : PhysicalConsumer
  propagatingTTStrain : PhysicalConsumer

data AdmissibleNonPromotingUse :
  SourceStudy → EvidenceKind → PhysicalConsumer → Set where
  toroidNominalSource :
    AdmissibleNonPromotingUse
      zhangXu2025Toroid reportedNominalInput experimentSourceMetadata
  toroidAssumedEM :
    AdmissibleNonPromotingUse
      zhangXu2025Toroid assumedWaveformPrediction ordinaryEMForceComparator
  patentNominalSource :
    AdmissibleNonPromotingUse
      zhangPatent2025Sphere reportedNominalInput experimentSourceMetadata
  independent2024Sensitivity :
    AdmissibleNonPromotingUse
      tajmar2024SteadyVacuumBalance authorNoiseScreening
      independentRegimeSensitivity
  independent2026Resolution :
    AdmissibleNonPromotingUse
      tajmar2026ThreeAmpereDCToroid instrumentalResolution
      independentRegimeSensitivity
  paisProposedSource :
    AdmissibleNonPromotingUse
      pais2019GravitationalWaveProposal reportedNominalInput
      experimentSourceMetadata

-- In particular, there is no constructor bridging a published nominal input
-- or a different experiment into a same-apparatus anomaly/metric/TT receipt.
noZhangNominalToSameApparatusAnomaly :
  AdmissibleNonPromotingUse
    zhangXu2025Toroid reportedNominalInput sameApparatusAnomaly →
  Zhang.Contradiction
noZhangNominalToSameApparatusAnomaly ()

noTajmar2024SensitivityToZhangMetric :
  AdmissibleNonPromotingUse
    tajmar2024SteadyVacuumBalance authorNoiseScreening
    gravitationalFreeFallMetric →
  Zhang.Contradiction
noTajmar2024SensitivityToZhangMetric ()

noTajmar2026ResolutionToZhangAnomaly :
  AdmissibleNonPromotingUse
    tajmar2026ThreeAmpereDCToroid instrumentalResolution
    sameApparatusAnomaly →
  Zhang.Contradiction
noTajmar2026ResolutionToZhangAnomaly ()

noPatentPowerToPaisTT :
  AdmissibleNonPromotingUse
    zhangPatent2025Sphere reportedNominalInput propagatingTTStrain →
  Zhang.Contradiction
noPatentPowerToPaisTT ()

------------------------------------------------------------------------
-- Exact masses from Xinjiang Steel 2025 Table / experimental paragraph.
-- The range is useful for designing a universal-acceleration discriminator.
-- It does NOT provide sample accelerations or an observed force interval.
------------------------------------------------------------------------

data Sample : Set where
  epoxy paper ceramic leaf aluminium porkSkin : Sample

massMg : Sample → Nat
massMg epoxy = 1500
massMg paper = 50
massMg ceramic = 1500
massMg leaf = 125
massMg aluminium = 2000
massMg porkSkin = 500

reportedFieldLowDeciTesla : Nat
reportedFieldLowDeciTesla = 1

reportedFieldHighDeciTesla : Nat
reportedFieldHighDeciTesla = 5

reportedExcitationHz : Nat
reportedExcitationHz = 50

aluminiumMassTwoGrams :
  massMg aluminium ≡ 2000
aluminiumMassTwoGrams = refl

paperMassFiftyMilligrams :
  massMg paper ≡ 50
paperMassFiftyMilligrams = refl

data HasCalibratedAcceleration : Sample → Set where

noPaperAccelerationFromNominalMass :
  HasCalibratedAcceleration paper → Zhang.Contradiction
noPaperAccelerationFromNominalMass ()

noAluminiumAccelerationFromNominalMass :
  HasCalibratedAcceleration aluminium → Zhang.Contradiction
noAluminiumAccelerationFromNominalMass ()

------------------------------------------------------------------------
-- Scoped evidence ledger: no 95% interval can be deduced without a defined
-- estimator, raw outcome distribution or independent-paired measurement law.
------------------------------------------------------------------------

record PublishedQuantitativeEvidenceBoundary : Set where
  constructor published-quantitative-evidence-boundary
  field
    originalZhangAcceleration95CIAvailable : Bool
    2024ThreeSigmaScreenIsFormal95CI : Bool
    2026PointOneMgIsFormal95CI : Bool
    independent2024IsSameZhangApparatus : Bool
    conditionalSinusoidalBderivativeIsMeasured : Bool
    sourceReportedSampleMassesAreAvailable : Bool
    independentNullCanConstrainItsOwnRegime : Bool

canonicalPublishedQuantitativeEvidenceBoundary :
  PublishedQuantitativeEvidenceBoundary
canonicalPublishedQuantitativeEvidenceBoundary =
  published-quantitative-evidence-boundary
    false false false false false true true
