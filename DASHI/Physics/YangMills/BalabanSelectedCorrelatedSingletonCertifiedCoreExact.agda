{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonCertifiedCoreExact where

------------------------------------------------------------------------
-- NON-CIRCULAR CERTIFIED CORRELATED-SINGLETON PRODUCER
--
-- The historical CorrelatedSingletonExtractionData stores ownerBudgets inside
-- the extraction object.  Later interval-certificate adapters were intended to
-- produce those same budgets, but therefore still required a full extraction
-- before the certificate could be consumed.
--
-- This module separates the genuine selected-variation/KKT extraction core
-- from the four surviving owner budgets.  A certified rational interval
-- envelope then produces BOTH:
--
--   * the legacy exact CorrelatedOwnerBudgets used by the old extraction; and
--   * the slack-preserving owner bounds used by LiteralSelectedPlaquetteWitness.
--
-- Thus the usable dependency is
--
--   extraction core + four-owner certificate
--       -> full historical extraction
--       -> literal selected plaquette witness/family.
--
-- No owner inequality, KKT pseudoinverse, stationarity theorem, or physical
-- interval certificate is fabricated here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedVariationSignConventionExact as Sign
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonClosureExact as Closure
import DASHI.Physics.YangMills.BalabanP33CertifiedPlaquetteOwnerEnvelopeExact as Envelope
import DASHI.Physics.YangMills.BalabanP33CertifiedPlaquetteEnvelopeToLiteralFamilyExact as EnvelopeBridge
import DASHI.Physics.YangMills.BalabanSelectedBackgroundLiteralPlaquetteFamilyProducerExact as Producer
import DASHI.Physics.YangMills.BalabanSelectedSinglePlaquetteWitnessExact as Plaquette

record CorrelatedSingletonExtractionCore
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    Multiplier : Set
    pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier
    firstVariationCovector : KKT.StateVector

    residualAuthority : Authority.CorrelatedResidualAuthority
      pseudoData firstVariationCovector
      (Closure.literalRawExtractor bondField plaquette)

    FineVariation : Set
    variation : FineVariation

    GaugeAdmissible : FineVariation → Set
    ConstraintTangent : FineVariation → Set
    SupportedNearPlaquette : FineVariation → Set

    gaugeAdmissible : GaugeAdmissible variation
    constraintTangent : ConstraintTangent variation
    localSupport : SupportedNearPlaquette variation

    variationNormSq : FineVariation → ℚ
    selectorConstant : ℚ
    selectorConstantNonnegative : 0ℚ ≤ selectorConstant
    variationChargeBound :
      variationNormSq variation
      ≤ selectorConstant * Wilson.plaquetteCrossCharge bondField plaquette

    firstVariation : FineVariation → ℚ

    selectedEulerLagrangeStationary :
      firstVariation variation ≡ 0ℚ

    projectedVariationExact :
      firstVariation variation
      ≡ Partition.physicalPlaquetteWilsonLinearPart
          background bondField plaquette
        + Sign.canonicalProjectedSpillover
            (Authority.rawLocalization residualAuthority)
            (Authority.canonicalMultiplierGreenPairing
              pseudoData firstVariationCovector
              (Closure.literalRawExtractor bondField plaquette))

    exactCancellation :
      Ownership.ExactCorrelatedCancellation
        (Authority.canonicalCorrelatedResidualFamily residualAuthority)

open CorrelatedSingletonExtractionCore public

attachOwnerBudgets :
  ∀ {background bondField plaquette}
    (core : CorrelatedSingletonExtractionCore
      background bondField plaquette) →
  Ownership.CorrelatedOwnerBudgets
    (Authority.canonicalCorrelatedResidualFamily (residualAuthority core))
    (Wilson.plaquetteCrossCharge bondField plaquette) →
  Closure.CorrelatedSingletonExtractionData background bondField plaquette
attachOwnerBudgets core budgets = record
  { Closure.CorrelatedSingletonExtractionData.Multiplier = Multiplier core
  ; Closure.CorrelatedSingletonExtractionData.pseudoData = pseudoData core
  ; Closure.CorrelatedSingletonExtractionData.firstVariationCovector =
      firstVariationCovector core
  ; Closure.CorrelatedSingletonExtractionData.residualAuthority =
      residualAuthority core
  ; Closure.CorrelatedSingletonExtractionData.FineVariation = FineVariation core
  ; Closure.CorrelatedSingletonExtractionData.variation = variation core
  ; Closure.CorrelatedSingletonExtractionData.GaugeAdmissible =
      GaugeAdmissible core
  ; Closure.CorrelatedSingletonExtractionData.ConstraintTangent =
      ConstraintTangent core
  ; Closure.CorrelatedSingletonExtractionData.SupportedNearPlaquette =
      SupportedNearPlaquette core
  ; Closure.CorrelatedSingletonExtractionData.gaugeAdmissible =
      gaugeAdmissible core
  ; Closure.CorrelatedSingletonExtractionData.constraintTangent =
      constraintTangent core
  ; Closure.CorrelatedSingletonExtractionData.localSupport = localSupport core
  ; Closure.CorrelatedSingletonExtractionData.variationNormSq =
      variationNormSq core
  ; Closure.CorrelatedSingletonExtractionData.selectorConstant =
      selectorConstant core
  ; Closure.CorrelatedSingletonExtractionData.selectorConstantNonnegative =
      selectorConstantNonnegative core
  ; Closure.CorrelatedSingletonExtractionData.variationChargeBound =
      variationChargeBound core
  ; Closure.CorrelatedSingletonExtractionData.firstVariation =
      firstVariation core
  ; Closure.CorrelatedSingletonExtractionData.selectedEulerLagrangeStationary =
      selectedEulerLagrangeStationary core
  ; Closure.CorrelatedSingletonExtractionData.projectedVariationExact =
      projectedVariationExact core
  ; Closure.CorrelatedSingletonExtractionData.exactCancellation =
      exactCancellation core
  ; Closure.CorrelatedSingletonExtractionData.ownerBudgets = budgets
  }

record CertifiedCorrelatedSingletonCore
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    core : CorrelatedSingletonExtractionCore background bondField plaquette

    intervalCertificate :
      Envelope.FourOwnerIntervalCertificate
        (Authority.canonicalCorrelatedResidualFamily (residualAuthority core))
        (Wilson.plaquetteCrossCharge bondField plaquette)

open CertifiedCorrelatedSingletonCore public

certifiedCoreOwnerBudgets :
  ∀ {background bondField plaquette}
    (data : CertifiedCorrelatedSingletonCore
      background bondField plaquette) →
  Ownership.CorrelatedOwnerBudgets
    (Authority.canonicalCorrelatedResidualFamily
      (residualAuthority (core data)))
    (Wilson.plaquetteCrossCharge bondField plaquette)
certifiedCoreOwnerBudgets data =
  Envelope.certifiedIntervalProducesCorrelatedOwnerBudgets
    (intervalCertificate data)

certifiedCoreToHistoricalExtraction :
  ∀ {background bondField plaquette} →
  CertifiedCorrelatedSingletonCore background bondField plaquette →
  Closure.CorrelatedSingletonExtractionData background bondField plaquette
certifiedCoreToHistoricalExtraction data =
  attachOwnerBudgets (core data) (certifiedCoreOwnerBudgets data)

certifiedCoreToLiteralWitness :
  ∀ {background bondField plaquette} →
  CertifiedCorrelatedSingletonCore background bondField plaquette →
  Plaquette.LiteralSelectedPlaquetteWitness background bondField plaquette
certifiedCoreToLiteralWitness data =
  Producer.correlatedSingletonWithSlackToLiteralWitness
    (record
      { Producer.CorrelatedSingletonWithSlack.extraction =
          certifiedCoreToHistoricalExtraction data
      ; Producer.CorrelatedSingletonWithSlack.ownerBounds =
          EnvelopeBridge.intervalCertificateToSlackBounds
            (intervalCertificate data)
      })

record CertifiedCorrelatedSingletonCoreFamily
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4) : Set₂ where
  field
    atPlaquette : ∀ plaquette →
      CertifiedCorrelatedSingletonCore background bondField plaquette

open CertifiedCorrelatedSingletonCoreFamily public

certifiedCoreFamilyToLiteralFamily :
  ∀ {background bondField} →
  CertifiedCorrelatedSingletonCoreFamily background bondField →
  Plaquette.LiteralSelectedPlaquetteFamily background bondField
certifiedCoreFamilyToLiteralFamily family = record
  { Plaquette.LiteralSelectedPlaquetteFamily.atPlaquette = λ plaquette →
      certifiedCoreToLiteralWitness (atPlaquette family plaquette) }

certifiedCoreExtractionSplitLevel : ProofLevel
certifiedCoreExtractionSplitLevel = machineChecked

certifiedCoreOwnerBudgetAttachmentLevel : ProofLevel
certifiedCoreOwnerBudgetAttachmentLevel = machineChecked

certifiedCoreToLiteralFamilyLevel : ProofLevel
certifiedCoreToLiteralFamilyLevel = machineChecked

-- Remaining physical inputs are now upstream and non-circular:
--
--   * selected KKT/variation/exact-cancellation extraction core;
--   * four certified rational owner bounds for each plaquette.
--
-- The legacy ownerBudgets field is compiler output, not an input to certificate
-- generation on this preferred route.
