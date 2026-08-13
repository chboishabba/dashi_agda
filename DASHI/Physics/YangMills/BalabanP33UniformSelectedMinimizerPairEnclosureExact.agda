module DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerPairEnclosureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Ramon E. Moore, R. Baker Kearfott, Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- DASHI CONTRIBUTION
--
-- G2 does NOT require a decimal approximation of the implicit minimizer.
-- It is enough to enclose the two signed correlated residual pairs uniformly
-- on any certified region known to contain the selected minimizer.
--
--   R_LT = localization + transport,
--   R_G  = nearGreen + farGreen.
--
-- If every configuration A in the certified region has sound upper enclosures
-- with the SAME coefficients c_LT,c_G and
--
--       c_LT + c_G <= 55/18874368,
--
-- then the actual selected minimizer inherits the singleton bound merely from
-- membership in that region.  This is stronger than point evaluation and keeps
-- cancellation before majorisation.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualBoundsExact as Bounds
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanP33CertifiedPlaquettePairEnvelopeExact as PairEnvelope

record UniformSelectedRegionPairEnclosure (Configuration : Set) : Set₁ where
  field
    InCertifiedRegion : Configuration → Set
    selectedMinimizer : Configuration
    selectedMinimizerInRegion : InCertifiedRegion selectedMinimizer

    familyAt : Configuration → Ownership.CorrelatedResidualFamily
    chargeAt : Configuration → ℚ
    cancellationAt : ∀ configuration →
      InCertifiedRegion configuration →
      Ownership.ExactCorrelatedCancellation (familyAt configuration)

    localizationPairCoefficient multiplierPairCoefficient : ℚ

    chargeNonnegativeAt : ∀ configuration →
      InCertifiedRegion configuration → 0ℚ ≤ chargeAt configuration

    localizationTransportUpperAt : ∀ configuration →
      InCertifiedRegion configuration →
      PairEnvelope.RationalSignedUpperEnclosure
        (Bounds.rawLocalizationSpillover (familyAt configuration))

    nearFarGreenUpperAt : ∀ configuration →
      InCertifiedRegion configuration →
      PairEnvelope.RationalSignedUpperEnclosure
        (Bounds.selectedMultiplierDefectContribution (familyAt configuration))

    localizationCertificateAt : ∀ configuration inRegion →
      PairEnvelope.upper (localizationTransportUpperAt configuration inRegion)
      ≤ localizationPairCoefficient * chargeAt configuration

    multiplierCertificateAt : ∀ configuration inRegion →
      PairEnvelope.upper (nearFarGreenUpperAt configuration inRegion)
      ≤ multiplierPairCoefficient * chargeAt configuration

    coefficientTotalFits :
      localizationPairCoefficient + multiplierPairCoefficient
      ≤ Selector.remainingSingletonCoefficient

open UniformSelectedRegionPairEnclosure public

pairEnvelopeAt :
  ∀ {Configuration}
    (uniform : UniformSelectedRegionPairEnclosure Configuration)
    configuration →
  InCertifiedRegion uniform configuration →
  PairEnvelope.CertifiedCorrelatedPairEnvelope
    (familyAt uniform configuration) (chargeAt uniform configuration)
pairEnvelopeAt uniform configuration inRegion = record
  { PairEnvelope.CertifiedCorrelatedPairEnvelope.localizationTransport =
      localizationTransportUpperAt uniform configuration inRegion
  ; PairEnvelope.CertifiedCorrelatedPairEnvelope.nearFarGreen =
      nearFarGreenUpperAt uniform configuration inRegion
  ; PairEnvelope.CertifiedCorrelatedPairEnvelope.localizationPairCoefficient =
      localizationPairCoefficient uniform
  ; PairEnvelope.CertifiedCorrelatedPairEnvelope.multiplierPairCoefficient =
      multiplierPairCoefficient uniform
  ; PairEnvelope.CertifiedCorrelatedPairEnvelope.localizationCertificate =
      localizationCertificateAt uniform configuration inRegion
  ; PairEnvelope.CertifiedCorrelatedPairEnvelope.multiplierCertificate =
      multiplierCertificateAt uniform configuration inRegion
  ; PairEnvelope.CertifiedCorrelatedPairEnvelope.coefficientTotalFits =
      coefficientTotalFits uniform
  ; PairEnvelope.CertifiedCorrelatedPairEnvelope.chargeNonnegative =
      chargeNonnegativeAt uniform configuration inRegion
  }

selectedMinimizerResidualClosesFromUniformRegion :
  ∀ {Configuration}
    (uniform : UniformSelectedRegionPairEnclosure Configuration) →
  Ownership.correlatedResidualTotal
      (familyAt uniform (selectedMinimizer uniform))
  ≤ Selector.remainingSingletonCoefficient
      * chargeAt uniform (selectedMinimizer uniform)
selectedMinimizerResidualClosesFromUniformRegion uniform =
  PairEnvelope.certifiedPairEnvelopeClosesResidual
    (cancellationAt uniform
      (selectedMinimizer uniform) (selectedMinimizerInRegion uniform))
    (pairEnvelopeAt uniform
      (selectedMinimizer uniform) (selectedMinimizerInRegion uniform))

p33UniformSelectedRegionPairEnclosureTransportLevel : ProofLevel
p33UniformSelectedRegionPairEnclosureTransportLevel = machineChecked

-- Remaining G2 computation is now explicitly a UNIFORM interval problem over
-- the certified minimizer region.  No numerical solution of A_* is logically
-- required if these two signed pair enclosures can be established uniformly.
p33PhysicalUniformSelectedRegionPairEnclosureLevel : ProofLevel
p33PhysicalUniformSelectedRegionPairEnclosureLevel = conditional
