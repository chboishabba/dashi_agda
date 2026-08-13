module DASHI.Physics.YangMills.BalabanP33CertifiedPlaquettePairEnvelopeExact where

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
-- Certified-computation interface for the cancellation-preserving G2 lane.
-- Instead of enclosing localization, transport, near-Green and far-Green
-- separately, certify the two SIGNED grouped quantities after their internal
-- cancellations have already occurred:
--
--   L_T = localization + transport,
--   G_NF = nearGreen + farGreen.
--
-- A rational interval/enclosure computation therefore only needs to prove
--
--   L_T <= c_LT * charge,
--   G_NF <= c_G * charge,
--   c_LT + c_G <= 55/18874368.
--
-- This is strictly at least as permissive as summing four independent upper
-- bounds and is the preferred numerical target whenever the pair members have
-- opposing signs.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualBoundsExact as Bounds
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedPairBudgetExact as Pair

record RationalSignedUpperEnclosure (value : ℚ) : Set where
  field
    upper : ℚ
    sound : value ≤ upper

open RationalSignedUpperEnclosure public

record CertifiedCorrelatedPairEnvelope
    (family : Ownership.CorrelatedResidualFamily)
    (charge : ℚ) : Set where
  field
    localizationTransport :
      RationalSignedUpperEnclosure (Bounds.rawLocalizationSpillover family)
    nearFarGreen :
      RationalSignedUpperEnclosure
        (Bounds.selectedMultiplierDefectContribution family)

    localizationPairCoefficient : ℚ
    multiplierPairCoefficient : ℚ

    localizationCertificate :
      upper localizationTransport ≤ localizationPairCoefficient * charge
    multiplierCertificate :
      upper nearFarGreen ≤ multiplierPairCoefficient * charge

    coefficientTotalFits :
      localizationPairCoefficient + multiplierPairCoefficient
      ≤ Pair.Selector.remainingSingletonCoefficient

    chargeNonnegative : 0ℚ ≤ charge

open CertifiedCorrelatedPairEnvelope public

certifiedPairEnvelopeToBudgets :
  ∀ {family charge} →
  CertifiedCorrelatedPairEnvelope family charge →
  Pair.CorrelatedPairBudgets family charge
certifiedPairEnvelopeToBudgets certificate = record
  { Pair.CorrelatedPairBudgets.localizationPairCoefficient =
      localizationPairCoefficient certificate
  ; Pair.CorrelatedPairBudgets.multiplierPairCoefficient =
      multiplierPairCoefficient certificate
  ; Pair.CorrelatedPairBudgets.localizationPairUpper =
      ℚ.≤-trans
        (sound (localizationTransport certificate))
        (localizationCertificate certificate)
  ; Pair.CorrelatedPairBudgets.multiplierPairUpper =
      ℚ.≤-trans
        (sound (nearFarGreen certificate))
        (multiplierCertificate certificate)
  ; Pair.CorrelatedPairBudgets.pairCoefficientTotalFits =
      coefficientTotalFits certificate
  ; Pair.CorrelatedPairBudgets.chargeNonnegative =
      chargeNonnegative certificate
  }

certifiedPairEnvelopeClosesResidual :
  ∀ {family charge} →
  Ownership.ExactCorrelatedCancellation family →
  CertifiedCorrelatedPairEnvelope family charge →
  Ownership.correlatedResidualTotal family
  ≤ Pair.Selector.remainingSingletonCoefficient * charge
certifiedPairEnvelopeClosesResidual cancellation certificate =
  Pair.correlatedPairBudgetsCloseResidual cancellation
    (certifiedPairEnvelopeToBudgets certificate)

p33CertifiedSignedPairEnvelopeLevel : ProofLevel
p33CertifiedSignedPairEnvelopeLevel = machineChecked
