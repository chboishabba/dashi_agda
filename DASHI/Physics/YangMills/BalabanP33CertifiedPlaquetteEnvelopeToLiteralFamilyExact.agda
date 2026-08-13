module DASHI.Physics.YangMills.BalabanP33CertifiedPlaquetteEnvelopeToLiteralFamilyExact where

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
-- Reuse the repository's existing physical `FourOwnerIntervalCertificate`
-- directly at the Round-47 literal-plaquette producer boundary.  The old
-- certificate spends an explicit nonnegative `padding` to make the legacy
-- coefficient identity exact.  For the newer slack interface we simply keep
-- that padding unused:
--
--   upper_loc + upper_tr + upper_near + upper_far
--     <= (... same sum ...) + padding
--      = remainingSingletonCoefficient.
--
-- Thus a checked physical interval envelope plus the existing correlated
-- singleton extraction is already enough to construct the literal witness and
-- family.  No second owner-budget computation is needed.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonClosureExact as Closure
import DASHI.Physics.YangMills.BalabanSelectedOwnerBudgetSlackExact as Slack
import DASHI.Physics.YangMills.BalabanP33CertifiedPlaquetteOwnerEnvelopeExact as Envelope
import DASHI.Physics.YangMills.BalabanSelectedBackgroundLiteralPlaquetteFamilyProducerExact as Producer
import DASHI.Physics.YangMills.BalabanSelectedSinglePlaquetteWitnessExact as Plaquette

intervalCertificateToSlackBounds :
  ∀ {family charge} →
  Envelope.FourOwnerIntervalCertificate family charge →
  Slack.CorrelatedOwnerBoundsWithSlack family charge
intervalCertificateToSlackBounds certificate =
  let
    loc = Envelope.upper (Envelope.localization certificate)
    tr = Envelope.upper (Envelope.transport certificate)
    near = Envelope.upper (Envelope.nearGreen certificate)
    far = Envelope.upper (Envelope.farGreen certificate)
    pad = Envelope.padding certificate

    totalBelowPadded :
      Slack.ownerCoefficientTotal loc tr near far
      ≤ Slack.ownerCoefficientTotal loc tr near far + pad
    totalBelowPadded =
      subst
        (λ left → left ≤ Slack.ownerCoefficientTotal loc tr near far + pad)
        (sym (ℚP.+-identityʳ (Slack.ownerCoefficientTotal loc tr near far)))
        (ℚP.+-monoʳ-≤
          (Slack.ownerCoefficientTotal loc tr near far)
          (Envelope.paddingNonnegative certificate))

    paddedIsRemaining :
      Slack.ownerCoefficientTotal loc tr near far + pad
      ≡ Producer.Selector.remainingSingletonCoefficient
    paddedIsRemaining =
      let
        raw = Envelope.certifiedBudgetIdentity certificate
      in
      subst
        (λ left → left ≡ Producer.Selector.remainingSingletonCoefficient)
        (ℚRing.solve-∀ loc tr near far pad)
        raw

    totalFits :
      Slack.ownerCoefficientTotal loc tr near far
      ≤ Producer.Selector.remainingSingletonCoefficient
    totalFits = subst
      (λ upper → Slack.ownerCoefficientTotal loc tr near far ≤ upper)
      paddedIsRemaining totalBelowPadded
  in
  record
    { Slack.CorrelatedOwnerBoundsWithSlack.localizationCoefficient = loc
    ; Slack.CorrelatedOwnerBoundsWithSlack.transportCoefficient = tr
    ; Slack.CorrelatedOwnerBoundsWithSlack.nearGreenCoefficient = near
    ; Slack.CorrelatedOwnerBoundsWithSlack.farGreenCoefficient = far
    ; Slack.CorrelatedOwnerBoundsWithSlack.localizationUpper =
        ℚP.≤-trans
          (Envelope.localizationContributionUpper certificate)
          (Envelope.coefficientUpperTimesCharge certificate
            (Envelope.localization certificate))
    ; Slack.CorrelatedOwnerBoundsWithSlack.transportUpper =
        Envelope.transportUpperFromInterval certificate
    ; Slack.CorrelatedOwnerBoundsWithSlack.nearGreenUpper =
        Envelope.nearGreenUpperFromInterval certificate
    ; Slack.CorrelatedOwnerBoundsWithSlack.farGreenUpper =
        Envelope.farGreenUpperFromInterval certificate
    ; Slack.CorrelatedOwnerBoundsWithSlack.coefficientTotalFits = totalFits
    ; Slack.CorrelatedOwnerBoundsWithSlack.chargeNonnegative =
        Envelope.chargeNonnegative certificate }

record PhysicalIntervalSingleton
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    extraction : Closure.CorrelatedSingletonExtractionData
      background bondField plaquette
    intervalCertificate :
      Envelope.FourOwnerIntervalCertificate
        (Authority.canonicalCorrelatedResidualFamily
          (Closure.residualAuthority extraction))
        (Wilson.plaquetteCrossCharge bondField plaquette)

open PhysicalIntervalSingleton public

physicalIntervalSingletonToLiteralWitness :
  ∀ {background bondField plaquette} →
  PhysicalIntervalSingleton background bondField plaquette →
  Plaquette.LiteralSelectedPlaquetteWitness background bondField plaquette
physicalIntervalSingletonToLiteralWitness data =
  Producer.correlatedSingletonWithSlackToLiteralWitness record
    { Producer.CorrelatedSingletonWithSlack.extraction = extraction data
    ; Producer.CorrelatedSingletonWithSlack.ownerBounds =
        intervalCertificateToSlackBounds (intervalCertificate data) }

record PhysicalIntervalSingletonFamily
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4) : Set₂ where
  field
    atPlaquette : ∀ plaquette →
      PhysicalIntervalSingleton background bondField plaquette

open PhysicalIntervalSingletonFamily public

physicalIntervalSingletonFamilyToLiteralFamily :
  ∀ {background bondField} →
  PhysicalIntervalSingletonFamily background bondField →
  Plaquette.LiteralSelectedPlaquetteFamily background bondField
physicalIntervalSingletonFamilyToLiteralFamily family = record
  { Plaquette.LiteralSelectedPlaquetteFamily.atPlaquette = λ plaquette →
      physicalIntervalSingletonToLiteralWitness (atPlaquette family plaquette) }

p33CertifiedEnvelopeToSlackLevel : ProofLevel
p33CertifiedEnvelopeToSlackLevel = machineChecked

p33CertifiedEnvelopeToLiteralFamilyLevel : ProofLevel
p33CertifiedEnvelopeToLiteralFamilyLevel = machineChecked
