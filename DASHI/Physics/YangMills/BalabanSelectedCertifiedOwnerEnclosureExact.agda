module DASHI.Physics.YangMills.BalabanSelectedCertifiedOwnerEnclosureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Ramon E. Moore; R. Baker Kearfott; Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Provide the exact bridge from certified rational enclosures to the physical
-- four-owner budget.  A computation need not expose closed-form entries of
-- K_A^+: it may instead certify a rational upper enclosure for each signed
-- owner contribution.  The theorem composes enclosure soundness with the
-- coefficient inequalities and returns the slack-preserving owner object
-- consumed by the single-plaquette witness.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedOwnerBudgetSlackExact as Slack
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector

record RationalUpperEnclosure (value : ℚ) : Set where
  field
    centre radius : ℚ
    radiusNonnegative : 0ℚ ≤ radius
    enclosedUpper : value ≤ centre + radius
open RationalUpperEnclosure public

record CertifiedCorrelatedOwnerEnclosures
    (family : Ownership.CorrelatedResidualFamily)
    (charge : ℚ) : Set where
  field
    localizationEnclosure : RationalUpperEnclosure
      (Ownership.ownerContribution family Ownership.localizationOwner)
    transportEnclosure : RationalUpperEnclosure
      (Ownership.ownerContribution family Ownership.transportOwner)
    nearGreenEnclosure : RationalUpperEnclosure
      (Ownership.ownerContribution family Ownership.nearGreenOwner)
    farGreenEnclosure : RationalUpperEnclosure
      (Ownership.ownerContribution family Ownership.farGreenOwner)

    localizationCoefficient transportCoefficient
      nearGreenCoefficient farGreenCoefficient : ℚ

    localizationCertificate :
      centre localizationEnclosure + radius localizationEnclosure
      ≤ localizationCoefficient * charge
    transportCertificate :
      centre transportEnclosure + radius transportEnclosure
      ≤ transportCoefficient * charge
    nearGreenCertificate :
      centre nearGreenEnclosure + radius nearGreenEnclosure
      ≤ nearGreenCoefficient * charge
    farGreenCertificate :
      centre farGreenEnclosure + radius farGreenEnclosure
      ≤ farGreenCoefficient * charge

    coefficientTotalFits :
      Slack.ownerCoefficientTotal localizationCoefficient
        transportCoefficient nearGreenCoefficient farGreenCoefficient
      ≤ Selector.remainingSingletonCoefficient

    chargeNonnegative : 0ℚ ≤ charge
open CertifiedCorrelatedOwnerEnclosures public

certifiedEnclosuresToOwnerBounds :
  ∀ {family charge} →
  CertifiedCorrelatedOwnerEnclosures family charge →
  Slack.CorrelatedOwnerBoundsWithSlack family charge
certifiedEnclosuresToOwnerBounds certificate = record
  { Slack.CorrelatedOwnerBoundsWithSlack.localizationCoefficient =
      localizationCoefficient certificate
  ; Slack.CorrelatedOwnerBoundsWithSlack.transportCoefficient =
      transportCoefficient certificate
  ; Slack.CorrelatedOwnerBoundsWithSlack.nearGreenCoefficient =
      nearGreenCoefficient certificate
  ; Slack.CorrelatedOwnerBoundsWithSlack.farGreenCoefficient =
      farGreenCoefficient certificate
  ; Slack.CorrelatedOwnerBoundsWithSlack.localizationUpper =
      ℚP.≤-trans
        (enclosedUpper (localizationEnclosure certificate))
        (localizationCertificate certificate)
  ; Slack.CorrelatedOwnerBoundsWithSlack.transportUpper =
      ℚP.≤-trans
        (enclosedUpper (transportEnclosure certificate))
        (transportCertificate certificate)
  ; Slack.CorrelatedOwnerBoundsWithSlack.nearGreenUpper =
      ℚP.≤-trans
        (enclosedUpper (nearGreenEnclosure certificate))
        (nearGreenCertificate certificate)
  ; Slack.CorrelatedOwnerBoundsWithSlack.farGreenUpper =
      ℚP.≤-trans
        (enclosedUpper (farGreenEnclosure certificate))
        (farGreenCertificate certificate)
  ; Slack.CorrelatedOwnerBoundsWithSlack.coefficientTotalFits =
      coefficientTotalFits certificate
  ; Slack.CorrelatedOwnerBoundsWithSlack.chargeNonnegative =
      chargeNonnegative certificate }

certifiedEnclosuresCloseCorrelatedResidual :
  ∀ {family charge} →
  Ownership.ExactCorrelatedCancellation family →
  CertifiedCorrelatedOwnerEnclosures family charge →
  Ownership.correlatedResidualTotal family
  ≤ Selector.remainingSingletonCoefficient * charge
certifiedEnclosuresCloseCorrelatedResidual cancellation certificate =
  Slack.correlatedResidualClosesWithUnusedSlack cancellation
    (certifiedEnclosuresToOwnerBounds certificate)

selectedCertifiedOwnerEnclosureLevel : ProofLevel
selectedCertifiedOwnerEnclosureLevel = machineChecked
