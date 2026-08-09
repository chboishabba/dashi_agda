module DASHI.Physics.YangMills.BalabanP33CertifiedPlaquetteOwnerEnvelopeExact where

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
-- Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Turn certified rational upper enclosures for the four surviving correlated
-- singleton owners into the exact `CorrelatedOwnerBudgets` object consumed by
-- the Round-40 selector reducer.
--
-- The certificate does not assert that the selected-background matrix entries
-- or Moore--Penrose inverse are rational.  It requires only rigorous rational
-- upper bounds on the four final owner coefficients, a nonnegative charge, and
-- explicit nonnegative budget padding:
--
--   upper_loc + upper_tr + upper_near + upper_far + padding
--     = 55 / 18874368.
--
-- The padding is assigned to the localization owner, and monotonicity proves
-- that every enclosed physical coefficient still fits.  This is the exact
-- bridge needed by interval/enclosure computations: numerical output cannot
-- promote itself, but a checked enclosure and exact slack identity can.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership

record CertifiedCoefficientInterval : Set where
  constructor certified-coefficient-interval
  field
    lower actual upper : ℚ
    lowerBelowActual : lower ≤ actual
    actualBelowUpper : actual ≤ upper

open CertifiedCoefficientInterval public

record FourOwnerIntervalCertificate
    (family : Ownership.CorrelatedResidualFamily)
    (charge : ℚ) : Set where
  field
    chargeNonnegative : 0ℚ ≤ charge

    localization transport nearGreen farGreen :
      CertifiedCoefficientInterval

    localizationActualNonnegative :
      0ℚ ≤ actual localization
    transportActualNonnegative :
      0ℚ ≤ actual transport
    nearGreenActualNonnegative :
      0ℚ ≤ actual nearGreen
    farGreenActualNonnegative :
      0ℚ ≤ actual farGreen

    localizationContributionUpper :
      Ownership.ownerContribution family Ownership.localizationOwner
      ≤ actual localization * charge
    transportContributionUpper :
      Ownership.ownerContribution family Ownership.transportOwner
      ≤ actual transport * charge
    nearGreenContributionUpper :
      Ownership.ownerContribution family Ownership.nearGreenOwner
      ≤ actual nearGreen * charge
    farGreenContributionUpper :
      Ownership.ownerContribution family Ownership.farGreenOwner
      ≤ actual farGreen * charge

    padding : ℚ
    paddingNonnegative : 0ℚ ≤ padding

    certifiedBudgetIdentity :
      upper localization
      + upper transport
      + upper nearGreen
      + upper farGreen
      + padding
      ≡ Selector.remainingSingletonCoefficient

open FourOwnerIntervalCertificate public

coefficientUpperTimesCharge :
  ∀ {family charge}
    (certificate : FourOwnerIntervalCertificate family charge)
    interval →
  actual interval * charge ≤ upper interval * charge
coefficientUpperTimesCharge {charge = charge} certificate interval =
  let
    instance
      chargeNN = nonNegative (chargeNonnegative certificate)
  in
  ℚP.*-monoʳ-≤-nonNeg charge (actualBelowUpper interval)

localizationPaddedCoefficient :
  ∀ {family charge} →
  FourOwnerIntervalCertificate family charge → ℚ
localizationPaddedCoefficient certificate =
  upper (localization certificate) + padding certificate

localizationUpperWithPadding :
  ∀ {family charge}
    (certificate : FourOwnerIntervalCertificate family charge) →
  Ownership.ownerContribution family Ownership.localizationOwner
  ≤ localizationPaddedCoefficient certificate * charge
localizationUpperWithPadding {family} {charge} certificate =
  let
    actualToUpper :
      actual (localization certificate) * charge
      ≤ upper (localization certificate) * charge
    actualToUpper =
      coefficientUpperTimesCharge certificate
        (localization certificate)

    upperBelowPadded :
      upper (localization certificate)
      ≤ upper (localization certificate) + padding certificate
    upperBelowPadded =
      subst
        (λ lower →
          lower
          ≤ upper (localization certificate) + padding certificate)
        (ℚP.+-identityʳ (upper (localization certificate)))
        (ℚP.+-monoʳ-≤
          (upper (localization certificate))
          (paddingNonnegative certificate))

    upperTimesChargeBelowPadded :
      upper (localization certificate) * charge
      ≤ localizationPaddedCoefficient certificate * charge
    upperTimesChargeBelowPadded =
      let
        instance
          chargeNN = nonNegative (chargeNonnegative certificate)
      in
      ℚP.*-monoʳ-≤-nonNeg charge upperBelowPadded
  in
  ℚP.≤-trans
    (localizationContributionUpper certificate)
    (ℚP.≤-trans actualToUpper upperTimesChargeBelowPadded)

transportUpperFromInterval :
  ∀ {family charge}
    (certificate : FourOwnerIntervalCertificate family charge) →
  Ownership.ownerContribution family Ownership.transportOwner
  ≤ upper (transport certificate) * charge
transportUpperFromInterval certificate =
  ℚP.≤-trans
    (transportContributionUpper certificate)
    (coefficientUpperTimesCharge certificate
      (transport certificate))

nearGreenUpperFromInterval :
  ∀ {family charge}
    (certificate : FourOwnerIntervalCertificate family charge) →
  Ownership.ownerContribution family Ownership.nearGreenOwner
  ≤ upper (nearGreen certificate) * charge
nearGreenUpperFromInterval certificate =
  ℚP.≤-trans
    (nearGreenContributionUpper certificate)
    (coefficientUpperTimesCharge certificate
      (nearGreen certificate))

farGreenUpperFromInterval :
  ∀ {family charge}
    (certificate : FourOwnerIntervalCertificate family charge) →
  Ownership.ownerContribution family Ownership.farGreenOwner
  ≤ upper (farGreen certificate) * charge
farGreenUpperFromInterval certificate =
  ℚP.≤-trans
    (farGreenContributionUpper certificate)
    (coefficientUpperTimesCharge certificate
      (farGreen certificate))

certifiedIntervalProducesCorrelatedOwnerBudgets :
  ∀ {family charge} →
  FourOwnerIntervalCertificate family charge →
  Ownership.CorrelatedOwnerBudgets family charge
certifiedIntervalProducesCorrelatedOwnerBudgets certificate = record
  { Ownership.CorrelatedOwnerBudgets.localizationCoefficient =
      localizationPaddedCoefficient certificate
  ; Ownership.CorrelatedOwnerBudgets.transportCoefficient =
      upper (transport certificate)
  ; Ownership.CorrelatedOwnerBudgets.nearGreenCoefficient =
      upper (nearGreen certificate)
  ; Ownership.CorrelatedOwnerBudgets.farGreenCoefficient =
      upper (farGreen certificate)
  ; Ownership.CorrelatedOwnerBudgets.localizationUpper =
      localizationUpperWithPadding certificate
  ; Ownership.CorrelatedOwnerBudgets.transportUpper =
      transportUpperFromInterval certificate
  ; Ownership.CorrelatedOwnerBudgets.nearGreenUpper =
      nearGreenUpperFromInterval certificate
  ; Ownership.CorrelatedOwnerBudgets.farGreenUpper =
      farGreenUpperFromInterval certificate
  ; Ownership.CorrelatedOwnerBudgets.coefficientsCloseSingletonBudget =
      trans
        (ℚRing.solve-∀
          (upper (localization certificate))
          (padding certificate)
          (upper (transport certificate))
          (upper (nearGreen certificate))
          (upper (farGreen certificate)))
        (certifiedBudgetIdentity certificate)
  }

record CertifiedSelectedPlaquetteEnvelope
    (family : Ownership.CorrelatedResidualFamily)
    (charge : ℚ) : Set where
  field
    exactCancellation :
      Ownership.ExactCorrelatedCancellation family
    intervalCertificate :
      FourOwnerIntervalCertificate family charge

open CertifiedSelectedPlaquetteEnvelope public

certifiedSelectedPlaquetteResidualUpper :
  ∀ {family charge} →
  CertifiedSelectedPlaquetteEnvelope family charge →
  Ownership.correlatedResidualTotal family
  ≤ Selector.remainingSingletonCoefficient * charge
certifiedSelectedPlaquetteResidualUpper envelope =
  Ownership.correlatedResidualClosesSingletonBudget
    (exactCancellation envelope)
    (certifiedIntervalProducesCorrelatedOwnerBudgets
      (intervalCertificate envelope))

certifiedPlaquetteIntervalBridgeLevel : ProofLevel
certifiedPlaquetteIntervalBridgeLevel = machineChecked

certifiedPlaquetteBudgetPaddingLevel : ProofLevel
certifiedPlaquetteBudgetPaddingLevel = machineChecked

physicalSelectedPlaquetteIntervalProducerLevel : ProofLevel
physicalSelectedPlaquetteIntervalProducerLevel = conditional

certifiedPlaquetteIntervalBridgeClosed : Bool
certifiedPlaquetteIntervalBridgeClosed = true

physicalSelectedPlaquetteIntervalConstructed : Bool
physicalSelectedPlaquetteIntervalConstructed = false

certifiedPlaquetteIntervalBridgeClosedIsTrue :
  certifiedPlaquetteIntervalBridgeClosed ≡ true
certifiedPlaquetteIntervalBridgeClosedIsTrue = refl
