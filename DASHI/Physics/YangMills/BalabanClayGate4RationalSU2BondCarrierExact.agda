module DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Covariance
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press, first published
-- 1983; open-access reissue 2022. DOI: 10.1017/9781009290395.
------------------------------------------------------------------------

RationalSU2BondField : Nat → Set
RationalSU2BondField n =
  Bond.PeriodicBondField n SU2.RationalUnitQuaternion

RationalSU2SiteGauge : Nat → Set
RationalSU2SiteGauge n =
  Bond.PeriodicSiteGauge n SU2.RationalUnitQuaternion

record RationalSU2BondData (n : Nat) : Set₁ where
  field
    exactGroup : Bond.ExactLinkGroup SU2.RationalUnitQuaternion
    stepInverseLaws : Covariance.PeriodicStepInverseLaws n
    links : RationalSU2BondField n
    siteGauge : RationalSU2SiteGauge n

open RationalSU2BondData public

realization :
  ∀ {n} (dataSet : RationalSU2BondData n) →
  Bond.PeriodicBondGaugeRealization
    n SU2.RationalUnitQuaternion (exactGroup dataSet)
realization dataSet =
  Covariance.literalPeriodicBondGaugeRealization
    (exactGroup dataSet)
    (stepInverseLaws dataSet)
    (links dataSet)
    (siteGauge dataSet)

rationalSU2PlaquetteHolonomy :
  ∀ {n} (dataSet : RationalSU2BondData n) →
  Plaquette.PeriodicPlaquette n → SU2.RationalUnitQuaternion
rationalSU2PlaquetteHolonomy dataSet =
  Bond.plaquetteHolonomyFromBonds (realization dataSet)

rationalSU2PathGaugeCancellation :
  ∀ {n} (dataSet : RationalSU2BondData n) site directions →
  Bond.transformedPathHolonomy (realization dataSet) site directions
  ≡ Bond.multiply (exactGroup dataSet)
      (Bond.multiply (exactGroup dataSet)
        (siteGauge dataSet site)
        (Bond.pathHolonomy (realization dataSet) site directions))
      (Bond.inverse (exactGroup dataSet)
        (siteGauge dataSet (Bond.walk site directions)))
rationalSU2PathGaugeCancellation dataSet =
  Bond.pathSiteGaugeCancellation (realization dataSet)

literalRationalSU2BondCarrierLevel : ProofLevel
literalRationalSU2BondCarrierLevel = machineChecked

literalRationalSU2PlaquetteHolonomyLevel : ProofLevel
literalRationalSU2PlaquetteHolonomyLevel = machineChecked

rationalSU2PathGaugeCancellationLevel : ProofLevel
rationalSU2PathGaugeCancellationLevel = machineChecked

rationalSU2ExactGroupLawInputsLevel : ProofLevel
rationalSU2ExactGroupLawInputsLevel = conditional

rationalSU2PeriodicStepInverseInputsLevel : ProofLevel
rationalSU2PeriodicStepInverseInputsLevel = conditional
