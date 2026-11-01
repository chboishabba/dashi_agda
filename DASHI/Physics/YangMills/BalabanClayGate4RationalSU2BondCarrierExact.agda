module DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Covariance
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as PeriodicGeometry
import DASHI.Physics.YangMills.BalabanClayGate4LiteralCubeBianchiExact as Cube
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- G. G. Batrouni,
-- "Plaquette Formulation and the Bianchi Identity for Lattice Gauge Theories",
-- Nuclear Physics B 208 (1982), 467--483.
-- DOI: 10.1016/0550-3213(82)90231-0.
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
    links : RationalSU2BondField n
    siteGauge : RationalSU2SiteGauge n

open RationalSU2BondData public

realization :
  ∀ {n} (dataSet : RationalSU2BondData n) →
  Bond.PeriodicBondGaugeRealization
    n SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
realization {n} dataSet =
  Covariance.literalPeriodicBondGaugeRealization
    Group.rationalSU2ExactLinkGroup
    (PeriodicGeometry.periodicStepInverseLaws n)
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
  ≡ Bond.multiply Group.rationalSU2ExactLinkGroup
      (Bond.multiply Group.rationalSU2ExactLinkGroup
        (siteGauge dataSet site)
        (Bond.pathHolonomy (realization dataSet) site directions))
      (Bond.inverse Group.rationalSU2ExactLinkGroup
        (siteGauge dataSet (Bond.walk site directions)))
rationalSU2PathGaugeCancellation dataSet =
  Bond.pathSiteGaugeCancellation (realization dataSet)

rationalSU2PlaquetteGaugeCancellation :
  ∀ {n} (dataSet : RationalSU2BondData n)
    (plaquette : Plaquette.PeriodicPlaquette n) →
  Bond.transformedPathHolonomy (realization dataSet)
    (Carrier.first plaquette)
    (Bond.plaquetteBoundaryDirections (Carrier.second plaquette))
  ≡ Bond.multiply Group.rationalSU2ExactLinkGroup
      (Bond.multiply Group.rationalSU2ExactLinkGroup
        (siteGauge dataSet (Carrier.first plaquette))
        (rationalSU2PlaquetteHolonomy dataSet plaquette))
      (Bond.inverse Group.rationalSU2ExactLinkGroup
        (siteGauge dataSet (Carrier.first plaquette)))
rationalSU2PlaquetteGaugeCancellation {n} dataSet =
  Bond.plaquetteGaugeCancellation
    (PeriodicGeometry.periodicPlaquetteClosure n)
    (realization dataSet)

rationalSU2CubeBianchi :
  ∀ {n} (dataSet : RationalSU2BondData n)
    site (axisA axisB axisC : Carrier.Axis4) →
  Bond.pathHolonomy (realization dataSet) site
    (Cube.cubeSixFaceBoundary axisA axisB axisC)
  ≡ Bond.identity Group.rationalSU2ExactLinkGroup
rationalSU2CubeBianchi {n} dataSet =
  Cube.literalCubeBianchi
    (PeriodicGeometry.periodicStepInverseLaws n)
    (realization dataSet)

literalRationalSU2BondCarrierLevel : ProofLevel
literalRationalSU2BondCarrierLevel = machineChecked

literalRationalSU2PlaquetteHolonomyLevel : ProofLevel
literalRationalSU2PlaquetteHolonomyLevel = machineChecked

rationalSU2PathGaugeCancellationLevel : ProofLevel
rationalSU2PathGaugeCancellationLevel = machineChecked

rationalSU2PlaquetteGaugeCancellationLevel : ProofLevel
rationalSU2PlaquetteGaugeCancellationLevel = machineChecked

rationalSU2CubeBianchiLevel : ProofLevel
rationalSU2CubeBianchiLevel = machineChecked

rationalSU2ExactGroupLawReuseLevel : ProofLevel
rationalSU2ExactGroupLawReuseLevel = Group.rationalSU2ExactGroupLawLevel

rationalSU2PeriodicGeometryReuseLevel : ProofLevel
rationalSU2PeriodicGeometryReuseLevel =
  PeriodicGeometry.literalPeriodicPlaquetteClosureLevel
