module DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
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
-- "Quarks, Gluons and Lattices", Cambridge University Press (1983).
-- DOI: 10.1017/CBO9780511622630.
------------------------------------------------------------------------

RationalSU2BondField : Nat → Set
RationalSU2BondField n =
  Bond.PeriodicBondField n SU2.RationalUnitQuaternion

RationalSU2SiteGauge : Nat → Set
RationalSU2SiteGauge n =
  Bond.PeriodicSiteGauge n SU2.RationalUnitQuaternion

record RationalSU2BondRealization (n : Nat) : Set₁ where
  field
    exactGroup : Bond.ExactLinkGroup SU2.RationalUnitQuaternion
    realization :
      Bond.PeriodicBondGaugeRealization
        n SU2.RationalUnitQuaternion exactGroup

open RationalSU2BondRealization public

rationalSU2Links : ∀ {n} → RationalSU2BondRealization n → RationalSU2BondField n
rationalSU2Links dataSet = Bond.bondField (realization dataSet)

rationalSU2SiteGauge : ∀ {n} → RationalSU2BondRealization n → RationalSU2SiteGauge n
rationalSU2SiteGauge dataSet = Bond.gauge (realization dataSet)

rationalSU2PlaquetteHolonomy :
  ∀ {n} (dataSet : RationalSU2BondRealization n) →
  Plaquette.PeriodicPlaquette n → SU2.RationalUnitQuaternion
rationalSU2PlaquetteHolonomy dataSet =
  Bond.plaquetteHolonomyFromBonds (realization dataSet)

rationalSU2PathGaugeCancellation :
  ∀ {n} (dataSet : RationalSU2BondRealization n) site directions →
  Bond.transformedPathHolonomy (realization dataSet) site directions
  ≡ Bond.multiply (exactGroup dataSet)
      (Bond.multiply (exactGroup dataSet)
        (rationalSU2SiteGauge dataSet site)
        (Bond.pathHolonomy (realization dataSet) site directions))
      (Bond.inverse (exactGroup dataSet)
        (rationalSU2SiteGauge dataSet (Bond.walk site directions)))
rationalSU2PathGaugeCancellation dataSet =
  Bond.pathSiteGaugeCancellation (realization dataSet)

literalRationalSU2BondCarrierLevel : ProofLevel
literalRationalSU2BondCarrierLevel = machineChecked

literalRationalSU2PlaquetteHolonomyLevel : ProofLevel
literalRationalSU2PlaquetteHolonomyLevel = machineChecked

rationalSU2PathGaugeCancellationLevel : ProofLevel
rationalSU2PathGaugeCancellationLevel = machineChecked

-- Propositional equality of the proof-carrying rational-unit-quaternion record
-- and covariance of negative-oriented links still require the exact group-law
-- inhabitant recorded by BalabanClayGate4PeriodicBondPathBianchiExact.
rationalSU2ExactGroupLawInputsLevel : ProofLevel
rationalSU2ExactGroupLawInputsLevel = conditional
