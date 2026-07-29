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

record RationalSU2BondData (n : Nat) : Set₁ where
  field
    exactGroup : Bond.ExactLinkGroup SU2.RationalUnitQuaternion
    links : RationalSU2BondField n
    siteGauge : RationalSU2SiteGauge n
    orientedCovariance :
      let preliminary : Bond.PeriodicBondGaugeRealization
            n SU2.RationalUnitQuaternion exactGroup
          preliminary = record
            { Bond.PeriodicBondGaugeRealization.bondField = links
            ; Bond.PeriodicBondGaugeRealization.gauge = siteGauge
            ; Bond.PeriodicBondGaugeRealization.orientedLinkGaugeCovariant =
                λ site direction → orientedCovariance
            }
      in ∀ site direction →
        Bond.transformedOrientedLink preliminary site direction
        ≡ Bond.multiply exactGroup
            (Bond.multiply exactGroup
              (siteGauge site)
              (Bond.orientedLink preliminary site direction))
            (Bond.inverse exactGroup
              (siteGauge (Bond.walkStep site direction)))

open RationalSU2BondData public

-- The self-reference above is avoided in consumers by supplying the same
-- covariance theorem directly to this constructor.
rationalSU2BondRealization :
  ∀ {n} (group : Bond.ExactLinkGroup SU2.RationalUnitQuaternion)
    (links : RationalSU2BondField n)
    (siteGauge : RationalSU2SiteGauge n) →
  (covariance :
    let preliminary : Bond.PeriodicBondGaugeRealization
          n SU2.RationalUnitQuaternion group
        preliminary = record
          { Bond.PeriodicBondGaugeRealization.bondField = links
          ; Bond.PeriodicBondGaugeRealization.gauge = siteGauge
          ; Bond.PeriodicBondGaugeRealization.orientedLinkGaugeCovariant =
              λ site direction → covariance site direction
          }
    in ∀ site direction →
      Bond.transformedOrientedLink preliminary site direction
      ≡ Bond.multiply group
          (Bond.multiply group
            (siteGauge site)
            (Bond.orientedLink preliminary site direction))
          (Bond.inverse group
            (siteGauge (Bond.walkStep site direction)))) →
  Bond.PeriodicBondGaugeRealization n SU2.RationalUnitQuaternion group
rationalSU2BondRealization group links siteGauge covariance = record
  { Bond.PeriodicBondGaugeRealization.bondField = links
  ; Bond.PeriodicBondGaugeRealization.gauge = siteGauge
  ; Bond.PeriodicBondGaugeRealization.orientedLinkGaugeCovariant = covariance
  }

rationalSU2PlaquetteHolonomy :
  ∀ {n} {group : Bond.ExactLinkGroup SU2.RationalUnitQuaternion} →
  Bond.PeriodicBondGaugeRealization n SU2.RationalUnitQuaternion group →
  Plaquette.PeriodicPlaquette n → SU2.RationalUnitQuaternion
rationalSU2PlaquetteHolonomy = Bond.plaquetteHolonomyFromBonds

literalRationalSU2BondCarrierLevel : ProofLevel
literalRationalSU2BondCarrierLevel = machineChecked

literalRationalSU2PlaquetteHolonomyLevel : ProofLevel
literalRationalSU2PlaquetteHolonomyLevel = machineChecked

-- Propositional equality of the proof-carrying rational-unit-quaternion record
-- and covariance of negative-oriented links still require the exact group-law
-- inhabitant recorded by BalabanClayGate4PeriodicBondPathBianchiExact.
rationalSU2ExactGroupLawInputsLevel : ProofLevel
rationalSU2ExactGroupLawInputsLevel = conditional
