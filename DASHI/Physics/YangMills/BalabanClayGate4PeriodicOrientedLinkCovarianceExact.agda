module DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Axis4; pair)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
------------------------------------------------------------------------

record PeriodicStepInverseLaws (n : Nat) : Set₁ where
  field
    positiveAfterNegative : ∀ site axis →
      Bond.positiveStep (Bond.negativeStep site axis) axis ≡ site
    negativeAfterPositive : ∀ site axis →
      Bond.negativeStep (Bond.positiveStep site axis) axis ≡ site

open PeriodicStepInverseLaws public

inverseGaugeTransformedLink :
  ∀ {Value} (group : Bond.ExactLinkGroup Value)
    gaugeAtStart link gaugeAtFinish →
  Bond.inverse group
    (Bond.multiply group
      (Bond.multiply group gaugeAtStart link)
      (Bond.inverse group gaugeAtFinish))
  ≡ Bond.multiply group
      (Bond.multiply group gaugeAtFinish (Bond.inverse group link))
      (Bond.inverse group gaugeAtStart)
inverseGaugeTransformedLink group gaugeAtStart link gaugeAtFinish =
  trans
    (Bond.inverseProduct group
      (Bond.multiply group gaugeAtStart link)
      (Bond.inverse group gaugeAtFinish))
    (trans
      (cong₂ (Bond.multiply group)
        (Bond.inverseInverse group gaugeAtFinish)
        (Bond.inverseProduct group gaugeAtStart link))
      (sym (Bond.multiplyAssociative group
        gaugeAtFinish (Bond.inverse group link)
        (Bond.inverse group gaugeAtStart))))

negativeOrientedLinkGaugeCovariant :
  ∀ {n Value}
    (group : Bond.ExactLinkGroup Value)
    (stepLaws : PeriodicStepInverseLaws n)
    (links : Bond.PeriodicBondField n Value)
    (gauge : Bond.PeriodicSiteGauge n Value)
    site axis →
  Bond.inverse group
    (Bond.multiply group
      (Bond.multiply group
        (gauge (Bond.negativeStep site axis))
        (links (pair (Bond.negativeStep site axis) axis)))
      (Bond.inverse group
        (gauge (Bond.positiveStep (Bond.negativeStep site axis) axis))))
  ≡ Bond.multiply group
      (Bond.multiply group
        (gauge site)
        (Bond.inverse group
          (links (pair (Bond.negativeStep site axis) axis))))
      (Bond.inverse group (gauge (Bond.negativeStep site axis)))
negativeOrientedLinkGaugeCovariant group stepLaws links gauge site axis =
  trans
    (inverseGaugeTransformedLink group
      (gauge (Bond.negativeStep site axis))
      (links (pair (Bond.negativeStep site axis) axis))
      (gauge (Bond.positiveStep (Bond.negativeStep site axis) axis)))
    (cong
      (λ endpoint → Bond.multiply group
        (Bond.multiply group
          (gauge endpoint)
          (Bond.inverse group
            (links (pair (Bond.negativeStep site axis) axis))))
        (Bond.inverse group (gauge (Bond.negativeStep site axis))))
      (positiveAfterNegative stepLaws site axis))

literalPeriodicBondGaugeRealization :
  ∀ {n Value}
    (group : Bond.ExactLinkGroup Value)
    (stepLaws : PeriodicStepInverseLaws n)
    (links : Bond.PeriodicBondField n Value)
    (gauge : Bond.PeriodicSiteGauge n Value) →
  Bond.PeriodicBondGaugeRealization n Value group
literalPeriodicBondGaugeRealization group stepLaws links gauge = record
  { Bond.PeriodicBondGaugeRealization.bondField = links
  ; Bond.PeriodicBondGaugeRealization.gauge = gauge
  ; Bond.PeriodicBondGaugeRealization.orientedLinkGaugeCovariant =
      λ { site (pair axis true) → refl
        ; site (pair axis false) →
            negativeOrientedLinkGaugeCovariant
              group stepLaws links gauge site axis
        }
  }

inverseGaugeTransformedLinkLevel : ProofLevel
inverseGaugeTransformedLinkLevel = machineChecked

negativeOrientedLinkGaugeCovarianceLevel : ProofLevel
negativeOrientedLinkGaugeCovarianceLevel = machineChecked

literalPeriodicBondGaugeRealizationLevel : ProofLevel
literalPeriodicBondGaugeRealizationLevel = machineChecked

-- The only remaining periodic-geometry input in this constructor is the exact
-- successor/predecessor inverse law for each cyclic coordinate.
periodicStepInverseLawInputsLevel : ProofLevel
periodicStepInverseLawInputsLevel = conditional
