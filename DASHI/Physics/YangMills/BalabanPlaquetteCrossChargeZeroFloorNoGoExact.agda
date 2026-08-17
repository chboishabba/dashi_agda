module DASHI.Physics.YangMills.BalabanPlaquetteCrossChargeZeroFloorNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION / FRONTIER GUARD
--
-- The literal plaquette cross charge used by the selected Wilson estimate is
-- quadratic in the physical variation.  In particular it vanishes exactly on
-- the zero physical field.  Therefore a STRICTLY positive absolute charge
-- floor cannot be demanded on any selected-region carrier that still contains
-- the zero variation.
--
-- A legitimate G2 closure must instead do at least one of:
--   * normalize the selected variation;
--   * prove the selected variation is quantitatively nonzero and exclude zero;
--   * formulate the uniform estimates relative to the charge itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonIncidenceExact as Incidence
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q

zeroPhysicalField : Coordinates.PhysicalSU2BondField4
zeroPhysicalField coordinate bond = 0ℚ

zeroInsertionQuaternion : ∀ axis site →
  Gauge.insertionQuaternion zeroPhysicalField axis site ≡ Q.zeroQ
zeroInsertionQuaternion axis site = Q.quaternionExt
  (ℚRing.solve []) (ℚRing.solve []) (ℚRing.solve []) (ℚRing.solve [])

zeroLinkInsertionCharge : ∀ axis site →
  Incidence.linkInsertionCharge zeroPhysicalField axis site ≡ 0ℚ
zeroLinkInsertionCharge axis site
  rewrite zeroInsertionQuaternion axis site = ℚRing.solve []

zeroPlaquetteDiagonalCharge : ∀ left right site →
  Incidence.plaquetteDiagonalCharge zeroPhysicalField left right site ≡ 0ℚ
zeroPlaquetteDiagonalCharge left right site =
  trans
    (Incidence.plaquetteDiagonalChargeExpanded
      zeroPhysicalField left right site)
    (let
      left0 = zeroLinkInsertionCharge left site
      rightForward = zeroLinkInsertionCharge right (Periodic.shiftForward left site)
      leftForward = zeroLinkInsertionCharge left (Periodic.shiftForward right site)
      right0 = zeroLinkInsertionCharge right site
     in cong4 left0 rightForward leftForward right0)
  where
  cong4 : ∀ {a b c d : ℚ} →
    a ≡ 0ℚ → b ≡ 0ℚ → c ≡ 0ℚ → d ≡ 0ℚ →
    a + b + c + d ≡ 0ℚ
  cong4 refl refl refl refl = ℚRing.solve []

zeroPlaquetteCrossCharge : ∀ left right site →
  Incidence.plaquetteCrossCharge zeroPhysicalField left right site ≡ 0ℚ
zeroPlaquetteCrossCharge left right site =
  trans
    (Incidence.plaquetteCrossChargeIsThreeDiagonal
      zeroPhysicalField left right site)
    (trans
      (cong ((+ 3 / 1) *_) (zeroPlaquetteDiagonalCharge left right site))
      (ℚRing.solve []))

zeroPhysicalFieldHasZeroCrossChargeLevel : ProofLevel
zeroPhysicalFieldHasZeroCrossChargeLevel = machineChecked
