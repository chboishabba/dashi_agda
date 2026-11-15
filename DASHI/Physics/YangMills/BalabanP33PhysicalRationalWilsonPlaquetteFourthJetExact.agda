module DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteFourthJetExact where

------------------------------------------------------------------------
-- PHYSICAL SIDE-FOUR WILSON PLAQUETTE FOUR-JET
--
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10
-- (1974), 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Martin Lüscher and Peter Weisz, "Background field technique and
-- renormalization in lattice gauge theory", Nuclear Physics B 452 (1995),
-- 213--233. DOI: 10.1016/0550-3213(95)00346-T.
--
-- DASHI CONTRIBUTION
--
-- This is the source-native bridge from the actual side-four background and
-- physical bond field to the literal four-link Wilson jet.  It uses precisely
-- the six positive plaquette orientations and the same shifted links as the
-- existing physical Wilson Hessian.  Hence cubic and quartic vertices now
-- come from that same finite lattice carrier rather than from an unconnected
-- generic four-factor datum.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
open import Data.Rational.Base using (ℚ)
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Wilson2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonFourthJetExact as Wilson4
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonLinkExponentialFourthJetExact as Link4
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

physicalPositiveLinkJet4 :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Periodic.Site4 → Periodic.Axis4 → Wilson4.QuaternionFactorJet4
physicalPositiveLinkJet4 background bondField site axis =
  Link4.positiveLinkExponentialJet4
    (Physical.link background (pair site axis))
    (Wilson2.pureQuaternion (Physical.insertionAt bondField axis site))

physicalInverseLinkJet4 :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Periodic.Site4 → Periodic.Axis4 → Wilson4.QuaternionFactorJet4
physicalInverseLinkJet4 background bondField site axis =
  Link4.inverseLinkExponentialJet4
    (Physical.inverseLink background (pair site axis))
    (Wilson2.pureQuaternion (Physical.insertionAt bondField axis site))

physicalPlaquetteFourthJet :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → Wilson4.LiteralFourLinkWilsonFourthJet
physicalPlaquetteFourthJet background bondField (pair site axes) =
  let
    left = Physical.pairLeft axes
    right = Physical.pairRight axes
  in
  record
    { Wilson4.link0 = physicalPositiveLinkJet4 background bondField site left
    ; Wilson4.link1 = physicalPositiveLinkJet4 background bondField
        (Periodic.shiftForward left site) right
    ; Wilson4.link2 = physicalInverseLinkJet4 background bondField
        (Periodic.shiftForward right site) left
    ; Wilson4.link3 = physicalInverseLinkJet4 background bondField site right
    }

physicalPlaquetteWilsonCubicCoefficient :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → ℚ
physicalPlaquetteWilsonCubicCoefficient background bondField plaquette =
  Wilson4.wilsonCubicCoefficient
    (physicalPlaquetteFourthJet background bondField plaquette)

physicalPlaquetteWilsonQuarticCoefficient :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 → ℚ
physicalPlaquetteWilsonQuarticCoefficient background bondField plaquette =
  Wilson4.wilsonQuarticCoefficient
    (physicalPlaquetteFourthJet background bondField plaquette)

-- These are the actual finite-lattice Wilson vertices.  No translation-
-- invariant or infinite-volume replacement occurs at this stage.
physicalWilsonCubicVertex :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 → ℚ
physicalWilsonCubicVertex background bondField =
  Sums.sumRational Physical.plaquettes4
    (physicalPlaquetteWilsonCubicCoefficient background bondField)

physicalWilsonQuarticVertex :
  Physical.RationalSU2Background4 → Coordinates.PhysicalSU2BondField4 → ℚ
physicalWilsonQuarticVertex background bondField =
  Sums.sumRational Physical.plaquettes4
    (physicalPlaquetteWilsonQuarticCoefficient background bondField)

physicalSideFourWilsonFourthJetCarrierLevel : ProofLevel
-- This finite-volume producer awaits a focused check; it is not evidence for
-- the cutoff-uniform beta theorem by itself.
physicalSideFourWilsonFourthJetCarrierLevel = conditional

physicalSideFourWilsonCubicQuarticVertexLevel : ProofLevel
physicalSideFourWilsonCubicQuarticVertexLevel = conditional
