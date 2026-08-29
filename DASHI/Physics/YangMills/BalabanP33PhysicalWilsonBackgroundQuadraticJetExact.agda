module DASHI.Physics.YangMills.BalabanP33PhysicalWilsonBackgroundQuadraticJetExact where

------------------------------------------------------------------------
-- ROW A1: PHYSICAL SU(2) BACKGROUND DERIVATIVE OF THE WILSON HESSIAN
--
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
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the generic mixed s t^2 quaternion product jet on the SAME
-- physical side-four SU(2) carrier used by the existing Wilson Hessian.
--
-- Positive oriented link convention:
--
--   U_b(s,t) = U_b exp(s Y_b) exp(t X_b).
--
-- Hence at (s,t)=(0,0):
--
--   value = U,
--   s     = U Y,
--   t     = U X,
--   tt    = U X^2,
--   st    = U Y X,
--   stt   = U Y X^2.
--
-- For an inverse occurrence,
--
--   U_b(s,t)^-1 = exp(-t X_b) exp(-s Y_b) U_b^-1,
--
-- giving
--
--   value = U^-1,
--   s     = -Y U^-1,
--   t     = -X U^-1,
--   tt    = X^2 U^-1,
--   st    = X Y U^-1,
--   stt   = -X^2 Y U^-1.
--
-- The fluctuation-only projection is definitionally the existing physical
-- right-exponential two-jet.  Thus this module genuinely extends, rather than
-- replaces, the already machine-checked Wilson Hessian carrier.
--
-- SOURCE-TRIVIALIZATION BOUNDARY
--
-- CMP99 writes its local background expansion in its own left/right group
-- convention.  The identification of this repository-native right-exponential
-- mixed jet with CMP99's printed D_background Delta is therefore kept as a
-- separate conditional theorem below; it is not silently assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair; Axis4)
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge4
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonJetExact as Jet
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonBackgroundQuadraticJetExact as Mixed
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

------------------------------------------------------------------------
-- Physical link mixed jets.
------------------------------------------------------------------------

positiveLinkBackgroundQuadraticJet :
  Plaquette.RationalSU2Background4 →
  Physical.PhysicalSU2BondField4 →
  Physical.PhysicalSU2BondField4 →
  Hodge4.Site4 → Axis4 →
  Mixed.QuaternionBackgroundQuadraticFactorJet
positiveLinkBackgroundQuadraticJet
    background backgroundField fluctuationField site axis =
  let
    u = Plaquette.link background (pair site axis)
    y = Jet.pureQuaternion
      (Plaquette.insertionAt backgroundField axis site)
    x = Jet.pureQuaternion
      (Plaquette.insertionAt fluctuationField axis site)
  in
  Mixed.mixedFactorJet
    u
    (u Jet.*q y)
    (u Jet.*q x)
    (u Jet.*q (x Jet.*q x))
    (u Jet.*q (y Jet.*q x))
    (u Jet.*q (y Jet.*q (x Jet.*q x)))

inverseLinkBackgroundQuadraticJet :
  Plaquette.RationalSU2Background4 →
  Physical.PhysicalSU2BondField4 →
  Physical.PhysicalSU2BondField4 →
  Hodge4.Site4 → Axis4 →
  Mixed.QuaternionBackgroundQuadraticFactorJet
inverseLinkBackgroundQuadraticJet
    background backgroundField fluctuationField site axis =
  let
    uInv = Plaquette.inverseLink background (pair site axis)
    y = Jet.pureQuaternion
      (Plaquette.insertionAt backgroundField axis site)
    x = Jet.pureQuaternion
      (Plaquette.insertionAt fluctuationField axis site)
  in
  Mixed.mixedFactorJet
    uInv
    (Jet.negQ y Jet.*q uInv)
    (Jet.negQ x Jet.*q uInv)
    ((x Jet.*q x) Jet.*q uInv)
    ((x Jet.*q y) Jet.*q uInv)
    (Jet.negQ ((x Jet.*q x) Jet.*q y) Jet.*q uInv)

------------------------------------------------------------------------
-- Regression to the existing physical t^2 Wilson jet.
------------------------------------------------------------------------

forgetBackground :
  Mixed.QuaternionBackgroundQuadraticFactorJet → Jet.QuaternionFactorJet
forgetBackground factor =
  Jet.factorJet
    (Mixed.factorValue factor)
    (Mixed.factorFluctuation factor)
    (Mixed.factorFluctuationSecond factor)

positiveFluctuationProjectionExact :
  ∀ background backgroundField fluctuationField site axis →
  forgetBackground
    (positiveLinkBackgroundQuadraticJet
      background backgroundField fluctuationField site axis)
  ≡ Plaquette.positiveLinkJet background fluctuationField site axis
positiveFluctuationProjectionExact
    background backgroundField fluctuationField site axis = refl

inverseFluctuationProjectionExact :
  ∀ background backgroundField fluctuationField site axis →
  forgetBackground
    (inverseLinkBackgroundQuadraticJet
      background backgroundField fluctuationField site axis)
  ≡ Plaquette.inverseLinkJet background fluctuationField site axis
inverseFluctuationProjectionExact
    background backgroundField fluctuationField site axis = refl

------------------------------------------------------------------------
-- Four-link physical plaquette mixed jet.
------------------------------------------------------------------------

plaquetteBackgroundQuadraticFactorJets :
  Plaquette.RationalSU2Background4 →
  Physical.PhysicalSU2BondField4 →
  Physical.PhysicalSU2BondField4 →
  Plaquette.Plaquette4 →
  List Mixed.QuaternionBackgroundQuadraticFactorJet
plaquetteBackgroundQuadraticFactorJets
    background backgroundField fluctuationField (pair site axes) =
  let
    left = Plaquette.pairLeft axes
    right = Plaquette.pairRight axes
  in
  Mixed.fourFactorJets
    (positiveLinkBackgroundQuadraticJet
      background backgroundField fluctuationField site left)
    (positiveLinkBackgroundQuadraticJet
      background backgroundField fluctuationField
      (Hodge4.shiftForward left site) right)
    (inverseLinkBackgroundQuadraticJet
      background backgroundField fluctuationField
      (Hodge4.shiftForward right site) left)
    (inverseLinkBackgroundQuadraticJet
      background backgroundField fluctuationField site right)

plaquetteWilsonBackgroundQuadraticVariation :
  Plaquette.RationalSU2Background4 →
  Physical.PhysicalSU2BondField4 →
  Physical.PhysicalSU2BondField4 →
  Plaquette.Plaquette4 → ℚ
plaquetteWilsonBackgroundQuadraticVariation
    background backgroundField fluctuationField plaquette =
  Mixed.wilsonBackgroundFluctuationSecondNumerator
    (plaquetteBackgroundQuadraticFactorJets
      background backgroundField fluctuationField plaquette)

plaquetteWilsonBackgroundQuadraticAtomSum :
  Plaquette.RationalSU2Background4 →
  Physical.PhysicalSU2BondField4 →
  Physical.PhysicalSU2BondField4 →
  Plaquette.Plaquette4 → ℚ
plaquetteWilsonBackgroundQuadraticAtomSum
    background backgroundField fluctuationField plaquette =
  Mixed.wilsonBackgroundFluctuationSecondAtomSum
    (plaquetteBackgroundQuadraticFactorJets
      background backgroundField fluctuationField plaquette)

plaquetteWilsonBackgroundQuadraticIs64Atoms :
  ∀ background backgroundField fluctuationField plaquette →
  plaquetteWilsonBackgroundQuadraticVariation
    background backgroundField fluctuationField plaquette
  ≡ plaquetteWilsonBackgroundQuadraticAtomSum
      background backgroundField fluctuationField plaquette
plaquetteWilsonBackgroundQuadraticIs64Atoms
    background backgroundField fluctuationField plaquette =
  Mixed.wilsonBackgroundFluctuationSecondIsAtomSum
    (plaquetteBackgroundQuadraticFactorJets
      background backgroundField fluctuationField plaquette)

plaquetteWilsonBackgroundQuadraticAtomCountExact :
  ∀ background backgroundField fluctuationField site axes →
  length
    (Mixed.backgroundFluctuationSecondTerms
      (plaquetteBackgroundQuadraticFactorJets
        background backgroundField fluctuationField (pair site axes)))
  ≡ 64
plaquetteWilsonBackgroundQuadraticAtomCountExact
    background backgroundField fluctuationField site axes = refl

------------------------------------------------------------------------
-- Full finite side-four Wilson mixed variation.
------------------------------------------------------------------------

physicalWilsonBackgroundQuadraticVariation :
  Plaquette.RationalSU2Background4 →
  Physical.PhysicalSU2BondField4 →
  Physical.PhysicalSU2BondField4 → ℚ
physicalWilsonBackgroundQuadraticVariation
    background backgroundField fluctuationField =
  Sums.sumRational Plaquette.plaquettes4
    (plaquetteWilsonBackgroundQuadraticVariation
      background backgroundField fluctuationField)

physicalWilsonBackgroundQuadraticAtomSum :
  Plaquette.RationalSU2Background4 →
  Physical.PhysicalSU2BondField4 →
  Physical.PhysicalSU2BondField4 → ℚ
physicalWilsonBackgroundQuadraticAtomSum
    background backgroundField fluctuationField =
  Sums.sumRational Plaquette.plaquettes4
    (plaquetteWilsonBackgroundQuadraticAtomSum
      background backgroundField fluctuationField)

physicalWilsonBackgroundQuadraticIs64AtomPlaquetteSum :
  ∀ background backgroundField fluctuationField →
  physicalWilsonBackgroundQuadraticVariation
    background backgroundField fluctuationField
  ≡ physicalWilsonBackgroundQuadraticAtomSum
      background backgroundField fluctuationField
physicalWilsonBackgroundQuadraticIs64AtomPlaquetteSum
    background backgroundField fluctuationField =
  Sums.sumRationalCong
    Plaquette.plaquettes4
    (plaquetteWilsonBackgroundQuadraticVariation
      background backgroundField fluctuationField)
    (plaquetteWilsonBackgroundQuadraticAtomSum
      background backgroundField fluctuationField)
    (plaquetteWilsonBackgroundQuadraticIs64Atoms
      background backgroundField fluctuationField)

------------------------------------------------------------------------
-- Proof levels / remaining physical weld.
------------------------------------------------------------------------

physicalWilsonBackgroundQuadraticLinkJetLevel : ProofLevel
physicalWilsonBackgroundQuadraticLinkJetLevel = machineChecked

physicalWilsonBackgroundQuadratic64AtomLevel : ProofLevel
physicalWilsonBackgroundQuadratic64AtomLevel = machineChecked

-- Source-facing identification still required: show this right-exponential
-- mixed coefficient is exactly D_background of the existing physical Wilson
-- Hessian inside CMP99's quadratic operator A(U), including normalization and
-- the source's left/right trivialization convention.
cmp99WilsonHessianBackgroundDerivativeIdentificationLevel : ProofLevel
cmp99WilsonHessianBackgroundDerivativeIdentificationLevel = conditional
