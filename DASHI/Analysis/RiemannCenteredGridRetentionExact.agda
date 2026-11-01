module DASHI.Analysis.RiemannCenteredGridRetentionExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Preferred G1 finite-coordinate geometry.
--
-- Choose the source height T to equal the ordinate gamma of the hypothetical
-- zero.  Then tau_0=T=gamma and
--
--   z - tau_k = -k h - i alpha.
--
-- For a real-even taper, complex Fourier symmetry gives conjugate/reflection
-- pairing of the k and -k samples.  In particular their imaginary parts have
-- opposite sign and equal square, while the k=0 sample phiHat(-i alpha) is
-- real.  Therefore the full imaginary-channel energy has the shape
--
--   B_full = 2 * sum_{k>=1} b_k^2,
--
-- whereas the source matrix uses the one-sided finite coordinates
--
--   B_fin = sum_{1<=k<d} b_k^2.
--
-- Hence
--
--   B_full = 2 * (B_fin + B_tail),
--
-- and a bound on the far positive lattice tail k>=d immediately retains a
-- positive fraction of the transverse channel in the exact `Fin d` matrix.
--
-- This module closes that algebra.  The analytic producer still has to supply
-- the actual source-grid tail from the existing strip estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

------------------------------------------------------------------------
-- The analytic symmetry has already been reduced upstream to a scalar energy
-- decomposition.  We keep no unsupported assertion about actual phiHat here.
------------------------------------------------------------------------

record CenteredImaginaryGridLedger : Set where
  constructor centeredImaginaryGridLedger
  field
    finitePositiveImaginaryEnergy : Nat
    omittedPositiveImaginaryTail : Nat
    fullImaginaryEnergy : Nat

    reflectionEnergyDecomposition :
      fullImaginaryEnergy
        ≡ 2 * (finitePositiveImaginaryEnergy + omittedPositiveImaginaryTail)

open CenteredImaginaryGridLedger public

record CenteredGridTailDomination
  (g : CenteredImaginaryGridLedger) : Set where
  constructor centeredGridTailDomination
  field
    retainedMargin : Nat
    tailPlusMarginIsFinite :
      omittedPositiveImaginaryTail g + retainedMargin
        ≡ finitePositiveImaginaryEnergy g

open CenteredGridTailDomination public

------------------------------------------------------------------------
-- Exact retained-energy consequence:
--
-- full = 2(fin+tail), tail+margin=fin
--       = 4 tail + 2 margin.
--
-- Thus any nonzero full transverse energy cannot disappear in the finite
-- one-sided grid once the tail is strictly dominated.
------------------------------------------------------------------------

record CenteredFiniteRetentionCertificate
  (g : CenteredImaginaryGridLedger) : Set where
  constructor centeredFiniteRetentionCertificate
  field
    tailEnergy : Nat
    margin : Nat
    fullEnergyAsFourTailPlusTwoMargin :
      fullImaginaryEnergy g ≡ 4 * tailEnergy + 2 * margin
    finiteEnergyAsTailPlusMargin :
      finitePositiveImaginaryEnergy g ≡ tailEnergy + margin

centeredTailDominationImpliesRetention :
  (g : CenteredImaginaryGridLedger) →
  CenteredGridTailDomination g →
  CenteredFiniteRetentionCertificate g
centeredTailDominationImpliesRetention g h =
  centeredFiniteRetentionCertificate
    (omittedPositiveImaginaryTail g)
    (retainedMargin h)
    fullRewrite
    (sym (tailPlusMarginIsFinite h))
  where
  fullRewrite :
    fullImaginaryEnergy g
      ≡ 4 * omittedPositiveImaginaryTail g + 2 * retainedMargin h
  fullRewrite
    rewrite reflectionEnergyDecomposition g
          | sym (tailPlusMarginIsFinite h) = refl

------------------------------------------------------------------------
-- Actual source-facing geometric ingredients.
------------------------------------------------------------------------

record TargetCenteredGridProducer : Set₁ where
  field
    ZeroPair : Set

    sourceHeight : ZeroPair → Set
    targetOrdinate : ZeroPair → Set
    sourceHeightEqualsTargetOrdinate :
      (rho : ZeroPair) → Set

    plusMinusSampleConjugation :
      (rho : ZeroPair) → Set
    zeroSampleIsReal :
      (rho : ZeroPair) → Set

    centeredLedger :
      (rho : ZeroPair) → CenteredImaginaryGridLedger

    positiveLatticeTailBound :
      (rho : ZeroPair) →
      CenteredGridTailDomination (centeredLedger rho)

producerCenteredFiniteRetention :
  (p : TargetCenteredGridProducer) →
  (rho : TargetCenteredGridProducer.ZeroPair p) →
  CenteredFiniteRetentionCertificate
    (TargetCenteredGridProducer.centeredLedger p rho)
producerCenteredFiniteRetention p rho =
  centeredTailDominationImpliesRetention
    (TargetCenteredGridProducer.centeredLedger p rho)
    (TargetCenteredGridProducer.positiveLatticeTailBound p rho)
