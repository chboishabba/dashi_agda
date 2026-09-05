module DASHI.Physics.Plasma.MHDDoubledInductionKernelNormalFormExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

------------------------------------------------------------------------
-- DIVISION-FREE ELSASSER -> INDUCTION KERNEL NORMAL FORM
--
-- Let
--
--   U~ = z+ + z-
--   B~ = z+ - z-.
--
-- The ordered difference appearing in the doubled magnetic tangent is
--
--   (z-_p . q) z+_q - (z+_p . q) z-_q.
--
-- Without dividing by two, twice this object is exactly
--
--   (U~_p . q) B~_q - (B~_p . q) U~_q.
--
-- This is the literal Fourier induction kernel in doubled coordinates.  The
-- theorem is pure commutative-field algebra and does not add PDE authority.
------------------------------------------------------------------------

private
  two : ∀ {r : Level} {F : C3.RealField r} → C3.Complex F
  two {F = F} = C3.complexAdd (C3.complexOne F) (C3.complexOne F)

  sub : ∀ {r : Level} {F : C3.RealField r} →
    C3.Complex F → C3.Complex F → C3.Complex F
  sub = C3.complexSubtract

orderedElsasserInductionScalar :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F
orderedElsasserInductionScalar zmP zpP zmQ zpQ =
  sub
    (C3.complexMultiply zmP zpQ)
    (C3.complexMultiply zpP zmQ)

doubledVelocityScalar :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F
doubledVelocityScalar = C3.complexAdd

doubledMagneticScalar :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F
doubledMagneticScalar = C3.complexSubtract

doubledInductionScalar :
  ∀ {r : Level} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F
doubledInductionScalar {F = F} zpP zmP zpQ zmQ =
  C3.complexSubtract
    (C3.complexMultiply
      (doubledVelocityScalar zpP zmP)
      (doubledMagneticScalar zpQ zmQ))
    (C3.complexMultiply
      (doubledMagneticScalar zpP zmP)
      (doubledVelocityScalar zpQ zmQ))

orderedElsasserDifferenceDoublesToInduction :
  ∀ {r : Level} {F : C3.RealField r}
    (zpP zmP zpQ zmQ : C3.Complex F) →
  C3.complexMultiply two
    (orderedElsasserInductionScalar zmP zpP zmQ zpQ)
  ≡ doubledInductionScalar zpP zmP zpQ zmQ
orderedElsasserDifferenceDoublesToInduction {F = F} zpP zmP zpQ zmQ =
  R.solve 4
    (λ zpP zmP zpQ zmQ →
      (((R.Κ (C3.complexOne F) R.⊕ R.Κ (C3.complexOne F))
        R.⊗ ((zmP R.⊗ zpQ) R.⊕ (R.⊝ (zpP R.⊗ zmQ))))
      R.⊜
      ((((zpP R.⊕ zmP) R.⊗ (zpQ R.⊕ (R.⊝ zmQ)))
        R.⊕
        (R.⊝ ((zpP R.⊕ (R.⊝ zmP)) R.⊗ (zpQ R.⊕ zmQ))))))
    refl zpP zmP zpQ zmQ
  where module R = Field.Solver F

record DoubledInductionKernelBoundary : Set where
  constructor doubled-induction-kernel-boundary
  field
    noHalfInverseIntroduced : Bool
    noHalfInverseIntroducedIsTrue : noHalfInverseIntroduced ≡ true

    elsasserDifferenceIsInductionKernelAfterDoubling : Bool
    elsasserDifferenceIsInductionKernelAfterDoublingIsTrue :
      elsasserDifferenceIsInductionKernelAfterDoubling ≡ true

    kernelIdentityAloneProvesMagneticHelicityConservation : Bool
    kernelIdentityAloneProvesMagneticHelicityConservationIsFalse :
      kernelIdentityAloneProvesMagneticHelicityConservation ≡ false

canonicalDoubledInductionKernelBoundary : DoubledInductionKernelBoundary
canonicalDoubledInductionKernelBoundary =
  doubled-induction-kernel-boundary true refl true refl false refl
