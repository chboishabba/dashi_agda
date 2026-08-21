module DASHI.Analysis.RiemannComplexPoissonHermitianReductionExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Reduce the desired Hermitian full-grid norm identity to a COMPLEX BILINEAR
-- extension of the source's already-proved real Gabor Poisson theorem.
--
-- Source-owned facts in `Zeta23/Taper/Fourier.lean`:
--
--   conj h_v(z) = h_v(-conj z)     for real v,
--   h_v(-z) = h_v(z)               for even v,
--
-- hence for the real-even taper phi:
--
--   conj(phiHat z) = phiHat(conj z).
--
-- Therefore
--
--   |phiHat(z-tau_k)|^2
--     = phiHat(z-tau_k) phiHat(conjugate(z)-tau_k).
--
-- If the source bilinear Poisson theorem is extended from real to complex
-- parameters,
--
--   Sum_k phiHat(z-tau_k) phiHat(w-tau_k) = L Phi(z-w),
--
-- then setting w=conjugate(z) yields the Hermitian norm identity immediately.
-- At z=gamma-i alpha, z-conjugate(z)=-2i alpha.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

record ComplexPoissonHermitianCarrier : Set₁ where
  field
    Complex Value : Set
    conjugate : Complex → Complex
    difference : Complex → Complex → Complex
    bilinearGridSum : Complex → Complex → Value
    hermitianGridSum : Complex → Value
    poissonKernelValue : Complex → Value

open ComplexPoissonHermitianCarrier public

record RealEvenFourierGridSymmetry
  (c : ComplexPoissonHermitianCarrier) : Set₁ where
  field
    hermitianGridIsConjugateBilinearGrid :
      (z : Complex c) →
      hermitianGridSum c z
        ≡ bilinearGridSum c z (conjugate c z)

record ComplexBilinearPoisson
  (c : ComplexPoissonHermitianCarrier) : Set₁ where
  field
    complexBilinearIdentity :
      (z w : Complex c) →
      bilinearGridSum c z w
        ≡ poissonKernelValue c (difference c z w)

hermitianPoissonFromComplexBilinear :
  (c : ComplexPoissonHermitianCarrier) →
  RealEvenFourierGridSymmetry c →
  ComplexBilinearPoisson c →
  (z : Complex c) →
  hermitianGridSum c z
    ≡ poissonKernelValue c (difference c z (conjugate c z))
hermitianPoissonFromComplexBilinear c symmetry poisson z =
  trans
    (RealEvenFourierGridSymmetry.hermitianGridIsConjugateBilinearGrid
      symmetry z)
    (ComplexBilinearPoisson.complexBilinearIdentity
      poisson z (conjugate c z))

record CentredConjugateDisplacement : Set₁ where
  field
    Complex Signed : Set
    centred : Signed → Signed → Complex
    conjugate : Complex → Complex
    difference : Complex → Complex → Complex
    minusTwoI : Signed → Complex

    centredMinusConjugate :
      (gamma alpha : Signed) →
      difference
        (centred gamma alpha)
        (conjugate (centred gamma alpha))
        ≡ minusTwoI alpha

record ComplexPoissonHermitianReductionBoundary : Set where
  field
    hermitianNormEqualityDerivedFromBilinearEquality : Bool
    signedDiagonalArgumentReducedToMinusTwoIAlpha : Bool
    sourceRealBilinearPoissonOwned : Bool
    sourceComplexPhiHatDefinitionAndDecayOwned : Bool
    sourceRealEvenFourierConjugationOwned : Bool
    complexBilinearPoissonExtensionProvedHere : Bool
    analyticMinusTwoIAlphaIdentityInstantiatedHere : Bool

complexPoissonHermitianReductionBoundary :
  ComplexPoissonHermitianReductionBoundary
complexPoissonHermitianReductionBoundary = record
  { hermitianNormEqualityDerivedFromBilinearEquality = true
  ; signedDiagonalArgumentReducedToMinusTwoIAlpha = true
  ; sourceRealBilinearPoissonOwned = true
  ; sourceComplexPhiHatDefinitionAndDecayOwned = true
  ; sourceRealEvenFourierConjugationOwned = true
  ; complexBilinearPoissonExtensionProvedHere = false
  ; analyticMinusTwoIAlphaIdentityInstantiatedHere = false
  }
