module DASHI.Analysis.RiemannComplexPoissonHermitianReductionExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Reduce the desired Hermitian full-grid norm identity to a COMPLEX BILINEAR
-- extension of the source's already-proved real Gabor Poisson theorem.
--
-- For a real even taper phi:
--
--   conjugate(phiHat z) = phiHat(-conjugate z) = phiHat(conjugate z),
--
-- hence
--
--   |phiHat(z-tau_k)|^2
--     = phiHat(z-tau_k) phiHat(conjugate(z)-tau_k).
--
-- If the source bilinear identity is extended to complex parameters,
--
--   Sum_k phiHat(z-tau_k) phiHat(w-tau_k) = L Phi(z-w),
--
-- then setting w=conjugate(z) yields the Hermitian norm identity immediately.
-- At z=gamma-i alpha, z-conjugate(z)=-2i alpha.
--
-- The final Hermitian equality is DERIVED below; it is not another producer
-- field.  The new analytic Poisson gap is therefore precisely the complex
-- bilinear extension plus the standard real-even Fourier symmetry needed to
-- identify the norm-square sum with the conjugate-pair bilinear sum.
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

------------------------------------------------------------------------
-- Real/even taper symmetry, already expected from the source definition of
-- paperFT.  The only equality the later proof actually needs is the aggregate
-- consequence identifying the norm-square grid with the bilinear grid at the
-- conjugate parameter.
------------------------------------------------------------------------

record RealEvenFourierGridSymmetry
  (c : ComplexPoissonHermitianCarrier) : Set₁ where
  field
    hermitianGridIsConjugateBilinearGrid :
      (z : Complex c) →
      hermitianGridSum c z
        ≡ bilinearGridSum c z (conjugate c z)

------------------------------------------------------------------------
-- The sole genuinely new Poisson continuation theorem required at this layer.
------------------------------------------------------------------------

record ComplexBilinearPoisson
  (c : ComplexPoissonHermitianCarrier) : Set₁ where
  field
    complexBilinearIdentity :
      (z w : Complex c) →
      bilinearGridSum c z w
        ≡ poissonKernelValue c (difference c z w)

------------------------------------------------------------------------
-- EXACT DERIVATION: Hermitian norm identity is not independent.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Signed-coordinate specialization.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Compose the two reductions: complex bilinear Poisson gives kernel at
-- z-conj(z), and signed-coordinate geometry rewrites that argument to -2iα.
------------------------------------------------------------------------

record SignedHermitianPoissonCarrier : Set₁ where
  field
    poisson : ComplexPoissonHermitianCarrier
    displacement : CentredConjugateDisplacement
    sameComplex :
      ComplexPoissonHermitianCarrier.Complex poisson
        ≡ CentredConjugateDisplacement.Complex displacement

record ComplexPoissonHermitianReductionBoundary : Set where
  field
    hermitianNormEqualityDerivedFromBilinearEquality : Bool
    signedDiagonalArgumentReducedToMinusTwoIAlpha : Bool
    sourceRealBilinearPoissonOwned : Bool
    sourceComplexPhiHatDefinitionAndDecayOwned : Bool
    realEvenFourierGridSymmetryProvedHere : Bool
    complexBilinearPoissonExtensionProvedHere : Bool
    analyticMinusTwoIAlphaIdentityInstantiatedHere : Bool

complexPoissonHermitianReductionBoundary :
  ComplexPoissonHermitianReductionBoundary
complexPoissonHermitianReductionBoundary = record
  { hermitianNormEqualityDerivedFromBilinearEquality = true
  ; signedDiagonalArgumentReducedToMinusTwoIAlpha = true
  ; sourceRealBilinearPoissonOwned = true
  ; sourceComplexPhiHatDefinitionAndDecayOwned = true
  ; realEvenFourierGridSymmetryProvedHere = false
  ; complexBilinearPoissonExtensionProvedHere = false
  ; analyticMinusTwoIAlphaIdentityInstantiatedHere = false
  }
