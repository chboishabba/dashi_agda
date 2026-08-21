module DASHI.Analysis.RiemannComplexPoissonHermitianReductionExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Reduce the desired Hermitian full-grid norm identity to a COMPLEX BILINEAR
-- extension of the source's already-proved real Gabor Poisson theorem.
--
-- For a real even taper phi one expects
--
--   conjugate(phiHat z) = phiHat(-conjugate z) = phiHat(conjugate z).
--
-- Therefore
--
--   |phiHat(z-tau_k)|^2
--     = phiHat(z-tau_k) phiHat(conjugate(z)-tau_k),
--
-- and a bilinear complex Poisson identity
--
--   Sum_k phiHat(z-tau_k) phiHat(w-tau_k) = L Phi(z-w)
--
-- specialized to w=conjugate(z) gives
--
--   Sum_k |phiHat(z-tau_k)|^2 = L Phi(z-conjugate(z)).
--
-- At z=gamma-i alpha, z-conjugate(z)=-2i alpha.
--
-- Hence the Hermitian diagonal identity is NOT an independent analytic target.
-- The genuinely new Poisson step is the complex-parameter bilinear extension.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Abstract carrier: exact analytic objects remain source-owned.
------------------------------------------------------------------------

record ComplexPoissonHermitianCarrier : Set₁ where
  field
    Complex Scalar : Set

    conjugate : Complex → Complex
    difference : Complex → Complex → Complex

    GridIndex : Set
    tau : GridIndex → Complex

    phiHat : Complex → Complex
    phiKernel : Complex → Scalar
    scale : Scalar

    multiplyC : Complex → Complex → Complex
    normSquare : Complex → Complex
    scaleKernel : Scalar → Scalar → Scalar

    BilinearGridSum : Complex → Complex → Complex
    HermitianGridSum : Complex → Complex

open ComplexPoissonHermitianCarrier public

------------------------------------------------------------------------
-- Existing/small symmetry connection for a real-even taper.
------------------------------------------------------------------------

record RealEvenFourierSymmetry
  (c : ComplexPoissonHermitianCarrier) : Set₁ where
  field
    conjugatePhiHat :
      (z : Complex c) →
      Set

    evenPhiHat :
      (z : Complex c) →
      Set

    normSquareAsConjugateProduct :
      (z : Complex c) →
      normSquare c (phiHat c z)
        ≡ multiplyC c (phiHat c z) (phiHat c (conjugate c z))

------------------------------------------------------------------------
-- New analytic bridge: same bilinear Poisson theorem, complex parameters.
------------------------------------------------------------------------

record ComplexBilinearPoisson
  (c : ComplexPoissonHermitianCarrier) : Set₁ where
  field
    complexBilinearIdentity :
      (z w : Complex c) →
      Set

    bilinearAtConjugateIdentifiesHermitianGrid :
      (z : Complex c) →
      BilinearGridSum c z (conjugate c z)
        ≡ HermitianGridSum c z

    bilinearKernelAtConjugate :
      (z : Complex c) →
      Set

------------------------------------------------------------------------
-- The exact reduction is represented proof-relevantly: no caller may promote
-- a Hermitian norm identity unless it has both the real-even symmetry and the
-- complex bilinear Poisson witness.
------------------------------------------------------------------------

record HermitianPoissonFromBilinear
  (c : ComplexPoissonHermitianCarrier)
  (symmetry : RealEvenFourierSymmetry c)
  (poisson : ComplexBilinearPoisson c) : Set₁ where
  field
    HermitianPoissonIdentity : Complex c → Set
    deriveHermitianIdentity :
      (z : Complex c) → HermitianPoissonIdentity z

------------------------------------------------------------------------
-- Signed-coordinate specialization.  This is purely geometric and records the
-- already-known difference/sum channel split without pretending to build the
-- analytic identity.
------------------------------------------------------------------------

record CentredConjugateDisplacement : Set₁ where
  field
    Complex Signed : Set
    centred : Signed → Signed → Complex
    conjugate : Complex → Complex
    difference : Complex → Complex → Complex
    imaginaryDoubleNegative : Signed → Complex

    centredMinusConjugate :
      (gamma alpha : Signed) →
      difference
        (centred gamma alpha)
        (conjugate (centred gamma alpha))
        ≡ imaginaryDoubleNegative alpha

record ComplexPoissonHermitianReductionBoundary : Set where
  field
    hermitianNormReducedToBilinearConjugatePair : Bool
    signedDiagonalArgumentReducedToMinusTwoIAlpha : Bool
    realEvenFourierSymmetrySourceExpected : Bool
    sourceRealBilinearPoissonOwned : Bool
    complexBilinearPoissonExtensionProvedHere : Bool
    analyticHermitianNormIdentityInstantiatedHere : Bool

complexPoissonHermitianReductionBoundary :
  ComplexPoissonHermitianReductionBoundary
complexPoissonHermitianReductionBoundary = record
  { hermitianNormReducedToBilinearConjugatePair = true
  ; signedDiagonalArgumentReducedToMinusTwoIAlpha = true
  ; realEvenFourierSymmetrySourceExpected = true
  ; sourceRealBilinearPoissonOwned = true
  ; complexBilinearPoissonExtensionProvedHere = false
  ; analyticHermitianNormIdentityInstantiatedHere = false
  }
