module DASHI.Algebra.VandermondeMomentNonCancellationExact where

------------------------------------------------------------------------
-- GENERIC MOMENT / VANDERMONDE NONCANCELLATION CORE
--
-- Duncan--Swisher Proposition 3.3 uses the finite moment map
--
--   (a_i)_i |-> (sum_i a_i alpha_i^k)_k
--
-- on distinct supersingular alpha_i.  The matrix is Vandermonde, hence
-- invertible; therefore a nonzero coefficient vector cannot have every moment
-- vanish.
--
-- This file isolates precisely the finite algebra needed downstream.  It does
-- NOT claim that an arbitrary transform is Vandermonde.  A source adapter must
-- supply the actual moment transform and a two-sided recovery map (or another
-- proof of invertibility).  Once supplied, noncancellation is derived.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import DASHI.Core.Prelude

record InvertibleMomentTransform
    {ℓc ℓm : Level}
    (CoefficientVector : Set ℓc)
    (MomentVector : Set ℓm) : Set (lsuc (ℓc ⊔ ℓm)) where
  field
    zeroCoefficient : CoefficientVector
    zeroMoment : MomentVector

    momentTransform : CoefficientVector → MomentVector
    recoverCoefficients : MomentVector → CoefficientVector

    recoverAfterMoments :
      (a : CoefficientVector) →
      recoverCoefficients (momentTransform a) ≡ a

    recoverZeroMoment :
      recoverCoefficients zeroMoment ≡ zeroCoefficient

open InvertibleMomentTransform public

momentsZeroForceCoefficientsZero :
  {ℓc ℓm : Level} →
  {C : Set ℓc} → {M : Set ℓm} →
  (T : InvertibleMomentTransform C M) →
  (a : C) →
  momentTransform T a ≡ zeroMoment T →
  a ≡ zeroCoefficient T
momentsZeroForceCoefficientsZero T a momentsZero =
  trans
    (sym (recoverAfterMoments T a))
    (trans
      (cong (recoverCoefficients T) momentsZero)
      (recoverZeroMoment T))

record NonzeroCoefficientVector
    {ℓc ℓm : Level}
    {C : Set ℓc} {M : Set ℓm}
    (T : InvertibleMomentTransform C M)
    (a : C) : Set ℓc where
  field
    nonzero : a ≡ zeroCoefficient T → ⊥

open NonzeroCoefficientVector public

nonzeroCoefficientsForceNonzeroMoments :
  {ℓc ℓm : Level} →
  {C : Set ℓc} → {M : Set ℓm} →
  (T : InvertibleMomentTransform C M) →
  (a : C) →
  NonzeroCoefficientVector T a →
  momentTransform T a ≡ zeroMoment T →
  ⊥
nonzeroCoefficientsForceNonzeroMoments T a nz momentsZero =
  nonzero nz (momentsZeroForceCoefficientsZero T a momentsZero)

------------------------------------------------------------------------
-- Source-facing name: an invertible moment transform together with the
-- declaration that it is the Vandermonde transform on distinct poles.
--
-- The mathematical work downstream uses the actual inverse, not the Boolean.
------------------------------------------------------------------------

record VandermondeMomentSeparation
    {ℓc ℓm : Level}
    (CoefficientVector : Set ℓc)
    (MomentVector : Set ℓm) : Set (lsuc (ℓc ⊔ ℓm)) where
  field
    transform : InvertibleMomentTransform CoefficientVector MomentVector
    distinctPoleVandermonde : Bool
    distinctPoleVandermondeIsTrue : distinctPoleVandermonde ≡ true

open VandermondeMomentSeparation public

vandermondeNoncancellation :
  {ℓc ℓm : Level} →
  {C : Set ℓc} → {M : Set ℓm} →
  (V : VandermondeMomentSeparation C M) →
  (a : C) →
  NonzeroCoefficientVector (transform V) a →
  momentTransform (transform V) a ≡ zeroMoment (transform V) →
  ⊥
vandermondeNoncancellation V a =
  nonzeroCoefficientsForceNonzeroMoments (transform V) a

record VandermondeMomentNonCancellationBoundary : Set where
  field
    finiteMomentTransformExplicit : Bool
    inverseCarriesActualProofLoad : Bool
    nonzeroImpliesNonzeroMomentDerived : Bool
    distinctPolesAloneDefinitionallyInvertible : Bool
    fieldSpecificVandermondeDeterminantProvedHere : Bool

canonicalVandermondeMomentNonCancellationBoundary :
  VandermondeMomentNonCancellationBoundary
canonicalVandermondeMomentNonCancellationBoundary = record
  { finiteMomentTransformExplicit = true
  ; inverseCarriesActualProofLoad = true
  ; nonzeroImpliesNonzeroMomentDerived = true
  ; distinctPolesAloneDefinitionallyInvertible = false
  ; fieldSpecificVandermondeDeterminantProvedHere = false
  }
