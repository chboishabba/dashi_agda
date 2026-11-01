module DASHI.Physics.SFGC.NonAbelian.DepthQuotientIso where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.SFGC.NonAbelian.GradedSFGCSite2D
open import DASHI.Physics.SFGC.NonAbelian.CliffordEvenSubalgebra
open import DASHI.Physics.SFGC.NonAbelian.CliffordToM2Iso
open import DASHI.Physics.Closure.TriadicMatrixGenerationTheorem as TMG using
  (M2BasisElement)

------------------------------------------------------------------------
-- Composed selected-lane depth witness.
--
-- The record composes the finite graded witness, the even basis package,
-- and the basis bijection into a single frontier object.

record DepthQuotientWitness : Set₁ where
  field
    gradedWitness :
      GradedSFGCSite2DWitness

    evenBasisWitness :
      CliffordEvenSubalgebraWitness

    basisIso :
      CliffordM2BasisIso

    quotientBasisMap :
      EvenBasis → TMG.M2BasisElement

    quotientBasisMapIsCanonical :
      quotientBasisMap ≡ cliffordToM2Basis

canonicalDepthQuotientWitness :
  DepthQuotientWitness
canonicalDepthQuotientWitness =
  record
    { gradedWitness =
        canonicalGradedSFGCSite2DWitness
    ; evenBasisWitness =
        canonicalCliffordEvenSubalgebraWitness
    ; basisIso =
        canonicalCliffordM2BasisIso
    ; quotientBasisMap =
        cliffordToM2Basis
    ; quotientBasisMapIsCanonical =
        refl
    }

open DepthQuotientWitness public
