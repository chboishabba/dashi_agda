module DASHI.Physics.SFGC.NonAbelian.NonAbelianSFGCCarrier where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.SFGC.NonAbelian.GradedSFGCSite2D using
  (GradedSFGCSite2DWitness; canonicalGradedSFGCSite2DWitness)
open import DASHI.Physics.SFGC.NonAbelian.CliffordEvenSubalgebra using
  (CliffordEvenSubalgebraWitness; canonicalCliffordEvenSubalgebraWitness)
open import DASHI.Physics.SFGC.NonAbelian.CliffordToM2Iso using
  (CliffordM2BasisIso; canonicalCliffordM2BasisIso)
open import DASHI.Physics.SFGC.NonAbelian.DepthQuotientIso using
  (DepthQuotientWitness; canonicalDepthQuotientWitness)

------------------------------------------------------------------------
-- Concrete nonabelian carrier bundle.
--
-- This file packages the already-inhabited finite witness modules into a
-- single witness surface. It does not add new algebraic structure; it just
-- exposes the selected graded lane, the Clifford-even basis, the basis
-- isomorphism, and the composed depth quotient as one coherent carrier
-- bundle.

record NonAbelianSFGCCarrierWitness : Set₁ where
  field
    gradedWitness :
      GradedSFGCSite2DWitness

    gradedWitnessIsCanonical :
      gradedWitness ≡ canonicalGradedSFGCSite2DWitness

    evenSubalgebraWitness :
      CliffordEvenSubalgebraWitness

    evenSubalgebraWitnessIsCanonical :
      evenSubalgebraWitness ≡ canonicalCliffordEvenSubalgebraWitness

    basisIso :
      CliffordM2BasisIso

    basisIsoIsCanonical :
      basisIso ≡ canonicalCliffordM2BasisIso

    depthQuotientWitness :
      DepthQuotientWitness

    depthQuotientWitnessIsCanonical :
      depthQuotientWitness ≡ canonicalDepthQuotientWitness

    witnessBoundary :
      String

canonicalNonAbelianSFGCCarrierWitness :
  NonAbelianSFGCCarrierWitness
canonicalNonAbelianSFGCCarrierWitness =
  record
    { gradedWitness =
        canonicalGradedSFGCSite2DWitness
    ; gradedWitnessIsCanonical =
        refl
    ; evenSubalgebraWitness =
        canonicalCliffordEvenSubalgebraWitness
    ; evenSubalgebraWitnessIsCanonical =
        refl
    ; basisIso =
        canonicalCliffordM2BasisIso
    ; basisIsoIsCanonical =
        refl
    ; depthQuotientWitness =
        canonicalDepthQuotientWitness
    ; depthQuotientWitnessIsCanonical =
        refl
    ; witnessBoundary =
        "finite nonabelian SFGC carrier bundle over the selected 7/11/13 lanes"
    }

open NonAbelianSFGCCarrierWitness public
