module DASHI.Physics.Closure.HEPDataT45TwoComponentShapeDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- HEP-R49: two-component gamma/Z shape diagnostic.
--
-- HEP-R48 showed that t45 is not primarily blocked by wide-bin midpoint
-- bias.  HEP-R49 tests the next governance-clean hypothesis: split the
-- above-Z shape into a flat photon component and a Z-like Sudakov component.
--
-- Result: under the current sigma_dashi neutral-current component model this
-- is effectively a no-op.  The 106-170 window is computed as almost entirely
-- Z-like:
--
--   gamma fraction        = 0.0000379589
--   gamma/Z interference = 0.0003167495
--   Z fraction            = 0.9996452915
--
-- Therefore t45 changes only from chi2/dof = 15.8545837677 to
-- chi2/dof = 15.8542832674.  The intended 20-30% flat photon contribution is
-- not present in the current mass-kernel decomposition.  The remaining gap is
-- therefore upstream of the phi-star shape wrapper: it is the above-Z
-- neutral-current/PDF mass-kernel decomposition itself.

record ComponentFractions : Set where
  field
    photon : Float
    gammaZInterference : Float
    pureZ : Float

record HEPDataT45TwoComponentShapeDiagnostic : Set where
  field
    implementationSurface : String

    numeratorFractionsHighMass : ComponentFractions
    denominatorFractionsZPeak : ComponentFractions

    t43Chi2Before : Float
    t45Chi2Before : Float
    t45MeanPredDataBefore : Float

    t43Chi2After : Float
    t45Chi2After : Float
    t45MeanPredDataAfter : Float

    expectedPhotonFractionPresent : Bool
    twoComponentHypothesisDominant : Bool

    remainingGap : String

    -- Explicit governance boundary.
    statusNonPromoting : ⊤
    noPromotion : ⊤

canonicalHEPDataT45TwoComponentShapeDiagnostic :
  HEPDataT45TwoComponentShapeDiagnostic
canonicalHEPDataT45TwoComponentShapeDiagnostic =
  record
    { implementationSurface =
        "DASHI.Physics.Prediction.sigma_dashi:_two_component_sudakov_ratio"
    ; numeratorFractionsHighMass =
        record
          { photon = 0.0000379589
          ; gammaZInterference = 0.0003167495
          ; pureZ = 0.9996452915
          }
    ; denominatorFractionsZPeak =
        record
          { photon = 0.0000011884
          ; gammaZInterference = -0.0000010235
          ; pureZ = 0.9999998352
          }
    ; t43Chi2Before = 2.1565191176
    ; t45Chi2Before = 15.8545837677
    ; t45MeanPredDataBefore = 0.9581222335
    ; t43Chi2After = 2.1565191176
    ; t45Chi2After = 15.8542832674
    ; t45MeanPredDataAfter = 0.9581304397
    ; expectedPhotonFractionPresent = false
    ; twoComponentHypothesisDominant = false
    ; remainingGap =
        "above-Z neutral-current/PDF mass-kernel decomposition; current component fractions are Z-dominated"
    ; statusNonPromoting = tt
    ; noPromotion = tt
    }

canonicalHEPDataT45TwoComponentNoPromotion :
  HEPDataT45TwoComponentShapeDiagnostic.noPromotion
    canonicalHEPDataT45TwoComponentShapeDiagnostic
    ≡ tt
canonicalHEPDataT45TwoComponentNoPromotion = refl
