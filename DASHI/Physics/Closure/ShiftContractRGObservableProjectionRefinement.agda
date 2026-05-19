module DASHI.Physics.Closure.ShiftContractRGObservableProjectionRefinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CA
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractEigenShadowOrbitSummaryObstruction as SEOSO
  using (sameCanonicalEigenShadowNormalized-CPCC)
open import DASHI.Physics.Closure.ShiftContractRGObservableProjection as RGP
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM
open import DASHI.Physics.Constraints.ConcreteInstance as CI

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Higher fallback lane:
-- the full normalized RG observable projection does control the
-- eigenShadow channel, but it still separates the canonical CP/CC seam.

rgObservable-controls-eigenShadow :
  ∀ x y →
  CA.canonicalRGObservableOf x ≡ CA.canonicalRGObservableOf y →
  CA.canonicalEigenShadowLevel x ≡ CA.canonicalEigenShadowLevel y
rgObservable-controls-eigenShadow _ _ eq =
  cong₂ _,_
    (cong PHEM.EigenProfile.earth (cong RGOI.RGObservable.eigenSummary eq))
    (cong PHEM.EigenProfile.hub (cong RGOI.RGObservable.eigenSummary eq))

rgObservable-CPCC-obstructed :
  CA.canonicalRGObservableOf CI.CP
    ≢
  CA.canonicalRGObservableOf CI.CC
rgObservable-CPCC-obstructed eq =
  CA.canonicalEigenLevel-CP-obstructed
    (cong RGOI.RGObservable.eigenSummary eq)

record ShiftContractRGObservableProjectionRefinement : Set₁ where
  field
    controls-eigenShadow :
      ∀ x y →
      CA.canonicalRGObservableOf x ≡ CA.canonicalRGObservableOf y →
      CA.canonicalEigenShadowLevel x ≡ CA.canonicalEigenShadowLevel y
    canonical-CPCC-obstruction :
      CA.canonicalRGObservableOf CI.CP
        ≢
      CA.canonicalRGObservableOf CI.CC
    normalized-same-but-full-diff :
      SEOSO.canonicalEigenShadowNormalized CI.CP
        ≡
      SEOSO.canonicalEigenShadowNormalized CI.CC

canonicalShiftContractRGObservableProjectionRefinement :
  ShiftContractRGObservableProjectionRefinement
canonicalShiftContractRGObservableProjectionRefinement =
  record
    { controls-eigenShadow = rgObservable-controls-eigenShadow
    ; canonical-CPCC-obstruction = rgObservable-CPCC-obstructed
    ; normalized-same-but-full-diff = sameCanonicalEigenShadowNormalized-CPCC
    }
