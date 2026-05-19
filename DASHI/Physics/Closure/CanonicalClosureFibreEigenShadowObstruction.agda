module DASHI.Physics.Closure.CanonicalClosureFibreEigenShadowObstruction where

open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.CanonicalClosureFibre as CCF
open import DASHI.Physics.Closure.CanonicalClosureFibreFields as CCFF
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- `eigenShadow` does not descend to the current coarse closure quotient:
-- `CR` and `CP` already inhabit the same coarse fibre, but their
-- eigen-shadow values differ.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

canonicalCoarseCRCP :
  CCF.π CI.CR ≡ CCF.π CI.CP
canonicalCoarseCRCP = refl

coarseCR-fibre : CCF.CanonicalFibre (CCF.π CI.CR)
coarseCR-fibre = CI.CR , refl

coarseCP-in-CR-fibre : CCF.CanonicalFibre (CCF.π CI.CR)
coarseCP-in-CR-fibre = CI.CP , canonicalCoarseCRCP

eigenShadow-sameFibre-CRCP-obstructed :
  CCFF.eigenShadowField coarseCR-fibre
    ≢
  CCFF.eigenShadowField coarseCP-in-CR-fibre
eigenShadow-sameFibre-CRCP-obstructed ()

sameFibre⇒sameEigenShadow-obstructed : Set
sameFibre⇒sameEigenShadow-obstructed =
  ∀ {q} →
  (x y : CCF.CanonicalFibre q) →
  CCFF.eigenShadowField x ≡ CCFF.eigenShadowField y

sameFibre⇒sameEigenShadow-obstructed-false :
  sameFibre⇒sameEigenShadow-obstructed → ⊥
sameFibre⇒sameEigenShadow-obstructed-false allSame =
  eigenShadow-sameFibre-CRCP-obstructed
    (allSame coarseCR-fibre coarseCP-in-CR-fibre)
