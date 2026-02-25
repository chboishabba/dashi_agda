module DASHI.Geometry.Signature31FromConeArrowIsotropy where

open import Level using (Level; _⊔_; suc; zero)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.ProjectionDefect
open import DASHI.Geometry.ConeTimeIsotropy

record SignatureAxioms {ℓv ℓs}
  (A : Additive ℓv) (F : ScalarField ℓs)
  (QF : QuadraticForm A F)
  : Set (suc (ℓv ⊔ ℓs)) where
  open Additive A
  open ScalarField F
  open QuadraticForm QF
  field
    ConeS : ConeStructure (Additive.Carrier A)
    Arrow : TimeArrow (Additive.Carrier A)
    Iso   : IsotropyAction (Additive.Carrier A)
    Timelike↔Cone : ∀ (x : Additive.Carrier A) → ⊤

open SignatureAxioms public

postulate
  Signature31Theorem :
    ∀ {ℓv ℓs} (A : Additive ℓv) (F : ScalarField ℓs)
      (QF : QuadraticForm A F)
      (Ax : SignatureAxioms A F QF)
    → Signature
