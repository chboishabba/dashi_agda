module DASHI.Geometry.Signature31FromConeArrowIsotropy where

open import Agda.Primitive using (Setω)
open import Level using (Level; _⊔_; suc; zero)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.ProjectionDefect
open import DASHI.Geometry.ConeTimeIsotropy

record SignatureAxioms {ℓv ℓs}
  (A : Additive ℓv) (F : ScalarField ℓs)
  (QF : QuadraticForm A F)
  : Setω where
  open Additive A
  open ScalarField F
  open QuadraticForm QF
  field
    ConeS : ConeStructure (Additive.Carrier A)
    Arrow : TimeArrow (Additive.Carrier A)
    Iso   : IsotropyAction (Additive.Carrier A)
    ShellS : ShellStructure (Additive.Carrier A)
    MoveS  : AdmissibleMove (Additive.Carrier A)
    ShellIso : ShellIsotropyAction (Additive.Carrier A) ShellS Iso
    FiniteShell : FiniteShellRealization (Additive.Carrier A)
    FiniteIso : FiniteIsotropyRealization (Additive.Carrier A) Iso FiniteShell
    Timelike↔Cone : ∀ (x : Additive.Carrier A) → ⊤

open SignatureAxioms public

record Signature31FromConeArrowIsotropyAxioms
  {ℓv ℓs} (A : Additive ℓv) (F : ScalarField ℓs)
  (QF : QuadraticForm A F) : Setω where
  field
    Signature31Theorem :
      (Ax : SignatureAxioms A F QF) → Signature

Signature31Theorem :
  ∀ {ℓv ℓs} (A : Additive ℓv) (F : ScalarField ℓs)
    (QF : QuadraticForm A F)
    (Ax : SignatureAxioms A F QF)
    → Signature31FromConeArrowIsotropyAxioms A F QF
    → Signature
Signature31Theorem A F QF Ax ax =
  Signature31FromConeArrowIsotropyAxioms.Signature31Theorem ax Ax
