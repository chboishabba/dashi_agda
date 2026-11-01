module DASHI.Geometry.ConeArrowIsotropyShellAction where

open import Level using (_⊔_; suc)

open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.ProjectionDefect using (Additive)
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.Signature31FromConeArrowIsotropy as S31

record AbstractShellAction {ℓv ℓs}
  (A : Additive ℓv) (F : ScalarField ℓs)
  (QF : QuadraticForm A F) : Set (suc (ℓv ⊔ ℓs)) where
  field
    coneS      : CTI.ConeStructure (Additive.Carrier A)
    arrow      : CTI.TimeArrow (Additive.Carrier A)
    iso        : CTI.IsotropyAction (Additive.Carrier A)
    shellS     : CTI.ShellStructure (Additive.Carrier A)
    moveS      : CTI.AdmissibleMove (Additive.Carrier A)
    shellIso   : CTI.ShellIsotropyAction (Additive.Carrier A) shellS iso
    finiteShell : CTI.FiniteShellRealization (Additive.Carrier A)
    finiteIso   : CTI.FiniteIsotropyRealization (Additive.Carrier A) iso finiteShell

open AbstractShellAction public

buildShellAction :
  ∀ {ℓv ℓs}
  (A : Additive ℓv) (F : ScalarField ℓs)
  (QF : QuadraticForm A F)
  (Ax : S31.SignatureAxioms A F QF) →
  AbstractShellAction A F QF
buildShellAction A F QF Ax =
  record
    { coneS = S31.SignatureAxioms.ConeS Ax
    ; arrow = S31.SignatureAxioms.Arrow Ax
    ; iso = S31.SignatureAxioms.Iso Ax
    ; shellS = S31.SignatureAxioms.ShellS Ax
    ; moveS = S31.SignatureAxioms.MoveS Ax
    ; shellIso = S31.SignatureAxioms.ShellIso Ax
    ; finiteShell = S31.SignatureAxioms.FiniteShell Ax
    ; finiteIso = S31.SignatureAxioms.FiniteIso Ax
    }
