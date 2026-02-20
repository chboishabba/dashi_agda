module DASHI.Quantum.AgreementDepth where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Unifier using (Tower; WaveLift; HilbertSpace)
open import DASHI.Algebra.Quantum.UVFinitenessHolographyTests using (AreaBound; UVFinitenessTheorem)
open import DASHI.Algebra.Quantum.UVFiniteness using (UVBounded; UVFinite; uvFiniteness)

record AgreementDepthBundle : Set₁ where
  field
    tower : Tower
    hs : HilbertSpace
    lift : WaveLift tower hs
    area-bound : AreaBound
    uv-bounded : UVBounded

record AgreementConsequences (bundle : AgreementDepthBundle) : Set₁ where
  field
    uv-finite : UVFinite (AgreementDepthBundle.uv-bounded bundle)
    area-bound : AreaBound

AgreementDepth-theorem : (bundle : AgreementDepthBundle) → UVFinite (AgreementDepthBundle.uv-bounded bundle)
AgreementDepth-theorem bundle =
  uvFiniteness (AgreementDepthBundle.uv-bounded bundle)
