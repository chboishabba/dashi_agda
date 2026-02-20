module DASHI.Quantum.AgreementDepth where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Unifier using (Tower; WaveLift; HilbertSpace)
open import DASHI.Algebra.Quantum.UVFinitenessHolographyTests using (AreaBound; UVFinite; UVFinitenessTheorem)

record AgreementDepthBundle : Set₁ where
  field
    tower : Tower
    hs : HilbertSpace
    lift : WaveLift tower hs
    area-bound : AreaBound

record AgreementConsequences (bundle : AgreementDepthBundle) : Set₁ where
  field
    uv-finite : UVFinite
    area-bound : AreaBound

AgreementDepth-theorem : AgreementDepthBundle → UVFinite
AgreementDepth-theorem bundle =
  UVFinitenessTheorem (AgreementDepthBundle.area-bound bundle)
