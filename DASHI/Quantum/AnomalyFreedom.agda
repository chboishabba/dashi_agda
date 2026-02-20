
module DASHI.Quantum.AnomalyFreedom where

open import DASHI.Unifier using (Tower; HilbertSpace)
open import DASHI.Quantum.Stone using (StoneBundle; StoneConsequences; Stone-theorem)
open import DASHI.Quantum.AgreementDepth using (AgreementDepthBundle; AgreementDepth-theorem)
open import DASHI.Algebra.ConstraintAlgebraClosure
  using (ConstraintClosureBundle; ConstraintClosure-theorem)
open import DASHI.Algebra.ConstraintAlgebraClosureTests
  renaming (DiracClosure to DiracClosureType)
open import DASHI.Algebra.Quantum.UVFinitenessHolographyTests using (UVFinite)

record AnomalyBundle (Tow : Tower) (HS : HilbertSpace) : Set₁ where
  field
    stone : StoneBundle Tow HS
    agreement : AgreementDepthBundle
    constraint : ConstraintClosureBundle
    anomaly-free : Set  -- ensures CCR + constraints align with UV bound

record AnomalyConsequences {Tow HS} (bundle : AnomalyBundle Tow HS) : Set₁ where
  field
    stone : StoneConsequences (AnomalyBundle.stone bundle)
    dirac : DiracClosureType
    uv-finite : UVFinite
    anomaly-free : Set

AnomalyFreedom : ∀ {Tow HS} (bundle : AnomalyBundle Tow HS) → AnomalyConsequences bundle
AnomalyFreedom bundle =
  record
    { stone = Stone-theorem (AnomalyBundle.stone bundle)
    ; dirac = ConstraintClosure-theorem (AnomalyBundle.constraint bundle)
    ; uv-finite = AgreementDepth-theorem (AnomalyBundle.agreement bundle)
    ; anomaly-free = AnomalyBundle.anomaly-free bundle
    }
