
module DASHI.Quantum.AnomalyFreedom where

open import Agda.Builtin.Equality using (_≡_)
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
    anomalyCarrier : Set          -- group/abelian value where anomalies live
    zero : anomalyCarrier
    cubic : anomalyCarrier
    mixed : anomalyCarrier
    cancel-cubic : cubic ≡ zero
    cancel-mixed : mixed ≡ zero

record AnomalyConsequences {Tow HS} (bundle : AnomalyBundle Tow HS) : Set₁ where
  field
    stone : StoneConsequences (AnomalyBundle.stone bundle)
    dirac : DiracClosureType
    uv-finite : UVFinite (AgreementDepthBundle.uv-bounded (AnomalyBundle.agreement bundle))
    cubic-zero : AnomalyBundle.cubic bundle ≡ AnomalyBundle.zero bundle
    mixed-zero : AnomalyBundle.mixed bundle ≡ AnomalyBundle.zero bundle

AnomalyFreedom : ∀ {Tow HS} (bundle : AnomalyBundle Tow HS) → AnomalyConsequences bundle
AnomalyFreedom bundle =
  record
    { stone = Stone-theorem (AnomalyBundle.stone bundle)
    ; dirac = ConstraintClosure-theorem (AnomalyBundle.constraint bundle)
    ; uv-finite = AgreementDepth-theorem (AnomalyBundle.agreement bundle)
    ; cubic-zero = AnomalyBundle.cancel-cubic bundle
    ; mixed-zero = AnomalyBundle.cancel-mixed bundle
    }
