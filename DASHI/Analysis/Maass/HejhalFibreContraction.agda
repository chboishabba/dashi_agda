module DASHI.Analysis.Maass.HejhalFibreContraction where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

open import Ultrametric as UMetric
import DASHI.Geometry.FiberContraction as FC
import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.RootsOfUnitySampling as ROS

------------------------------------------------------------------------
-- This is the reusable *shape* of the normalized Hejhal solve.  Unlike
-- MaassRestorationShift, it makes no tail-zeroing claim.  An instance has to
-- provide an actual coefficient carrier, ultrametric, update, and strict
-- fibre contraction.

FixP : {A : Set} → (A → A) → A → Set
FixP P a = P a ≡ a

record HejhalFibreContraction (Γ : MFC.ΓMaass) : Setω where
  field
    CoefficientState : Set
    ultrametric : UMetric.Ultrametric CoefficientState
    stateAsFourier : CoefficientState → MFC.TruncatedFourierState Γ

    normalisationProjection : CoefficientState → CoefficientState
    automorphyProjection : CoefficientState → CoefficientState
    hejhalUpdate : CoefficientState → CoefficientState

    updatePreservesNormalisation :
      ∀ a → normalisationProjection (hejhalUpdate a)
          ≡ normalisationProjection a
    automorphyContractiveOnFibres :
      FC.ContractiveOnFibers ultrametric automorphyProjection

    fixedImpliesSamplingClosed :
      ∀ a → FixP automorphyProjection a →
      ROS.ExactTruncatedRecovery Γ (stateAsFourier a)

    finiteAutomorphyClosed :
      ∀ a → FixP automorphyProjection a → Set

open HejhalFibreContraction public
