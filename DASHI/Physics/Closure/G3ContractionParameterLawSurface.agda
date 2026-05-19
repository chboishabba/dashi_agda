module DASHI.Physics.Closure.G3ContractionParameterLawSurface where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.G3ConcreteOperators as G3Concrete
import DASHI.Physics.Closure.G3ContractionCarrier as G3Contraction
import DASHI.Physics.Closure.G3P2AdicNormMetricSurface as G3Norm
import DASHI.Physics.Closure.G3P2LimitConvergenceSurface as G3Limit
import DASHI.Physics.Closure.G3WaveFunctionOperatorAlgebra as G3Wave

------------------------------------------------------------------------
-- G3 contraction-parameter law surface.
--
-- This module is intentionally fail-closed.  The selected G3 stack already
-- gives a concrete p2 exponent on GL.FactorVec and proves that the selected
-- H/p2 bump increments it.  That is enough to state the contraction
-- parameter target precisely.  The selected p2-adic norm-index surface is
-- now available in G3P2AdicNormMetricSurface; this module remains
-- fail-closed because no convergence-to-zero limit or selected SES carrier
-- compatibility primitive is currently available.

data G3ContractionParameterLawStatus : Set where
  selectedP2ParameterSurfaceOnlyNoContractionPromotion :
    G3ContractionParameterLawStatus

data G3ContractionParameterLawMissingPrimitive : Set where
  missingP2AdicNormMetricPrimitive :
    G3ContractionParameterLawMissingPrimitive

  missingP2LimitConvergencePrimitive :
    G3ContractionParameterLawMissingPrimitive

  missingSelectedP2OperatorUltrametricForLimitPrimitive :
    G3ContractionParameterLawMissingPrimitive

  missingSelectedP2RescaledBoostCauchyAndZeroLimit :
    G3ContractionParameterLawMissingPrimitive

  missingSESPoincareGalileiCarrierCompatibility :
    G3ContractionParameterLawMissingPrimitive

SelectedState :
  Set
SelectedState =
  G3Wave.SelectedG3State

WaveFunction :
  Set
WaveFunction =
  G3Wave.WaveFunction

WaveFunctionOperator :
  Set
WaveFunctionOperator =
  G3Wave.WaveFunctionOperator

p2Exponent :
  SelectedState →
  Nat
p2Exponent =
  G3Concrete.selectedP2Filtration

contractionParameter :
  Nat →
  Nat
contractionParameter n =
  suc n

p2BumpIncrementsExponent :
  (v : SelectedState) →
  p2Exponent (G3Concrete.selectedH v) ≡ suc (p2Exponent v)
p2BumpIncrementsExponent =
  G3Concrete.selectedHFiltrationStep

record G3SelectedP2ContractionMetricLimitPrimitive : Setω where
  field
    p2OperatorDistance :
      WaveFunctionOperator →
      WaveFunctionOperator →
      Nat

    p2OperatorDistanceUsesSelectedExponent :
      List String

    tendsToZeroAtP2Infinity :
      (sequence : Nat → WaveFunctionOperator) →
      Set

    rescaledBoostLimitStatement :
      (d : G3Concrete.G3SpatialDirection) →
      tendsToZeroAtP2Infinity
        (λ _ → G3Wave.selectedKψ d)

record G3SelectedContractionParameterSESCompatibility
  (metricLimit : G3SelectedP2ContractionMetricLimitPrimitive) : Setω where
  field
    poincareCarrier :
      G3Contraction.SchrodingerPoincareSectorCarrier

    galileiCarrier :
      G3Contraction.SchrodingerGalileiSectorCarrier

    metricLimitFeedsSESCarrier :
      G3Contraction.SchrodingerPoincareToGalileiContractionCarrier

record G3SelectedContractionParameterLawObligation : Setω where
  field
    selectedAlgebra :
      G3Wave.G3SelectedWaveFunctionOperatorAlgebra

    selectedAlgebraName :
      String

    selectedState :
      Set

    selectedStateIsCurrent :
      selectedState ≡ SelectedState

    waveFunction :
      Set

    waveFunctionIsCurrent :
      waveFunction ≡ WaveFunction

    waveFunctionOperator :
      Set

    waveFunctionOperatorIsCurrent :
      waveFunctionOperator ≡ WaveFunctionOperator

    p2ExponentAccessor :
      SelectedState →
      Nat

    p2ExponentAccessorIsSelectedFiltration :
      p2ExponentAccessor ≡ p2Exponent

    p2BumpExponentStep :
      (v : SelectedState) →
      p2ExponentAccessor (G3Concrete.selectedH v)
      ≡
      suc (p2ExponentAccessor v)

    contractionParameterAtExponent :
      Nat →
      Nat

    contractionParameterIsSuccessor :
      (n : Nat) →
      contractionParameterAtExponent n ≡ suc n

    momentumOperator :
      G3Concrete.G3SpatialDirection →
      WaveFunctionOperator

    momentumOperatorIsSelectedP :
      momentumOperator ≡ G3Wave.selectedPψ

    energyOperator :
      WaveFunctionOperator

    energyOperatorIsSelectedH :
      energyOperator ≡ G3Wave.selectedHψ

    boostOperator :
      G3Concrete.G3SpatialDirection →
      WaveFunctionOperator

    boostOperatorIsSelectedK :
      boostOperator ≡ G3Wave.selectedKψ

    selectedP2AdicNormMetricSurface :
      G3Norm.G3SelectedP2AdicNormMetricSurface

    selectedP2LimitConvergenceSurface :
      G3Limit.G3P2LimitConvergenceFailClosedReceipt

    requiredMetricLimitPrimitiveName :
      String

    requiredSESCompatibilityPrimitiveName :
      String

    exactSchrodingerContractionCarrierTarget :
      Set

    exactSchrodingerContractionCarrierTargetIsExact :
      exactSchrodingerContractionCarrierTarget
      ≡
      G3Contraction.SchrodingerPoincareToGalileiContractionCarrier

record G3ContractionParameterLawFailClosedReceipt : Setω where
  field
    status :
      G3ContractionParameterLawStatus

    obligation :
      G3SelectedContractionParameterLawObligation

    firstMissing :
      G3ContractionParameterLawMissingPrimitive

    remainingMissing :
      List G3ContractionParameterLawMissingPrimitive

    exactFirstMissingClassification :
      String

    currentPositiveEvidence :
      List String

    nonPromotionBoundary :
      List String

canonicalG3SelectedContractionParameterLawObligation :
  G3SelectedContractionParameterLawObligation
canonicalG3SelectedContractionParameterLawObligation =
  record
    { selectedAlgebra =
        G3Wave.canonicalG3SelectedWaveFunctionOperatorAlgebra
    ; selectedAlgebraName =
        "G3Wave.canonicalG3SelectedWaveFunctionOperatorAlgebra"
    ; selectedState =
        SelectedState
    ; selectedStateIsCurrent =
        refl
    ; waveFunction =
        WaveFunction
    ; waveFunctionIsCurrent =
        refl
    ; waveFunctionOperator =
        WaveFunctionOperator
    ; waveFunctionOperatorIsCurrent =
        refl
    ; p2ExponentAccessor =
        p2Exponent
    ; p2ExponentAccessorIsSelectedFiltration =
        refl
    ; p2BumpExponentStep =
        p2BumpIncrementsExponent
    ; contractionParameterAtExponent =
        contractionParameter
    ; contractionParameterIsSuccessor =
        λ _ → refl
    ; momentumOperator =
        G3Wave.selectedPψ
    ; momentumOperatorIsSelectedP =
        refl
    ; energyOperator =
        G3Wave.selectedHψ
    ; energyOperatorIsSelectedH =
        refl
    ; boostOperator =
        G3Wave.selectedKψ
    ; boostOperatorIsSelectedK =
        refl
    ; selectedP2AdicNormMetricSurface =
        G3Norm.canonicalG3SelectedP2AdicNormMetricSurface
    ; selectedP2LimitConvergenceSurface =
        G3Limit.canonicalG3P2LimitConvergenceFailClosedReceipt
    ; requiredMetricLimitPrimitiveName =
        "G3SelectedP2OperatorUltrametricAPI plus G3SelectedP2LimitConvergencePrimitive from G3P2LimitConvergenceSurface"
    ; requiredSESCompatibilityPrimitiveName =
        "G3SelectedP2ContractionMetricLimitPrimitive -> G3SelectedContractionParameterSESCompatibility"
    ; exactSchrodingerContractionCarrierTarget =
        G3Contraction.SchrodingerPoincareToGalileiContractionCarrier
    ; exactSchrodingerContractionCarrierTargetIsExact =
        refl
    }

canonicalG3ContractionParameterLawFailClosedReceipt :
  G3ContractionParameterLawFailClosedReceipt
canonicalG3ContractionParameterLawFailClosedReceipt =
  record
    { status =
        selectedP2ParameterSurfaceOnlyNoContractionPromotion
    ; obligation =
        canonicalG3SelectedContractionParameterLawObligation
    ; firstMissing =
        missingSelectedP2OperatorUltrametricForLimitPrimitive
    ; remainingMissing =
        missingSelectedP2OperatorUltrametricForLimitPrimitive
        ∷ missingSelectedP2RescaledBoostCauchyAndZeroLimit
        ∷ missingSESPoincareGalileiCarrierCompatibility
        ∷ []
    ; exactFirstMissingClassification =
        "limit primitive reduced: Nat-valued ultrametric completeness is available in G3P2LimitConvergenceSurface; first missing is now the selected p2 operator ultrametric whose distance semantics are tied to the existing p2 norm-index evidence"
    ; currentPositiveEvidence =
        "SelectedState is the current G3Wave.SelectedG3State"
        ∷ "p2Exponent is exactly G3Concrete.selectedP2Filtration"
        ∷ "selectedH increments p2Exponent by G3Concrete.selectedHFiltrationStep"
        ∷ "contractionParameter n is fixed as suc n, tied to the selected p2 exponent level"
        ∷ "P, H, and K are exactly the selected wave-function operators from G3WaveFunctionOperatorAlgebra"
        ∷ "G3Norm.canonicalG3SelectedP2AdicNormMetricSurface binds selected P/H/K/mass to Nat-valued p2 norm-index evidence"
        ∷ "G3Limit.canonicalG3P2LimitConvergenceFailClosedReceipt binds CompleteUltrametricNat.completeNatUltrametric to the selected WaveFunctionOperator carrier"
        ∷ []
    ; nonPromotionBoundary =
        "Fail-closed receipt only: no SchrodingerPoincareToGalileiContractionCarrier is inhabited"
        ∷ "No p2 operator ultrametric, rescaled boost Cauchy witness, or convergence-to-zero theorem is fabricated here"
        ∷ "No associated-graded Galilei identification is claimed here"
        ∷ "SES carrier compatibility remains an explicit downstream primitive after a real metric/limit surface exists"
        ∷ []
    }
