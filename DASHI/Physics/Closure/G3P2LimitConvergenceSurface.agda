module DASHI.Physics.Closure.G3P2LimitConvergenceSurface where

open import Agda.Primitive using (Set; Setω; lzero; lsuc)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

import Ultrametric as UMetric
import DASHI.Geometry.CompleteUltrametric as CompleteU
import DASHI.Geometry.CompleteUltrametricNat as CompleteUNat
import DASHI.Physics.Closure.G3ConcreteOperators as G3Concrete
import DASHI.Physics.Closure.G3P2AdicNormMetricSurface as G3Norm
import DASHI.Physics.Closure.G3WaveFunctionOperatorAlgebra as G3Wave

------------------------------------------------------------------------
-- Selected p2 limit-convergence surface.
--
-- The repo already contains the only general convergence theorem this lane
-- can honestly consume without adding analytic real-number machinery:
-- every Nat-valued ultrametric is complete.  This surface connects that
-- theorem to the selected G3 wave-function operator carrier and narrows the
-- former "missingP2LimitConvergencePrimitive" into the concrete missing
-- pieces needed by the contraction lane:
--
--   1. a selected p2 operator ultrametric whose Nat distance is tied to the
--      existing p2 norm-index evidence;
--   2. a rescaled-boost sequence in that ultrametric;
--   3. a Cauchy/convergence witness for that sequence.
--
-- No Schrodinger/Poincare-to-Galilei contraction carrier is promoted here.

data G3P2LimitConvergenceStatus : Set where
  selectedP2LimitReducedToNatUltrametricCompletenessNoPromotion :
    G3P2LimitConvergenceStatus

data G3P2LimitConvergenceMissingPrimitive : Set where
  missingSelectedP2OperatorDistancePrimitive :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorNormIndexFunction :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorDifferenceNormIndex :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorNormIdentityZero :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorDifferenceNormSymmetry :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorDifferenceNormUltrametric :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedP2OperatorUltrametric :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedP2OperatorRescalingPrimitive :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedOperatorRescalingDistanceBound :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedP2RescaledBoostSequence :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedP2RescaledBoostCauchyWitness :
    G3P2LimitConvergenceMissingPrimitive

  missingSelectedP2RescaledBoostZeroLimitWitness :
    G3P2LimitConvergenceMissingPrimitive

SelectedOperator :
  Set
SelectedOperator =
  G3Wave.WaveFunctionOperator

SelectedP2OperatorUltrametric :
  Set (lsuc lzero)
SelectedP2OperatorUltrametric =
  UMetric.Ultrametric SelectedOperator

selectedP2OperatorCompleteIfNatUltrametric :
  (U : SelectedP2OperatorUltrametric) →
  CompleteU.Complete U
selectedP2OperatorCompleteIfNatUltrametric =
  CompleteUNat.completeNatUltrametric

record G3SelectedP2OperatorUltrametricAPI : Setω where
  field
    operatorCarrier :
      Set

    operatorCarrierIsSelected :
      operatorCarrier ≡ SelectedOperator

    p2OperatorUltrametric :
      SelectedP2OperatorUltrametric

    operatorDistancePrimitive :
      G3Norm.G3SelectedP2OperatorDistancePrimitive

    p2OperatorUltrametricIsFromDistancePrimitive :
      p2OperatorUltrametric
      ≡
      G3Norm.selectedP2OperatorUltrametricFromDistancePrimitive
        operatorDistancePrimitive

    distanceSemantics :
      List String

    distanceUsesSelectedNormIndex :
      List String

    normMetricSurface :
      G3Norm.G3SelectedP2AdicNormMetricSurface

selectedP2OperatorUltrametricAPIFromDistancePrimitive :
  G3Norm.G3SelectedP2OperatorDistancePrimitive →
  G3SelectedP2OperatorUltrametricAPI
selectedP2OperatorUltrametricAPIFromDistancePrimitive distance =
  record
    { operatorCarrier =
        SelectedOperator
    ; operatorCarrierIsSelected =
        refl
    ; p2OperatorUltrametric =
        G3Norm.selectedP2OperatorUltrametricFromDistancePrimitive
          distance
    ; operatorDistancePrimitive =
        distance
    ; p2OperatorUltrametricIsFromDistancePrimitive =
        refl
    ; distanceSemantics =
        "Selected p2 operator ultrametric is constructed from G3SelectedP2OperatorDistancePrimitive"
        ∷ "The distance primitive must supply identity, symmetry, and ultrametric laws on selected WaveFunctionOperator"
        ∷ []
    ; distanceUsesSelectedNormIndex =
        G3Norm.G3SelectedP2OperatorDistancePrimitive.distanceTiedToSelectedNormIndex
          distance
    ; normMetricSurface =
        G3Norm.canonicalG3SelectedP2AdicNormMetricSurface
    }

record G3SelectedP2RescaledBoostCauchyZeroLimitAPI
  (api : G3SelectedP2OperatorUltrametricAPI) : Setω where
  open G3SelectedP2OperatorUltrametricAPI api

  field
    rescalingPrimitive :
      G3Norm.G3SelectedP2OperatorRescalingPrimitive
        operatorDistancePrimitive

    rescaledBoostIsCauchy :
      (d : G3Concrete.G3SpatialDirection) →
      CompleteU.Cauchy p2OperatorUltrametric

    rescaledBoostCauchyIsTheRescaledSequence :
      (d : G3Concrete.G3SpatialDirection) →
      CompleteU.Cauchy.seq (rescaledBoostIsCauchy d)
      ≡
      G3Norm.G3SelectedP2OperatorRescalingPrimitive.rescaledBoostSequence
        rescalingPrimitive d

    rescaledBoostLimitIsSelectedZeroOperator :
      (d : G3Concrete.G3SpatialDirection) →
      CompleteU.Complete.limit
        (CompleteUNat.completeNatUltrametric p2OperatorUltrametric)
        (rescaledBoostIsCauchy d)
      ≡
      G3Norm.G3SelectedP2OperatorRescalingPrimitive.zeroLimitOperator
        rescalingPrimitive

    exactCauchyZeroLimitSemantics :
      List String

record G3SelectedP2LimitConvergencePrimitive
  (api : G3SelectedP2OperatorUltrametricAPI) : Setω where
  open G3SelectedP2OperatorUltrametricAPI api

  field
    rescaledBoostSequence :
      G3Concrete.G3SpatialDirection →
      Nat →
      SelectedOperator

    rescaledBoostSequenceSemantics :
      List String

    rescaledBoostIsCauchy :
      (d : G3Concrete.G3SpatialDirection) →
      CompleteU.Cauchy p2OperatorUltrametric

    rescaledBoostCauchyIsTheSequence :
      (d : G3Concrete.G3SpatialDirection) →
      CompleteU.Cauchy.seq (rescaledBoostIsCauchy d)
      ≡
      rescaledBoostSequence d

    rescaledBoostLimit :
      (d : G3Concrete.G3SpatialDirection) →
      SelectedOperator

    rescaledBoostLimitIsZeroOperator :
      List String

    rescaledBoostLimitIsCompleteNatLimit :
      (d : G3Concrete.G3SpatialDirection) →
      rescaledBoostLimit d
      ≡
      CompleteU.Complete.limit
        (CompleteUNat.completeNatUltrametric p2OperatorUltrametric)
        (rescaledBoostIsCauchy d)

selectedP2LimitConvergencePrimitiveFromCauchyZeroLimitAPI :
  (api : G3SelectedP2OperatorUltrametricAPI) →
  G3SelectedP2RescaledBoostCauchyZeroLimitAPI api →
  G3SelectedP2LimitConvergencePrimitive api
selectedP2LimitConvergencePrimitiveFromCauchyZeroLimitAPI api cauchyZero =
  let
    open G3SelectedP2OperatorUltrametricAPI api
    open G3SelectedP2RescaledBoostCauchyZeroLimitAPI cauchyZero
  in
  record
    { rescaledBoostSequence =
        G3Norm.G3SelectedP2OperatorRescalingPrimitive.rescaledBoostSequence
          rescalingPrimitive
    ; rescaledBoostSequenceSemantics =
        G3Norm.G3SelectedP2OperatorRescalingPrimitive.exactRescalingSemantics
          rescalingPrimitive
    ; rescaledBoostIsCauchy =
        rescaledBoostIsCauchy
    ; rescaledBoostCauchyIsTheSequence =
        rescaledBoostCauchyIsTheRescaledSequence
    ; rescaledBoostLimit =
        λ _ →
          G3Norm.G3SelectedP2OperatorRescalingPrimitive.zeroLimitOperator
            rescalingPrimitive
    ; rescaledBoostLimitIsZeroOperator =
        "Limit operator is the zeroLimitOperator of G3SelectedP2OperatorRescalingPrimitive"
        ∷ "The rescaling primitive must prove zeroLimitOperatorIsSelectedZero"
        ∷ exactCauchyZeroLimitSemantics
    ; rescaledBoostLimitIsCompleteNatLimit =
        λ d →
          sym (rescaledBoostLimitIsSelectedZeroOperator d)
    }

record G3P2LimitConvergenceFailClosedReceipt : Setω where
  field
    status :
      G3P2LimitConvergenceStatus

    selectedOperatorCarrier :
      Set

    selectedOperatorCarrierIsCurrent :
      selectedOperatorCarrier ≡ SelectedOperator

    natUltrametricCompletenessAvailable :
      (U : SelectedP2OperatorUltrametric) →
      CompleteU.Complete U

    normMetricSurface :
      G3Norm.G3SelectedP2AdicNormMetricSurface

    distanceConstructionAttempt :
      G3Norm.G3SelectedP2OperatorDistanceConstructionAttempt

    exactReducedPrimitiveName :
      String

    selectedOperatorUltrametricFromDistancePrimitiveAvailable :
      G3Norm.G3SelectedP2OperatorDistancePrimitive →
      G3SelectedP2OperatorUltrametricAPI

    selectedLimitPrimitiveFromCauchyZeroLimitAvailable :
      (api : G3SelectedP2OperatorUltrametricAPI) →
      G3SelectedP2RescaledBoostCauchyZeroLimitAPI api →
      G3SelectedP2LimitConvergencePrimitive api

    firstMissing :
      G3P2LimitConvergenceMissingPrimitive

    remainingMissing :
      List G3P2LimitConvergenceMissingPrimitive

    positiveEvidence :
      List String

    nonPromotionBoundary :
      List String

canonicalG3P2LimitConvergenceFailClosedReceipt :
  G3P2LimitConvergenceFailClosedReceipt
canonicalG3P2LimitConvergenceFailClosedReceipt =
  record
    { status =
        selectedP2LimitReducedToNatUltrametricCompletenessNoPromotion
    ; selectedOperatorCarrier =
        SelectedOperator
    ; selectedOperatorCarrierIsCurrent =
        refl
    ; natUltrametricCompletenessAvailable =
        selectedP2OperatorCompleteIfNatUltrametric
    ; normMetricSurface =
        G3Norm.canonicalG3SelectedP2AdicNormMetricSurface
    ; distanceConstructionAttempt =
        G3Norm.canonicalSelectedP2OperatorDistanceConstructionAttempt
    ; exactReducedPrimitiveName =
        "(api : G3SelectedP2OperatorUltrametricAPI) -> G3SelectedP2LimitConvergencePrimitive api"
    ; selectedOperatorUltrametricFromDistancePrimitiveAvailable =
        selectedP2OperatorUltrametricAPIFromDistancePrimitive
    ; selectedLimitPrimitiveFromCauchyZeroLimitAvailable =
        selectedP2LimitConvergencePrimitiveFromCauchyZeroLimitAPI
    ; firstMissing =
        missingSelectedP2OperatorDistancePrimitive
    ; remainingMissing =
        missingSelectedP2OperatorDistancePrimitive
        ∷ missingSelectedOperatorNormIndexFunction
        ∷ missingSelectedOperatorDifferenceNormIndex
        ∷ missingSelectedOperatorNormIdentityZero
        ∷ missingSelectedOperatorDifferenceNormSymmetry
        ∷ missingSelectedOperatorDifferenceNormUltrametric
        ∷ missingSelectedP2OperatorRescalingPrimitive
        ∷ missingSelectedOperatorRescalingDistanceBound
        ∷ missingSelectedP2RescaledBoostSequence
        ∷ missingSelectedP2RescaledBoostCauchyWitness
        ∷ missingSelectedP2RescaledBoostZeroLimitWitness
        ∷ []
    ; positiveEvidence =
        "DASHI.Geometry.CompleteUltrametricNat.completeNatUltrametric proves completeness for any Nat-valued ultrametric"
        ∷ "The selected carrier for the limit lane is exactly G3Wave.WaveFunctionOperator"
        ∷ "G3P2AdicNormMetricSurface already binds selected P/H/K/mass to Nat-valued p2 norm-index evidence"
        ∷ "G3Wave.waveFunctionOperatorSubtraction gives the candidate difference operator A - B"
        ∷ "The selected p2 distance construction attempt is narrowed to exact norm-index, identity, symmetry, ultrametric, and rescaling-bound blockers"
        ∷ "A selected p2 operator ultrametric is now constructible from G3SelectedP2OperatorDistancePrimitive"
        ∷ "A selected p2 limit primitive is now constructible from G3SelectedP2RescaledBoostCauchyZeroLimitAPI"
        ∷ "The old missingP2LimitConvergencePrimitive is now reduced to exact selected operator distance, rescaling, Cauchy, and zero-limit witnesses"
        ∷ []
    ; nonPromotionBoundary =
        "No p2 operator distance is fabricated here"
        ∷ "No coefficient extraction or selected operator norm-index function is fabricated here"
        ∷ "No identity/symmetry/ultrametric law for a difference norm is fabricated here"
        ∷ "No p2-level rescaling operation on WaveFunctionOperator is fabricated here"
        ∷ "No rescaling distance bound is fabricated here"
        ∷ "No rescaled boost Cauchy or convergence-to-zero witness is fabricated here"
        ∷ "No SchrodingerPoincareToGalileiContractionCarrier is inhabited here"
        ∷ []
    }
