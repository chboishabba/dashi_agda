module DASHI.Physics.QuantumVacuum.CasimirRadialMeasureOneSixthCutsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact as Transverse
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseRadialReductionBidiExact as Radial

------------------------------------------------------------------------
-- TRANSVERSE/RADIAL 1/6 PRODUCER CUTSET
------------------------------------------------------------------------

record PolarMeasureTheorem : Set₁ where
  field
    CartesianPoint Radius Angle Scalar : Set
    cartesianMeasure : Set
    radialMeasure : Set
    angularMeasure : Set

    rotationallyInvariant : Set
    polarMapMeasurable : Set
    jacobianIsRadius : Set
    angularIntegralIsTwoPi : Set
    normalizedTwoDimensionalMeasure : Set
    zeroSetTreatment : Set
    reading : String

open PolarMeasureTheorem public

record RadialChangeOfVariablesTheorem : Set₁ where
  field
    Radius EnergyVariable Scalar : Set
    map : Radius → EnergyVariable
    derivativeSemantics : Set
    monotoneOnDomain : Set
    jacobianIdentity : Set
    endpointIdentity : Set
    measurableTransport : Set
    integralTransport : Set
    reading : String

open RadialChangeOfVariablesTheorem public

record RegulatedRadialIntegralEvaluation : Set₁ where
  field
    Scalar Regulator Mode : Set
    regulatedIntegral : Regulator → Mode → Scalar
    finitePart : Mode → Scalar

    integrableAtEveryRegulator : Set
    exactPrimitiveOrEquivalentEvaluation : Set
    subtractionCompatible : Set
    regulatorRemovalCompatible : Set
    finitePartIsCubicModeWeight : Set
    reading : String

open RegulatedRadialIntegralEvaluation public

record TransverseOneSixthReceipt
    (kernel : Casimir.CasimirScalarModel)
    (T : Transverse.CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    radialReduction : Radial.CasimirRadialReduction kernel T
    polarMeasure : PolarMeasureTheorem
    substitution : RadialChangeOfVariablesTheorem
    radialEvaluation : RegulatedRadialIntegralEvaluation

    sameRegulatedCasimirIntegrand : Set
    sameLongitudinalModeWeight : Set
    normalizationProducesOneSixth : Set
    oneSixthFeedsFinitePart : Set
    reading : String

open TransverseOneSixthReceipt public

data PolarNotationAutomaticallyIsMeasureTheorem : Set where
data ChangeVariableNotationAutomaticallyEvaluates : Set where

polarNotationNeedsMeasureProof : PolarNotationAutomaticallyIsMeasureTheorem → ⊥
polarNotationNeedsMeasureProof ()

changeVariableNeedsAnalyticProof :
  ChangeVariableNotationAutomaticallyEvaluates → ⊥
changeVariableNeedsAnalyticProof ()
