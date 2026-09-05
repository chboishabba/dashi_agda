module DASHI.Physics.QuantumVacuum.ParallelPlateConstructiveRealScalarBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as CRS
import DASHI.Analysis.MarxConstructiveRealTopology as CRT
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir

------------------------------------------------------------------------
-- CASIMIR SCALAR <-> EXISTING CONSTRUCTIVE REAL SAME-OBJECT WELD
--
-- CasimirParallelPlateKernel intentionally leaves Scalar abstract.  This owner
-- states exactly what must be proved to instantiate that scalar with the repo's
-- ConstructedOrderedCompleteReal rather than creating a second real ontology.
------------------------------------------------------------------------

record CasimirConstructiveRealScalarWeld
    (kernel : Casimir.CasimirScalarModel)
    (R : CRS.ConstructedOrderedCompleteReal) : Set₁ where
  field
    scalarIsConstructedReal : Casimir.Scalar kernel ≡ CRS.Real R

    zeroWeld : Set
    oneWeld : Set
    additionWeld : Set
    multiplicationWeld : Set
    negationWeld : Set
    inverseWeld : Set
    naturalEmbeddingWeld : Set

    piWeld : Set
    hbarWeld : Set
    lightSpeedWeld : Set
    lengthValueWeld : Set

    inverseCubeWeld : Set
    inverseFourthPowerWeld : Set

    reading : String

open CasimirConstructiveRealScalarWeld public

record CasimirConstructiveRealAnalyticPackage
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    real : CRS.ConstructedOrderedCompleteReal
    absoluteValueLaws : CRT.ConstructedRealAbsoluteValueLaws real
    metricLaws : CRT.ConstructedRealMetricLaws real absoluteValueLaws
    scalarWeld : CasimirConstructiveRealScalarWeld kernel real
    packageReading : String

open CasimirConstructiveRealAnalyticPackage public

------------------------------------------------------------------------
-- Authority boundaries.
------------------------------------------------------------------------

data EqualScalarCardinalityIdentifiesRealPermission : Set where

data CasimirClosedFormAutomaticallySuppliesRealWeldPermission : Set where

cardinalityCannotIdentifyScalarCarrier :
  EqualScalarCardinalityIdentifiesRealPermission → ⊥
cardinalityCannotIdentifyScalarCarrier ()

closedFormDoesNotAutoSupplyRealWeld :
  CasimirClosedFormAutomaticallySuppliesRealWeldPermission → ⊥
closedFormDoesNotAutoSupplyRealWeld ()

record ScalarBridgeStatus : Set where
  field
    constructiveRealSpineExists : Bool
    absoluteValueMetricExists : Bool
    casimirScalarSameObjectWeldInterfaceOwned : Bool
    concreteCasimirRealInstantiationClosed : Bool

    constructiveRealSpineExistsIsTrue : constructiveRealSpineExists ≡ true
    absoluteValueMetricExistsIsTrue : absoluteValueMetricExists ≡ true
    casimirScalarSameObjectWeldInterfaceOwnedIsTrue :
      casimirScalarSameObjectWeldInterfaceOwned ≡ true
    concreteCasimirRealInstantiationClosedIsFalse :
      concreteCasimirRealInstantiationClosed ≡ false

open ScalarBridgeStatus public

canonicalScalarBridgeStatus : ScalarBridgeStatus
canonicalScalarBridgeStatus = record
  { constructiveRealSpineExists = true
  ; absoluteValueMetricExists = true
  ; casimirScalarSameObjectWeldInterfaceOwned = true
  ; concreteCasimirRealInstantiationClosed = false
  ; constructiveRealSpineExistsIsTrue = refl
  ; absoluteValueMetricExistsIsTrue = refl
  ; casimirScalarSameObjectWeldInterfaceOwnedIsTrue = refl
  ; concreteCasimirRealInstantiationClosedIsFalse = refl
  }
