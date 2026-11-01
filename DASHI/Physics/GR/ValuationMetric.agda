module DASHI.Physics.GR.ValuationMetric where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Core.Q as Q
import Ontology.GodelLattice as GL
import DASHI.Physics.Closure.FactorVecDiscreteMetricTensorSurface as FV

ValuationCarrier : Set
ValuationCarrier = GL.FactorVec

ValuationDirection : Set
ValuationDirection = FV.FactorVecTangentDirection

ValuationScalar : Set
ValuationScalar = Q.ℚ

valuationMetricAt :
  ValuationCarrier →
  ValuationDirection →
  ValuationDirection →
  ValuationScalar
valuationMetricAt =
  FV.factorVecValuationDependentP2LorentzMetric

valuationMetricSymmetric :
  (base : ValuationCarrier) →
  (mu nu : ValuationDirection) →
  valuationMetricAt base mu nu ≡ valuationMetricAt base nu mu
valuationMetricSymmetric =
  FV.factorVecValuationDependentP2LorentzMetricSymmetric

record ValuationMetricSurface : Setω where
  field
    Base :
      Set

    TangentDirection :
      Set

    Scalar :
      Set

    metricAt :
      Base →
      TangentDirection →
      TangentDirection →
      Scalar

    symmetric :
      (base : Base) →
      (mu nu : TangentDirection) →
      metricAt base mu nu ≡ metricAt base nu mu

open ValuationMetricSurface public

canonicalValuationMetricSurface :
  ValuationMetricSurface
canonicalValuationMetricSurface =
  record
    { Base = ValuationCarrier
    ; TangentDirection = ValuationDirection
    ; Scalar = ValuationScalar
    ; metricAt = valuationMetricAt
    ; symmetric = valuationMetricSymmetric
    }
