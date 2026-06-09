module DASHI.Physics.GR.Christoffel where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
import DASHI.Physics.Closure.FactorVecDiscreteMetricTensorSurface as FV
import DASHI.Physics.GR.ValuationMetric as VM

ChristoffelCarrier : Set
ChristoffelCarrier = VM.ValuationCarrier

ChristoffelDirection : Set
ChristoffelDirection = VM.ValuationDirection

ChristoffelScalar : Set
ChristoffelScalar = VM.ValuationScalar

christoffelSymbol :
  ChristoffelCarrier →
  ChristoffelDirection →
  ChristoffelDirection →
  ChristoffelDirection →
  ChristoffelScalar
christoffelSymbol =
  FV.factorVecChristoffelSymbol

christoffelSymbolTorsionFree :
  (base : ChristoffelCarrier) →
  (lambda mu nu : ChristoffelDirection) →
  christoffelSymbol base lambda mu nu ≡ christoffelSymbol base lambda nu mu
christoffelSymbolTorsionFree =
  FV.factorVecChristoffelTorsionFree

record ChristoffelSurface : Setω where
  field
    Carrier :
      Set

    TangentDirection :
      Set

    Scalar :
      Set

    symbol :
      Carrier →
      TangentDirection →
      TangentDirection →
      TangentDirection →
      Scalar

    torsionFree :
      (base : Carrier) →
      (lambda mu nu : TangentDirection) →
      symbol base lambda mu nu ≡ symbol base lambda nu mu

    valuationMetric :
      VM.ValuationMetricSurface

open ChristoffelSurface public

canonicalChristoffelSurface :
  ChristoffelSurface
canonicalChristoffelSurface =
  record
    { Carrier = ChristoffelCarrier
    ; TangentDirection = ChristoffelDirection
    ; Scalar = ChristoffelScalar
    ; symbol = christoffelSymbol
    ; torsionFree = christoffelSymbolTorsionFree
    ; valuationMetric = VM.canonicalValuationMetricSurface
    }
