module DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q

------------------------------------------------------------------------
-- Equation-facing carrier for the ideal parallel-plate Casimir kernel.
--
-- The report uses
--   E/A = -π² ħ c / (720 d³)
--   F/A = -π² ħ c / (240 d⁴).
--
-- Rather than postulating real arithmetic globally, this module records the
-- exact analytic operations and identities that a later real-valued instance
-- must provide.  No extraction claim follows from these equations alone.
------------------------------------------------------------------------

record CasimirScalarModel : Set₁ where
  constructor mkCasimirScalarModel
  field
    Scalar : Set
    zero one : Scalar
    _+_ _*_ : Scalar → Scalar → Scalar
    negate inverse : Scalar → Scalar
    fromNat : Nat → Scalar
    pi hbar lightSpeed : Scalar

    lengthValue : Q.Length → Scalar
    areaValue   : Q.Area → Scalar

    power3 power4 : Scalar → Scalar

    energyPerArea : Q.Length → Scalar
    pressure      : Q.Length → Scalar

    energyLaw : (d : Q.Length) →
      energyPerArea d ≡
        negate
          (((pi * pi) * (hbar * lightSpeed)) *
           inverse (fromNat 720 * power3 (lengthValue d)))

    pressureLaw : (d : Q.Length) →
      pressure d ≡
        negate
          (((pi * pi) * (hbar * lightSpeed)) *
           inverse (fromNat 240 * power4 (lengthValue d)))

------------------------------------------------------------------------
-- Finite stroke accounting derived from endpoint work receipts.
------------------------------------------------------------------------

record ConductiveStroke : Set where
  constructor mkConductiveStroke
  field
    initialSeparation finalSeparation : Q.Length
    plateArea : Q.Area
    availableWork : Q.Work

record StrokeWorkReceipt (s : ConductiveStroke) : Set where
  constructor mkStrokeWorkReceipt
  field
    positiveMagnitude : Nat
    closes :
      Q.Work.magnitude (ConductiveStroke.availableWork s) ≡ suc positiveMagnitude

record CasimirEquationReceipt (s : ConductiveStroke) : Set₁ where
  constructor mkCasimirEquationReceipt
  field
    model : CasimirScalarModel
    endpointIntegrationCarrier : Set
    integratedPressureWork : endpointIntegrationCarrier
    agreesWithAvailableWork : Set

-- The equation receipt establishes boundary stress/work modelling only.
-- Reset, switching and replication remain separate obligations.

record BoundaryStressEstablished : Set where
  constructor boundaryStressEstablished
  field
    stroke : ConductiveStroke
    workReceipt : StrokeWorkReceipt stroke

boundaryStressDoesNotCloseCycle :
  BoundaryStressEstablished → Set
boundaryStressDoesNotCloseCycle stress =
  StrokeWorkReceipt (BoundaryStressEstablished.stroke stress)
