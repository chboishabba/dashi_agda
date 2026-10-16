module DASHI.Physics.QuantumVacuum.CasimirBrownMaclaySymmetricStressReductionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact as Sym
import DASHI.Physics.QuantumVacuum.CasimirGRQFTUnificationCrossPollinationExact as Casimir

------------------------------------------------------------------------
-- BROWN-MACLAY-SPECIFIC TEN-COMPONENT REDUCTION
--
-- The generic CMP119 owner already proves that coordinate symmetry reduces a
-- 4x4 stress tensor from sixteen component payments to ten.  This module uses
-- exactly that symmetry interface but targets the normalized Brown-Maclay
-- tensor rather than the finite-GR fixture used by the generic compiler.
------------------------------------------------------------------------

record CasimirBrownMaclaySymmetricTenComponentPayment
    {StressTensor : Set}
    (evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor)
    (stress : StressTensor) : Set where
  field
    symmetry : Sym.PairingComponentSymmetry evaluator stress

    qft00 : Cut.component evaluator stress Flat.timeAxis Flat.timeAxis
      ≡ Casimir.casimirNormalizedRationalTensor4 Flat.timeAxis Flat.timeAxis
    qft01 : Cut.component evaluator stress Flat.timeAxis Flat.xAxis
      ≡ Casimir.casimirNormalizedRationalTensor4 Flat.timeAxis Flat.xAxis
    qft02 : Cut.component evaluator stress Flat.timeAxis Flat.yAxis
      ≡ Casimir.casimirNormalizedRationalTensor4 Flat.timeAxis Flat.yAxis
    qft03 : Cut.component evaluator stress Flat.timeAxis Flat.zAxis
      ≡ Casimir.casimirNormalizedRationalTensor4 Flat.timeAxis Flat.zAxis
    qft11 : Cut.component evaluator stress Flat.xAxis Flat.xAxis
      ≡ Casimir.casimirNormalizedRationalTensor4 Flat.xAxis Flat.xAxis
    qft12 : Cut.component evaluator stress Flat.xAxis Flat.yAxis
      ≡ Casimir.casimirNormalizedRationalTensor4 Flat.xAxis Flat.yAxis
    qft13 : Cut.component evaluator stress Flat.xAxis Flat.zAxis
      ≡ Casimir.casimirNormalizedRationalTensor4 Flat.xAxis Flat.zAxis
    qft22 : Cut.component evaluator stress Flat.yAxis Flat.yAxis
      ≡ Casimir.casimirNormalizedRationalTensor4 Flat.yAxis Flat.yAxis
    qft23 : Cut.component evaluator stress Flat.yAxis Flat.zAxis
      ≡ Casimir.casimirNormalizedRationalTensor4 Flat.yAxis Flat.zAxis
    qft33 : Cut.component evaluator stress Flat.zAxis Flat.zAxis
      ≡ Casimir.casimirNormalizedRationalTensor4 Flat.zAxis Flat.zAxis

open CasimirBrownMaclaySymmetricTenComponentPayment public

casimirTenComponentsCompileToTensorEquality :
  ∀ {StressTensor : Set}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor}
    {stress : StressTensor} →
  CasimirBrownMaclaySymmetricTenComponentPayment evaluator stress →
  ∀ a b →
  Cut.component evaluator stress a b
  ≡ Casimir.casimirNormalizedRationalTensor4 a b
casimirTenComponentsCompileToTensorEquality payment Flat.timeAxis Flat.timeAxis = qft00 payment
casimirTenComponentsCompileToTensorEquality payment Flat.timeAxis Flat.xAxis = qft01 payment
casimirTenComponentsCompileToTensorEquality payment Flat.timeAxis Flat.yAxis = qft02 payment
casimirTenComponentsCompileToTensorEquality payment Flat.timeAxis Flat.zAxis = qft03 payment
casimirTenComponentsCompileToTensorEquality payment Flat.xAxis Flat.timeAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.xAxis Flat.timeAxis)
    (qft01 payment)
casimirTenComponentsCompileToTensorEquality payment Flat.xAxis Flat.xAxis = qft11 payment
casimirTenComponentsCompileToTensorEquality payment Flat.xAxis Flat.yAxis = qft12 payment
casimirTenComponentsCompileToTensorEquality payment Flat.xAxis Flat.zAxis = qft13 payment
casimirTenComponentsCompileToTensorEquality payment Flat.yAxis Flat.timeAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.yAxis Flat.timeAxis)
    (qft02 payment)
casimirTenComponentsCompileToTensorEquality payment Flat.yAxis Flat.xAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.yAxis Flat.xAxis)
    (qft12 payment)
casimirTenComponentsCompileToTensorEquality payment Flat.yAxis Flat.yAxis = qft22 payment
casimirTenComponentsCompileToTensorEquality payment Flat.yAxis Flat.zAxis = qft23 payment
casimirTenComponentsCompileToTensorEquality payment Flat.zAxis Flat.timeAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.zAxis Flat.timeAxis)
    (qft03 payment)
casimirTenComponentsCompileToTensorEquality payment Flat.zAxis Flat.xAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.zAxis Flat.xAxis)
    (qft13 payment)
casimirTenComponentsCompileToTensorEquality payment Flat.zAxis Flat.yAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.zAxis Flat.yAxis)
    (qft23 payment)
casimirTenComponentsCompileToTensorEquality payment Flat.zAxis Flat.zAxis = qft33 payment

independentBrownMaclayComponentPayments : Nat
independentBrownMaclayComponentPayments = 10

record CasimirBrownMaclaySymmetricReductionBoundary : Set where
  constructor casimir-brown-maclay-symmetric-reduction-boundary
  field
    genericCMP119SymmetryReductionReused : Bool
    symmetricTenComponentCompilerOwned : Bool
    sixteenIndependentComponentPaymentsRequired : Bool
    actualSelectedQFTTenComponentPaymentPaid : Bool

open CasimirBrownMaclaySymmetricReductionBoundary public

canonicalCasimirBrownMaclaySymmetricReductionBoundary :
  CasimirBrownMaclaySymmetricReductionBoundary
canonicalCasimirBrownMaclaySymmetricReductionBoundary =
  casimir-brown-maclay-symmetric-reduction-boundary
    true true false false

casimirBrownMaclaySymmetricReductionReading : String
casimirBrownMaclaySymmetricReductionReading =
  "A symmetric actual selected-QFT stress needs ten independent Brown-Maclay component payments, not sixteen. The six lower-triangular components are compiled from the existing CMP119 PairingComponentSymmetry interface. The remaining ten payments are 00,01,02,03,11,12,13,22,23,33 on the same stress/evaluator; no Brown-Maclay physical equality is asserted until those ten equations and symmetry are inhabited."
