module DASHI.Physics.QuantumVacuum.CasimirBrownMaclaySymmetricStressReductionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact as Sym
import DASHI.Physics.Foundations.CMP119SymmetrySemanticBridgeExact as SymSemantic
import DASHI.Physics.QuantumVacuum.CasimirGRQFTUnificationCrossPollinationExact as Casimir

------------------------------------------------------------------------
-- BROWN-MACLAY-SPECIFIC TEN-COMPONENT REDUCTION
------------------------------------------------------------------------

record CasimirBrownMaclayTenIndependentValues
    {StressTensor : Set}
    (evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor)
    (stress : StressTensor) : Set where
  field
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

open CasimirBrownMaclayTenIndependentValues public

record CasimirBrownMaclaySymmetricTenComponentPayment
    {StressTensor : Set}
    (evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor)
    (stress : StressTensor) : Set where
  field
    symmetry : Sym.PairingComponentSymmetry evaluator stress
    values : CasimirBrownMaclayTenIndependentValues evaluator stress

open CasimirBrownMaclaySymmetricTenComponentPayment public

compileSymmetryAndTenValues :
  ∀ {StressTensor : Set}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor}
    {stress : StressTensor} →
  Sym.PairingComponentSymmetry evaluator stress →
  CasimirBrownMaclayTenIndependentValues evaluator stress →
  CasimirBrownMaclaySymmetricTenComponentPayment evaluator stress
compileSymmetryAndTenValues symmetryReceipt valueReceipt = record
  { symmetry = symmetryReceipt
  ; values = valueReceipt
  }

compileYMSymmetrySemanticBridgeAndTenValues :
  ∀ {StressTensor : Set}
    {Symmetric : StressTensor → Set}
    {stress : StressTensor}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor} →
  SymSemantic.YMSymmetryMeansMetricBasisComponentSymmetry
    Symmetric stress evaluator →
  CasimirBrownMaclayTenIndependentValues evaluator stress →
  CasimirBrownMaclaySymmetricTenComponentPayment evaluator stress
compileYMSymmetrySemanticBridgeAndTenValues bridge values =
  compileSymmetryAndTenValues
    (SymSemantic.compileYMSymmetryToComponentSymmetry bridge)
    values

casimirTenComponentsCompileToTensorEquality :
  ∀ {StressTensor : Set}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor}
    {stress : StressTensor} →
  CasimirBrownMaclaySymmetricTenComponentPayment evaluator stress →
  ∀ a b →
  Cut.component evaluator stress a b
  ≡ Casimir.casimirNormalizedRationalTensor4 a b
casimirTenComponentsCompileToTensorEquality payment Flat.timeAxis Flat.timeAxis =
  qft00 (values payment)
casimirTenComponentsCompileToTensorEquality payment Flat.timeAxis Flat.xAxis =
  qft01 (values payment)
casimirTenComponentsCompileToTensorEquality payment Flat.timeAxis Flat.yAxis =
  qft02 (values payment)
casimirTenComponentsCompileToTensorEquality payment Flat.timeAxis Flat.zAxis =
  qft03 (values payment)
casimirTenComponentsCompileToTensorEquality payment Flat.xAxis Flat.timeAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.xAxis Flat.timeAxis)
    (qft01 (values payment))
casimirTenComponentsCompileToTensorEquality payment Flat.xAxis Flat.xAxis =
  qft11 (values payment)
casimirTenComponentsCompileToTensorEquality payment Flat.xAxis Flat.yAxis =
  qft12 (values payment)
casimirTenComponentsCompileToTensorEquality payment Flat.xAxis Flat.zAxis =
  qft13 (values payment)
casimirTenComponentsCompileToTensorEquality payment Flat.yAxis Flat.timeAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.yAxis Flat.timeAxis)
    (qft02 (values payment))
casimirTenComponentsCompileToTensorEquality payment Flat.yAxis Flat.xAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.yAxis Flat.xAxis)
    (qft12 (values payment))
casimirTenComponentsCompileToTensorEquality payment Flat.yAxis Flat.yAxis =
  qft22 (values payment)
casimirTenComponentsCompileToTensorEquality payment Flat.yAxis Flat.zAxis =
  qft23 (values payment)
casimirTenComponentsCompileToTensorEquality payment Flat.zAxis Flat.timeAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.zAxis Flat.timeAxis)
    (qft03 (values payment))
casimirTenComponentsCompileToTensorEquality payment Flat.zAxis Flat.xAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.zAxis Flat.xAxis)
    (qft13 (values payment))
casimirTenComponentsCompileToTensorEquality payment Flat.zAxis Flat.yAxis =
  trans
    (Sym.componentSymmetric (symmetry payment) Flat.zAxis Flat.yAxis)
    (qft23 (values payment))
casimirTenComponentsCompileToTensorEquality payment Flat.zAxis Flat.zAxis =
  qft33 (values payment)

independentBrownMaclayComponentPayments : Nat
independentBrownMaclayComponentPayments = 10

record CasimirBrownMaclaySymmetricReductionBoundary : Set where
  constructor casimir-brown-maclay-symmetric-reduction-boundary
  field
    genericCMP119SymmetryReductionReused : Bool
    tenIndependentValuesRecordOwned : Bool
    symmetryAndTenValuesCompilerOwned : Bool
    ymSymmetrySemanticBridgeCompilerOwned : Bool
    symmetricTenComponentCompilerOwned : Bool
    sixteenIndependentComponentPaymentsRequired : Bool
    actualSelectedQFTSymmetryPaid : Bool
    actualSelectedQFTTenComponentValuesPaid : Bool
    actualSelectedQFTTenComponentPaymentPaid : Bool

open CasimirBrownMaclaySymmetricReductionBoundary public

canonicalCasimirBrownMaclaySymmetricReductionBoundary :
  CasimirBrownMaclaySymmetricReductionBoundary
canonicalCasimirBrownMaclaySymmetricReductionBoundary =
  casimir-brown-maclay-symmetric-reduction-boundary
    true true true true true false false false false

casimirBrownMaclaySymmetricReductionReading : String
casimirBrownMaclaySymmetricReductionReading =
  "The Brown-Maclay selected-stress target is factored into PairingComponentSymmetry and ten independent values. If the selected YM stress carries the repo's YMSymmetryMeansMetricBasisComponentSymmetry receipt, the existing semantic compiler pays the coordinate-symmetry side without a second symmetry theorem. Ten values 00,01,02,03,11,12,13,22,23,33 plus symmetry compile to all sixteen Axis4 equalities."
