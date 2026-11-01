module DASHI.Physics.Closure.NSTriadKNOutputLocalSelectorFixedOutputReductionExact where

------------------------------------------------------------------------
-- S2b2d0 / OUTPUT-LOCAL 0/1 WEIGHTS DISAPPEAR ON A FIXED OUTPUT FIBRE
--
-- R294 already proves that any p/q-swap-invariant cell weight preserves the
-- exact fixed-output product-rule -> mixed-commutator collapse before norms.
-- The #957 exact-shell collar weight is even simpler: it depends only on the
-- final output k.  Therefore, on one fixed-output fibre, it is constant.
--
-- This owner factors out the domain-independent theorem first.  For ANY Boolean
-- selector on outputs, the induced 0/1 scalar weight is:
--
--   * the identity weight on a fibre whose output is selected;
--   * the zero weight on a fibre whose output is not selected.
--
-- The exact-shell collar is only a periodic specialization of this generic
-- statement.  No quantitative commutator estimate, norm bound, shell gain,
-- cutoff-uniform budget, or Clay promotion is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNUpperShellCollarRemoteSplitExact as Collar

selectorScalar :
  ∀ {r : Level} (F : C3.RealField r) → Bool → C3.Complex F
selectorScalar F true = C3.complexOne F
selectorScalar F false = C3.complexZero F

outputLocalCellWeight :
  ∀ {r : Level} (F : C3.RealField r) →
  (Z3.FourierMode → Bool) →
  Physical.PhysicalTriadIncidence → C3.Complex F
outputLocalCellWeight F selected tau =
  selectorScalar F (selected (Physical.k tau))

outputLocalCellWeightSwapInvariant :
  ∀ {r : Level} (F : C3.RealField r) →
  (selected : Z3.FourierMode → Bool) →
  (tau : Physical.PhysicalTriadIncidence) →
  outputLocalCellWeight F selected (Symmetry.swapTriad tau)
  ≡ outputLocalCellWeight F selected tau
outputLocalCellWeightSwapInvariant F selected tau
  rewrite Symmetry.swapTriadK tau = refl

outputLocalSwapInvariantWeight :
  ∀ {r : Level} (F : C3.RealField r) →
  (Z3.FourierMode → Bool) →
  R294.SwapInvariantCellWeight F
outputLocalSwapInvariantWeight F selected = record
  { R294.weight = outputLocalCellWeight F selected
  ; R294.swapInvariant = outputLocalCellWeightSwapInvariant F selected
  }

unweightedCommutatorCell :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
unweightedCommutatorCell S velocity forcing tau =
  C3.complex3Subtract
    (R230.plusForceMinusVelocity S velocity forcing tau)
    (R230.minusForcePlusVelocity S velocity forcing tau)

activeCellReduction :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (selected : Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  selected output ≡ true →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ output →
  R294.weightedCommutatorCell
      (outputLocalSwapInvariantWeight F selected)
      S velocity forcing tau
  ≡ unweightedCommutatorCell S velocity forcing tau
activeCellReduction {F = F}
    selected output selectedOutput S velocity forcing tau outputEq
  rewrite outputEq | selectedOutput
        | R106.complex3ScaleOne
            (R230.plusForceMinusVelocity S velocity forcing tau)
        | R106.complex3ScaleOne
            (R230.minusForcePlusVelocity S velocity forcing tau)
  = refl

inactiveCellReduction :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (selected : Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  selected output ≡ false →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ output →
  R294.weightedCommutatorCell
      (outputLocalSwapInvariantWeight F selected)
      S velocity forcing tau
  ≡ C3.complex3Zero F
inactiveCellReduction {F = F}
    selected output selectedOutput S velocity forcing tau outputEq
  rewrite outputEq | selectedOutput
        | R106.complex3ScaleZeroScalar
            (R230.plusForceMinusVelocity S velocity forcing tau)
        | R106.complex3ScaleZeroScalar
            (R230.minusForcePlusVelocity S velocity forcing tau)
        | R106.complex3SubtractSelf (C3.complex3Zero F)
  = refl

activeFoldGo :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (selected : Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  selected output ≡ true →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  ((tau : Physical.PhysicalTriadIncidence) →
    tau Cube.∈ items → Physical.k tau ≡ output) →
  R224.foldVector
    (R294.weightedCommutatorCell
      (outputLocalSwapInvariantWeight F selected) S velocity forcing)
    items
  ≡ R224.foldVector (unweightedCommutatorCell S velocity forcing) items
activeFoldGo selected output selectedOutput S velocity forcing [] allOutput = refl
activeFoldGo selected output selectedOutput S velocity forcing (tau ∷ rest) allOutput =
  cong₂ C3.complex3Add
    (activeCellReduction selected output selectedOutput S velocity forcing tau
      (allOutput tau (Cube.here refl)))
    (activeFoldGo selected output selectedOutput S velocity forcing rest
      (λ chosen member → allOutput chosen (Cube.there member)))

inactiveFoldGo :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (selected : Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  selected output ≡ false →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  ((tau : Physical.PhysicalTriadIncidence) →
    tau Cube.∈ items → Physical.k tau ≡ output) →
  R224.foldVector
    (R294.weightedCommutatorCell
      (outputLocalSwapInvariantWeight F selected) S velocity forcing)
    items
  ≡ C3.complex3Zero F
inactiveFoldGo {F = F}
    selected output selectedOutput S velocity forcing [] allOutput = refl
inactiveFoldGo {F = F}
    selected output selectedOutput S velocity forcing (tau ∷ rest) allOutput =
  trans
    (cong₂ C3.complex3Add
      (inactiveCellReduction selected output selectedOutput S velocity forcing tau
        (allOutput tau (Cube.here refl)))
      (inactiveFoldGo selected output selectedOutput S velocity forcing rest
        (λ chosen member → allOutput chosen (Cube.there member))))
    (Field.complex3AddZeroLeft (C3.complex3Zero F))

outputLocalActiveFixedOutputReduction :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (selected : Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  selected output ≡ true →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  R224.foldVector
    (R294.weightedCommutatorCell
      (outputLocalSwapInvariantWeight F selected) S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
  ≡
  R224.foldVector
    (unweightedCommutatorCell S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
outputLocalActiveFixedOutputReduction
    selected output selectedOutput S velocity forcing cutoff =
  activeFoldGo selected output selectedOutput S velocity forcing
    (Output.physicalOutputFiber cutoff output)
    (λ tau member → Output.physicalOutputFiberSound member)

outputLocalInactiveFixedOutputReduction :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (selected : Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  selected output ≡ false →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  R224.foldVector
    (R294.weightedCommutatorCell
      (outputLocalSwapInvariantWeight F selected) S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
  ≡ C3.complex3Zero F
outputLocalInactiveFixedOutputReduction
    selected output selectedOutput S velocity forcing cutoff =
  inactiveFoldGo selected output selectedOutput S velocity forcing
    (Output.physicalOutputFiber cutoff output)
    (λ tau member → Output.physicalOutputFiberSound member)

collarActiveFixedOutputReduction :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (shell : Nat) (output : Z3.FourierMode) →
  Collar.collarShellPacket shell output ≡ true →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  R224.foldVector
    (R294.weightedCommutatorCell
      (outputLocalSwapInvariantWeight F (Collar.collarShellPacket shell))
      S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
  ≡
  R224.foldVector
    (unweightedCommutatorCell S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
collarActiveFixedOutputReduction shell output active =
  outputLocalActiveFixedOutputReduction
    (Collar.collarShellPacket shell) output active

collarInactiveFixedOutputReduction :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  (shell : Nat) (output : Z3.FourierMode) →
  Collar.collarShellPacket shell output ≡ false →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  R224.foldVector
    (R294.weightedCommutatorCell
      (outputLocalSwapInvariantWeight F (Collar.collarShellPacket shell))
      S velocity forcing)
    (Output.physicalOutputFiber cutoff output)
  ≡ C3.complex3Zero F
collarInactiveFixedOutputReduction shell output inactive =
  outputLocalInactiveFixedOutputReduction
    (Collar.collarShellPacket shell) output inactive

outputLocalActiveFixedOutputReductionClosed : Bool
outputLocalActiveFixedOutputReductionClosed = true

outputLocalInactiveFixedOutputReductionClosed : Bool
outputLocalInactiveFixedOutputReductionClosed = true

collarFixedOutputSelectorReductionClosed : Bool
collarFixedOutputSelectorReductionClosed = true

collarQuantitativeFixedOutputPaymentClosed : Bool
collarQuantitativeFixedOutputPaymentClosed = false

outputLocalActiveFixedOutputReductionClosedIsTrue :
  outputLocalActiveFixedOutputReductionClosed ≡ true
outputLocalActiveFixedOutputReductionClosedIsTrue = refl

outputLocalInactiveFixedOutputReductionClosedIsTrue :
  outputLocalInactiveFixedOutputReductionClosed ≡ true
outputLocalInactiveFixedOutputReductionClosedIsTrue = refl

collarFixedOutputSelectorReductionClosedIsTrue :
  collarFixedOutputSelectorReductionClosed ≡ true
collarFixedOutputSelectorReductionClosedIsTrue = refl

collarQuantitativeFixedOutputPaymentClosedIsFalse :
  collarQuantitativeFixedOutputPaymentClosed ≡ false
collarQuantitativeFixedOutputPaymentClosedIsFalse = refl
