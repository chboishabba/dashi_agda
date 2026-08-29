module DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact where

------------------------------------------------------------------------
-- ROUND225 / COMPLETE FIXED-OUTPUT QUADRATIC COMPANION = FOUR MIXED CHANNEL
--
-- R223 removes the ++/-- helicity channels pointwise:
--
--   i K_pq = 2 (A_pq - B_pq),
--   A_pq = u_p+ x u_q-,
--   B_pq = u_p- x u_q+.
--
-- R224 proves exact fixed-output swap reindexing B -> -A.  Therefore on the
-- COMPLETE physical output fibre
--
--   sum i K_pq = 4 sum A_pq.
--
-- This is an exact finite identity, not a norm estimate.  It identifies the
-- remaining Package-A coherent object with ONE mixed-helicity convolution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNMixedHelicityQuadraticKernelRound223Exact as R223
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224

complex3NegateAdd :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.complex3Negate (C3.complex3Add u v)
  ≡ C3.complex3Add (C3.complex3Negate u) (C3.complex3Negate v)
complex3NegateAdd {F = F} (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Field.complex3Ext
    (R.solve 2 (λ u v → R.⊝ (u R.⊕ v) R.⊜ ((R.⊝ u) R.⊕ (R.⊝ v))) refl ux vx)
    (R.solve 2 (λ u v → R.⊝ (u R.⊕ v) R.⊜ ((R.⊝ u) R.⊕ (R.⊝ v))) refl uy vy)
    (R.solve 2 (λ u v → R.⊝ (u R.⊕ v) R.⊜ ((R.⊝ u) R.⊕ (R.⊝ v))) refl uz vz)
  where module R = Ring.Solver F

complex3NegateZero :
  ∀ {r} {F : C3.RealField r} →
  C3.complex3Negate (C3.complex3Zero F) ≡ C3.complex3Zero F
complex3NegateZero {F = F} =
  Field.complex3Ext
    (R.solve 0 (R.⊝ R.Κ (C3.complexZero F) R.⊜ R.Κ (C3.complexZero F)) refl)
    (R.solve 0 (R.⊝ R.Κ (C3.complexZero F) R.⊜ R.Κ (C3.complexZero F)) refl)
    (R.solve 0 (R.⊝ R.Κ (C3.complexZero F) R.⊜ R.Κ (C3.complexZero F)) refl)
  where module R = Ring.Solver F

foldPointwiseAdd :
  ∀ {r} {F : C3.RealField r}
    (left right : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector (λ tau → C3.complex3Add (left tau) (right tau)) items
  ≡ C3.complex3Add (R224.foldVector left items) (R224.foldVector right items)
foldPointwiseAdd {F = F} left right [] =
  Field.complex3Ext
    (R.solve 0
      (R.Κ (C3.complexZero F) R.⊜
        (R.Κ (C3.complexZero F) R.⊕ R.Κ (C3.complexZero F))) refl)
    (R.solve 0
      (R.Κ (C3.complexZero F) R.⊜
        (R.Κ (C3.complexZero F) R.⊕ R.Κ (C3.complexZero F))) refl)
    (R.solve 0
      (R.Κ (C3.complexZero F) R.⊜
        (R.Κ (C3.complexZero F) R.⊕ R.Κ (C3.complexZero F))) refl)
  where module R = Ring.Solver F
foldPointwiseAdd {F = F} left right (tau ∷ rest) =
  trans
    (cong (C3.complex3Add (C3.complex3Add (left tau) (right tau)))
      (foldPointwiseAdd left right rest))
    (vectorAddRegroup
      (left tau) (right tau)
      (R224.foldVector left rest) (R224.foldVector right rest))
  where
  vectorAddRegroup : ∀ (a b c d : C3.Complex3 F) →
    C3.complex3Add (C3.complex3Add a b) (C3.complex3Add c d)
    ≡ C3.complex3Add (C3.complex3Add a c) (C3.complex3Add b d)
  vectorAddRegroup
      (C3.complex3 ax ay az) (C3.complex3 bx by bz)
      (C3.complex3 cx cy cz) (C3.complex3 dx dy dz) =
    Field.complex3Ext
      (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl ax bx cx dx)
      (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl ay by cy dy)
      (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (c R.⊕ d)) R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d))) refl az bz cz dz)
    where module R = Ring.Solver F

foldPointwiseNegate :
  ∀ {r} {F : C3.RealField r}
    (value : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector (λ tau → C3.complex3Negate (value tau)) items
  ≡ C3.complex3Negate (R224.foldVector value items)
foldPointwiseNegate value [] = sym complex3NegateZero
foldPointwiseNegate value (tau ∷ rest) =
  trans
    (cong (C3.complex3Add (C3.complex3Negate (value tau)))
      (foldPointwiseNegate value rest))
    (sym (complex3NegateAdd (value tau) (R224.foldVector value rest)))

foldPointwiseSubtract :
  ∀ {r} {F : C3.RealField r}
    (left right : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector (λ tau → C3.complex3Subtract (left tau) (right tau)) items
  ≡ C3.complex3Subtract
      (R224.foldVector left items)
      (R224.foldVector right items)
foldPointwiseSubtract left right items =
  trans
    (foldPointwiseAdd left (λ tau → C3.complex3Negate (right tau)) items)
    (cong (C3.complex3Add (R224.foldVector left items))
      (foldPointwiseNegate right items))

fixedOutputMinusPlusSumIsNegativePlusMinusSum :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (R224.mixedMinusPlus S velocity)
    (Output.physicalOutputFiber cutoff output)
  ≡ C3.complex3Negate
      (R224.foldVector (R224.mixedPlusMinus S velocity)
        (Output.physicalOutputFiber cutoff output))
fixedOutputMinusPlusSumIsNegativePlusMinusSum S velocity cutoff output =
  trans
    (R224.fixedOutputMinusPlusReindexesToNegativePlusMinus
      S velocity cutoff output)
    (foldPointwiseNegate (R224.mixedPlusMinus S velocity)
      (Output.physicalOutputFiber cutoff output))

fourCopies :
  ∀ {r} {F : C3.RealField r} → C3.Complex3 F → C3.Complex3 F
fourCopies value =
  C3.complex3Add
    (C3.complex3Add value value)
    (C3.complex3Add value value)

mixedDifferenceCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
mixedDifferenceCell S velocity tau =
  C3.complex3Subtract
    (R224.mixedPlusMinus S velocity tau)
    (R224.mixedMinusPlus S velocity tau)

doubleMixedCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
doubleMixedCell S velocity tau =
  C3.complex3Add
    (mixedDifferenceCell S velocity tau)
    (mixedDifferenceCell S velocity tau)

fixedOutputDoubleMixedSumIsFourPlusMinusSum :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (doubleMixedCell S velocity)
    (Output.physicalOutputFiber cutoff output)
  ≡ fourCopies
      (R224.foldVector (R224.mixedPlusMinus S velocity)
        (Output.physicalOutputFiber cutoff output))
fixedOutputDoubleMixedSumIsFourPlusMinusSum {F = F}
    S velocity cutoff output =
  let
    fibre = Output.physicalOutputFiber cutoff output
    A = R224.foldVector (R224.mixedPlusMinus S velocity) fibre
    B = R224.foldVector (R224.mixedMinusPlus S velocity) fibre
    Bneg = fixedOutputMinusPlusSumIsNegativePlusMinusSum S velocity cutoff output
    first = foldPointwiseAdd
      (mixedDifferenceCell S velocity) (mixedDifferenceCell S velocity) fibre
    diff = foldPointwiseSubtract
      (R224.mixedPlusMinus S velocity) (R224.mixedMinusPlus S velocity) fibre
    endpoint :
      C3.complex3Add
        (C3.complex3Subtract A (C3.complex3Negate A))
        (C3.complex3Subtract A (C3.complex3Negate A))
      ≡ fourCopies A
    endpoint = additiveFour A
  in
  trans first
    (trans
      (cong₂ C3.complex3Add diff diff)
      (trans
        (cong₂ C3.complex3Add
          (cong (C3.complex3Subtract A) Bneg)
          (cong (C3.complex3Subtract A) Bneg))
        endpoint))
  where
  additiveFour : (a : C3.Complex3 F) →
    C3.complex3Add
      (C3.complex3Subtract a (C3.complex3Negate a))
      (C3.complex3Subtract a (C3.complex3Negate a))
    ≡ fourCopies a
  additiveFour (C3.complex3 ax ay az) =
    Field.complex3Ext
      (R.solve 1
        (λ a → ((a R.⊕ (R.⊝ (R.⊝ a))) R.⊕ (a R.⊕ (R.⊝ (R.⊝ a))))
          R.⊜ ((a R.⊕ a) R.⊕ (a R.⊕ a))) refl ax)
      (R.solve 1
        (λ a → ((a R.⊕ (R.⊝ (R.⊝ a))) R.⊕ (a R.⊕ (R.⊝ (R.⊝ a))))
          R.⊜ ((a R.⊕ a) R.⊕ (a R.⊕ a))) refl ay)
      (R.solve 1
        (λ a → ((a R.⊕ (R.⊝ (R.⊝ a))) R.⊕ (a R.⊕ (R.⊝ (R.⊝ a))))
          R.⊜ ((a R.⊕ a) R.⊕ (a R.⊕ a))) refl az)
    where module R = Ring.Solver F

record PhysicalFixedOutputHelicityData
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (velocity : Z3.FourierMode → C3.Complex3 F) : Set r where
  constructor physical-fixed-output-helicity-data
  field
    velocityTransverse :
      (mode : Z3.FourierMode) → Helical.Transverse E mode (velocity mode)

open PhysicalFixedOutputHelicityData public

iQuadraticKernelCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
iQuadraticKernelCell {E = E} S velocity tau =
  C3.complex3Scale (C3.complexI _)
    (R145.slotKernel
      (R167.normalizedDirection E S (Physical.p tau))
      (R167.normalizedDirection E S (Physical.q tau))
      (velocity (Physical.p tau))
      (velocity (Physical.q tau)))

iQuadraticKernelCellIsDoubleMixedCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    {velocity : Z3.FourierMode → C3.Complex3 F}
    (P : PhysicalFixedOutputHelicityData E I S L H velocity)
    (tau : Physical.PhysicalTriadIncidence) →
  iQuadraticKernelCell S velocity tau ≡ doubleMixedCell S velocity tau
iQuadraticKernelCellIsDoubleMixedCell {E = E} {I = I} {S = S}
    {L = L} {H = H} {velocity = velocity} P tau =
  R223.iQuadraticKernelIsDoubleMixedHelicity
    (Physical.p tau) (Physical.q tau)
    (velocity (Physical.p tau)) (velocity (Physical.q tau))
    (R223.physical-helicity-pair
      (velocityTransverse P (Physical.p tau))
      (velocityTransverse P (Physical.q tau)))

fixedOutputQuadraticKernelIsFourMixedHelicityConvolution :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    {velocity : Z3.FourierMode → C3.Complex3 F}
    (P : PhysicalFixedOutputHelicityData E I S L H velocity)
    (cutoff : Nat) (output : Z3.FourierMode) →
  R224.foldVector (iQuadraticKernelCell S velocity)
    (Output.physicalOutputFiber cutoff output)
  ≡ fourCopies
      (R224.foldVector (R224.mixedPlusMinus S velocity)
        (Output.physicalOutputFiber cutoff output))
fixedOutputQuadraticKernelIsFourMixedHelicityConvolution
    {S = S} {velocity = velocity} P cutoff output =
  trans
    (foldPointwise
      (Output.physicalOutputFiber cutoff output))
    (fixedOutputDoubleMixedSumIsFourPlusMinusSum S velocity cutoff output)
  where
  foldPointwise :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector (iQuadraticKernelCell S velocity) items
    ≡ R224.foldVector (doubleMixedCell S velocity) items
  foldPointwise [] = refl
  foldPointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (iQuadraticKernelCellIsDoubleMixedCell P tau)
      (foldPointwise rest)

round225CompleteFixedOutputKernelMixedHelicityCollapseClosed : Bool
round225CompleteFixedOutputKernelMixedHelicityCollapseClosed = true

round225SameHelicityChannelsSurviveInCompanion : Bool
round225SameHelicityChannelsSurviveInCompanion = false

round225MixedHelicityIntegratedBudgetClosed : Bool
round225MixedHelicityIntegratedBudgetClosed = false

round225PackageAClosed : Bool
round225PackageAClosed = false

round225ClayPromotion : Bool
round225ClayPromotion = false

round225CompleteFixedOutputKernelMixedHelicityCollapseClosedIsTrue :
  round225CompleteFixedOutputKernelMixedHelicityCollapseClosed ≡ true
round225CompleteFixedOutputKernelMixedHelicityCollapseClosedIsTrue = refl

round225SameHelicityChannelsSurviveInCompanionIsFalse :
  round225SameHelicityChannelsSurviveInCompanion ≡ false
round225SameHelicityChannelsSurviveInCompanionIsFalse = refl

round225MixedHelicityIntegratedBudgetClosedIsFalse :
  round225MixedHelicityIntegratedBudgetClosed ≡ false
round225MixedHelicityIntegratedBudgetClosedIsFalse = refl

round225PackageAClosedIsFalse : round225PackageAClosed ≡ false
round225PackageAClosedIsFalse = refl

round225ClayPromotionIsFalse : round225ClayPromotion ≡ false
round225ClayPromotionIsFalse = refl
