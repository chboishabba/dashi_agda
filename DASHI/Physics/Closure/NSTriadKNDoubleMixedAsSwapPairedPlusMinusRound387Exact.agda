module DASHI.Physics.Closure.NSTriadKNDoubleMixedAsSwapPairedPlusMinusRound387Exact where

------------------------------------------------------------------------
-- ROUND387 / DOUBLE-MIXED CELL AS TWO PLUS-MINUS SWAP PARTNERS
--
-- R386 identifies the literal R378 Gram debt with the pointwise double-mixed
-- carrier.  R382 already owns the exact damped tangent for the plus-minus
-- mixed cell.  The shortest same-object bridge is therefore to rewrite the
-- second mixed channel by the existing p/q swap, rather than proving a second
-- helical-projector tangent from scratch.
--
-- R224 proves
--
--   B(swap tau) = - A(tau).
--
-- By swap involutivity,
--
--   B(tau) = - A(swap tau),
--
-- hence R225's pointwise
--
--   doubleMixed(tau) = 2 (A(tau) - B(tau))
--
-- becomes exactly
--
--   doubleMixed(tau) = 2 A(tau) + 2 A(swap tau).
--
-- This is finite carrier algebra only.  It is the representation in which the
-- already-closed R382 plus-minus tangent can be applied to both summands.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225

mixedMinusPlusIsNegativeSwappedPlusMinus :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  R224.mixedMinusPlus S velocity tau
  ≡ C3.complex3Negate
      (R224.mixedPlusMinus S velocity (Symmetry.swapTriad tau))
mixedMinusPlusIsNegativeSwappedPlusMinus S velocity tau =
  let
    atSwap = R224.mixedMinusPlusAfterSwapIsNegativePlusMinus
      S velocity (Symmetry.swapTriad tau)
  in
  trans
    (cong (R224.mixedMinusPlus S velocity)
      (R38.swapTriadInvolutiveExact tau))
    atSwap

doublePlus :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F
doublePlus value = C3.complex3Add value value

doubleMixedIsSwapPairedPlusMinus :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  R225.doubleMixedCell S velocity tau
  ≡ C3.complex3Add
      (doublePlus (R224.mixedPlusMinus S velocity tau))
      (doublePlus
        (R224.mixedPlusMinus S velocity (Symmetry.swapTriad tau)))
doubleMixedIsSwapPairedPlusMinus {F = F} S velocity tau =
  let
    A = R224.mixedPlusMinus S velocity tau
    As = R224.mixedPlusMinus S velocity (Symmetry.swapTriad tau)
    B = R224.mixedMinusPlus S velocity tau
    Bneg = mixedMinusPlusIsNegativeSwappedPlusMinus S velocity tau
  in
  trans
    (cong
      (λ selectedB →
        C3.complex3Add
          (C3.complex3Subtract A selectedB)
          (C3.complex3Subtract A selectedB))
      Bneg)
    (expand A As)
  where
  expand : (a b : C3.Complex3 F) →
    C3.complex3Add
      (C3.complex3Subtract a (C3.complex3Negate b))
      (C3.complex3Subtract a (C3.complex3Negate b))
    ≡ C3.complex3Add (doublePlus a) (doublePlus b)
  expand
      (C3.complex3 ax ay az)
      (C3.complex3 bx by bz) =
    Field.complex3Ext
      (R.solve 2
        (λ a b → ((a R.⊕ (R.⊝ (R.⊝ b))) R.⊕ (a R.⊕ (R.⊝ (R.⊝ b))))
          R.⊜ ((a R.⊕ a) R.⊕ (b R.⊕ b))) refl ax bx)
      (R.solve 2
        (λ a b → ((a R.⊕ (R.⊝ (R.⊝ b))) R.⊕ (a R.⊕ (R.⊝ (R.⊝ b))))
          R.⊜ ((a R.⊕ a) R.⊕ (b R.⊕ b))) refl ay by)
      (R.solve 2
        (λ a b → ((a R.⊕ (R.⊝ (R.⊝ b))) R.⊕ (a R.⊕ (R.⊝ (R.⊝ b))))
          R.⊜ ((a R.⊕ a) R.⊕ (b R.⊕ b))) refl az bz)
    where module R = Ring.Solver F

round387DoubleMixedReducedToTwoR382Cells : Bool
round387DoubleMixedReducedToTwoR382Cells = true

round387SecondProjectorTangentNeeded : Bool
round387SecondProjectorTangentNeeded = false

round387DoubleMixedReducedToTwoR382CellsIsTrue :
  round387DoubleMixedReducedToTwoR382Cells ≡ true
round387DoubleMixedReducedToTwoR382CellsIsTrue = refl
