module DASHI.Physics.Closure.NSTriadKNCenteredPartnerSlotDefectExact where

------------------------------------------------------------------------
-- PR #890 / QUOTIENT-CORRECT SLOT DEFECT
--
-- The observable quotient is the physical slot-kernel value itself.  Define
-- the pair defect by the squared norm of the literal slot-kernel difference.
-- This vanishes on every incidence fibre erased by the slot map, so it does
-- not manufacture separation on raw-incidence labels.
--
-- The P0 adapter already proves
--
--   B_alpha - B_beta = (K_alpha-K_beta) + (K_alpha-K_beta).
--
-- This file records the exact norm consequence
--
--   ||B_alpha-B_beta||^2 = 4 ||K_alpha-K_beta||^2.
--
-- No radial/Pluecker lower bound, centered-moment estimate, cutoff estimate,
-- spacetime estimate, or Clay promotion is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComparableRawCurlPartnerMassRound205Exact as R205
import DASHI.Physics.Closure.NSTriadKNCenteredPartnerDifferenceAdapterExact as Adapter

F : C3.RealField _
F = Rational.rationalRealField

four : ℚ
four = (1ℚ + 1ℚ) * (1ℚ + 1ℚ)

slotObservableDefect :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  R205.LocalizedComparableRawCurlPartner system →
  R205.LocalizedComparableRawCurlPartner system → ℚ
slotObservableDefect alpha beta =
  L2.complex3NormSquared
    (Adapter.compressedPartnerSlotKernelDifference alpha beta)

doubleVectorNormSquared :
  (value : C3.Complex3 F) →
  L2.complex3NormSquared (C3.complex3Add value value)
  ≡ four * L2.complex3NormSquared value
doubleVectorNormSquared
    (C3.complex3
      (C3.complex xr xi)
      (C3.complex yr yi)
      (C3.complex zr zi)) =
  solve (xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi ∷ [])

compressedPartnerDifferenceNormIsFourSlotDefect :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (alpha beta : R205.LocalizedComparableRawCurlPartner system) →
  L2.complex3NormSquared (Adapter.compressedPartnerDifference alpha beta)
  ≡ four * slotObservableDefect alpha beta
compressedPartnerDifferenceNormIsFourSlotDefect alpha beta =
  trans
    (cong L2.complex3NormSquared
      (Adapter.compressedPartnerDifferenceIsDoubleSlotKernelDifference alpha beta))
    (doubleVectorNormSquared
      (Adapter.compressedPartnerSlotKernelDifference alpha beta))

roundCenteredPartnerSlotObservableDefectConstructed : Bool
roundCenteredPartnerSlotObservableDefectConstructed = true

roundCenteredPartnerCompressedDifferenceIsFourSlotDefect : Bool
roundCenteredPartnerCompressedDifferenceIsFourSlotDefect = true

roundCenteredPartnerSlotDefectRadialPlueckerLowerBoundClosed : Bool
roundCenteredPartnerSlotDefectRadialPlueckerLowerBoundClosed = false

roundCenteredPartnerSlotDefectClayPromotion : Bool
roundCenteredPartnerSlotDefectClayPromotion = false

roundCenteredPartnerCompressedDifferenceIsFourSlotDefectIsTrue :
  roundCenteredPartnerCompressedDifferenceIsFourSlotDefect ≡ true
roundCenteredPartnerCompressedDifferenceIsFourSlotDefectIsTrue = refl

roundCenteredPartnerSlotDefectRadialPlueckerLowerBoundClosedIsFalse :
  roundCenteredPartnerSlotDefectRadialPlueckerLowerBoundClosed ≡ false
roundCenteredPartnerSlotDefectRadialPlueckerLowerBoundClosedIsFalse = refl
