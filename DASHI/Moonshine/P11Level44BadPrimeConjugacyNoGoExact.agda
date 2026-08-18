module DASHI.Moonshine.P11Level44BadPrimeConjugacyNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", GTM 228, Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- Kimball Martin,
-- "The basis problem revisited", Trans. Amer. Math. Soc. 373 (2020),
-- 4523--4559. DOI: 10.1090/tran/8077.
--
-- DASHI CONTRIBUTION
--
-- Strengthen P11Level44BadPrimeOperatorSeparationExact from a failure of the
-- canonical common-coordinate comparison to a genuine arbitrary linear-change-
-- of-basis no-go.
--
-- The internal marked operator on Old3 is
--
--          [ 0 -1 -1 ]
--   R2  =  [-1  0 -1 ]
--          [-1 -1  0 ].
--
-- Its integral adjugate-style companion
--
--          [ 1 -1 -1 ]
--   B   =  [-1  1 -1 ]
--          [-1 -1  1 ]
--
-- satisfies B R2 = 2 I.  Integer cancellation therefore proves R2 has
-- trivial kernel on the exact integral Old3 carrier.
--
-- The classical Gamma_0(4) U2 already has the explicit nonzero kernel vector
-- (1,2,2).  Consequently there is NO zero-preserving invertible map A with
--
--     A U2 = R2 A.
--
-- Thus the missing local p=11 test-vector comparison cannot rescue the
-- internally-discovered positive marked R2 by a clever change of basis.  The
-- correct principal-level-2 bad-prime operator, if transported from analytic
-- U2, must be a DIFFERENT source-native local operator.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
import Data.Integer.Properties as ℤP
import Data.Integer.Tactic.RingSolver as ℤRing

import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Old
import DASHI.Moonshine.P11Level44BadPrimeOperatorSeparationExact as Bad

------------------------------------------------------------------------
-- Old3 extensionality.
------------------------------------------------------------------------

old3Ext :
  (u v : Old.Old3) →
  Old.x1 u ≡ Old.x1 v →
  Old.x2 u ≡ Old.x2 v →
  Old.x4 u ≡ Old.x4 v →
  u ≡ v
old3Ext
  (Old.old3 a b c)
  (Old.old3 a' b' c')
  refl refl refl = refl

------------------------------------------------------------------------
-- Integral adjugate witness B R2 = 2 I.
------------------------------------------------------------------------

markedR2Adjugate : Old.Old3 → Old.Old3
markedR2Adjugate (Old.old3 x y z) = Old.old3
  (x +ℤ ((-[1+ 0 ]) *ℤ y) +ℤ ((-[1+ 0 ]) *ℤ z))
  (((-[1+ 0 ]) *ℤ x) +ℤ y +ℤ ((-[1+ 0 ]) *ℤ z))
  (((-[1+ 0 ]) *ℤ x) +ℤ ((-[1+ 0 ]) *ℤ y) +ℤ z)

markedR2AdjugateAtZero :
  markedR2Adjugate Bad.zeroOld3 ≡ Bad.zeroOld3
markedR2AdjugateAtZero = refl

adjugateAfterMarkedR2IsTwoIdentity :
  (v : Old.Old3) →
  markedR2Adjugate (Bad.markedR2OnOld3 v)
  ≡ Old.scaleOld3 (+ 2) v
adjugateAfterMarkedR2IsTwoIdentity (Old.old3 x y z) =
  old3Ext _ _
    (ℤRing.solve (x ∷ y ∷ z ∷ []))
    (ℤRing.solve (x ∷ y ∷ z ∷ []))
    (ℤRing.solve (x ∷ y ∷ z ∷ []))

------------------------------------------------------------------------
-- Multiplication by 2 is cancellable over the exact integer coordinates.
------------------------------------------------------------------------

twoTimesIntegerZeroImpliesZero :
  (x : ℤ) → (+ 2) *ℤ x ≡ (+ 0) → x ≡ (+ 0)
twoTimesIntegerZeroImpliesZero x equation =
  ℤP.*-cancelˡ-≡ (+ 2) x (+ 0)
    (trans equation (sym (ℤRing.solve (x ∷ []))))

scaleTwoZeroImpliesZero :
  (v : Old.Old3) →
  Old.scaleOld3 (+ 2) v ≡ Bad.zeroOld3 →
  v ≡ Bad.zeroOld3
scaleTwoZeroImpliesZero (Old.old3 x y z) equation =
  old3Ext _ _
    (twoTimesIntegerZeroImpliesZero x
      (cong Old.x1 equation))
    (twoTimesIntegerZeroImpliesZero y
      (cong Old.x2 equation))
    (twoTimesIntegerZeroImpliesZero z
      (cong Old.x4 equation))

------------------------------------------------------------------------
-- Internal marked R2 has trivial kernel.  This is all the conjugacy no-go
-- actually needs; no separate assumption-aware matrix solver is introduced.
------------------------------------------------------------------------

markedR2KernelTrivial :
  (v : Old.Old3) →
  Bad.markedR2OnOld3 v ≡ Bad.zeroOld3 →
  v ≡ Bad.zeroOld3
markedR2KernelTrivial v equation =
  scaleTwoZeroImpliesZero v
    (trans
      (sym (adjugateAfterMarkedR2IsTwoIdentity v))
      (trans
        (cong markedR2Adjugate equation)
        markedR2AdjugateAtZero))

------------------------------------------------------------------------
-- Any genuine linear comparison needs an invertible zero-preserving map and
-- the operator commuting square.  Those hypotheses are already inconsistent.
------------------------------------------------------------------------

record U2R2LinearConjugacy : Set where
  field
    forward backward : Old.Old3 → Old.Old3
    backwardAfterForward :
      (v : Old.Old3) → backward (forward v) ≡ v
    forwardZero : forward Bad.zeroOld3 ≡ Bad.zeroOld3
    intertwinesBadPrime :
      (v : Old.Old3) →
      forward (Bad.analyticU2 v)
      ≡ Bad.markedR2OnOld3 (forward v)

open U2R2LinearConjugacy public

u2R2LinearConjugacyImpossible : U2R2LinearConjugacy → Bad.Impossible
u2R2LinearConjugacyImpossible C =
  let
    kernel = Bad.analyticU2KernelVector

    imageKilled :
      Bad.markedR2OnOld3 (forward C kernel) ≡ Bad.zeroOld3
    imageKilled =
      trans
        (sym (intertwinesBadPrime C kernel))
        (trans
          (cong (forward C) Bad.analyticU2HasNonzeroKernel)
          (forwardZero C))

    imageZero : forward C kernel ≡ Bad.zeroOld3
    imageZero = markedR2KernelTrivial (forward C kernel) imageKilled

    backwardZero : backward C Bad.zeroOld3 ≡ Bad.zeroOld3
    backwardZero =
      trans
        (cong (backward C) (sym (forwardZero C)))
        (backwardAfterForward C Bad.zeroOld3)

    kernelZero : kernel ≡ Bad.zeroOld3
    kernelZero =
      trans
        (sym (backwardAfterForward C kernel))
        (trans
          (cong (backward C) imageZero)
          backwardZero)
  in
  Bad.analyticKernelVectorNonzero kernelZero

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record P11Level44BadPrimeConjugacyNoGoBoundary : Set where
  field
    integralAdjugateConstructed : Bool
    adjugateTimesMarkedR2EqualsTwoIdentity : Bool
    markedR2KernelTrivialDerived : Bool
    analyticU2HasNonzeroKernel : Bool
    arbitraryInvertibleU2R2IntertwinerPossible : Bool
    transportedPrincipalLevel2OperatorMustDifferFromInternalR2 : Bool
    actualTwoAdicTestVectorTransformConstructedHere : Bool

canonicalP11Level44BadPrimeConjugacyNoGoBoundary :
  P11Level44BadPrimeConjugacyNoGoBoundary
canonicalP11Level44BadPrimeConjugacyNoGoBoundary = record
  { integralAdjugateConstructed = true
  ; adjugateTimesMarkedR2EqualsTwoIdentity = true
  ; markedR2KernelTrivialDerived = true
  ; analyticU2HasNonzeroKernel = true
  ; arbitraryInvertibleU2R2IntertwinerPossible = false
  ; transportedPrincipalLevel2OperatorMustDifferFromInternalR2 = true
  ; actualTwoAdicTestVectorTransformConstructedHere = false
  }
