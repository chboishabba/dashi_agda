module DASHI.Physics.Closure.NSTriadKNOutputTransverseCrossLerayCancellationRound131Exact where

------------------------------------------------------------------------
-- ROUND131 / EXACT EXTREMAL HH CANCELLATION FROM OUTPUT TRANSVERSALITY
--
-- Companion Lean result:
--   RequestProject/NavierStokes/WaleffeHighHighOutputGain.lean
--
-- The Lean lane observed that the sharp radial-gap endpoint is collinear and
-- contributes zero because two velocities transverse to the output direction
-- have a cross product parallel to that output, hence killed by Leray.
--
-- This file proves the exact algebraic core on the repository's literal C^3
-- carrier.  No norm, square root, angle, shell count, cardinality, or estimate
-- is used.
--
--  1. BAC-CAB is proved directly by the complex commutative-ring solver.
--  2. If k.u = k.v = 0 then k x (u x v) = 0.
--  3. If k x w = 0 then |k|^2 w = (k.w) k.
--  4. For a nonzero Fourier output, the exact inverse-square law converts this
--     into w = |k|^{-2}(k.w)k, so P_k w = 0.
--
-- Consequently
--
--   k.u = 0, k.v = 0  ==>  P_k(u x v) = 0.
--
-- This is the exact vector cancellation needed by the collinear extremal
-- incidences of the HH->low multiplier-gap bound.  A later physical bridge
-- only has to transport incompressibility of collinear input legs to
-- transversality against the common output direction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as ScalarLinear
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayExact

------------------------------------------------------------------------
-- Exact vector triple product.
------------------------------------------------------------------------

bacCab :
  ∀ {r} {F : C3.RealField r}
    (a b c : C3.Complex3 F) →
  Cross.complex3Cross a (Cross.complex3Cross b c)
  ≡
  C3.complex3Subtract
    (C3.complex3Scale (C3.bilinearDot3 a c) b)
    (C3.complex3Scale (C3.bilinearDot3 a b) c)
bacCab {F = F}
    (C3.complex3 ax ay az)
    (C3.complex3 bx by bz)
    (C3.complex3 cx cy cz) =
  Field.complex3Ext
    (R.solve 9
      (λ ax ay az bx by bz cx cy cz →
        (ay R.⊗ ((bx R.⊗ cy) R.⊕ (R.⊝ (by R.⊗ cx))))
          R.⊕
        (R.⊝ (az R.⊗ ((bz R.⊗ cx) R.⊕ (R.⊝ (bx R.⊗ cz)))))
        R.⊜
        (bx R.⊗ (((ax R.⊗ cx) R.⊕ (ay R.⊗ cy)) R.⊕ (az R.⊗ cz)))
          R.⊕
        (R.⊝ (cx R.⊗ (((ax R.⊗ bx) R.⊕ (ay R.⊗ by)) R.⊕ (az R.⊗ bz)))))
      refl ax ay az bx by bz cx cy cz)
    (R.solve 9
      (λ ax ay az bx by bz cx cy cz →
        (az R.⊗ ((by R.⊗ cz) R.⊕ (R.⊝ (bz R.⊗ cy))))
          R.⊕
        (R.⊝ (ax R.⊗ ((bx R.⊗ cy) R.⊕ (R.⊝ (by R.⊗ cx)))))
        R.⊜
        (by R.⊗ (((ax R.⊗ cx) R.⊕ (ay R.⊗ cy)) R.⊕ (az R.⊗ cz)))
          R.⊕
        (R.⊝ (cy R.⊗ (((ax R.⊗ bx) R.⊕ (ay R.⊗ by)) R.⊕ (az R.⊗ bz)))))
      refl ax ay az bx by bz cx cy cz)
    (R.solve 9
      (λ ax ay az bx by bz cx cy cz →
        (ax R.⊗ ((bz R.⊗ cx) R.⊕ (R.⊝ (bx R.⊗ cz))))
          R.⊕
        (R.⊝ (ay R.⊗ ((by R.⊗ cz) R.⊕ (R.⊝ (bz R.⊗ cy)))))
        R.⊜
        (bz R.⊗ (((ax R.⊗ cx) R.⊕ (ay R.⊗ cy)) R.⊕ (az R.⊗ cz)))
          R.⊕
        (R.⊝ (cz R.⊗ (((ax R.⊗ bx) R.⊕ (ay R.⊗ by)) R.⊕ (az R.⊗ bz)))))
      refl ax ay az bx by bz cx cy cz)
  where module R = Ring.Solver F

crossZeroRight :
  ∀ {r} {F : C3.RealField r}
    (value : C3.Complex3 F) →
  Cross.complex3Cross value (C3.complex3Zero F) ≡ C3.complex3Zero F
crossZeroRight {F = F} (C3.complex3 x y z) =
  Field.complex3Ext
    (R.solve 2
      (λ y z →
        (y R.⊗ R.Κ (C3.complexZero F))
          R.⊕ (R.⊝ (z R.⊗ R.Κ (C3.complexZero F)))
        R.⊜ R.Κ (C3.complexZero F)) refl y z)
    (R.solve 2
      (λ z x →
        (z R.⊗ R.Κ (C3.complexZero F))
          R.⊕ (R.⊝ (x R.⊗ R.Κ (C3.complexZero F)))
        R.⊜ R.Κ (C3.complexZero F)) refl z x)
    (R.solve 2
      (λ x y →
        (x R.⊗ R.Κ (C3.complexZero F))
          R.⊕ (R.⊝ (y R.⊗ R.Κ (C3.complexZero F)))
        R.⊜ R.Κ (C3.complexZero F)) refl x y)
  where module R = Ring.Solver F

------------------------------------------------------------------------
-- Additive cancellation on the weak RealField/Complex carrier.
------------------------------------------------------------------------

complexSubtractZeroImpliesEqual :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Complex F) →
  C3.complexSubtract left right ≡ C3.complexZero F →
  left ≡ right
complexSubtractZeroImpliesEqual {F = F}
    (C3.complex lr li) (C3.complex rr ri) proof =
  Field.complexExt
    (realSubtractZeroImpliesEqual lr rr
      (cong C3.real proof))
    (realSubtractZeroImpliesEqual li ri
      (cong C3.imaginary proof))
  where
  realSubtractZeroImpliesEqual :
    (a b : C3.Carrier F) →
    C3.add F a (C3.negate F b) ≡ C3.zero F →
    a ≡ b
  realSubtractZeroImpliesEqual a b zeroDifference =
    let
      negbEqualsNega : C3.negate F b ≡ C3.negate F a
      negbEqualsNega =
        trans
          (sym (C3.addZeroLeft F (C3.negate F b)))
          (trans
            (cong (λ x → C3.add F x (C3.negate F b))
              (sym (C3.addInverseLeft F a)))
            (trans
              (C3.addAssociative F (C3.negate F a) a (C3.negate F b))
              (trans
                (cong (C3.add F (C3.negate F a)) zeroDifference)
                (trans
                  (C3.addZeroLeft F (C3.negate F a))
                  refl))))
    in
    sym
      (trans
        (sym (C3.negateInvolutive F b))
        (trans
          (cong (C3.negate F) negbEqualsNega)
          (C3.negateInvolutive F a)))

complex3SubtractZeroImpliesEqual :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Complex3 F) →
  C3.complex3Subtract left right ≡ C3.complex3Zero F →
  left ≡ right
complex3SubtractZeroImpliesEqual
    (C3.complex3 lx ly lz) (C3.complex3 rx ry rz) proof =
  Field.complex3Ext
    (complexSubtractZeroImpliesEqual lx rx (cong C3.x proof))
    (complexSubtractZeroImpliesEqual ly ry (cong C3.y proof))
    (complexSubtractZeroImpliesEqual lz rz (cong C3.z proof))

------------------------------------------------------------------------
-- Output-transverse pair => cross lies in the output line.
------------------------------------------------------------------------

outputTransversePairCrossKernel :
  ∀ {r} {F : C3.RealField r}
    (wave u v : C3.Complex3 F) →
  C3.bilinearDot3 wave u ≡ C3.complexZero F →
  C3.bilinearDot3 wave v ≡ C3.complexZero F →
  Cross.complex3Cross wave (Cross.complex3Cross u v)
  ≡ C3.complex3Zero F
outputTransversePairCrossKernel {F = F} wave u v transverseU transverseV =
  trans
    (bacCab wave u v)
    (trans
      (cong₂ C3.complex3Subtract
        (trans
          (cong (λ scalar → C3.complex3Scale scalar u) transverseV)
          (R106.complex3ScaleZeroScalar u))
        (trans
          (cong (λ scalar → C3.complex3Scale scalar v) transverseU)
          (R106.complex3ScaleZeroScalar v)))
      (R106.complex3SubtractSelf (C3.complex3Zero F)))

crossKernelScaledLongitudinal :
  ∀ {r} {F : C3.RealField r}
    (wave value : C3.Complex3 F) →
  Cross.complex3Cross wave value ≡ C3.complex3Zero F →
  C3.complex3Scale (C3.bilinearDot3 wave wave) value
  ≡ C3.complex3Scale (C3.bilinearDot3 wave value) wave
crossKernelScaledLongitudinal {F = F} wave value crossZero =
  let
    triple = bacCab wave wave value
    leftZero :
      Cross.complex3Cross wave (Cross.complex3Cross wave value)
      ≡ C3.complex3Zero F
    leftZero =
      trans
        (cong (Cross.complex3Cross wave) crossZero)
        (crossZeroRight wave)

    differenceZero :
      C3.complex3Subtract
        (C3.complex3Scale (C3.bilinearDot3 wave value) wave)
        (C3.complex3Scale (C3.bilinearDot3 wave wave) value)
      ≡ C3.complex3Zero F
    differenceZero = trans (sym triple) leftZero
  in
  sym
    (complex3SubtractZeroImpliesEqual
      (C3.complex3Scale (C3.bilinearDot3 wave value) wave)
      (C3.complex3Scale (C3.bilinearDot3 wave wave) value)
      differenceZero)

------------------------------------------------------------------------
-- Exact Leray cancellation.
------------------------------------------------------------------------

lerayKillsOutputTransverseCross :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  (u v : C3.Complex3 F) →
  C3.bilinearDot3 (C3.modeVector E mode) u ≡ C3.complexZero F →
  C3.bilinearDot3 (C3.modeVector E mode) v ≡ C3.complexZero F →
  C3.lerayProject3 E I mode (Cross.complex3Cross u v)
  ≡ C3.complex3Zero F
lerayKillsOutputTransverseCross {F = F} E I mode nonzero u v transverseU transverseV =
  let
    wave = C3.modeVector E mode
    value = Cross.complex3Cross u v
    inverse = C3.realEmbed F (C3.inverseNormSquared I mode)
    squared = C3.realEmbed F (C3.normSquared I mode)
    dotSelf = C3.bilinearDot3 wave wave
    dotValue = C3.bilinearDot3 wave value

    crossZero = outputTransversePairCrossKernel wave u v transverseU transverseV
    scaledLong = crossKernelScaledLongitudinal wave value crossZero
    dotSelfMeaning = LerayExact.modeSelfDotIsEmbeddedNormSquared E I mode
    inverseMeaning = LerayExact.embeddedInverseSquareLaw E I mode nonzero

    valueIsCorrection :
      value
      ≡ C3.complex3Scale (C3.complexMultiply inverse dotValue) wave
    valueIsCorrection =
      trans
        (sym (R106.complex3ScaleOne value))
        (trans
          (cong (λ scalar → C3.complex3Scale scalar value)
            (sym inverseMeaning))
          (trans
            (cong
              (λ scalar → C3.complex3Scale scalar value)
              (cong (C3.complexMultiply inverse) (sym dotSelfMeaning)))
            (trans
              (sym (ScalarLinear.complex3ScaleAssociative inverse dotSelf value))
              (trans
                (cong (C3.complex3Scale inverse) scaledLong)
                (ScalarLinear.complex3ScaleAssociative inverse dotValue wave)))))
  in
  trans
    (cong (C3.complex3Subtract value) (sym valueIsCorrection))
    (R106.complex3SubtractSelf value)

round131BACCBExact : Bool
round131BACCBExact = true

round131OutputTransverseCrossKernelClosed : Bool
round131OutputTransverseCrossKernelClosed = true

round131LerayKillsOutputTransverseCrossClosed : Bool
round131LerayKillsOutputTransverseCrossClosed = true

round131PhysicalCollinearLegTransportClosed : Bool
round131PhysicalCollinearLegTransportClosed = false

round131CriticalHHPaymentClosed : Bool
round131CriticalHHPaymentClosed = false

round131LerayKillsOutputTransverseCrossClosedIsTrue :
  round131LerayKillsOutputTransverseCrossClosed ≡ true
round131LerayKillsOutputTransverseCrossClosedIsTrue = refl

round131PhysicalCollinearLegTransportClosedIsFalse :
  round131PhysicalCollinearLegTransportClosed ≡ false
round131PhysicalCollinearLegTransportClosedIsFalse = refl

round131CriticalHHPaymentClosedIsFalse :
  round131CriticalHHPaymentClosed ≡ false
round131CriticalHHPaymentClosedIsFalse = refl
