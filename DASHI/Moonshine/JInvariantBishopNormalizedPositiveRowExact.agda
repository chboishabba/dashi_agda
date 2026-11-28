module DASHI.Moonshine.JInvariantBishopNormalizedPositiveRowExact where

-- Source-written, kernel pending. C1b producer: all positive horizontal
-- rows, actual q^m, and normalization by the constructed even-zeta
-- values. No interchange of infinite row/degree sums is asserted here.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (ℤ; +_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Product.Base using (_,_)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Foundations.BishopNatRealPositiveExact as Pos
import DASHI.Moonshine.JInvariantBishopCenteredDyadicSummandLimitExact as Leaf
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowClosureExact as Close
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as LR
import DASHI.Moonshine.JInvariantBishopHalfIntegerBoundaryClosureExact as H
import DASHI.Moonshine.JInvariantBishopEvenZetaNormalizationExact as Z
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantBishopFourierRowRationalExact as Rat
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; powC; scaleC)
open Comp using (complexTrans; complexSym)
open Z using (realC; realCong; realMul)

factorSquare : Rat.square LR.factor ≈C realC (R.- (((+ 4 / 1) ⋆) * R.pow D.pi 2))
factorSquare =
  (let open P.ℝ-Solver in solve 1
    (λ p → Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 2 / 1) ⊗ p)
      ⊜ ⊝ (Κ (+ 4 / 1) ⊗ ((Κ 1ℚᵘ ⊗ p) ⊗ p))) P.≃-refl D.pi) ,
  (let open P.ℝ-Solver in solve 1
    (λ p → Κ 0ℚᵘ ⊗ (Κ (+ 2 / 1) ⊗ p) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ
      ⊜ Κ 0ℚᵘ) P.≃-refl D.pi)

factor4 : powC LR.factor 4 ≈C realC (((+ 16 / 1) ⋆) * R.pow D.pi 4)
factor4 =
  let a = R.- (((+ 4 / 1) ⋆) * R.pow D.pi 2)
  in complexTrans (complexSym (LR.powFour LR.factor))
    (complexTrans (A.mulCCongruent factorSquare factorSquare)
      (complexTrans (realMul a a) (realCong
        (let open P.ℝ-Solver in solve 1
          (λ p → (⊝ (Κ (+ 4 / 1) ⊗ ((Κ 1ℚᵘ ⊗ p) ⊗ p))) ⊗
                  (⊝ (Κ (+ 4 / 1) ⊗ ((Κ 1ℚᵘ ⊗ p) ⊗ p)))
            ⊜ Κ (+ 16 / 1) ⊗ ((((Κ 1ℚᵘ ⊗ p) ⊗ p) ⊗ p) ⊗ p))
          P.≃-refl D.pi))))

factor6 : powC LR.factor 6 ≈C realC (R.- (((+ 64 / 1) ⋆) * R.pow D.pi 6))
factor6 =
  let a = R.- (((+ 4 / 1) ⋆) * R.pow D.pi 2)
      b = ((+ 16 / 1) ⋆) * R.pow D.pi 4
  in complexTrans (complexSym (LR.powAdd LR.factor 2 4))
    (complexTrans (A.mulCCongruent (complexTrans (complexSym (LR.powTwo LR.factor)) factorSquare) factor4)
      (complexTrans (realMul a b) (realCong
        (let open P.ℝ-Solver in solve 1
          (λ p → (⊝ (Κ (+ 4 / 1) ⊗ ((Κ 1ℚᵘ ⊗ p) ⊗ p))) ⊗
                  (Κ (+ 16 / 1) ⊗ ((((Κ 1ℚᵘ ⊗ p) ⊗ p) ⊗ p) ⊗ p))
            ⊜ ⊝ (Κ (+ 64 / 1) ⊗ ((((((Κ 1ℚᵘ ⊗ p) ⊗ p) ⊗ p) ⊗ p) ⊗ p) ⊗ p)))
          P.≃-refl D.pi))))

scaleReal : ∀ h a → scaleC h (realC a) ≈C realC (h * a)
scaleReal h a = P.≃-refl ,
  (let open P.ℝ-Solver in solve 1 (λ h → h ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl h)

realScale : ∀ a z → (realC a *C z) ≈C scaleC a z
realScale a (C.complex r i) =
  (let open P.ℝ-Solver in solve 3 (λ a r i → a ⊗ r ⊖ Κ 0ℚᵘ ⊗ i ⊜ a ⊗ r) P.≃-refl a r i) ,
  (let open P.ℝ-Solver in solve 3 (λ a r i → a ⊗ i ⊕ Κ 0ℚᵘ ⊗ r ⊜ a ⊗ i) P.≃-refl a r i)

positivePoint : U.BishopUpperHalfPlanePoint → Nat → U.BishopUpperHalfPlanePoint
positivePoint p m = U.bishop-upper-half-plane-point
  (scaleC (N.natReal (suc m)) (U.tau p))
  (Leaf.positiveProduct (Pos.natRealSuccessorStrictlyPositive m) (U.imaginaryPositive p))

notOrigin : ∀ {m} → (+ suc m) ≡ (+ zero) → L.⊥
notOrigin ()

index : Nat → ℤ → K.NonzeroLatticePoint
index m j = K.nonzero-lattice-point (L.lattice-point (+ suc m) j)
  (λ eq → notOrigin (cong L.horizontal eq))

module At (inputs : Round11.BishopCutset) (p : U.BishopUpperHalfPlanePoint) where
  module Rw = D.At inputs
  module Zn = Z.At inputs
  module Lf = Leaf.At inputs
  module Axis = H.At inputs

  coeff4 coeff6 : ℝ
  coeff4 = ((+ 240 / 1) ⋆) * Z.zeta 2
  coeff6 = R.- (((+ 504 / 1) ⋆) * Z.zeta 4)

  undo4Read : Axis.undo4 ≈C realC coeff4
  undo4Read = complexTrans (A.scaleCCongruent factor4 ((+ 1 / 6) ⋆))
    (complexTrans (scaleReal _ _) (realCong
      (P.≃-trans
        (let open P.ℝ-Solver in solve 1
          (λ p → Κ (+ 1 / 6) ⊗ (Κ (+ 16 / 1) ⊗ p)
            ⊜ Κ (+ 240 / 1) ⊗ (Κ (+ 1 / 90) ⊗ p)) P.≃-refl (R.pow D.pi 4))
        (P.*-congˡ (P.≃-symm Zn.zeta4)))))

  undo6Read : Axis.undo6 ≈C realC coeff6
  undo6Read = complexTrans (A.scaleCCongruent factor6 ((+ 1 / 120) ⋆))
    (complexTrans (scaleReal _ _) (realCong
      (P.≃-trans
        (let open P.ℝ-Solver in solve 1
          (λ p → Κ (+ 1 / 120) ⊗ (⊝ (Κ (+ 64 / 1) ⊗ p))
            ⊜ ⊝ (Κ (+ 504 / 1) ⊗ (Κ (+ 1 / 945) ⊗ p))) P.≃-refl (R.pow D.pi 6))
        (P.-‿cong (P.*-congˡ (P.≃-symm Zn.zeta6))))))

  exponentScale : ∀ m → Rw.exponent (positivePoint p m) ≈C
    scaleC (N.natReal (suc m)) (Rw.exponent p)
  exponentScale m =
    (let open P.ℝ-Solver in solve 3
      (λ p y m → ⊝ ((Κ (+ 2 / 1) ⊗ p) ⊗ (m ⊗ y))
        ⊜ m ⊗ (⊝ ((Κ (+ 2 / 1) ⊗ p) ⊗ y))) P.≃-refl D.pi (C.im (U.tau p)) (N.natReal (suc m))) ,
    (let open P.ℝ-Solver in solve 3
      (λ p x m → (Κ (+ 2 / 1) ⊗ p) ⊗ (m ⊗ x)
        ⊜ m ⊗ ((Κ (+ 2 / 1) ⊗ p) ⊗ x)) P.≃-refl D.pi (C.re (U.tau p)) (N.natReal (suc m)))

  exponentStep : ∀ m → Rw.exponent (positivePoint p (suc m)) ≈C
    (Rw.exponent p +C Rw.exponent (positivePoint p m))
  exponentStep m = complexTrans (exponentScale (suc m))
    (complexTrans (Leaf.scaleCong (N.natRealSuccessor (suc m)) (C.≈C-refl _))
      (complexTrans distributive (A.addCCongruent (C.≈C-refl _) (complexSym (exponentScale m)))))
    where
    distributive : scaleC (N.natReal (suc m) + R.1ℝ) (Rw.exponent p) ≈C
      (Rw.exponent p +C scaleC (N.natReal (suc m)) (Rw.exponent p))
    distributive =
      (let open P.ℝ-Solver in solve 2
        (λ m x → (m ⊕ Κ 1ℚᵘ) ⊗ x ⊜ x ⊕ m ⊗ x) P.≃-refl (N.natReal (suc m)) (C.re (Rw.exponent p))) ,
      (let open P.ℝ-Solver in solve 2
        (λ m x → (m ⊕ Κ 1ℚᵘ) ⊗ x ⊜ x ⊕ m ⊗ x) P.≃-refl (N.natReal (suc m)) (C.im (Rw.exponent p)))

  qPower : ∀ m → Rw.q (positivePoint p m) ≈C powC (Rw.q p) (suc m)
  qPower zero = complexTrans
    (Weld.originalBishopExpOnSeriesCongruent Rw.T
      (complexTrans (exponentScale zero) (Lim.scaleOne (Rw.exponent p))))
    (complexSym (LR.powOne (Rw.q p)))
  qPower (suc m) = complexTrans (Weld.originalBishopExpOnSeriesCongruent Rw.T (exponentStep m))
    (complexTrans (Rw.expAddS (Rw.exponent p) (Rw.exponent (positivePoint p m)))
      (A.mulCCongruent (C.≈C-refl _) (qPower m)))

  module PositiveRow (m : Nat) where
    point = positivePoint p m
    module Read = LR.At inputs point

    q = powC (Rw.q p) (suc m)
    nz = D.guardCong (D.gapCong (qPower m)) (Rw.gapNZ point)
    F4 = Row.P4 (Row.X q nz)
    F6 = Row.P6 (Row.X q nz)

    row4Read : Rw.row4 point ≈C F4
    row4Read = D.P4Cong (D.XC (Rw.gapNZ point) nz (qPower m))
    row6Read : Rw.row6 point ≈C F6
    row6Read = D.P6Cong (D.XC (Rw.gapNZ point) nz (qPower m))

    denomRead : ∀ j → K.latticeDenominator (K.point (index m j)) (U.tau p) ≈C LR.denom point j
    denomRead j = complexTrans
      (P.≃-refl , P.+-identityʳ (N.natReal (suc m) * C.im (U.tau p)))
      (complexSym (LR.denomRead point j))

    lattice : Nat → ℤ → BishopComplex
    lattice w j = K.latticeEisensteinSummand U.upperHalfPlaneDenominatorGeometry w (index m j) p

    termRead : ∀ w j → lattice w j ≈C Read.lattice w j
    termRead w j = A.powCCongruent (G.reciprocalCong _ _ _ _ (denomRead j)) w

    actualRow4 : Lim.Conv (Close.pairPrefix (lattice 4)) (scaleC coeff4 F4)
    actualRow4 = Lim.limitTransport
      (complexTrans (A.mulCCongruent undo4Read row4Read) (realScale coeff4 F4))
      (Lim.convTransport (LR.prefixCong (Read.lattice 4) (lattice 4) (λ j → complexSym (termRead 4 j))) Read.latticeRow4)

    actualRow6 : Lim.Conv (Close.pairPrefix (lattice 6)) (scaleC coeff6 F6)
    actualRow6 = Lim.limitTransport
      (complexTrans (A.mulCCongruent undo6Read row6Read) (realScale coeff6 F6))
      (Lim.convTransport (LR.prefixCong (Read.lattice 6) (lattice 6) (λ j → complexSym (termRead 6 j))) Read.latticeRow6)
