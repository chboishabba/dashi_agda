module DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact where

-- Source-written, uncompiled. Read the actual fixed row endpoint as
-- the original lattice kernel on (1,j), with the literal (2*pi*i)^-k
-- factor outside. No choice of a complex root or alternate pi.
open import Agda.Builtin.Nat as Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₂)
open import Relation.Binary.PropositionalEquality using (cong)
import Real as R
open R using (_*_; _+_; _⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as Pi
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopCenteredDyadicSummandLimitExact as Leaf
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowClosureExact as Close
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantBishopFourierRowRationalExact as Rat
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; powC)
open Comp using (complexTrans; complexSym)

notOrigin1 : (+ 1) ≡ (+ 0) → L.⊥
notOrigin1 ()

index : ℤ → K.NonzeroLatticePoint
index j = K.nonzero-lattice-point (L.lattice-point (+ 1) j)
  (λ eq → notOrigin1 (cong L.horizontal eq))

denom : U.BishopUpperHalfPlanePoint → ℤ → BishopComplex
denom p j = K.latticeDenominator (K.point (index j)) (U.tau p)

denomRead : ∀ p j → denom p j ≈C U.tau (Leaf.shifted p j)
denomRead p j =
  (let open P.ℝ-Solver in solve 2
    (λ x j → Κ 1ℚᵘ ⊗ x ⊕ j ⊜ x ⊕ j) P.≃-refl (C.re (U.tau p)) (K.embedInteger j)) ,
  (let open P.ℝ-Solver in solve 1
    (λ y → Κ 1ℚᵘ ⊗ y ⊕ Κ 0ℚᵘ ⊜ y) P.≃-refl (C.im (U.tau p)))

factor : BishopComplex
factor = C.complex R.0ℝ (D.two * D.pi)

factorNZ : Rec.BishopComplexNonzero factor
factorNZ = NZ.complexNonzeroFromImagApart (inj₂
  (Leaf.positiveProduct twoPositive Pi.machinPiPositive))
  where
  twoPositive = Radius.twoPositive

V : BishopComplex
V = Rec.reciprocalC factor factorNZ

W : U.BishopUpperHalfPlanePoint → ℤ → BishopComplex
W p j = K.latticeReciprocal U.upperHalfPlaneDenominatorGeometry p (index j)

-- Read the regrouped powers using associativity rather than another
-- generated degree-six ring expression.
powOne : ∀ z → powC z 1 ≈C z
powOne z = Laws.complexMultiplyRightIdentity z

powTwo : ∀ z → Rat.square z ≈C powC z 2
powTwo z = A.mulCCongruent (C.≈C-refl _) (complexSym (powOne z))

powAdd : ∀ z a b → (powC z a *C powC z b) ≈C powC z (Nat._+_ a b)
powAdd z Nat.zero b = Laws.complexMultiplyLeftIdentity (powC z b)
powAdd z (Nat.suc a) b = complexTrans (Laws.complexMultiplyAssociative z (powC z a) (powC z b))
  (A.mulCCongruent (C.≈C-refl _) (powAdd z a b))

powFour : ∀ z → Rat.square (Rat.square z) ≈C powC z 4
powFour z = complexTrans (A.mulCCongruent (powTwo z) (powTwo z)) (powAdd z 2 2)

powSix : ∀ z → Rat.cube (Rat.square z) ≈C powC z 6
powSix z = complexTrans (A.mulCCongruent (powTwo z) (powFour z)) (powAdd z 2 4)

scaleProduct : ∀ h a b → A.scaleC h (a *C b) ≈C (A.scaleC h a *C b)
scaleProduct h (C.complex a b) (C.complex c d) =
  (let open P.ℝ-Solver in solve 5
    (λ h a b c d → h ⊗ (a ⊗ c ⊖ b ⊗ d)
      ⊜ (h ⊗ a) ⊗ c ⊖ (h ⊗ b) ⊗ d) P.≃-refl h a b c d) ,
  (let open P.ℝ-Solver in solve 5
    (λ h a b c d → h ⊗ (a ⊗ d ⊕ b ⊗ c)
      ⊜ (h ⊗ a) ⊗ d ⊕ (h ⊗ b) ⊗ c) P.≃-refl h a b c d)

module At (inputs : Round11.BishopCutset) (p : U.BishopUpperHalfPlanePoint) where
  module Rw = D.At inputs
  module Lf = Leaf.At inputs
  module Cl = Close.At inputs p

  exponentRead : ∀ j → Lf.Fixed.z p j ≈C (factor *C denom p j)
  exponentRead j = complexTrans raw
    (A.mulCCongruent (C.≈C-refl _) (complexSym (denomRead p j)))
    where
    raw : Lf.Fixed.z p j ≈C (factor *C U.tau (Leaf.shifted p j))
    raw =
      (let open P.ℝ-Solver in solve 3
        (λ pi x y → ⊝ ((Κ (+ 2 / 1) ⊗ pi) ⊗ y)
          ⊜ Κ 0ℚᵘ ⊗ x ⊖ (Κ (+ 2 / 1) ⊗ pi) ⊗ y)
        P.≃-refl D.pi (C.re (U.tau (Leaf.shifted p j))) (C.im (U.tau p))) ,
      (let open P.ℝ-Solver in solve 3
        (λ pi x y → (Κ (+ 2 / 1) ⊗ pi) ⊗ x
          ⊜ Κ 0ℚᵘ ⊗ y ⊕ (Κ (+ 2 / 1) ⊗ pi) ⊗ x)
        P.≃-refl D.pi (C.re (U.tau (Leaf.shifted p j))) (C.im (U.tau p)))

  inverseRead : ∀ j → Rec.reciprocalC (Lf.Fixed.z p j) (Lf.Fixed.directionNZ p j) ≈C (V *C W p j)
  inverseRead j = G.reciprocalUnique (Lf.Fixed.z p j) (Lf.Fixed.directionNZ p j) (V *C W p j)
    (complexTrans (A.mulCCongruent (exponentRead j) (C.≈C-refl _))
      (complexTrans (G.shuffle factor (denom p j) V (W p j))
        (complexTrans (A.mulCCongruent (Rec.multiplyReciprocal factor factorNZ)
          (Rec.multiplyReciprocal (denom p j) (K.denominatorNonzero U.upperHalfPlaneDenominatorGeometry p (index j))))
          (Laws.complexMultiplyLeftIdentity A.oneC))))

  lattice : Nat → ℤ → BishopComplex
  lattice k j = K.latticeEisensteinSummand U.upperHalfPlaneDenominatorGeometry k (index j) p

  prefactor4 prefactor6 : BishopComplex
  prefactor4 = Row.scale 6 (powC V 4)
  prefactor6 = Row.scale 120 (powC V 6)

  g4Read : ∀ j → Cl.g4 j ≈C (prefactor4 *C lattice 4 j)
  g4Read j = complexTrans (Row.scaleCong 6 (powFour _))
    (complexTrans (Row.scaleCong 6 (A.powCCongruent (inverseRead j) 4))
      (complexTrans (Row.scaleCong 6 (G.powProduct V (W p j) 4))
        (scaleProduct ((+ 6 / 1) ⋆) (powC V 4) (lattice 4 j))))

  g6Read : ∀ j → Cl.g6 j ≈C (prefactor6 *C lattice 6 j)
  g6Read j = complexTrans (Row.scaleCong 120 (powSix _))
    (complexTrans (Row.scaleCong 120 (A.powCCongruent (inverseRead j) 6))
      (complexTrans (Row.scaleCong 120 (G.powProduct V (W p j) 6))
        (scaleProduct ((+ 120 / 1) ⋆) (powC V 6) (lattice 6 j))))
