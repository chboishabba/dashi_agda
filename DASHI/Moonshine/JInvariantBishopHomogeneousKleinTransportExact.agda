module DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact where

-- Source-written, kernel pending. Use the original proof-relevant Klein
-- quotient, but carry its homogeneous numerator and denominator first.
-- No E4 nonzero condition: elliptic j=0 is admitted.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Data.Rational.Unnormalised.Properties as QP
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Moonshine.JInvariantBishopNativeProofRelevantKleinExact as K
import DASHI.Moonshine.JInvariantBishopLatticeFourierSameObjectExact as E
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as LR
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC; scaleC)
open Comp using (complexTrans; complexSym)

cubeCong : ∀ {x y} → x ≈C y → K.cube x ≈C K.cube y
cubeCong h = A.mulCCongruent (A.mulCCongruent h h) h

cubePow : ∀ z → K.cube z ≈C powC z 3
cubePow z = complexTrans (Laws.complexMultiplyCommutative (z *C z) z)
  (A.mulCCongruent (C.≈C-refl z)
    (A.mulCCongruent (C.≈C-refl z) (complexSym (LR.powOne z))))

cubeWeight : ∀ z a → K.cube (powC z 4 *C a) ≈C (powC z 12 *C K.cube a)
cubeWeight z a = complexTrans (cubePow _)
  (complexTrans (G.powProduct (powC z 4) a 3)
    (A.mulCCongruent weight (complexSym (cubePow a))))
  where
  weight : powC (powC z 4) 3 ≈C powC z 12
  weight = complexTrans (complexSym (cubePow _))
    (complexTrans (A.mulCCongruent (LR.powAdd z 4 4) (C.≈C-refl _))
      (LR.powAdd z 8 4))

squareWeight : ∀ z a → ((powC z 6 *C a) *C (powC z 6 *C a)) ≈C
  (powC z 12 *C (a *C a))
squareWeight z a = complexTrans (G.shuffle _ _ _ _)
  (A.mulCCongruent (LR.powAdd z 6 6) (C.≈C-refl _))

deltaCong : ∀ {a b x y} → a ≈C x → b ≈C y →
  K.normalizedDelta a b ≈C K.normalizedDelta x y
deltaCong h k = A.scaleCCongruent (A.subCCongruent (cubeCong h) (A.mulCCongruent k k)) _

scaleSubFactor : ∀ h w a b →
  scaleC h ((w *C a) -C (w *C b)) ≈C (w *C scaleC h (a -C b))
scaleSubFactor h (C.complex x y) (C.complex a b) (C.complex c d) =
  (let open P.ℝ-Solver in solve 7
    (λ h x y a b c d → h ⊗ ((x ⊗ a ⊖ y ⊗ b) ⊖ (x ⊗ c ⊖ y ⊗ d))
      ⊜ x ⊗ (h ⊗ (a ⊖ c)) ⊖ y ⊗ (h ⊗ (b ⊖ d))) P.≃-refl h x y a b c d) ,
  (let open P.ℝ-Solver in solve 7
    (λ h x y a b c d → h ⊗ ((x ⊗ b ⊕ y ⊗ a) ⊖ (x ⊗ d ⊕ y ⊗ c))
      ⊜ x ⊗ (h ⊗ (b ⊖ d)) ⊕ y ⊗ (h ⊗ (a ⊖ c))) P.≃-refl h x y a b c d)

deltaWeight : ∀ z a b →
  K.normalizedDelta (powC z 4 *C a) (powC z 6 *C b) ≈C
  (powC z 12 *C K.normalizedDelta a b)
deltaWeight z a b = complexTrans
  (A.scaleCCongruent (A.subCCongruent (cubeWeight z a) (squareWeight z b)) _)
  (scaleSubFactor _ (powC z 12) (K.cube a) (b *C b))

positiveMul : ∀ {a b} → R._<_ R.0ℝ a → R._<_ R.0ℝ b → R._<_ R.0ℝ (R._*_ a b)
positiveMul a b = P.posx⇒0<x (P.posx,y⇒posx*y (P.0<x⇒posx a) (P.0<x⇒posx b))

nonzeroMul : ∀ {a b} → Rec.BishopComplexNonzero a → Rec.BishopComplexNonzero b →
  Rec.BishopComplexNonzero (a *C b)
nonzeroMul {a} {b} x y = record
  { normSquarePositive = P.<-respʳ-≃ (P.≃-symm (Norm.normSqMultiply a b))
      (positiveMul (Rec.normSquarePositive x) (Rec.normSquarePositive y)) }

nonzeroOne : Rec.BishopComplexNonzero A.oneC
nonzeroOne = record { normSquarePositive = P.<-respʳ-≃ (P.≃-symm Norm.normSqOne)
  (P.p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (QP.positive⁻¹ 1ℚᵘ)) }

nonzeroPower : ∀ {a} → Rec.BishopComplexNonzero a → ∀ n → Rec.BishopComplexNonzero (powC a n)
nonzeroPower nz zero = nonzeroOne
nonzeroPower nz (suc n) = nonzeroMul nz (nonzeroPower nz n)

-- Quotient congruence never identifies the proof witnesses themselves.
quot : ∀ n d → Rec.BishopComplexNonzero d → BishopComplex
quot n d nz = n *C Rec.reciprocalC d nz

quotCong : ∀ {n n' d d'} → n ≈C n' → d ≈C d' →
  (a : Rec.BishopComplexNonzero d) → (b : Rec.BishopComplexNonzero d') →
  quot n d a ≈C quot n' d' b
quotCong h k a b = A.mulCCongruent h (G.reciprocalCong _ _ a b k)

clearQuot : ∀ n d nz → (d *C quot n d nz) ≈C n
clearQuot n d nz = complexTrans (complexSym (Laws.complexMultiplyAssociative d n _))
  (complexTrans (A.mulCCongruent (Laws.complexMultiplyCommutative d n) (C.≈C-refl _))
    (complexTrans (Laws.complexMultiplyAssociative n d _)
      (complexTrans (A.mulCCongruent (C.≈C-refl n) (Rec.multiplyReciprocal d nz))
        (Laws.complexMultiplyRightIdentity n))))

cancelLeft : ∀ w a b → Rec.BishopComplexNonzero w → (w *C a) ≈C (w *C b) → a ≈C b
cancelLeft w a b nz h = complexTrans (complexSym (read a))
  (complexTrans (A.mulCCongruent (C.≈C-refl _) h) (read b))
  where
  v = Rec.reciprocalC w nz
  read : ∀ x → (v *C (w *C x)) ≈C x
  read x = complexTrans (complexSym (Laws.complexMultiplyAssociative v w x))
    (complexTrans (A.mulCCongruent
      (complexTrans (Laws.complexMultiplyCommutative v w) (Rec.multiplyReciprocal w nz))
      (C.≈C-refl x)) (Laws.complexMultiplyLeftIdentity x))

quotScale : ∀ w n d (wnz : Rec.BishopComplexNonzero w) (dnz : Rec.BishopComplexNonzero d)
  (nz : Rec.BishopComplexNonzero (w *C d)) →
  quot (w *C n) (w *C d) nz ≈C quot n d dnz
quotScale w n d wnz dnz nz = cancelLeft (w *C d) _ _ nz
  (complexTrans (clearQuot (w *C n) (w *C d) nz)
    (complexSym (complexTrans (Laws.complexMultiplyAssociative w d _)
      (A.mulCCongruent (C.≈C-refl w) (clearQuot n d dnz)))))

module At (inputs : Round11.BishopCutset) where
  module Q = E.For inputs
  module Ph = Phase.At inputs
  N : U.BishopUpperHalfPlanePoint → BishopComplex
  N p = K.cube (Q.qE4 p)

  D : U.BishopUpperHalfPlanePoint → BishopComplex
  D p = K.normalizedDelta (Q.qE4 p) (Q.qE6 p)

  NS : ∀ p → N (G.actS p) ≈C (powC (U.tau p) 12 *C N p)
  NS p = complexTrans (cubeCong (Q.qE4S p)) (cubeWeight (U.tau p) (Q.qE4 p))

  DS : ∀ p → D (G.actS p) ≈C (powC (U.tau p) 12 *C D p)
  DS p = complexTrans (deltaCong (Q.qE4S p) (Q.qE6S p))
    (deltaWeight (U.tau p) (Q.qE4 p) (Q.qE6 p))

  NT : ∀ p → N (G.actT p) ≈C N p
  NT p = cubeCong (Q.qE4T p)

  DT : ∀ p → D (G.actT p) ≈C D p
  DT p = deltaCong (Q.qE4T p) (Q.qE6T p)

  Guard : U.BishopUpperHalfPlanePoint → Set
  Guard p = Rec.BishopComplexNonzero (D p)

  guardS : ∀ p → Guard p → Guard (G.actS p)
  guardS p nz = Phase.guardCong (complexSym (DS p))
    (nonzeroMul (nonzeroPower (G.tauNZ p) 12) nz)

  guardT : ∀ p → Guard p → Guard (G.actT p)
  guardT p nz = Phase.guardCong (complexSym (DT p)) nz

  j : ∀ p → Guard p → BishopComplex
  j p = quot (N p) (D p)

  jS : ∀ p (a : Guard p) (b : Guard (G.actS p)) → j (G.actS p) b ≈C j p a
  jS p a b = complexTrans (quotCong (NS p) (DS p) b nz)
    (quotScale _ _ _ (nonzeroPower (G.tauNZ p) 12) a nz)
    where nz = nonzeroMul (nonzeroPower (G.tauNZ p) 12) a

  jT : ∀ p (a : Guard p) (b : Guard (G.actT p)) → j (G.actT p) b ≈C j p a
  jT p a b = quotCong (NT p) (DT p) b a

  -- The homogeneous statement is valid without a discriminant guard.
  crossS : ∀ p → (N (G.actS p) *C D p) ≈C (D (G.actS p) *C N p)
  crossS p = complexTrans (A.mulCCongruent (NS p) (C.≈C-refl _))
    (complexTrans (Laws.complexMultiplyAssociative _ _ _)
      (complexTrans (A.mulCCongruent (C.≈C-refl _) (Laws.complexMultiplyCommutative _ _))
        (complexTrans (complexSym (Laws.complexMultiplyAssociative _ _ _))
          (A.mulCCongruent (complexSym (DS p)) (C.≈C-refl _)))))

  crossT : ∀ p → (N (G.actT p) *C D p) ≈C (D (G.actT p) *C N p)
  crossT p = complexTrans (A.mulCCongruent (NT p) (C.≈C-refl _))
    (complexTrans (Laws.complexMultiplyCommutative _ _)
      (A.mulCCongruent (complexSym (DT p)) (C.≈C-refl _)))

