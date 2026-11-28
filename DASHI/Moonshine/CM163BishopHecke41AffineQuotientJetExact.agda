module DASHI.Moonshine.CM163BishopHecke41AffineQuotientJetExact where

-- SOURCE-WRITTEN, kernel pending. Divide a genuine nested two-jet
-- by its actual affine coordinate, guarded by original apartness.
-- This is the J=q*j seam; never divide by the increment q-q0.
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact as J2
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_*C_; _-C_)
open Comp using (complexTrans; complexSym)

clearRearrange : ∀ a b x y → (a *C x -C a *C y) ≈C
  ((a *C x -C b *C y) -C (a -C b) *C y)
clearRearrange (C.complex ar ai) (C.complex br bi) (C.complex xr xi) (C.complex yr yi) =
  (let open P.ℝ-Solver in solve 8
    (λ a b c d x y u v →
      (a ⊗ x ⊖ b ⊗ y) ⊖ (a ⊗ u ⊖ b ⊗ v)
      ⊜ ((a ⊗ x ⊖ b ⊗ y) ⊖ (c ⊗ u ⊖ d ⊗ v))
        ⊖ ((a ⊖ c) ⊗ u ⊖ (b ⊖ d) ⊗ v)) P.≃-refl ar ai br bi xr xi yr yi) ,
  (let open P.ℝ-Solver in solve 8
    (λ a b c d x y u v →
      (a ⊗ y ⊕ b ⊗ x) ⊖ (a ⊗ v ⊕ b ⊗ u)
      ⊜ ((a ⊗ y ⊕ b ⊗ x) ⊖ (c ⊗ v ⊕ d ⊗ u))
        ⊖ ((a ⊖ c) ⊗ v ⊕ (b ⊖ d) ⊗ u)) P.≃-refl ar ai br bi xr xi yr yi)

read : ∀ q (nz : Rec.BishopComplexNonzero q) z →
  (q *C (Rec.reciprocalC q nz *C z)) ≈C z
read q nz z =
  complexTrans (complexSym (L.complexMultiplyAssociative q (Rec.reciprocalC q nz) z))
    (complexTrans (A.mulCCongruent (Rec.multiplyReciprocal q nz) (C.≈C-refl _))
      (L.complexMultiplyLeftIdentity z))

-- The same one-step identity is applied to the value and then to the
-- first quotient. This is a bidirectional cleared product calculation.
step : ∀ q u (nz : Rec.BishopComplexNonzero q) g h f a s →
  (q *C g) ≈C f → (u *C h) ≈C a →
  (f -C a) ≈C ((q -C u) *C s) →
  (g -C h) ≈C ((q -C u) *C (Rec.reciprocalC q nz *C (s -C h)))
step q u nz g h f a s qg uh inc =
  let d = q -C u
      inv = Rec.reciprocalC q nz
      x = s -C h
      lhs = complexTrans (Alg.mulSub q g h)
        (complexTrans (clearRearrange q u g h)
          (complexTrans (A.subCCongruent (A.subCCongruent qg uh) (C.≈C-refl _))
            (complexTrans (A.subCCongruent inc (C.≈C-refl _))
              (complexSym (Alg.mulSub d s h)))))
      rhs = complexTrans (complexSym (L.complexMultiplyAssociative q d (inv *C x)))
        (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative q d) (C.≈C-refl _))
          (complexTrans (L.complexMultiplyAssociative d q (inv *C x))
            (A.mulCCongruent (C.≈C-refl _) (read q nz x))))
  in Cancel.cancelLeft q _ _ nz (complexTrans lhs (complexSym rhs))

module At (q : Nat → BishopComplex) (u : BishopComplex)
  (nz : ∀ n → Rec.BishopComplexNonzero (q n))
  (un : Rec.BishopComplexNonzero u) (cv : Lim.Conv q u)
  (f g : Nat → BishopComplex) (a h b c : BishopComplex)
  (qg : ∀ n → (q n *C g n) ≈C f n)
  (uh : (u *C h) ≈C a)
  (jet : J2.Jet2 (λ n → q n -C u) f a b c) where

  inv = Rec.reciprocalC u un
  iv : Nat → BishopComplex
  iv n = Rec.reciprocalC (q n) (nz n)

  ivLimit : Lim.Conv iv inv
  ivLimit = Conv.inverseLimit un cv (λ n → Rec.multiplyReciprocal (q n) (nz n))

  firstCenter : BishopComplex
  firstCenter = inv *C (b -C h)

  secondCenter : BishopComplex
  secondCenter = inv *C (c -C firstCenter)

  r : Nat → BishopComplex
  r n = iv n *C (J.quotient (J2.first jet) n -C h)

  firstJet : J.Jet (λ n → q n -C u) g h firstCenter
  firstJet = record
    { J.quotient = r
    ; J.factor = λ n → step (q n) u (nz n) (g n) h (f n) a
        (J.quotient (J2.first jet) n) (qg n) uh (J.factor (J2.first jet) n)
    ; J.limit = Conv.mulConv ivLimit (Lim.subConv (J.limit (J2.first jet)) (Lim.constantC h)) }

  secondJet : J.Jet (λ n → q n -C u) r firstCenter secondCenter
  secondJet = record
    { J.quotient = λ n → iv n *C (J.quotient (J2.second jet) n -C firstCenter)
    ; J.factor = λ n → step (q n) u (nz n) (r n) firstCenter
        (J.quotient (J2.first jet) n -C h) (b -C h)
        (J.quotient (J2.second jet) n)
        (read (q n) (nz n) _) (read u un _)
        (complexTrans (J.subStep (J.quotient (J2.first jet) n) h b h)
          (complexTrans (A.subCCongruent (C.≈C-refl _) (J.sameSub h))
            (complexTrans (J.subZero _) (J.factor (J2.second jet) n))))
    ; J.limit = Conv.mulConv ivLimit
        (Lim.subConv (J.limit (J2.second jet)) (Lim.constantC firstCenter)) }

  actual : J2.Jet2 (λ n → q n -C u) g h firstCenter secondCenter
  actual = record { J2.first = firstJet ; J2.second = secondJet }
