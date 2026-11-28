module DASHI.Moonshine.CM163BishopHecke41DiagonalEulerMomentsExact where

-- SOURCE-WRITTEN / KERNEL PENDING. Actual diagonal wings at the
-- normalized source coordinate: u Q_n = n u^n and
-- u Q_n + 2 u^2 T_n = n^2 u^n. No division by u or by n.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (_+_; _*_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact as D
import DASHI.Moonshine.CM163BishopHecke41SecondPowerWingExact as T
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; powC; scaleC)
open Comp using (complexTrans; complexSym)

firstStep : ∀ u p n → (u *C (p +C scaleC n p)) ≈C scaleC (n + R.1ℝ) (u *C p)
firstStep u p n = (let open P.ℝ-Solver in solve 5 (λ ur ui pr pi n →
    ((ur ⊗ (pr ⊕ (n ⊗ pr))) ⊖ (ui ⊗ (pi ⊕ (n ⊗ pi)))) ⊜ ((n ⊕ Κ 1ℚᵘ) ⊗ ((ur ⊗ pr) ⊖ (ui ⊗ pi)))) P.≃-refl (C.re u) (C.im u) (C.re p) (C.im p) n) ,
  (let open P.ℝ-Solver in solve 5 (λ ur ui pr pi n →
    ((ur ⊗ (pi ⊕ (n ⊗ pi))) ⊕ (ui ⊗ (pr ⊕ (n ⊗ pr)))) ⊜ ((n ⊕ Κ 1ℚᵘ) ⊗ ((ur ⊗ pi) ⊕ (ui ⊗ pr)))) P.≃-refl (C.re u) (C.im u) (C.re p) (C.im p) n)

secondStep : ∀ u p q t →
  ((u *C (p +C u *C q)) +C
    ((u *C (u *C (q +C u *C t))) +C (u *C (u *C (q +C u *C t))))) ≈C
  (u *C ((p +C ((u *C q) +C (u *C q))) +C ((u *C q) +C
    ((u *C (u *C t)) +C (u *C (u *C t))))))
secondStep u p q t = (let open P.ℝ-Solver in solve 8 (λ ur ui pr pi qr qi tr ti →
    (((ur ⊗ (pr ⊕ ((ur ⊗ qr) ⊖ (ui ⊗ qi)))) ⊖ (ui ⊗ (pi ⊕ ((ur ⊗ qi) ⊕ (ui ⊗ qr))))) ⊕ (((ur ⊗ ((ur ⊗ (qr ⊕ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))) ⊖ (ui ⊗ (qi ⊕ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))))) ⊖ (ui ⊗ ((ur ⊗ (qi ⊕ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))) ⊕ (ui ⊗ (qr ⊕ ((ur ⊗ tr) ⊖ (ui ⊗ ti))))))) ⊕ ((ur ⊗ ((ur ⊗ (qr ⊕ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))) ⊖ (ui ⊗ (qi ⊕ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))))) ⊖ (ui ⊗ ((ur ⊗ (qi ⊕ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))) ⊕ (ui ⊗ (qr ⊕ ((ur ⊗ tr) ⊖ (ui ⊗ ti))))))))) ⊜ ((ur ⊗ ((pr ⊕ (((ur ⊗ qr) ⊖ (ui ⊗ qi)) ⊕ ((ur ⊗ qr) ⊖ (ui ⊗ qi)))) ⊕ (((ur ⊗ qr) ⊖ (ui ⊗ qi)) ⊕ (((ur ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti))) ⊖ (ui ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))) ⊕ ((ur ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti))) ⊖ (ui ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))))))) ⊖ (ui ⊗ ((pi ⊕ (((ur ⊗ qi) ⊕ (ui ⊗ qr)) ⊕ ((ur ⊗ qi) ⊕ (ui ⊗ qr)))) ⊕ (((ur ⊗ qi) ⊕ (ui ⊗ qr)) ⊕ (((ur ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr))) ⊕ (ui ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))) ⊕ ((ur ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr))) ⊕ (ui ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))))))))) P.≃-refl (C.re u) (C.im u) (C.re p) (C.im p) (C.re q) (C.im q) (C.re t) (C.im t)) ,
  (let open P.ℝ-Solver in solve 8 (λ ur ui pr pi qr qi tr ti →
    (((ur ⊗ (pi ⊕ ((ur ⊗ qi) ⊕ (ui ⊗ qr)))) ⊕ (ui ⊗ (pr ⊕ ((ur ⊗ qr) ⊖ (ui ⊗ qi))))) ⊕ (((ur ⊗ ((ur ⊗ (qi ⊕ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))) ⊕ (ui ⊗ (qr ⊕ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))))) ⊕ (ui ⊗ ((ur ⊗ (qr ⊕ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))) ⊖ (ui ⊗ (qi ⊕ ((ur ⊗ ti) ⊕ (ui ⊗ tr))))))) ⊕ ((ur ⊗ ((ur ⊗ (qi ⊕ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))) ⊕ (ui ⊗ (qr ⊕ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))))) ⊕ (ui ⊗ ((ur ⊗ (qr ⊕ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))) ⊖ (ui ⊗ (qi ⊕ ((ur ⊗ ti) ⊕ (ui ⊗ tr))))))))) ⊜ ((ur ⊗ ((pi ⊕ (((ur ⊗ qi) ⊕ (ui ⊗ qr)) ⊕ ((ur ⊗ qi) ⊕ (ui ⊗ qr)))) ⊕ (((ur ⊗ qi) ⊕ (ui ⊗ qr)) ⊕ (((ur ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr))) ⊕ (ui ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))) ⊕ ((ur ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr))) ⊕ (ui ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))))))) ⊕ (ui ⊗ ((pr ⊕ (((ur ⊗ qr) ⊖ (ui ⊗ qi)) ⊕ ((ur ⊗ qr) ⊖ (ui ⊗ qi)))) ⊕ (((ur ⊗ qr) ⊖ (ui ⊗ qi)) ⊕ (((ur ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti))) ⊖ (ui ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))) ⊕ ((ur ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti))) ⊖ (ui ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))))))))) P.≃-refl (C.re u) (C.im u) (C.re p) (C.im p) (C.re q) (C.im q) (C.re t) (C.im t))

squareStep : ∀ u p n →
  (u *C ((p +C (scaleC n p +C scaleC n p)) +C scaleC (n * n) p)) ≈C
  scaleC ((n + R.1ℝ) * (n + R.1ℝ)) (u *C p)
squareStep u p n = (let open P.ℝ-Solver in solve 5 (λ ur ui pr pi n →
    ((ur ⊗ ((pr ⊕ ((n ⊗ pr) ⊕ (n ⊗ pr))) ⊕ (((n ⊗ n) ⊖ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ)) ⊗ pr))) ⊖ (ui ⊗ ((pi ⊕ ((n ⊗ pi) ⊕ (n ⊗ pi))) ⊕ (((n ⊗ n) ⊖ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ)) ⊗ pi)))) ⊜ ((((n ⊕ Κ 1ℚᵘ) ⊗ (n ⊕ Κ 1ℚᵘ)) ⊖ ((Κ 0ℚᵘ ⊕ Κ 0ℚᵘ) ⊗ (Κ 0ℚᵘ ⊕ Κ 0ℚᵘ))) ⊗ ((ur ⊗ pr) ⊖ (ui ⊗ pi)))) P.≃-refl (C.re u) (C.im u) (C.re p) (C.im p) n) ,
  (let open P.ℝ-Solver in solve 5 (λ ur ui pr pi n →
    ((ur ⊗ ((pi ⊕ ((n ⊗ pi) ⊕ (n ⊗ pi))) ⊕ (((n ⊗ n) ⊖ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ)) ⊗ pi))) ⊕ (ui ⊗ ((pr ⊕ ((n ⊗ pr) ⊕ (n ⊗ pr))) ⊕ (((n ⊗ n) ⊖ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ)) ⊗ pr)))) ⊜ ((((n ⊕ Κ 1ℚᵘ) ⊗ (n ⊕ Κ 1ℚᵘ)) ⊖ ((Κ 0ℚᵘ ⊕ Κ 0ℚᵘ) ⊗ (Κ 0ℚᵘ ⊕ Κ 0ℚᵘ))) ⊗ ((ur ⊗ pi) ⊕ (ui ⊗ pr)))) P.≃-refl (C.re u) (C.im u) (C.re p) (C.im p) n)

firstTermShuffle : ∀ u f q → (u *C (f *C q)) ≈C (f *C (u *C q))
firstTermShuffle u f q = (let open P.ℝ-Solver in solve 6 (λ ur ui fr fi qr qi →
    ((ur ⊗ ((fr ⊗ qr) ⊖ (fi ⊗ qi))) ⊖ (ui ⊗ ((fr ⊗ qi) ⊕ (fi ⊗ qr)))) ⊜ ((fr ⊗ ((ur ⊗ qr) ⊖ (ui ⊗ qi))) ⊖ (fi ⊗ ((ur ⊗ qi) ⊕ (ui ⊗ qr))))) P.≃-refl (C.re u) (C.im u) (C.re f) (C.im f) (C.re q) (C.im q)) ,
  (let open P.ℝ-Solver in solve 6 (λ ur ui fr fi qr qi →
    ((ur ⊗ ((fr ⊗ qi) ⊕ (fi ⊗ qr))) ⊕ (ui ⊗ ((fr ⊗ qr) ⊖ (fi ⊗ qi)))) ⊜ ((fr ⊗ ((ur ⊗ qi) ⊕ (ui ⊗ qr))) ⊕ (fi ⊗ ((ur ⊗ qr) ⊖ (ui ⊗ qi))))) P.≃-refl (C.re u) (C.im u) (C.re f) (C.im f) (C.re q) (C.im q))

secondTermShuffle : ∀ u f q t →
  ((u *C (f *C q)) +C ((u *C (u *C (f *C t))) +C (u *C (u *C (f *C t))))) ≈C
  (f *C ((u *C q) +C ((u *C (u *C t)) +C (u *C (u *C t)))))
secondTermShuffle u f q t = (let open P.ℝ-Solver in solve 8 (λ ur ui fr fi qr qi tr ti →
    (((ur ⊗ ((fr ⊗ qr) ⊖ (fi ⊗ qi))) ⊖ (ui ⊗ ((fr ⊗ qi) ⊕ (fi ⊗ qr)))) ⊕ (((ur ⊗ ((ur ⊗ ((fr ⊗ tr) ⊖ (fi ⊗ ti))) ⊖ (ui ⊗ ((fr ⊗ ti) ⊕ (fi ⊗ tr))))) ⊖ (ui ⊗ ((ur ⊗ ((fr ⊗ ti) ⊕ (fi ⊗ tr))) ⊕ (ui ⊗ ((fr ⊗ tr) ⊖ (fi ⊗ ti)))))) ⊕ ((ur ⊗ ((ur ⊗ ((fr ⊗ tr) ⊖ (fi ⊗ ti))) ⊖ (ui ⊗ ((fr ⊗ ti) ⊕ (fi ⊗ tr))))) ⊖ (ui ⊗ ((ur ⊗ ((fr ⊗ ti) ⊕ (fi ⊗ tr))) ⊕ (ui ⊗ ((fr ⊗ tr) ⊖ (fi ⊗ ti)))))))) ⊜ ((fr ⊗ (((ur ⊗ qr) ⊖ (ui ⊗ qi)) ⊕ (((ur ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti))) ⊖ (ui ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))) ⊕ ((ur ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti))) ⊖ (ui ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr))))))) ⊖ (fi ⊗ (((ur ⊗ qi) ⊕ (ui ⊗ qr)) ⊕ (((ur ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr))) ⊕ (ui ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))) ⊕ ((ur ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr))) ⊕ (ui ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti))))))))) P.≃-refl (C.re u) (C.im u) (C.re f) (C.im f) (C.re q) (C.im q) (C.re t) (C.im t)) ,
  (let open P.ℝ-Solver in solve 8 (λ ur ui fr fi qr qi tr ti →
    (((ur ⊗ ((fr ⊗ qi) ⊕ (fi ⊗ qr))) ⊕ (ui ⊗ ((fr ⊗ qr) ⊖ (fi ⊗ qi)))) ⊕ (((ur ⊗ ((ur ⊗ ((fr ⊗ ti) ⊕ (fi ⊗ tr))) ⊕ (ui ⊗ ((fr ⊗ tr) ⊖ (fi ⊗ ti))))) ⊕ (ui ⊗ ((ur ⊗ ((fr ⊗ tr) ⊖ (fi ⊗ ti))) ⊖ (ui ⊗ ((fr ⊗ ti) ⊕ (fi ⊗ tr)))))) ⊕ ((ur ⊗ ((ur ⊗ ((fr ⊗ ti) ⊕ (fi ⊗ tr))) ⊕ (ui ⊗ ((fr ⊗ tr) ⊖ (fi ⊗ ti))))) ⊕ (ui ⊗ ((ur ⊗ ((fr ⊗ tr) ⊖ (fi ⊗ ti))) ⊖ (ui ⊗ ((fr ⊗ ti) ⊕ (fi ⊗ tr)))))))) ⊜ ((fr ⊗ (((ur ⊗ qi) ⊕ (ui ⊗ qr)) ⊕ (((ur ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr))) ⊕ (ui ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti)))) ⊕ ((ur ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr))) ⊕ (ui ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti))))))) ⊕ (fi ⊗ (((ur ⊗ qr) ⊖ (ui ⊗ qi)) ⊕ (((ur ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti))) ⊖ (ui ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr)))) ⊕ ((ur ⊗ ((ur ⊗ tr) ⊖ (ui ⊗ ti))) ⊖ (ui ⊗ ((ur ⊗ ti) ⊕ (ui ⊗ tr))))))))) P.≃-refl (C.re u) (C.im u) (C.re f) (C.im f) (C.re q) (C.im q) (C.re t) (C.im t))

scaleShuffle : ∀ f p n → (f *C scaleC n p) ≈C (scaleC n f *C p)
scaleShuffle f p n = (let open P.ℝ-Solver in solve 5 (λ fr fi pr pi n →
    ((fr ⊗ (n ⊗ pr)) ⊖ (fi ⊗ (n ⊗ pi))) ⊜ (((n ⊗ fr) ⊗ pr) ⊖ ((n ⊗ fi) ⊗ pi))) P.≃-refl (C.re f) (C.im f) (C.re p) (C.im p) n) ,
  (let open P.ℝ-Solver in solve 5 (λ fr fi pr pi n →
    ((fr ⊗ (n ⊗ pi)) ⊕ (fi ⊗ (n ⊗ pr))) ⊜ (((n ⊗ fr) ⊗ pi) ⊕ ((n ⊗ fi) ⊗ pr))) P.≃-refl (C.re f) (C.im f) (C.re p) (C.im p) n)


firstPow : ∀ u n → (u *C D.Q u u n) ≈C scaleC (NR.natReal n) (powC u n)
firstPow u zero = complexTrans (L.complexMultiplyRightZero u) (complexSym (Ram.scaleZero A.oneC))
firstPow u (suc n) = complexTrans
  (A.mulCCongruent (C.≈C-refl _) (D.qStep u u n))
  (complexTrans (A.mulCCongruent (C.≈C-refl _)
    (A.addCCongruent (C.≈C-refl _) (firstPow u n)))
    (complexTrans (firstStep u (powC u n) (NR.natReal n))
      (A.scaleCCongruent (C.≈C-refl _) (P.≃-symm (NR.natRealSuccessor n)))))

squareScale : ∀ n → R._≃_ (NR.natReal (suc n) * NR.natReal (suc n))
  ((NR.natReal n + R.1ℝ) * (NR.natReal n + R.1ℝ))
squareScale n = P.*-cong (NR.natRealSuccessor n) (NR.natRealSuccessor n)

squarePow : ∀ u n →
  ((u *C D.Q u u n) +C ((u *C (u *C T.T u u u n)) +C (u *C (u *C T.T u u u n)))) ≈C
  scaleC (NR.natReal n * NR.natReal n) (powC u n)
squarePow u zero =
  let z = u *C (u *C A.zeroC)
      zz = complexTrans (A.mulCCongruent (C.≈C-refl _) (L.complexMultiplyRightZero u))
        (L.complexMultiplyRightZero u)
  in complexTrans (A.addCCongruent (L.complexMultiplyRightZero u) (A.addCCongruent zz zz))
    (complexTrans (L.complexAddLeftIdentity _) (complexTrans (L.complexAddRightIdentity _)
      (complexSym (complexTrans
        (A.scaleCCongruent (C.≈C-refl _) (P.*-zeroˡ R.0ℝ)) (Ram.scaleZero A.oneC)))))
squarePow u (suc n) =
  let p = powC u n
      q = D.Q u u n
      t = T.T u u u n
      p1 = firstPow u n
      p2 = squarePow u n
      qread = A.mulCCongruent (C.≈C-refl _) (D.qStep u u n)
  in complexTrans (A.addCCongruent qread (C.≈C-refl _))
    (complexTrans (secondStep u p q t)
      (complexTrans (A.mulCCongruent (C.≈C-refl _)
        (A.addCCongruent (A.addCCongruent (C.≈C-refl _) (A.addCCongruent p1 p1)) p2))
        (complexTrans (squareStep u p (NR.natReal n))
          (A.scaleCCongruent (C.≈C-refl _) (P.≃-symm (squareScale n))))))

-- The original formal Euler coefficient, as a complex scaling.
dScale : ∀ f n → scaleC (NR.natReal n) (f n) ≈C E.δ f n
dScale f n = P.≃-symm (U.D1Meaning (C.realTerms f) n) ,
  P.≃-symm (U.D1Meaning (C.imagTerms f) n)

dSquare : ∀ f n → scaleC (NR.natReal n * NR.natReal n) (f n) ≈C E.δ (E.δ f) n
dSquare f n =
  (P.≃-trans (P.*-assoc _ _ _)
    (P.≃-trans (P.*-congˡ (P.≃-symm (U.D1Meaning (C.realTerms f) n)))
      (P.≃-symm (U.D1Meaning (C.realTerms (E.δ f)) n)))) ,
  (P.≃-trans (P.*-assoc _ _ _)
    (P.≃-trans (P.*-congˡ (P.≃-symm (U.D1Meaning (C.imagTerms f) n)))
      (P.≃-symm (U.D1Meaning (C.imagTerms (E.δ f)) n))))

firstTerm : ∀ f u n → (u *C D.terms f u u n) ≈C N.twist u (E.δ f) n
firstTerm f u n = complexTrans (firstTermShuffle u (f n) (D.Q u u n))
  (complexTrans (A.mulCCongruent (C.≈C-refl _) (firstPow u n))
    (complexTrans (scaleShuffle (f n) (powC u n) (NR.natReal n))
      (A.mulCCongruent (dScale f n) (C.≈C-refl _))))

secondTerm : ∀ f u n →
  ((u *C D.terms f u u n) +C
    ((u *C (u *C T.terms f u u u n)) +C (u *C (u *C T.terms f u u u n)))) ≈C
  N.twist u (E.δ (E.δ f)) n
secondTerm f u n =
  complexTrans (secondTermShuffle u (f n) (D.Q u u n) (T.T u u u n))
    (complexTrans (A.mulCCongruent (C.≈C-refl _) (squarePow u n))
      (complexTrans (scaleShuffle (f n) (powC u n) (NR.natReal n * NR.natReal n))
        (A.mulCCongruent (dSquare f n) (C.≈C-refl _))))
