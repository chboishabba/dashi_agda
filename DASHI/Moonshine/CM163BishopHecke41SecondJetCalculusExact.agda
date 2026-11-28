module DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact where

-- SOURCE-WRITTEN, kernel pending. A two-jet is the first quotient
-- together with its own first jet, not a second independent value.
-- All operations preserve the original function and do not divide
-- by a perturbation, including the zero perturbation.
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (_⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Pow
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41ComplexExpSecondJetExact as Exp
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC)
open Comp using (complexTrans; complexSym)

record Jet2 (w f : Nat → BishopComplex) (a b c : BishopComplex) : Set where
  field
    first : J.Jet w f a b
    second : J.Jet w (J.quotient first) b c
open Jet2 public

cong2 : ∀ {w f g a a' b b' c c'} →
  (∀ n → f n ≈C g n) → a ≈C a' → b ≈C b' → c ≈C c' →
  Jet2 w f a b c → Jet2 w g a' b' c'
cong2 eq ha hb hc j = record
  { first = J.congJet eq ha hb (first j)
  ; second = J.congJet (λ _ → C.≈C-refl _) hb hc (second j) }

scaleJet : ∀ {w f a b} (k : BishopComplex) → J.Jet w f a b →
  J.Jet w (λ n → k *C f n) (k *C a) (k *C b)
scaleJet {w} {f} {a} k j = record
  { J.quotient = λ n → k *C J.quotient j n
  ; J.factor = λ n → complexTrans (complexSym (Alg.mulSub k (f n) a))
      (complexTrans (A.mulCCongruent (C.≈C-refl _) (J.factor j n))
        (complexTrans (complexSym (L.complexMultiplyAssociative k (w n) (J.quotient j n)))
          (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative k (w n)) (C.≈C-refl _))
            (L.complexMultiplyAssociative (w n) k (J.quotient j n)))))
  ; J.limit = Lim.mulConst k (J.limit j) }

scale2 : ∀ {w f a b c} k → Jet2 w f a b c →
  Jet2 w (λ n → k *C f n) (k *C a) (k *C b) (k *C c)
scale2 k j = record { first = scaleJet k (first j) ; second = scaleJet k (second j) }

add2 : ∀ {w f g a b c d e h} → Jet2 w f a b c → Jet2 w g d e h →
  Jet2 w (λ n → f n +C g n) (a +C d) (b +C e) (c +C h)
add2 j k = record { first = J.addJet (first j) (first k) ; second = J.addJet (second j) (second k) }

sub2 : ∀ {w f g a b c d e h} → Jet2 w f a b c → Jet2 w g d e h →
  Jet2 w (λ n → f n -C g n) (a -C d) (b -C e) (c -C h)
sub2 j k = record { first = J.subJet (first j) (first k) ; second = J.subJet (second j) (second k) }

mul2 : ∀ {w f g a b c d e h} → Lim.Conv w A.zeroC →
  Jet2 w f a b c → Jet2 w g d e h →
  Jet2 w (λ n → f n *C g n) (a *C d) (b *C d +C a *C e)
    ((c *C d +C b *C e) +C a *C h)
mul2 {a = a} cv j k = record
  { first = J.mulJet cv (first j) (first k)
  ; second = J.addJet (J.mulJet cv (second j) (first k)) (scaleJet a (second k)) }

-- A genuine chain rule for first and second coefficients. The outer
-- slope is evaluated along the ACTUAL increment, not an independent
-- sequence whose connection to the inner jet is forgotten.
reparam : ∀ {w g f a b c d} → J.Jet w g a b →
  J.Jet (λ n → g n -C a) f c d →
  J.Jet w f c (b *C d)
reparam {w} {g} j k = record
  { J.quotient = λ n → J.quotient j n *C J.quotient k n
  ; J.factor = λ n → complexTrans (J.factor k n)
      (complexTrans (A.mulCCongruent (J.factor j n) (C.≈C-refl _))
        (L.complexMultiplyAssociative (w n) (J.quotient j n) (J.quotient k n)))
  ; J.limit = Conv.mulConv (J.limit j) (J.limit k) }

compose : ∀ {w g f a b c d e h} → Lim.Conv w A.zeroC →
  Jet2 w g a b c → Jet2 (λ n → g n -C a) f d e h →
  Jet2 w f d (b *C e) (c *C e +C b *C (b *C h))
compose cv j k = record
  { first = reparam (first j) (first k)
  ; second = J.mulJet cv (second j) (reparam (first j) (second k)) }

expFactor : ∀ w r → (((A.oneC +C w) +C (w *C w) *C r) -C A.oneC) ≈C (w *C (A.oneC +C w *C r))
expFactor w r =
  (let open P.ℝ-Solver in solve 4 (λ wr wi rr ri → (((Κ 1ℚᵘ ⊕ wr) ⊕ ((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ rr) ⊖ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ ri))) ⊖ Κ 1ℚᵘ) ⊜ ((wr ⊗ (Κ 1ℚᵘ ⊕ ((wr ⊗ rr) ⊖ (wi ⊗ ri)))) ⊖ (wi ⊗ (Κ 0ℚᵘ ⊕ ((wr ⊗ ri) ⊕ (wi ⊗ rr)))))) P.≃-refl (C.re w) (C.im w) (C.re r) (C.im r)) ,
  (let open P.ℝ-Solver in solve 4 (λ wr wi rr ri → (((Κ 0ℚᵘ ⊕ wi) ⊕ ((((wr ⊗ wr) ⊖ (wi ⊗ wi)) ⊗ ri) ⊕ (((wr ⊗ wi) ⊕ (wi ⊗ wr)) ⊗ rr))) ⊖ Κ 0ℚᵘ) ⊜ ((wr ⊗ (Κ 0ℚᵘ ⊕ ((wr ⊗ ri) ⊕ (wi ⊗ rr)))) ⊕ (wi ⊗ (Κ 1ℚᵘ ⊕ ((wr ⊗ rr) ⊖ (wi ⊗ ri)))))) P.≃-refl (C.re w) (C.im w) (C.re r) (C.im r))


exp2 : (T : Cartesian.BishopSetoidComplexTranscendentals) →
  (w : Nat → BishopComplex) → (inside : ∀ n → Exp.Inside (w n)) →
  Lim.Conv w A.zeroC →
  Jet2 w (λ n → Weld.originalBishopExpOnSeries T (w n)) A.oneC A.oneC (Poly.realC ((+ 1 / 2) ⋆))
exp2 T w inside cv = record
  { first = record
      { J.quotient = λ n → Exp.slope (w n) (inside n)
      ; J.factor = λ n → complexTrans (A.subCCongruent (Exp.expansion T (w n) (inside n)) (C.≈C-refl _))
          (complexTrans (A.subCCongruent (A.addCCongruent (C.≈C-refl _)
            (A.mulCCongruent (complexSym (Pow.powTwo (w n))) (C.≈C-refl _))) (C.≈C-refl _))
            (expFactor (w n) (Exp.remainder (w n) (inside n))))
      ; J.limit = J.continuous cv (Exp.slopeJet w inside cv) }
  ; second = Exp.slopeJet w inside cv }

module At (inputs : Round11.BishopCutset) where
  module Ph = Phase.At inputs

  -- This is the original q at an actual upper-half-plane sequence.
  -- The exponent increment comes from the actual chart geometry.
  actualPhase2 : (p : U.BishopUpperHalfPlanePoint)
    (v : Nat → U.BishopUpperHalfPlanePoint) (w : Nat → BishopComplex) →
    (∀ n → Ph.exponent (v n) ≈C (Ph.exponent p +C w n)) →
    (inside : ∀ n → Exp.Inside (w n)) → Lim.Conv w A.zeroC →
    Jet2 w (λ n → Ph.q (v n)) (Ph.q p) (Ph.q p)
      (Ph.q p *C Poly.realC ((+ 1 / 2) ⋆))
  actualPhase2 p v w he inside cv =
    cong2 (λ n → complexSym (complexTrans
      (Weld.originalBishopExpOnSeriesCongruent Ph.T (he n))
      (Ph.expAddS (Ph.exponent p) (w n))))
      (L.complexMultiplyRightIdentity _) (L.complexMultiplyRightIdentity _) (C.≈C-refl _)
      (scale2 (Ph.q p) (exp2 Ph.T w inside cv))
