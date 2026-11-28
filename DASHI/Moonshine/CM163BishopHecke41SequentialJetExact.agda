module DASHI.Moonshine.CM163BishopHecke41SequentialJetExact where

-- SOURCE-WRITTEN, kernel pending. Division-free first-order germ
-- calculus on the actual Bishop complex carrier, along a null sequence.
-- The coordinate is cancelled only to compare two equal germs, never
-- to define a slope at the center.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised using (ℚᵘ; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (_⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.CM163BishopHecke41ComplexPacketShiftExact as Shift
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Packet
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_)
open Comp using (complexTrans; complexSym)

record Jet (w f : Nat → BishopComplex) (a b : BishopComplex) : Set where
  field
    quotient : Nat → BishopComplex
    factor : ∀ n → (f n -C a) ≈C (w n *C quotient n)
    limit : Lim.Conv quotient b
open Jet public

sameSub : ∀ a → (a -C a) ≈C A.zeroC
sameSub a =
  (let open P.ℝ-Solver in solve 2 (λ ar ai → (ar ⊖ ar) ⊜ Κ 0ℚᵘ) P.≃-refl (C.re a) (C.im a)) ,
  (let open P.ℝ-Solver in solve 2 (λ ar ai → (ai ⊖ ai) ⊜ Κ 0ℚᵘ) P.≃-refl (C.re a) (C.im a))

subZero : ∀ a → (a -C A.zeroC) ≈C a
subZero a =
  (let open P.ℝ-Solver in solve 2 (λ ar ai → (ar ⊖ Κ 0ℚᵘ) ⊜ ar) P.≃-refl (C.re a) (C.im a)) ,
  (let open P.ℝ-Solver in solve 2 (λ ar ai → (ai ⊖ Κ 0ℚᵘ) ⊜ ai) P.≃-refl (C.re a) (C.im a))

recover : ∀ a b → a ≈C (b +C (a -C b))
recover a b =
  (let open P.ℝ-Solver in solve 4 (λ ar ai br bi → ar ⊜ (br ⊕ (ar ⊖ br))) P.≃-refl (C.re a) (C.im a) (C.re b) (C.im b)) ,
  (let open P.ℝ-Solver in solve 4 (λ ar ai br bi → ai ⊜ (bi ⊕ (ai ⊖ bi))) P.≃-refl (C.re a) (C.im a) (C.re b) (C.im b))

addStep : ∀ f g a c → ((f +C g) -C (a +C c)) ≈C ((f -C a) +C (g -C c))
addStep f g a c =
  (let open P.ℝ-Solver in solve 8 (λ fr fi gr gi ar ai cr ci → ((fr ⊕ gr) ⊖ (ar ⊕ cr)) ⊜ ((fr ⊖ ar) ⊕ (gr ⊖ cr))) P.≃-refl (C.re f) (C.im f) (C.re g) (C.im g) (C.re a) (C.im a) (C.re c) (C.im c)) ,
  (let open P.ℝ-Solver in solve 8 (λ fr fi gr gi ar ai cr ci → ((fi ⊕ gi) ⊖ (ai ⊕ ci)) ⊜ ((fi ⊖ ai) ⊕ (gi ⊖ ci))) P.≃-refl (C.re f) (C.im f) (C.re g) (C.im g) (C.re a) (C.im a) (C.re c) (C.im c))

subStep : ∀ f g a c → ((f -C g) -C (a -C c)) ≈C ((f -C a) -C (g -C c))
subStep f g a c =
  (let open P.ℝ-Solver in solve 8 (λ fr fi gr gi ar ai cr ci → ((fr ⊖ gr) ⊖ (ar ⊖ cr)) ⊜ ((fr ⊖ ar) ⊖ (gr ⊖ cr))) P.≃-refl (C.re f) (C.im f) (C.re g) (C.im g) (C.re a) (C.im a) (C.re c) (C.im c)) ,
  (let open P.ℝ-Solver in solve 8 (λ fr fi gr gi ar ai cr ci → ((fi ⊖ gi) ⊖ (ai ⊖ ci)) ⊜ ((fi ⊖ ai) ⊖ (gi ⊖ ci))) P.≃-refl (C.re f) (C.im f) (C.re g) (C.im g) (C.re a) (C.im a) (C.re c) (C.im c))

subFactor : ∀ w a b → (w *C a -C w *C b) ≈C (w *C (a -C b))
subFactor w a b =
  (let open P.ℝ-Solver in solve 6 (λ wr wi ar ai br bi → (((wr ⊗ ar) ⊖ (wi ⊗ ai)) ⊖ ((wr ⊗ br) ⊖ (wi ⊗ bi))) ⊜ ((wr ⊗ (ar ⊖ br)) ⊖ (wi ⊗ (ai ⊖ bi)))) P.≃-refl (C.re w) (C.im w) (C.re a) (C.im a) (C.re b) (C.im b)) ,
  (let open P.ℝ-Solver in solve 6 (λ wr wi ar ai br bi → (((wr ⊗ ai) ⊕ (wi ⊗ ar)) ⊖ ((wr ⊗ bi) ⊕ (wi ⊗ br))) ⊜ ((wr ⊗ (ai ⊖ bi)) ⊕ (wi ⊗ (ar ⊖ br)))) P.≃-refl (C.re w) (C.im w) (C.re a) (C.im a) (C.re b) (C.im b))

mulStep : ∀ f g a c → (f *C g -C a *C c) ≈C ((f -C a) *C g +C a *C (g -C c))
mulStep f g a c =
  (let open P.ℝ-Solver in solve 8 (λ fr fi gr gi ar ai cr ci → (((fr ⊗ gr) ⊖ (fi ⊗ gi)) ⊖ ((ar ⊗ cr) ⊖ (ai ⊗ ci))) ⊜ ((((fr ⊖ ar) ⊗ gr) ⊖ ((fi ⊖ ai) ⊗ gi)) ⊕ ((ar ⊗ (gr ⊖ cr)) ⊖ (ai ⊗ (gi ⊖ ci))))) P.≃-refl (C.re f) (C.im f) (C.re g) (C.im g) (C.re a) (C.im a) (C.re c) (C.im c)) ,
  (let open P.ℝ-Solver in solve 8 (λ fr fi gr gi ar ai cr ci → (((fr ⊗ gi) ⊕ (fi ⊗ gr)) ⊖ ((ar ⊗ ci) ⊕ (ai ⊗ cr))) ⊜ ((((fr ⊖ ar) ⊗ gi) ⊕ ((fi ⊖ ai) ⊗ gr)) ⊕ ((ar ⊗ (gi ⊖ ci)) ⊕ (ai ⊗ (gr ⊖ cr))))) P.≃-refl (C.re f) (C.im f) (C.re g) (C.im g) (C.re a) (C.im a) (C.re c) (C.im c))

mulFactor : ∀ w u g a v → ((w *C u) *C g +C a *C (w *C v)) ≈C (w *C (u *C g +C a *C v))
mulFactor w u g a v =
  (let open P.ℝ-Solver in solve 10 (λ wr wi ur ui gr gi ar ai vr vi → (((((wr ⊗ ur) ⊖ (wi ⊗ ui)) ⊗ gr) ⊖ (((wr ⊗ ui) ⊕ (wi ⊗ ur)) ⊗ gi)) ⊕ ((ar ⊗ ((wr ⊗ vr) ⊖ (wi ⊗ vi))) ⊖ (ai ⊗ ((wr ⊗ vi) ⊕ (wi ⊗ vr))))) ⊜ ((wr ⊗ (((ur ⊗ gr) ⊖ (ui ⊗ gi)) ⊕ ((ar ⊗ vr) ⊖ (ai ⊗ vi)))) ⊖ (wi ⊗ (((ur ⊗ gi) ⊕ (ui ⊗ gr)) ⊕ ((ar ⊗ vi) ⊕ (ai ⊗ vr)))))) P.≃-refl (C.re w) (C.im w) (C.re u) (C.im u) (C.re g) (C.im g) (C.re a) (C.im a) (C.re v) (C.im v)) ,
  (let open P.ℝ-Solver in solve 10 (λ wr wi ur ui gr gi ar ai vr vi → (((((wr ⊗ ur) ⊖ (wi ⊗ ui)) ⊗ gi) ⊕ (((wr ⊗ ui) ⊕ (wi ⊗ ur)) ⊗ gr)) ⊕ ((ar ⊗ ((wr ⊗ vi) ⊕ (wi ⊗ vr))) ⊕ (ai ⊗ ((wr ⊗ vr) ⊖ (wi ⊗ vi))))) ⊜ ((wr ⊗ (((ur ⊗ gi) ⊕ (ui ⊗ gr)) ⊕ ((ar ⊗ vi) ⊕ (ai ⊗ vr)))) ⊕ (wi ⊗ (((ur ⊗ gr) ⊖ (ui ⊗ gi)) ⊕ ((ar ⊗ vr) ⊖ (ai ⊗ vi)))))) P.≃-refl (C.re w) (C.im w) (C.re u) (C.im u) (C.re g) (C.im g) (C.re a) (C.im a) (C.re v) (C.im v))

subtractHead : ∀ a b → ((a +C b) -C a) ≈C b
subtractHead a b =
  (let open P.ℝ-Solver in solve 4 (λ ar ai br bi → ((ar ⊕ br) ⊖ ar) ⊜ br) P.≃-refl (C.re a) (C.im a) (C.re b) (C.im b)) ,
  (let open P.ℝ-Solver in solve 4 (λ ar ai br bi → ((ai ⊕ bi) ⊖ ai) ⊜ bi) P.≃-refl (C.re a) (C.im a) (C.re b) (C.im b))


constant : ∀ w a → Jet w (λ _ → a) a A.zeroC
constant w a = record
  { quotient = λ _ → A.zeroC
  ; factor = λ n → complexTrans (sameSub a) (complexSym (L.complexMultiplyRightZero (w n)))
  ; limit = Lim.constantC A.zeroC }

coordinate : ∀ w → Jet w w A.zeroC A.oneC
coordinate w = record
  { quotient = λ _ → A.oneC
  ; factor = λ n → complexTrans (subZero (w n)) (complexSym (L.complexMultiplyRightIdentity (w n)))
  ; limit = Lim.constantC A.oneC }

congJet : ∀ {w f g a b c d} → (∀ n → f n ≈C g n) → a ≈C c → b ≈C d →
  Jet w f a b → Jet w g c d
congJet eq h k j = record
  { quotient = quotient j
  ; factor = λ n → complexTrans (A.subCCongruent (complexSym (eq n)) (complexSym h)) (factor j n)
  ; limit = Lim.limitTransport k (limit j) }

continuous : ∀ {w f a b} → Lim.Conv w A.zeroC → Jet w f a b → Lim.Conv f a
continuous {w} {f} {a} cv j =
  Lim.convTransport (λ n → complexSym (complexTrans (recover (f n) a)
    (A.addCCongruent (C.≈C-refl a) (factor j n))))
    (Lim.limitTransport (complexTrans (A.addCCongruent (C.≈C-refl _) (L.complexMultiplyLeftZero _))
      (L.complexAddRightIdentity _))
      (Lim.addConv (Lim.constantC a) (Conv.mulConv cv (limit j))))

addJet : ∀ {w f g a b c d} → Jet w f a b → Jet w g c d →
  Jet w (λ n → f n +C g n) (a +C c) (b +C d)
addJet {w} {f} {g} {a} {b} {c} {d} j k = record
  { quotient = λ n → quotient j n +C quotient k n
  ; factor = λ n → complexTrans (addStep (f n) (g n) a c)
      (complexTrans (A.addCCongruent (factor j n) (factor k n))
        (complexSym (L.complexMultiplyDistributesLeft (w n) _ _)))
  ; limit = Lim.addConv (limit j) (limit k) }

subJet : ∀ {w f g a b c d} → Jet w f a b → Jet w g c d →
  Jet w (λ n → f n -C g n) (a -C c) (b -C d)
subJet {w} {f} {g} {a} {b} {c} {d} j k = record
  { quotient = λ n → quotient j n -C quotient k n
  ; factor = λ n → complexTrans (subStep (f n) (g n) a c)
      (complexTrans (A.subCCongruent (factor j n) (factor k n))
        (subFactor (w n) (quotient j n) (quotient k n)))
  ; limit = Lim.subConv (limit j) (limit k) }

mulJet : ∀ {w f g a b c d} → Lim.Conv w A.zeroC →
  Jet w f a b → Jet w g c d →
  Jet w (λ n → f n *C g n) (a *C c) (b *C c +C a *C d)
mulJet {w} {f} {g} {a} {b} {c} {d} cv j k = record
  { quotient = λ n → quotient j n *C g n +C a *C quotient k n
  ; factor = λ n → complexTrans (mulStep (f n) (g n) a c)
      (complexTrans (A.addCCongruent
        (A.mulCCongruent (factor j n) (C.≈C-refl _))
        (A.mulCCongruent (C.≈C-refl _) (factor k n)))
        (mulFactor (w n) (quotient j n) (g n) a (quotient k n)))
  ; limit = Lim.addConv (Conv.mulConv (limit j) (continuous cv k))
      (Conv.mulConv (Lim.constantC a) (limit k)) }

coordinateMul : ∀ {w f a} → Lim.Conv f a → Jet w (λ n → w n *C f n) A.zeroC a
coordinateMul {w} {f} cv = record
  { quotient = f
  ; factor = λ n → subZero (w n *C f n)
  ; limit = cv }

unique : ∀ {w f g a b c d} → (∀ n → Rec.BishopComplexNonzero (w n)) →
  Lim.Conv w A.zeroC → (∀ n → f n ≈C g n) →
  Jet w f a b → Jet w g c d → b ≈C d
unique {w} {f} {g} {a} {b} {c} {d} nz cv eq j k =
  let centers = Lim.convUnique (Lim.convTransport eq (continuous cv j)) (continuous cv k)
      sameQuot : ∀ n → quotient j n ≈C quotient k n
      sameQuot n = J.cancelLeft (w n) _ _ (nz n)
        (complexTrans (complexSym (factor j n))
          (complexTrans (A.subCCongruent (eq n) centers) (factor k n)))
  in Lim.convUnique (Lim.convTransport sameQuot (limit j)) (limit k)

-- Literal ascending polynomial at a vanishing coordinate: the center
-- and derivative are exactly the first two original coefficients.
ascZero : ∀ cs → Shift.asc A.zeroC cs ≈C Poly.realC (Packet.head cs ⋆)
ascZero [] = C.≈C-refl _
ascZero (c ∷ cs) = complexTrans (A.addCCongruent (C.≈C-refl _) (L.complexMultiplyLeftZero _))
  (L.complexAddRightIdentity _)

ascContinuous : ∀ cs {f : Nat → BishopComplex} {z} → Lim.Conv f z →
  Lim.Conv (λ n → Shift.asc (f n) cs) (Shift.asc z cs)
ascContinuous [] cv = Lim.constantC A.zeroC
ascContinuous (c ∷ cs) cv = Lim.addConv (Lim.constantC (Poly.realC (c ⋆)))
  (Conv.mulConv cv (ascContinuous cs cv))

ascJet : ∀ cs {w f a} → Lim.Conv w A.zeroC → Jet w f A.zeroC a →
  Jet w (λ n → Shift.asc (f n) cs) (Poly.realC (Packet.head cs ⋆))
    (a *C Poly.realC (Packet.head (Packet.tail cs) ⋆))
ascJet [] cv j = congJet (λ _ → C.≈C-refl _) (C.≈C-refl _)
  (complexSym (L.complexMultiplyRightZero _)) (constant _ A.zeroC)
ascJet (c ∷ cs) {w} {f} {a} cv j =
  let tailCv = ascContinuous cs (continuous cv j)
      tailValue = Poly.realC (Packet.head cs ⋆)
      q : Nat → BishopComplex
      q n = quotient j n *C Shift.asc (f n) cs
      qCv = Conv.mulConv (limit j) (Lim.limitTransport (ascZero cs) tailCv)
  in record { quotient = q
    ; factor = λ n → complexTrans (subtractHead (Poly.realC (c ⋆)) (f n *C Shift.asc (f n) cs))
        (complexTrans (A.mulCCongruent (complexTrans (complexSym (subZero (f n))) (factor j n))
          (C.≈C-refl _)) (L.complexMultiplyAssociative (w n) (quotient j n) (Shift.asc (f n) cs)))
    ; limit = qCv }
