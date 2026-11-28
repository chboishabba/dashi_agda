module DASHI.Moonshine.CM163BishopHecke41SelectedRootWeldExact where

-- SOURCE-WRITTEN, kernel pending. The selected original fixed chart
-- product is already zero. The only remaining global input here is
-- its actual product-to-polynomial residual at that same chart.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (ℚᵘ; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _⋆; _*_; _+_; _-_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.CM163BishopHecke41CuspResidualExact as Res
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Shift
import DASHI.Moonshine.JInvariantBishopCM163SharpRootEnclosureExact as Sharp
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as Jet
import DASHI.Moonshine.JInvariantBishopCM163LiteralTerminalExact as Terminal
import DASHI.Foundations.BishopChudnovskyRawCoordinateWeldExact as Raw
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (_≈C_)
open A using (_*C_; _+C_; powC)
open Comp using (complexTrans; complexSym)
open Poly using (realC)

realMul : ∀ a b → (realC a *C realC b) ≈C realC (a * b)
realMul a b =
  (let open P.ℝ-Solver in solve 2 (λ a b → a ⊗ b ⊖ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊜ a ⊗ b)
    P.≃-refl a b) ,
  (let open P.ℝ-Solver in solve 2 (λ a b → a ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ b ⊜ Κ 0ℚᵘ)
    P.≃-refl a b)

realAdd : ∀ a b → (realC a +C realC b) ≈C realC (a + b)
realAdd a b = P.≃-refl , P.+-identityʳ R.0ℝ

realPow : ∀ a n → powC (realC a) n ≈C realC (R.pow a n)
realPow a zero = C.≈C-refl _
realPow a (suc n) = complexTrans (A.mulCCongruent (C.≈C-refl _) (realPow a n))
  (complexTrans (realMul a (R.pow a n)) (P.*-comm a (R.pow a n) , P.≃-refl))

polyR : ℝ → List ℚᵘ → ℝ
polyR a [] = R.0ℝ
polyR a (c ∷ cs) = (c ⋆) * R.pow a (length cs) + polyR a cs

polyReal : ∀ a cs → Poly.poly (realC a) cs ≈C realC (polyR a cs)
polyReal a [] = C.≈C-refl _
polyReal a (c ∷ cs) = complexTrans (A.addCCongruent
  (complexTrans (A.mulCCongruent (C.≈C-refl _) (realPow a (length cs)))
    (realMul (c ⋆) (R.pow a (length cs)))) (polyReal a cs))
  (realAdd ((c ⋆) * R.pow a (length cs)) (polyR a cs))

-- Descending Horner accumulator equals the literal polynomial sum.
-- This identifies the new complex polynomial with the exact original
-- real packet consumer used by the half-unit isolation theorem.
hornerRead : ∀ x a cs → Shift.descending x a cs ≃ a * R.pow x (length cs) + polyR x cs
hornerRead x a [] = P.≃-symm (P.≃-trans (P.+-cong (P.*-identityʳ a) P.≃-refl) (P.+-identityʳ a))
hornerRead x a (c ∷ cs) =
  P.≃-trans (hornerRead x ((c ⋆) + x * a) cs)
    (let open P.ℝ-Solver in solve 5
      (λ c x a p r → (c ⊕ x ⊗ a) ⊗ p ⊕ r ⊜ a ⊗ (p ⊗ x) ⊕ (c ⊗ p ⊕ r))
      P.≃-refl (c ⋆) x a (R.pow x (length cs)) (polyR x cs))

hornerZero : ∀ x cs → Shift.descending x R.0ℝ cs ≃ polyR x cs
hornerZero x cs = P.≃-trans (hornerRead x R.0ℝ cs)
  (P.≃-trans (P.+-cong (P.*-zeroˡ _) P.≃-refl) (P.+-identityˡ _))

module At (inputs : Round11.BishopCutset) where
  module R0 = Res.At inputs
  module G = R0.G
  module F = Fixed.At inputs

  selectedSame : G.j Fixed.p ≈C realC Guard.Root.j
  selectedSame = complexTrans
    (J.quotCong (C.≈C-refl _) (C.≈C-refl _) (G.globalGuard Fixed.p) F.guard)
    (complexTrans F.selectedJ
      (P.≃-refl , CM.Selected.RealSlice.jReal Guard.negativeDelta))

  actualPolynomial : C.re (Poly.poly (G.j Fixed.p) Packet.diagonal) ≃
    Shift.descending Guard.Root.j R.0ℝ Packet.diagonal
  actualPolynomial = P.≃-trans (proj₁ (Poly.polyCong selectedSame Packet.diagonal))
    (P.≃-trans (proj₁ (polyReal Guard.Root.j Packet.diagonal))
      (P.≃-symm (hornerZero Guard.Root.j Packet.diagonal)))

  -- The exact selected product zero is already constructed from
  -- the two reciprocal Hecke charts. No independent root premise.
  diagonalFromResidual : R0.d Fixed.p ≈C A.zeroC →
    Shift.descending Guard.Root.j R.0ℝ Packet.diagonal ≃ R.0ℝ
  diagonalFromResidual h =
    let x = C.re (G.diagonal Fixed.p)
        y = C.re (Poly.poly (G.j Fixed.p) Packet.diagonal)
    in P.≃-trans (P.≃-symm actualPolynomial)
      (P.≃-trans (let open P.ℝ-Solver in solve 2 (λ x y → y ⊜ x ⊖ (x ⊖ y))
        P.≃-refl x y)
        (P.≃-trans (P.+-cong (proj₁ G.selectedDiagonalZero) (P.-‿cong (proj₁ h)))
          (P.+-inverseʳ R.0ℝ)))

  rootFromResidual : R0.d Fixed.p ≈C A.zeroC → Jet.CMRoot
  rootFromResidual h = Shift.rootFromLiteralDiagonal Sharp.enclosure (diagonalFromResidual h)

  allRaw : R0.d Fixed.p ≈C A.zeroC → Terminal.OriginalRayResidual → (k : Nat) → Raw.RawCross k
  allRaw h ray = Terminal.allRawFromDiagonalAndRay (diagonalFromResidual h) ray
