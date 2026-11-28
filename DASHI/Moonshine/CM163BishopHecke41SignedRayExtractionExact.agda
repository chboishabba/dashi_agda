module DASHI.Moonshine.CM163BishopHecke41SignedRayExtractionExact where

-- SOURCE-WRITTEN, kernel pending. Extract the actual literal scalar
-- residual from the normalized original cross using division-free
-- sequential first jets. The forty-factor slope needs only a limit,
-- never a derivative. Actual germ/symmetry production stays explicit.
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Integer.Base using (+_; -_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _⋆; _+_; _-_; _*_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.JInvariantBishopCM163ReciprocalGeometryExact as Geo
import DASHI.Moonshine.JInvariantBishopCM163DiskCrossCoefficientExact as Disk
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as CM
import DASHI.Moonshine.JInvariantBishopCM163QuotientJetExact as QJ
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163LiteralTerminalExact as Terminal
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.CM163BishopHecke41SelectedRootWeldExact as Real
import DASHI.Moonshine.CM163BishopHecke41ComplexPacketShiftExact as Shift
import DASHI.Moonshine.CM163BishopHecke41ActualCrossExact as Cross
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC)
open Comp using (complexTrans; complexSym)
open Poly using (realC)

realSub : ∀ a b → (realC a -C realC b) ≈C realC (a - b)
realSub a b = P.≃-refl , P.+-inverseʳ R.0ℝ

module Along (w : Nat → BishopComplex) (cv : Lim.Conv w A.zeroC)
  (nz : ∀ n → Rec.BishopComplexNonzero (w n)) where

  RealJet : (Nat → BishopComplex) → ℝ → ℝ → Set
  RealJet f a b = J.Jet w f (realC a) (realC b)

  mul : ∀ {f g a b c d} → RealJet f a b → RealJet g c d →
    RealJet (λ n → f n *C g n) (a * c) (b * c + a * d)
  mul {f} {g} {a} {b} {c} {d} j k = J.congJet (λ _ → C.≈C-refl _)
    (Real.realMul a c)
    (complexTrans (A.addCCongruent (Real.realMul b c) (Real.realMul a d))
      (Real.realAdd (b * c) (a * d)))
    (J.mulJet cv j k)

  sub : ∀ {f g a b c d} → RealJet f a b → RealJet g c d →
    RealJet (λ n → f n -C g n) (a - c) (b - d)
  sub {f} {g} {a} {b} {c} {d} j k = J.congJet (λ _ → C.≈C-refl _)
    (realSub a c) (realSub b d) (J.subJet j k)

  module Branches (X Xp Xm T : Nat → BishopComplex) (a b : ℝ)
    (jx : RealJet X a b)
    (jp : J.Jet w Xp (Geo.p0 a) (Geo.p1 b))
    (jm : J.Jet w Xm (Geo.m0 a) (Geo.m1 b))
    (tCv : Lim.Conv T (realC (Packet.s3 ⋆))) where

    x n = w n *C X n
    N n = Xp n *C Xm n
    M n = (X n -C Xp n) *C (X n -C Xm n)
    p n = Shift.pComplement (x n)
    s n = Shift.sComplement (x n)
    W n = w n *C T n

    n0 = a * a
    n1 = (((- (+ 81)) / 41) ⋆) * a * b
    m0 = Disk.c * (a * a)
    m1 = Disk.m * a * b
    p0 = Packet.p2 ⋆
    p1 = (Packet.p3 ⋆) * a
    s0 = Packet.s2 ⋆
    s1 = (Packet.s3 ⋆) * a
    t1 = Packet.s3 ⋆

    Njet : RealJet N n0 n1
    Njet = J.congJet (λ _ → C.≈C-refl _) (Geo.N0 a) (Geo.N1 a b)
      (J.mulJet cv jp jm)

    Mjet : RealJet M m0 m1
    Mjet = J.congJet (λ _ → C.≈C-refl _) (Geo.M0 a b) (Geo.M1 a b)
      (J.mulJet cv (J.subJet jx jp) (J.subJet jx jm))

    xjet : RealJet x R.0ℝ a
    xjet = J.coordinateMul (J.continuous cv jx)

    Pjet : RealJet p p0 p1
    Pjet = J.congJet (λ _ → C.≈C-refl _) (C.≈C-refl _)
      (complexTrans (Real.realMul a (Packet.p3 ⋆)) (P.*-comm a (Packet.p3 ⋆) , P.≃-refl))
      (J.ascJet (Packet.drop 2 Packet.Pshift) cv xjet)

    Sjet : RealJet s s0 s1
    Sjet = J.congJet (λ _ → C.≈C-refl _) (C.≈C-refl _)
      (complexTrans (Real.realMul a (Packet.s3 ⋆)) (P.*-comm a (Packet.s3 ⋆) , P.≃-refl))
      (J.ascJet (Packet.drop 2 Packet.Sshift) cv xjet)

    Wjet : RealJet W R.0ℝ t1
    Wjet = J.coordinateMul tCv

    lhs n = (N n *C p n -C M n *C s n) *C powC (X n) 2
    rhs n = (N n *C M n) *C (X n *C W n)

    left1 = ((n1 * p0 + n0 * p1) - (m1 * s0 + m0 * s1)) * (a * a)
      + (n0 * p0 - m0 * s0) * (b * a + a * b)
    right1 = (n1 * m0 + n0 * m1) * (a * R.0ℝ)
      + (n0 * m0) * (b * R.0ℝ + a * t1)

    Ljet : RealJet lhs ((n0 * p0 - m0 * s0) * (a * a)) left1
    Ljet = J.congJet (λ n → A.mulCCongruent (C.≈C-refl _) (Power.powTwo (X n)))
      (C.≈C-refl _) (C.≈C-refl _)
      (mul (sub (mul Njet Pjet) (mul Mjet Sjet)) (mul jx jx))

    Rjet : RealJet rhs ((n0 * m0) * (a * R.0ℝ)) right1
    Rjet = mul (mul Njet Mjet) (mul jx Wjet)

    -- This is precisely the ORIGINAL literalResidual, including the
    -- zero-mode term and the sign of the reciprocal multiplier trace.
    coefficientRead : (left1 - right1) ≃ Disk.literalResidual a b (Packet.s2 ⋆) (Packet.s3 ⋆) (Packet.p2 ⋆) (Packet.p3 ⋆)
    coefficientRead = let open P.ℝ-Solver in solve 6
      (λ a b s t u v → ((((((((Κ (- (+ 81) / 41) ⊗ a) ⊗ b) ⊗ u) ⊕ ((a ⊗ a) ⊗ (v ⊗ a))) ⊖ ((((Κ (+ 163 / 1681) ⊗ a) ⊗ b) ⊗ s) ⊕ ((Κ (+ 163 / 41) ⊗ (a ⊗ a)) ⊗ (t ⊗ a)))) ⊗ (a ⊗ a)) ⊕ ((((a ⊗ a) ⊗ u) ⊖ ((Κ (+ 163 / 41) ⊗ (a ⊗ a)) ⊗ s)) ⊗ ((b ⊗ a) ⊕ (a ⊗ b)))) ⊖ ((((((Κ (- (+ 81) / 41) ⊗ a) ⊗ b) ⊗ (Κ (+ 163 / 41) ⊗ (a ⊗ a))) ⊕ ((a ⊗ a) ⊗ ((Κ (+ 163 / 1681) ⊗ a) ⊗ b))) ⊗ (a ⊗ Κ 0ℚᵘ)) ⊕ (((a ⊗ a) ⊗ (Κ (+ 163 / 41) ⊗ (a ⊗ a))) ⊗ ((b ⊗ Κ 0ℚᵘ) ⊕ (a ⊗ t))))) ⊜ ((((((((Κ (- (+ 81) / 41) ⊗ a) ⊗ b) ⊗ u) ⊕ (((a ⊗ a) ⊗ v) ⊗ a)) ⊖ ((((Κ (+ 163 / 1681) ⊗ a) ⊗ b) ⊗ s) ⊕ (((Κ (+ 163 / 41) ⊗ (a ⊗ a)) ⊗ t) ⊗ a))) ⊗ (a ⊗ a)) ⊕ ((((a ⊗ a) ⊗ u) ⊖ ((Κ (+ 163 / 41) ⊗ (a ⊗ a)) ⊗ s)) ⊗ ((Κ (+ 2 / 1) ⊗ a) ⊗ b))) ⊖ ((((a ⊗ a) ⊗ (Κ (+ 163 / 41) ⊗ (a ⊗ a))) ⊗ a) ⊗ t)))
      P.≃-refl a b (Packet.s2 ⋆) (Packet.s3 ⋆) (Packet.p2 ⋆) (Packet.p3 ⋆)

    residual : (∀ n → lhs n ≈C rhs n) →
      Disk.literalResidual a b (Packet.s2 ⋆) (Packet.s3 ⋆) (Packet.p2 ⋆) (Packet.p3 ⋆) ≃ R.0ℝ
    residual eq = P.≃-trans (P.≃-symm coefficientRead)
      (P.≃-trans (P.+-cong (proj₁ (J.unique nz cv eq Ljet Rjet)) P.≃-refl)
        (P.+-inverseʳ right1))

module At (inputs : Round11.BishopCutset) where
  module H = Cross.At inputs

  a = Disk.A CM.p QJ.a
  b = Disk.diskB CM.p QJ.a QJ.b

  -- On an actual nonzero real-disk ray, the three normalized branches
  -- and the single finite slope limit are the exact remaining inputs.
  -- The global residual identities are the same as C1/C2, not a
  -- different cross or polynomial.
  rayFromActual :
    (w : Nat → BishopComplex) (p : Nat → U.BishopUpperHalfPlanePoint)
    (X Xp Xm : Nat → BishopComplex) →
    (cv : Lim.Conv w A.zeroC) → (nz : ∀ n → Rec.BishopComplexNonzero (w n)) →
    (∀ n → H.x (p n) ≈C (w n *C X n)) →
    (∀ n → H.xp (p n) ≈C (w n *C Xp n)) →
    (∀ n → H.xm (p n) ≈C (w n *C Xm n)) →
    J.Jet w X (realC a) (realC b) →
    J.Jet w Xp (Geo.p0 a) (Geo.p1 b) →
    J.Jet w Xm (Geo.m0 a) (Geo.m1 b) →
    Lim.Conv (λ n → Cross.slope (H.c (p n)) (H.x (p n))) (realC (Packet.s3 ⋆)) →
    (∀ n → H.R.d (p n) ≈C A.zeroC) → (∀ n → H.R.s (p n) ≈C A.zeroC) →
    Terminal.OriginalRayResidual
  rayFromActual w p X Xp Xm cv nz hx hp hm jx jp jm ht hd hs =
    let module V = Along w cv nz
        module B = V.Branches X Xp Xm (λ n → Cross.slope (H.c (p n)) (H.x (p n))) a b jx jp jm ht
    in B.residual (λ n →
      complexTrans
        (A.mulCCongruent (A.subCCongruent
          (A.mulCCongruent (C.≈C-refl _) (ascCong (complexSym (hx n)) (Packet.drop 2 Packet.Pshift)))
          (A.mulCCongruent (C.≈C-refl _) (ascCong (complexSym (hx n)) (Packet.drop 2 Packet.Sshift))))
          (C.≈C-refl _))
        (H.normalizedCross (p n) (w n) (X n) (Xp n) (Xm n) (nz n) (hx n) (hp n) (hm n) (hd n) (hs n)))
    where
    ascCong : ∀ {z v} → z ≈C v → ∀ cs → Shift.asc z cs ≈C Shift.asc v cs
    ascCong h [] = C.≈C-refl _
    ascCong h (c ∷ cs) = A.addCCongruent (C.≈C-refl _) (A.mulCCongruent h (ascCong h cs))
