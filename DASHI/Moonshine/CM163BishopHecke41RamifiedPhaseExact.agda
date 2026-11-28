module DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact where

-- SOURCE-WRITTEN, kernel pending. Actual Machin exp phase, not an
-- abstract choice of a root. All chart identities live on the original
-- Bishop upper half-plane and preserve the signed finite shifts.
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Agda.Builtin.Nat as Nat
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₂)
import Real as R
open R using (ℝ; _⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaNonvanishingExact as Global
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.CM163BishopHecke41AnalyticChartsExact as Chart
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; scaleC; powC)
open Comp using (complexTrans; complexSym)

scaleZero : ∀ z → scaleC R.0ℝ z ≈C A.zeroC
scaleZero (C.complex x y) = P.*-zeroˡ x , P.*-zeroˡ y

scaleOne : ∀ z → scaleC R.1ℝ z ≈C z
scaleOne (C.complex x y) = P.*-identityˡ x , P.*-identityˡ y

scaleSuccessor : ∀ n z →
  (z +C scaleC (NR.natReal n) z) ≈C scaleC (NR.natReal (suc n)) z
scaleSuccessor n (C.complex x y) =
  (P.≃-trans
    (let open P.ℝ-Solver in solve 2 (λ n x → x ⊕ n ⊗ x ⊜ (n ⊕ Κ 1ℚᵘ) ⊗ x)
      P.≃-refl (NR.natReal n) x)
    (P.*-congʳ (P.≃-symm (NR.natRealSuccessor n)))) ,
  (P.≃-trans
    (let open P.ℝ-Solver in solve 2 (λ n y → y ⊕ n ⊗ y ⊜ (n ⊕ Κ 1ℚᵘ) ⊗ y)
      P.≃-refl (NR.natReal n) y)
    (P.*-congʳ (P.≃-symm (NR.natRealSuccessor n))))

powPow : ∀ z a b → powC (powC z a) b ≈C powC z (b Nat.* a)
powPow z a zero = C.≈C-refl _
powPow z a (suc b) = complexTrans (A.mulCCongruent (C.≈C-refl _) (powPow z a b))
  (Power.powAdd z a (b Nat.* a))

negativeSquare : (Gen.minusOneC *C Gen.minusOneC) ≈C A.oneC
negativeSquare =
  (let open P.ℝ-Solver in solve 0
    ((⊝ Κ 1ℚᵘ) ⊗ (⊝ Κ 1ℚᵘ) ⊖ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊜ Κ 1ℚᵘ) P.≃-refl) ,
  (let open P.ℝ-Solver in solve 0
    ((⊝ Κ 1ℚᵘ) ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ (⊝ Κ 1ℚᵘ) ⊜ Κ 0ℚᵘ) P.≃-refl)

module At (inputs : Round11.BishopCutset) where
  module Ph = Phase.At inputs
  module G = Global.At inputs

  expCong : ∀ {a b} → a ≈C b → Ph.expS a ≈C Ph.expS b
  expCong = Weld.originalBishopExpOnSeriesCongruent Ph.T

  piI : BishopComplex
  piI = C.complex R.0ℝ Phase.pi

  piExp : Ph.expS piI ≈C Gen.minusOneC
  piExp = Ph.shiftPhase Phase.positive

  piNZ : Rec.BishopComplexNonzero (Ph.expS piI)
  piNZ = Phase.guardCong (complexSym piExp)
    (Global.inverseGivesGuard Gen.minusOneC Gen.minusOneC negativeSquare)

  expZero : Ph.expS A.zeroC ≈C A.oneC
  expZero = J.cancelLeft (Ph.expS piI) _ _ piNZ
    (complexTrans (complexSym (Ph.expAddS piI A.zeroC))
      (complexTrans (expCong (L.complexAddRightIdentity piI))
        (complexSym (L.complexMultiplyRightIdentity (Ph.expS piI)))))

  expPow : ∀ z n → powC (Ph.expS z) n ≈C Ph.expS (scaleC (NR.natReal n) z)
  expPow z zero = complexTrans (complexSym expZero) (expCong (complexSym (scaleZero z)))
  expPow z (suc n) = complexTrans
    (A.mulCCongruent (C.≈C-refl _) (expPow z n))
    (complexTrans (complexSym (Ph.expAddS z (scaleC (NR.natReal n) z)))
      (expCong (scaleSuccessor n z)))

  angle : BishopComplex
  angle = C.complex R.0ℝ (R._*_ (R._*_ Phase.two Phase.pi) Chart.inv41)

  zeta : BishopComplex
  zeta = Ph.expS angle

  rotation : Nat → BishopComplex
  rotation k = C.complex R.0ℝ (R._*_ (R._*_ Phase.two Phase.pi)
    (R._*_ Chart.inv41 (NR.natReal k)))

  rotationRead : ∀ k → scaleC (NR.natReal k) angle ≈C rotation k
  rotationRead k =
    P.*-zeroʳ _ ,
    (let open P.ℝ-Solver in solve 2
      (λ p k → k ⊗ ((Κ (+ 2 / 1) ⊗ p) ⊗ Κ (+ 1 / 41))
        ⊜ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ k))
      P.≃-refl Phase.pi (NR.natReal k))

  phaseRead : ∀ k → powC zeta k ≈C Ph.expS (rotation k)
  phaseRead k = complexTrans (expPow angle k) (expCong (rotationRead k))

  fortyOneRotation : rotation 41 ≈C (piI +C piI)
  fortyOneRotation =
    P.≃-symm (P.+-identityʳ R.0ℝ) ,
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 41 / 1)) ⊜ p ⊕ p)
      P.≃-refl Phase.pi)

  phaseOrder : powC zeta 41 ≈C A.oneC
  phaseOrder = complexTrans (phaseRead 41)
    (complexTrans (expCong fortyOneRotation)
      (complexTrans (Ph.expAddS piI piI)
        (complexTrans (A.mulCCongruent piExp piExp) negativeSquare)))

  zetaNZ : Rec.BishopComplexNonzero zeta
  zetaNZ = Global.inverseGivesGuard zeta (powC zeta 40) phaseOrder

  t : U.BishopUpperHalfPlanePoint → BishopComplex
  t p = Ph.q (Chart.finitePoint zero p)

  tNZ : ∀ p → Rec.BishopComplexNonzero (t p)
  tNZ p = G.qNonzero (Chart.finitePoint zero p)

  finiteExponent : ∀ k p → Ph.exponent (Chart.finitePoint k p) ≈C
    (rotation k +C Ph.exponent (Chart.finitePoint zero p))
  finiteExponent k p =
    P.≃-symm (P.+-identityˡ (C.re (Ph.exponent (Chart.finitePoint zero p)))) ,
    (let open P.ℝ-Solver in solve 3
      (λ b a k →
        (Κ (+ 2 / 1) ⊗ b) ⊗ (Κ (+ 1 / 41) ⊗ (a ⊕ k))
        ⊜ (Κ (+ 2 / 1) ⊗ b) ⊗ (Κ (+ 1 / 41) ⊗ k) ⊕
          (Κ (+ 2 / 1) ⊗ b) ⊗ (Κ (+ 1 / 41) ⊗ (a ⊕ Κ 0ℚᵘ)))
      P.≃-refl Phase.pi (C.re (U.tau p)) (NR.natReal k))

  finiteQ : ∀ k p → Ph.q (Chart.finitePoint k p) ≈C (powC zeta k *C t p)
  finiteQ k p = complexTrans (expCong (finiteExponent k p))
    (complexTrans (Ph.expAddS (rotation k) (Ph.exponent (Chart.finitePoint zero p)))
      (A.mulCCongruent (complexSym (phaseRead k)) (C.≈C-refl _)))

  tExponent : ∀ p → scaleC (NR.natReal 41) (Ph.exponent (Chart.finitePoint zero p)) ≈C Ph.exponent p
  tExponent p =
    (let open P.ℝ-Solver in solve 2
      (λ b y → Κ (+ 41 / 1) ⊗ (⊝ ((Κ (+ 2 / 1) ⊗ b) ⊗ (Κ (+ 1 / 41) ⊗ y)))
        ⊜ ⊝ ((Κ (+ 2 / 1) ⊗ b) ⊗ y))
      P.≃-refl Phase.pi (C.im (U.tau p))) ,
    (let open P.ℝ-Solver in solve 2
      (λ b x → Κ (+ 41 / 1) ⊗ ((Κ (+ 2 / 1) ⊗ b) ⊗ (Κ (+ 1 / 41) ⊗ (x ⊕ Κ 0ℚᵘ)))
        ⊜ (Κ (+ 2 / 1) ⊗ b) ⊗ x)
      P.≃-refl Phase.pi (C.re (U.tau p)))

  tPower : ∀ p → powC (t p) 41 ≈C Ph.q p
  tPower p = complexTrans (expPow (Ph.exponent (Chart.finitePoint zero p)) 41)
    (expCong (tExponent p))

  infinityExponent : ∀ p → scaleC (NR.natReal 41) (Ph.exponent p) ≈C Ph.exponent (Chart.infinityPoint p)
  infinityExponent p =
    (let open P.ℝ-Solver in solve 2
      (λ b y → Κ (+ 41 / 1) ⊗ (⊝ ((Κ (+ 2 / 1) ⊗ b) ⊗ y))
        ⊜ ⊝ ((Κ (+ 2 / 1) ⊗ b) ⊗ (Κ (+ 41 / 1) ⊗ y)))
      P.≃-refl Phase.pi (C.im (U.tau p))) ,
    (let open P.ℝ-Solver in solve 2
      (λ b x → Κ (+ 41 / 1) ⊗ ((Κ (+ 2 / 1) ⊗ b) ⊗ x)
        ⊜ (Κ (+ 2 / 1) ⊗ b) ⊗ (Κ (+ 41 / 1) ⊗ x))
      P.≃-refl Phase.pi (C.re (U.tau p)))

  infinityQ : ∀ p → Ph.q (Chart.infinityPoint p) ≈C powC (Ph.q p) 41
  infinityQ p = complexSym (complexTrans (expPow (Ph.exponent p) 41) (expCong (infinityExponent p)))

  finitePower : ∀ k p → powC (Ph.q (Chart.finitePoint k p)) 41 ≈C Ph.q p
  finitePower k p = complexTrans (A.powCCongruent (finiteQ k p) 41)
    (complexTrans (Gen.powProduct (powC zeta k) (t p) 41)
      (complexTrans (A.mulCCongruent
        (complexTrans (powPow zeta k 41)
          (complexTrans (powComm k)
            (complexTrans (complexSym (powPow zeta 41 k))
              (complexTrans (A.powCCongruent phaseOrder k) (Power.powUnit k)))))
        (tPower p)) (L.complexMultiplyLeftIdentity _)))
    where
    powComm : ∀ k → powC zeta (41 Nat.* k) ≈C powC zeta (k Nat.* 41)
    powComm k = P.≃-refl₂ (cong (λ n → C.re (powC zeta n)) (NP.*-comm 41 k)) ,
      P.≃-refl₂ (cong (λ n → C.im (powC zeta n)) (NP.*-comm 41 k))
