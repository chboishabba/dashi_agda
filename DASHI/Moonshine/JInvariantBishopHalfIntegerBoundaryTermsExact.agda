module DASHI.Moonshine.JInvariantBishopHalfIntegerBoundaryTermsExact where

-- Source-written. Actual signed half-integer denominator, including the
-- zero-index term j=0. No reciprocal at a pole, even on the boundary.
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_+_ to _+N_)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Integer.Base using (+_; -[1+_])
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopPositiveCrossReciprocalUpperExact as Cross
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as Bounds
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopSquareNonnegativeExact as Sq
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Foundations.BishopNatEmbeddingMonotoneExact as Mono
import DASHI.Foundations.BishopNatRealPositiveExact as Pos
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as BaselRead
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as IS
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowExact as Chart
import DASHI.Moonshine.JInvariantBishopCenteredDyadicSummandLimitExact as Leaf
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as LR
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowClosureExact as Close
import DASHI.Moonshine.JInvariantBishopDyadicRowTailMajorantExact as Tail
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
open C using (BishopComplex; _≈C_)
open A using (_*C_; _+C_; powC)
open Comp using (complexTrans; complexSym)
open Completion using (original-bishop-pointwise-complex-converges)

half = D.half
four : ℝ
four = (+ 4 / 1) ⋆
fourNN : R.NonNegative four
fourNN = Bounds.ratNN (+ 4 / 1) (QP.nonNegative⁻¹ (+ 4 / 1))

point : Nat → U.BishopUpperHalfPlanePoint
point n = U.bishop-upper-half-plane-point (C.complex half (Chart.h n)) (Leaf.hPositive n)

mag : Nat → ℝ
mag k = N.natReal k + half
J : Nat → ℝ
J k = N.natReal (suc k)
natNN : ∀ k → R.NonNegative (N.natReal k)
natNN k = P.0≤x⇒nonNegx (Mono.natRealMonotone {m = zero} {n = k} z≤n)

halfJBelow : ∀ k → half * J k ≤ mag k
halfJBelow k =
  let a = N.natReal k
      halfA = half * a
      halfANN = P.nonNegx,y⇒nonNegx*y Leaf.halfNN (natNN k)
      lo = Tail.plusNN halfANN
  in P.≤-respˡ-≃
    (P.≃-trans (P.*-congˡ (N.natRealSuccessor k))
      (let open P.ℝ-Solver in solve 1
        (λ a → Κ (+ 1 / 2) ⊗ (a ⊕ Κ 1ℚᵘ) ⊜ Κ (+ 1 / 2) ⊗ a ⊕ Κ (+ 1 / 2))
        P.≃-refl a))
    (P.≤-respʳ-≃
      (let open P.ℝ-Solver in solve 1
        (λ a → (Κ (+ 1 / 2) ⊗ a ⊕ Κ (+ 1 / 2)) ⊕ Κ (+ 1 / 2) ⊗ a
          ⊜ a ⊕ Κ (+ 1 / 2)) P.≃-refl a) lo)

magPositive : ∀ k → R.0ℝ < mag k
magPositive k = P.<-≤-trans D.halfPositive
  (P.≤-respʳ-≃ (P.+-comm half (N.natReal k)) (Tail.plusNN (natNN k)))

data Side : Set where
  plus minus : Side

signed : Side → ℝ → ℝ
signed plus x = x
signed minus x = R.- x

z : Side → Nat → ℝ → BishopComplex
z side k y = C.complex (signed side (mag k)) y

guard : ∀ side k y → Rec.BishopComplexNonzero (z side k y)
guard plus k y = NZ.complexNonzeroFromRealApart (inj₂ (magPositive k))
guard minus k y = NZ.complexNonzeroFromRealApart (inj₁ (NZ.positiveNegatesNegative (magPositive k)))

w : Side → Nat → ℝ → BishopComplex
w side k y = Rec.reciprocalC (z side k y) (guard side k y)

signedSquare : ∀ side a → Norm.square (signed side a) ≃ Norm.square a
signedSquare plus a = P.≃-refl
signedSquare minus a = let open P.ℝ-Solver in solve 1
  (λ a → (⊝ a) ⊗ (⊝ a) ⊜ a ⊗ a) P.≃-refl a

lower : ∀ side k y → Norm.square (J k) ≤ four * Norm.normSqC (z side k y)
lower side k y =
  let a = mag k
      j = J k
      nn = P.nonNegx,y⇒nonNegx*y Leaf.halfNN (P.pos⇒nonNeg (P.0<x⇒posx (Pos.natRealSuccessorStrictlyPositive k)))
      lo = Tail.squareMono nn (halfJBelow k)
      raw = P.*-monoˡ-≤-nonNeg lo fourNN
      lo2 = P.≤-trans raw (P.*-monoˡ-≤-nonNeg (Tail.plusNN (Sq.bishopSquareNonnegative y)) fourNN)
  in P.≤-respˡ-≃
    (let open P.ℝ-Solver in solve 1
      (λ j → j ⊗ j ⊜ Κ (+ 4 / 1) ⊗ ((Κ (+ 1 / 2) ⊗ j) ⊗ (Κ (+ 1 / 2) ⊗ j))) P.≃-refl j)
    (P.≤-respʳ-≃ (P.*-congˡ (P.+-cong (P.≃-symm (signedSquare side a)) P.≃-refl)) lo2)

baselCross : ∀ k → Basel.baselTerm k * Norm.square (J k) ≃ R.1ℝ
baselCross k = P.≃-trans
  (P.*-congʳ (P.≃-symm (BaselRead.natRealSuccessorInverseSquareIsBaselTerm k)))
  (IS.inverseSquareCancelsSquare (J k) (Cross.positiveNonzero (Pos.natRealSuccessorStrictlyPositive k)))

normBound : ∀ side k y → Norm.normSqC (w side k y) ≤ four * Basel.baselTerm k
normBound side k y =
  let d = Norm.normSqC (z side k y)
      i = Norm.normSqC (w side k y)
      b = Basel.baselTerm k
      product = Inv.normInverse (z side k y) (w side k y)
        (Rec.multiplyReciprocal (z side k y) (guard side k y))
      raw = P.*-monoʳ-≤-nonNeg
        (P.*-monoʳ-≤-nonNeg (lower side k y) (Inv.normNN (w side k y))) (Basel.baselTermNonnegative k)
      l = P.≃-trans
        (let open P.ℝ-Solver in solve 3
          (λ j i b → ((j ⊗ j) ⊗ i) ⊗ b ⊜ (b ⊗ (j ⊗ j)) ⊗ i)
          P.≃-refl (J k) i b)
        (P.≃-trans (P.*-congʳ (baselCross k)) (P.*-identityˡ i))
      r = P.≃-trans
        (let open P.ℝ-Solver in solve 3
          (λ d i b → (Κ (+ 4 / 1) ⊗ d) ⊗ i ⊗ b ⊜ (Κ (+ 4 / 1) ⊗ (d ⊗ i)) ⊗ b)
          P.≃-refl d i b)
        (P.≃-trans (P.*-congʳ (P.*-congˡ product)) (P.*-congʳ (P.*-identityʳ four)))
  in P.≤-respʳ-≃ r (P.≤-respˡ-≃ (P.≃-symm l) raw)

-- Uniform in y, including y=0. Bound even powers by a fixed
-- coefficient times the original Basel term.
baselOne : ∀ k → Basel.baselTerm k ≤ R.1ℝ
baselOne k =
  let r = Basel.embed (BaselRead.reciprocalNatRational k)
      e = P.≃-trans (P.≃-symm (P.⋆-distrib-*
        (BaselRead.reciprocalNatRational k) (BaselRead.reciprocalNatRational k)))
        (P.⋆-cong (BaselRead.reciprocalNatSquareIsBaselRational k))
  in P.≤-respˡ-≃ (P.≃-symm e)
    (P.≤-respʳ-≃ (P.*-identityˡ R.1ℝ)
      (Tail.squareMono (BaselRead.reciprocalNonnegative k) (BaselRead.reciprocalAtMostOne k)))

powBound : ∀ side k y n → Norm.normSqC (powC (w side k y) n) ≤ R.pow (four * Basel.baselTerm k) n
powBound side k y n = P.≤-respˡ-≃ (Norm.normSqPower (w side k y) n)
  (Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ n (normBound side k y) (Inv.normNN (w side k y)))

powerMajorant : ∀ side k y n → Tail.Box (powC (w side k y) (n +N n)) (R.pow (four * Basel.baselTerm k) n)
powerMajorant side k y n = Tail.boxFromNorm _ _
  (Seq.nonNegx⇒nonNegxⁿ n (P.nonNegx,y⇒nonNegx*y fourNN (Basel.baselTermNonnegative k)))
  (P.≤-respʳ-≃ (P.≃-symm (P.xⁿxᵐ≃xⁿ⁺ᵐ (four * Basel.baselTerm k) n n)) (powBound side k y (n +N n)))

majorant4 : ∀ side k y → Tail.Box (powC (w side k y) 4) (((+ 16 / 1) ⋆) * Basel.baselTerm k)
majorant4 side k y =
  let b = Basel.baselTerm k
      bn = Basel.baselTermNonnegative k
      b2 = P.≤-respʳ-≃ (P.*-identityʳ b) (P.*-monoˡ-≤-nonNeg (baselOne k) bn)
      raw = P.*-monoˡ-≤-nonNeg b2 (Bounds.ratNN (+ 16 / 1) (QP.nonNegative⁻¹ (+ 16 / 1)))
      le = P.≤-respˡ-≃
        (let open P.ℝ-Solver in solve 1
          (λ b → (Κ 1ℚᵘ ⊗ (Κ (+ 4 / 1) ⊗ b)) ⊗ (Κ (+ 4 / 1) ⊗ b)
            ⊜ Κ (+ 16 / 1) ⊗ (b ⊗ b)) P.≃-refl b) raw
      r , i = powerMajorant side k y 2
  in P.≤-trans r le , P.≤-trans i le

majorant6 : ∀ side k y → Tail.Box (powC (w side k y) 6) (((+ 64 / 1) ⋆) * Basel.baselTerm k)
majorant6 side k y =
  let b = Basel.baselTerm k
      bn = Basel.baselTermNonnegative k
      b2 = P.≤-respʳ-≃ (P.*-identityʳ b) (P.*-monoˡ-≤-nonNeg (baselOne k) bn)
      b3 = P.≤-trans (P.*-monoʳ-≤-nonNeg b2 bn) b2
      raw = P.*-monoˡ-≤-nonNeg b3 (Bounds.ratNN (+ 64 / 1) (QP.nonNegative⁻¹ (+ 64 / 1)))
      le = P.≤-respˡ-≃
        (let open P.ℝ-Solver in solve 1
          (λ b → ((Κ 1ℚᵘ ⊗ (Κ (+ 4 / 1) ⊗ b)) ⊗ (Κ (+ 4 / 1) ⊗ b)) ⊗ (Κ (+ 4 / 1) ⊗ b)
            ⊜ Κ (+ 64 / 1) ⊗ ((b ⊗ b) ⊗ b)) P.≃-refl b) raw
      r , i = powerMajorant side k y 3
  in P.≤-trans r le , P.≤-trans i le

fixed : ∀ side k → Lim.Conv (λ n → w side k (Chart.h n)) (w side k R.0ℝ)
fixed side k = Inv.inverseLimit (guard side k R.0ℝ)
  (original-bishop-pointwise-complex-converges (Power.constantConverges (signed side (mag k))) Leaf.hNull)
  (λ n → Rec.multiplyReciprocal (z side k (Chart.h n)) (guard side k (Chart.h n)))

powerConv : ∀ {f : Nat → BishopComplex} {v} → Lim.Conv f v → ∀ k → Lim.Conv (λ n → powC (f n) k) (powC v k)
powerConv cv zero = Lim.constantC A.oneC
powerConv cv (suc k) = Inv.mulConv cv (powerConv cv k)

-- The actual original kernel terms at (1,+k) and (1,-k-1).
denomPlus : ∀ n k → LR.denom (point n) (+ k) ≈C z plus k (Chart.h n)
denomPlus n k = complexTrans (LR.denomRead (point n) (+ k)) (P.+-comm half (N.natReal k) , P.≃-refl)

denomMinus : ∀ n k → LR.denom (point n) (-[1+ k ]) ≈C z minus k (Chart.h n)
denomMinus n k = complexTrans (LR.denomRead (point n) (-[1+ k ]))
  (P.≃-trans (P.+-cong P.≃-refl (P.-‿cong (N.natRealSuccessor k)))
    (let open P.ℝ-Solver in solve 1
      (λ k → Κ (+ 1 / 2) ⊕ (⊝ (k ⊕ Κ 1ℚᵘ)) ⊜ ⊝ (k ⊕ Κ (+ 1 / 2))) P.≃-refl (N.natReal k)) , P.≃-refl)

readPlus : ∀ n k → LR.W (point n) (+ k) ≈C w plus k (Chart.h n)
readPlus n k = G.reciprocalCong _ _ _ _ (denomPlus n k)

readMinus : ∀ n k → LR.W (point n) (-[1+ k ]) ≈C w minus k (Chart.h n)
readMinus n k = G.reciprocalCong _ _ _ _ (denomMinus n k)
