module DASHI.Moonshine.JInvariantBishopEvenZetaRHSourceWeldExact where

-- Source-written, kernel pending. Reuse the RH original log inverse,
-- actual source exponential and actual above-two Dirichlet completion.
-- Neither the original opaque ZetaHalfPlaneLayer nor RH is inferred.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _*_; _⋆)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopRiemannOriginalZetaAboveTwoExact as RH
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopK04dNatLogFromOriginalGapExact as Log
import DASHI.Analysis.BishopOriginalNegativeLogTerminalFromMeshExact as Mesh
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Moonshine.JInvariantBishopEvenZetaNormalizationExact as Z
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11

L = Terms.sourceCanonicalNatLogCandidate
logInverse = Log.sourceCanonicalNatLogAllIndicesExpInverse Mesh.originalBishopNegativeLogExponentialGap

-- The native repeated negative log is exactly the actual real
-- exponential argument, for every natural exponent.
logRead : ∀ n w → Terms.sourceNegativeLogSum L n w ≃ (R.- (N.natReal w)) * L n
logRead n zero =
  let open P.ℝ-Solver in solve 1 (λ a → Κ 0ℚᵘ ⊜ (⊝ Κ 0ℚᵘ) ⊗ a) P.≃-refl (L n)
logRead n (suc w) =
  P.≃-trans (P.+-cong (logRead n w) P.≃-refl)
    (P.≃-trans
      (let open P.ℝ-Solver in solve 2
        (λ a l → (⊝ a) ⊗ l ⊕ (⊝ l) ⊜ (⊝ (a ⊕ Κ 1ℚᵘ)) ⊗ l)
        P.≃-refl (N.natReal w) (L n))
      (P.*-congʳ (P.-‿cong (P.≃-symm (N.natRealSuccessor w)))))

module At (inputs : Round11.BishopCutset) where
  module Actual = RH.FromOriginalNegativeLog inputs Mesh.originalBishopNegativeLogExponentialGap
  module Norm = Z.At inputs

  point : Nat → BC.BishopComplex
  point w = Terms.sourceRealAxisExponent (N.natReal w)

  realTerm : ∀ w n → BC.re (Actual.sourceTerms (point w) n) ≃ Z.term w n
  realTerm w n = P.≃-trans
    (Terms.sourceRealAxisExponentialRealCoefficient inputs L (N.natReal w) n)
    (P.≃-trans (ExpCong.bishopExpCongruent (P.≃-symm (logRead n w)))
      (Terms.sourceExpNegativeLogSumIsReciprocalPower L n (logInverse n) w))

  imagTerm : ∀ w n → BC.im (Actual.sourceTerms (point w) n) ≃ R.0ℝ
  imagTerm w n = Terms.sourceRealAxisExponentialImaginaryZero inputs L (N.natReal w) n

  realValue : ∀ extra (inside : Actual.sourceRegion (point (suc (suc extra)))) →
    BC.re (Actual.originalZetaAboveTwo (point (suc (suc extra))) inside) ≃ Z.zeta extra
  realValue extra inside =
    let w = suc (suc extra)
        cv = proj₁ (Actual.originalZetaIsSourceDirichletLimit (point w) inside)
        same = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
          (λ {(suc n) → Z.prefixCong _ _ (realTerm w) (suc n)}) (_ , cv)
    in Seq.uniqueness-of-limits same (proj₂ (Z.zetaConvergent extra))

  zeroPrefix : ∀ n → Seq.SeriesOf (λ _ → R.0ℝ) n ≃ R.0ℝ
  zeroPrefix zero = P.≃-refl
  zeroPrefix (suc n) = P.≃-trans (P.+-cong (zeroPrefix n) P.≃-refl) (P.+-identityʳ R.0ℝ)

  imagValue : ∀ w (inside : Actual.sourceRegion (point w)) →
    BC.im (Actual.originalZetaAboveTwo (point w) inside) ≃ R.0ℝ
  imagValue w inside =
    Seq.uniqueness-of-limits
      (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ {(suc n) → P.≃-trans (Z.prefixCong _ _ (imagTerm w) (suc n)) (zeroPrefix (suc n))})
        (_ , proj₂ (Actual.originalZetaIsSourceDirichletLimit (point w) inside)))
      (Power.constantConverges R.0ℝ)

  above4 : Actual.sourceRegion (point 4)
  above4 = P.p<q⇒p⋆<q⋆ (+ 2 / 1) (+ 4 / 1)
    (toWitness {a? = QP._<?_ (+ 2 / 1) (+ 4 / 1)} _)
  above6 : Actual.sourceRegion (point 6)
  above6 = P.p<q⇒p⋆<q⋆ (+ 2 / 1) (+ 6 / 1)
    (toWitness {a? = QP._<?_ (+ 2 / 1) (+ 6 / 1)} _)

  originalZeta4 : BC.re (Actual.originalZetaAboveTwo (point 4) above4) ≃ ((+ 1 / 90) ⋆) * R.pow D.pi 4
  originalZeta4 = P.≃-trans (realValue 2 above4) Norm.zeta4

  originalZeta6 : BC.re (Actual.originalZetaAboveTwo (point 6) above6) ≃ ((+ 1 / 945) ⋆) * R.pow D.pi 6
  originalZeta6 = P.≃-trans (realValue 4 above6) Norm.zeta6

  originalZeta4ImagZero : BC.im (Actual.originalZetaAboveTwo (point 4) above4) ≃ R.0ℝ
  originalZeta4ImagZero = imagValue 4 above4
  originalZeta6ImagZero : BC.im (Actual.originalZetaAboveTwo (point 6) above6) ≃ R.0ℝ
  originalZeta6ImagZero = imagValue 6 above6
