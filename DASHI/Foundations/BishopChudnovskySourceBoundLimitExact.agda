module DASHI.Foundations.BishopChudnovskySourceBoundLimitExact where

-- Source-written; not kernel checked. This consumes the literal computed
-- interval and an all-index rational order proof. It does not postulate
-- that the certificate exists. The analytic identity/finite source
-- correspondence still must produce the certificate.

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised as Q using
  (ℚᵘ; _*_; _-_; _≤_; ∣_∣)
import Real as R
import RealProperties as RP
import Sequence as S
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as MStage
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as B
import DASHI.Analysis.BishopPolynomialSuccessorFactorLimitExact as C
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as V

-- Literal rational expression 4*(1/(k+1)); retain source normalization.
errorQ : Nat → ℚᵘ
errorQ k = M.four Q.* B.reciprocalPositiveNat k

errorR : Nat → R.ℝ
errorR k = R._⋆ (errorQ k)

errorConvergesZero : S._ConvergesTo_ errorR R.0ℝ
errorConvergesZero =
  S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc k) →
      RP.≃-symm
        (RP.⋆-distrib-* M.four (B.reciprocalPositiveNat (suc k)))})
    (R.0ℝ ,
      S.xₙ→x∧x≃y⇒xₙ→y
        (S.xₙyₙ→x₀y₀
          (R._⋆ M.four , C.constantSequenceConverges (R._⋆ M.four))
          (R.0ℝ , B.reciprocalSequenceConvergesZero))
        (RP.*-zeroʳ (R._⋆ M.four)))

-- There is NO candidate-sequence field: the midpoint is a projection
-- of the actual reference evaluator's returned interval.
record StageCertificate (k : Nat) : Set where
  field
    window : CH.Interval
    computed : CH.intervalAt k ≡ just window
    rationalError :
      Q.∣ CH.midpoint window Q.- MStage.qMachinStage k ∣ Q.≤ errorQ k
open StageCertificate

candidate : (∀ k → StageCertificate k) → Nat → ℚᵘ
candidate cert k = CH.midpoint (window (cert k))

-- The exact rational inequality is transported using the pinned vendor
-- subtraction and absolute-value embedding laws, not a new real axiom.
embeddedError :
  (cert : ∀ k → StageCertificate k) → ∀ k →
  R._≤_
    (R.∣ R._-_ (R._⋆ (candidate cert k))
                 (R._⋆ (MStage.qMachinStage k)) ∣)
    (R.∣ errorR k ∣)
embeddedError cert k =
  RP.≤-trans
    (RP.≤-respˡ-≃
      (RP.≃-trans
        (RP.∣p∣⋆≃∣p⋆∣ (candidate cert k Q.- MStage.qMachinStage k))
        (RP.∣-∣-cong
          (RP.⋆-distrib-to-p⋆-q⋆ (candidate cert k) (MStage.qMachinStage k))))
      (RP.p≤q⇒p⋆≤q⋆
        (Q.∣ candidate cert k Q.- MStage.qMachinStage k ∣)
        (errorQ k) (rationalError (cert k))))
    RP.x≤∣x∣

literalMidpointsConvergeToOriginalMachin :
  (cert : ∀ k → StageCertificate k) →
  S._ConvergesTo_ (λ k → R._⋆ (candidate cert k)) M.bishopMachinPi
literalMidpointsConvergeToOriginalMachin cert =
  V.vanishingDifferenceConvergence
    MStage.rationalMachinStagesConvergeToOriginalMachinPi
    errorConvergesZero
    (embeddedError cert)

literalMidpointLimitIsOriginalMachin :
  (cert : ∀ k → StageCertificate k) → ∀ {limit : R.ℝ} →
  S._ConvergesTo_ (λ k → R._⋆ (candidate cert k)) limit →
  R._≃_ limit M.bishopMachinPi
literalMidpointLimitIsOriginalMachin cert converges =
  S.uniqueness-of-limits converges
    (literalMidpointsConvergeToOriginalMachin cert)
