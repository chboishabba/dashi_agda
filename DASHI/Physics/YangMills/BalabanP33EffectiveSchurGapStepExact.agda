module DASHI.Physics.YangMills.BalabanP33EffectiveSchurGapStepExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Volker Bach, Thomas Chen, Jürg Fröhlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
--
-- Formalize the exact signed bookkeeping for one Hessian RG/Feshbach step.
-- The effective coarse quadratic contribution is represented literally as
--
--   retained - SchurFeedback + effectiveRemainder.
--
-- A retained lower floor, an upper bound on the positive Schur feedback, and
-- a signed lower bound on the remainder imply
--
--   retainedFloor - couplingLoss - remainderLoss
--     <= retained - SchurFeedback + effectiveRemainder.
--
-- The coarse--fine coupling loss and the residual effective-action loss remain
-- separate named quantities.  They are combined only when constructing the
-- exact GapTransferStep consumed by the terminal pullback chain:
--
--   coarse <= 2*fine + couplingLoss + remainderLoss
--   ------------------------------------------------
--   (coarse-couplingLoss-remainderLoss)/2 <= fine.
--
-- No physical RG estimate is asserted here.  A later producer must derive the
-- retained floor, coupling bound, norm-rescaling factor and signed remainder
-- estimate from the repository's actual block map and effective action.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33TerminalScaleGapPullbackExact as Pullback

------------------------------------------------------------------------
-- Signed Schur-complement lower bookkeeping.
------------------------------------------------------------------------

effectiveSchurQuadratic : ℚ → ℚ → ℚ → ℚ
effectiveSchurQuadratic retained feedback remainder =
  retained - feedback + remainder

effectiveSchurLower :
  ∀ retainedFloor retained feedback feedbackUpper remainder remainderLoss →
  retainedFloor ≤ retained →
  feedback ≤ feedbackUpper →
  - remainderLoss ≤ remainder →
  retainedFloor - feedbackUpper - remainderLoss
  ≤ effectiveSchurQuadratic retained feedback remainder
effectiveSchurLower
    retainedFloor retained feedback feedbackUpper remainder remainderLoss
    retainedLower feedbackUpperBound remainderLower =
  let
    negativeFeedbackLower : - feedbackUpper ≤ - feedback
    negativeFeedbackLower = ℚP.neg-antimono-≤ feedbackUpperBound

    retainedMinusFeedbackLower :
      retainedFloor + (- feedbackUpper)
      ≤ retained + (- feedback)
    retainedMinusFeedbackLower =
      ℚP.+-mono-≤ retainedLower negativeFeedbackLower

    withRemainderLower :
      (retainedFloor + (- feedbackUpper)) + (- remainderLoss)
      ≤ (retained + (- feedback)) + remainder
    withRemainderLower =
      ℚP.+-mono-≤ retainedMinusFeedbackLower remainderLower
  in
  subst
    (λ lower →
      lower ≤ effectiveSchurQuadratic retained feedback remainder)
    (ℚRing.solve-∀ retainedFloor feedbackUpper remainderLoss)
    (subst
      (λ upper →
        (retainedFloor + (- feedbackUpper)) + (- remainderLoss)
        ≤ upper)
      (ℚRing.solve-∀ retained feedback remainder)
      withRemainderLower)

------------------------------------------------------------------------
-- Keep the two analytic losses separate until the transfer step is formed.
------------------------------------------------------------------------

totalRGStepLoss : ℚ → ℚ → ℚ
totalRGStepLoss couplingLoss remainderLoss =
  couplingLoss + remainderLoss

record SplitRGGapStep
    (fine coarse couplingLoss remainderLoss : ℚ) : Set where
  field
    coarseControlledByFineWithSplitLoss :
      coarse ≤
        Pullback.two * fine + couplingLoss + remainderLoss

open SplitRGGapStep public

splitStepAsGapTransferStep :
  ∀ {fine coarse couplingLoss remainderLoss} →
  SplitRGGapStep fine coarse couplingLoss remainderLoss →
  Pullback.GapTransferStep
    fine coarse (totalRGStepLoss couplingLoss remainderLoss)
splitStepAsGapTransferStep
    {fine} {coarse} {couplingLoss} {remainderLoss} split =
  record
    { Pullback.GapTransferStep.coarseControlledByFine =
        subst
          (λ upper →
            coarse ≤ upper)
          (ℚRing.solve-∀ fine couplingLoss remainderLoss)
          (coarseControlledByFineWithSplitLoss split)
    }

splitOneStepPullbackLower :
  ∀ {fine coarse couplingLoss remainderLoss} →
  SplitRGGapStep fine coarse couplingLoss remainderLoss →
  Pullback.half
    * (coarse - couplingLoss - remainderLoss)
  ≤ fine
splitOneStepPullbackLower
    {fine} {coarse} {couplingLoss} {remainderLoss} split =
  let
    combined :
      Pullback.half
        * (coarse - totalRGStepLoss couplingLoss remainderLoss)
      ≤ fine
    combined =
      Pullback.oneStepPullbackLower
        (splitStepAsGapTransferStep split)
  in
  subst
    (λ lower → lower ≤ fine)
    (ℚRing.solve-∀ coarse couplingLoss remainderLoss)
    combined

splitPullbackArgumentExact :
  ∀ coarse couplingLoss remainderLoss →
  Pullback.half
    * (coarse - totalRGStepLoss couplingLoss remainderLoss)
  ≡ Pullback.half
    * (coarse - couplingLoss - remainderLoss)
splitPullbackArgumentExact = ℚRing.solve-∀

------------------------------------------------------------------------
-- A quantitative local producer can feed the abstract split step directly.
------------------------------------------------------------------------

splitStepFromCoarseEstimate :
  ∀ fine coarse couplingLoss remainderLoss →
  coarse ≤ Pullback.two * fine + couplingLoss + remainderLoss →
  SplitRGGapStep fine coarse couplingLoss remainderLoss
splitStepFromCoarseEstimate
    fine coarse couplingLoss remainderLoss estimate =
  record
    { coarseControlledByFineWithSplitLoss = estimate }

schurSignedLowerBookkeepingLevel : ProofLevel
schurSignedLowerBookkeepingLevel = machineChecked

coarseFineSplitGapStepLevel : ProofLevel
coarseFineSplitGapStepLevel = machineChecked

physicalEffectiveActionSecondDerivativeLevel : ProofLevel
physicalEffectiveActionSecondDerivativeLevel = conditional

physicalCoarseFineCouplingLossLevel : ProofLevel
physicalCoarseFineCouplingLossLevel = conditional

physicalEffectiveRemainderLossLevel : ProofLevel
physicalEffectiveRemainderLossLevel = conditional
