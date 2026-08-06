module DASHI.Physics.YangMills.BalabanP33StrictTerminalGapMarginExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence",
-- Annales Henri Poincare 15 (2014), 2133--2175.
-- DOI: 10.1007/s00023-013-0303-3.
--
-- DASHI CONTRIBUTION
--
-- Strengthen the nonnegative terminal pullback to a quantitative positive
-- witness.  Instead of merely requiring
--
--   discountedLoss <= discountedTerminal,
--
-- require a named margin m_*:
--
--   m_* + discountedLoss <= discountedTerminal.
--
-- The exact closed pullback identity then proves
--
--   m_* <= pullBackGap <= fineGap.
--
-- For four steps ending at the literal P33 floor 1/32, this becomes
--
--   m_* + loss0/2 + loss1/4 + loss2/8 + loss3/16 <= 1/512.
--
-- Thus strict positivity is represented constructively by an explicit lower
-- witness, not by replacing <= with an untracked prose claim.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33
import DASHI.Physics.YangMills.BalabanP33TerminalScaleGapPullbackExact as Pullback
import DASHI.Physics.YangMills.BalabanP33FixedVolumeTerminalScaleSeparationExact as Fixed

marginBudgetAdmissible : ℚ → List ℚ → ℚ → Set
marginBudgetAdmissible terminalGap losses margin =
  margin + Pullback.discountedLossBudget losses
  ≤ Pullback.discountFactor (Pullback.listLength losses) * terminalGap

marginBelowDifference :
  ∀ {margin loss upper} →
  margin + loss ≤ upper →
  margin ≤ upper - loss
marginBelowDifference {margin} {loss} {upper} withMargin =
  subst
    (λ lower → lower ≤ upper - loss)
    (ℚRing.solve-∀ margin loss)
    (Pullback.subtractRightMonotone loss withMargin)

admissibleMarginBelowPullback :
  ∀ terminalGap losses margin →
  marginBudgetAdmissible terminalGap losses margin →
  margin ≤ Pullback.pullBackGap terminalGap losses
admissibleMarginBelowPullback terminalGap losses margin admissible =
  let
    belowClosedDifference :
      margin
      ≤ Pullback.discountFactor (Pullback.listLength losses) * terminalGap
        - Pullback.discountedLossBudget losses
    belowClosedDifference =
      marginBelowDifference admissible
  in
  subst
    (λ upper → margin ≤ upper)
    (sym (Pullback.pullBackGapClosedForm terminalGap losses))
    belowClosedDifference

admissibleMarginBelowFineGap :
  ∀ {fineGap losses terminalGap margin} →
  Pullback.GapTransferChain fineGap losses terminalGap →
  marginBudgetAdmissible terminalGap losses margin →
  margin ≤ fineGap
admissibleMarginBelowFineGap
    {fineGap} {losses} {terminalGap} {margin}
    chain admissible =
  ℚP.≤-trans
    (admissibleMarginBelowPullback
      terminalGap losses margin admissible)
    (Pullback.pullBackGapBelowFine chain)

FourStepPhysicalPositiveMarginBudget :
  ℚ → ℚ → ℚ → ℚ → ℚ → Set
FourStepPhysicalPositiveMarginBudget
    margin loss0 loss1 loss2 loss3 =
  margin + Fixed.fourStepWeightedLoss loss0 loss1 loss2 loss3
  ≤ + 1 / 512

fourStepPhysicalMarginAdmissible :
  ∀ margin loss0 loss1 loss2 loss3 →
  FourStepPhysicalPositiveMarginBudget
    margin loss0 loss1 loss2 loss3 →
  marginBudgetAdmissible
    P33.p33PhysicalFloor
    (loss0 ∷ loss1 ∷ loss2 ∷ loss3 ∷ [])
    margin
fourStepPhysicalMarginAdmissible
    margin loss0 loss1 loss2 loss3 budget
  rewrite Fixed.fourStepDiscountedLossExact
      loss0 loss1 loss2 loss3
        | Fixed.p33FourStepDiscountedTerminalExact
      loss0 loss1 loss2 loss3 =
  budget

fourStepPhysicalMarginBelowPullback :
  ∀ margin loss0 loss1 loss2 loss3 →
  FourStepPhysicalPositiveMarginBudget
    margin loss0 loss1 loss2 loss3 →
  margin ≤ Pullback.pullBackGap
    P33.p33PhysicalFloor
    (loss0 ∷ loss1 ∷ loss2 ∷ loss3 ∷ [])
fourStepPhysicalMarginBelowPullback
    margin loss0 loss1 loss2 loss3 budget =
  admissibleMarginBelowPullback
    P33.p33PhysicalFloor
    (loss0 ∷ loss1 ∷ loss2 ∷ loss3 ∷ [])
    margin
    (fourStepPhysicalMarginAdmissible
      margin loss0 loss1 loss2 loss3 budget)

fourStepPhysicalMarginBelowFineGap :
  ∀ {fineGap margin loss0 loss1 loss2 loss3} →
  Pullback.GapTransferChain
    fineGap
    (loss0 ∷ loss1 ∷ loss2 ∷ loss3 ∷ [])
    P33.p33PhysicalFloor →
  FourStepPhysicalPositiveMarginBudget
    margin loss0 loss1 loss2 loss3 →
  margin ≤ fineGap
fourStepPhysicalMarginBelowFineGap
    {margin = margin}
    {loss0} {loss1} {loss2} {loss3}
    chain budget =
  admissibleMarginBelowFineGap
    chain
    (fourStepPhysicalMarginAdmissible
      margin loss0 loss1 loss2 loss3 budget)

strictTerminalGapMarginLevel : ProofLevel
strictTerminalGapMarginLevel = machineChecked

physicalStrictLossBudgetProducerLevel : ProofLevel
physicalStrictLossBudgetProducerLevel = conditional
