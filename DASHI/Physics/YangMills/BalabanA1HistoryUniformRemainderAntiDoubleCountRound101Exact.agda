{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1HistoryUniformRemainderAntiDoubleCountRound101Exact where

------------------------------------------------------------------------
-- ROUND101: HISTORY IS AN ARGUMENT OF THE CURRENT beta, NOT A SECOND DEBT
--
-- PR #583 already isolated the correct source logic: CMP109 defines beta_(k+1)
-- from the current effective interaction, and then warns after (5.42) that this
-- coefficient depends on all preceding couplings.  That dependence does not by
-- itself create an additional additive term in beta.
--
-- This current-master port keeps exactly the theorem needed by the Round101
-- pointwise source cut.  If the five physical finite-g channels are bounded
-- uniformly over the whole admissible generated history, then
--
--     beta(history) = betaZ(history) + betaInt(history)
--
-- and
--
--     betaZ(history) >= b,
--     betaInt(history) >= - C_beta(history) gamma(history)^4
--
-- imply the pointwise lower bound
--
--     b - C_beta(history) gamma(history)^4 <= beta(history).
--
-- No H_marg/H_irr term is subtracted afterwards.  Localization/history
-- estimates may be used INSIDE the proof that the channel constants are uniform
-- over admissible histories, or in the shooting/tuning theorem, but subtracting
-- them again from this already-history-uniform current beta would double count.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109A1CrossPollinatedDebtProducersExact as Debt
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five

record HistoryUniformCMP109BetaSplit (History Cell : Set) : Set₁ where
  field
    interaction : History → Debt.A1FiveChannelQuarticProducer Cell

    betaZ beta : History → ℚ

    -- The history variable is already an argument of the same current CMP109
    -- coefficient.  This is the anti-double-count same-object identity.
    betaExact : ∀ history →
      beta history ≡
        betaZ history + Five.betaInt (Debt.dataSet (interaction history))

    gaussianFloor : ℚ
    gaussianFloorUniform : ∀ history → gaussianFloor ≤ betaZ history

open HistoryUniformCMP109BetaSplit public

historyUniformCurrentRemainderLower :
  ∀ {History Cell}
    (dataSet : HistoryUniformCMP109BetaSplit History Cell)
    history →
  gaussianFloor dataSet
    - Debt.fiveChannelInteractionDebtAtGamma (interaction dataSet history)
  ≤ beta dataSet history
historyUniformCurrentRemainderLower dataSet history =
  let
    producer = interaction dataSet history
    gaussian = gaussianFloorUniform dataSet history
    remainder = Debt.fiveChannelInteractionUniformLower producer
    summed :
      gaussianFloor dataSet
        + (- Debt.fiveChannelInteractionDebtAtGamma producer)
      ≤ betaZ dataSet history + Five.betaInt (Debt.dataSet producer)
    summed = ℚP.+-mono-≤ gaussian remainder
  in
  subst
    (λ upper →
      gaussianFloor dataSet
        - Debt.fiveChannelInteractionDebtAtGamma producer
      ≤ upper)
    (sym (betaExact dataSet history))
    summed

historyUniformCurrentRemainderAntiDoubleCountLevel : ProofLevel
historyUniformCurrentRemainderAntiDoubleCountLevel = machineChecked

-- Physical source leaf: instantiate the five-channel data uniformly over the
-- complete admissible preceding-coupling history carried by the SAME generated
-- CMP109 trajectory.  If this is proved, no additional history subtraction is
-- part of the final pointwise beta margin.
cmp109LiteralFiveChannelUniformOverHistoryLevel : ProofLevel
cmp109LiteralFiveChannelUniformOverHistoryLevel = conditional
