module DASHI.Physics.YangMills.BalabanA1HistoryUniformRemainderAntiDoubleCountExact where

------------------------------------------------------------------------
-- ROW A1: HISTORY IS AN ARGUMENT OF betaInt, NOT AUTOMATICALLY A SECOND DEBT
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- SOURCE POINT
--
-- CMP109 (2.13) defines the new effective interaction E^(k+1) by the current
-- fluctuation integral, and (1.20),(1.22),(5.42) define beta_(k+1) from that same
-- E^(k+1).  The text after (5.42) warns that beta_j depends on all preceding
-- couplings although the notation displays only g_(j-1).
--
-- Therefore preceding-coupling history is a dependency of the CURRENT betaInt.
-- It is not, without another source decomposition, an additional additive debt.
-- If the physical five-channel lower bound is uniform over the admissible
-- history carrier, subtracting a separate history term after betaInt would count
-- the same dependence twice.
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

    -- Same CMP109 coefficient: history enters through the current effective
    -- interaction, not through a separately appended summand.
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

------------------------------------------------------------------------
-- Authority boundary
------------------------------------------------------------------------

historyUniformCurrentRemainderAntiDoubleCountLevel : ProofLevel
historyUniformCurrentRemainderAntiDoubleCountLevel = machineChecked

-- Physical seam: show that the five-channel data instantiated from CMP109/CMP116
-- are uniform over the full admissible preceding-coupling history.  If this is
-- inhabited, no separate additive H_marg or H_irr is needed in the FINAL beta
-- margin; localization/history estimates may instead be used internally to
-- establish the uniform five-channel atom bounds.
cmp109LiteralFiveChannelUniformOverHistoryLevel : ProofLevel
cmp109LiteralFiveChannelUniformOverHistoryLevel = conditional
