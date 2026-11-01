{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticAbsoluteBetaRound102Exact where

------------------------------------------------------------------------
-- ROUND102 A: THE SAME FIVE PHYSICAL CHANNELS GIVE A TWO-SIDED QUARTIC BOUND
--
-- The older five-channel owner kept only the lower half needed for positivity.
-- The frozen Row-A endpoint also wants a finite pointwise upper beta slope.
-- Analytic/Cauchy quotient control is naturally absolute, so do not introduce a
-- separate upper mechanism: add the missing upper half to the SAME literal
-- determinant / interaction / chart / gauge / localization remainders.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Beta
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five

record FiveChannelQuarticAbsoluteBetaData (Cell : Set) : Set₁ where
  field
    lowerData : Five.FiveChannelQuarticBetaData Cell

    determinantUpper : ∀ cell →
      Five.determinantRemainder lowerData cell
      ≤ Five.determinantCoefficient lowerData cell * Beta.power4 (Five.coupling lowerData)
    interactionUpper : ∀ cell →
      Five.interactionRemainder lowerData cell
      ≤ Five.interactionCoefficient lowerData cell * Beta.power4 (Five.coupling lowerData)
    chartUpper : ∀ cell →
      Five.chartRemainder lowerData cell
      ≤ Five.chartCoefficient lowerData cell * Beta.power4 (Five.coupling lowerData)
    gaugeUpper : ∀ cell →
      Five.gaugeRemainder lowerData cell
      ≤ Five.gaugeCoefficient lowerData cell * Beta.power4 (Five.coupling lowerData)
    localizationUpper : ∀ cell →
      Five.localizationRemainder lowerData cell
      ≤ Five.localizationCoefficient lowerData cell * Beta.power4 (Five.coupling lowerData)

open FiveChannelQuarticAbsoluteBetaData public

channelUpper :
  ∀ {Cell} (dataSet : FiveChannelQuarticAbsoluteBetaData Cell)
    cell channel →
  Five.channelRemainder (lowerData dataSet) cell channel
  ≤ Five.channelCoefficient (lowerData dataSet) cell channel
      * Beta.power4 (Five.coupling (lowerData dataSet))
channelUpper dataSet cell Five.determinant = determinantUpper dataSet cell
channelUpper dataSet cell Five.interaction = interactionUpper dataSet cell
channelUpper dataSet cell Five.chart = chartUpper dataSet cell
channelUpper dataSet cell Five.gauge = gaugeUpper dataSet cell
channelUpper dataSet cell Five.localization = localizationUpper dataSet cell

localQuarticUpper :
  ∀ {Cell} (dataSet : FiveChannelQuarticAbsoluteBetaData Cell) cell →
  Five.localRemainder (lowerData dataSet) cell
  ≤ Five.localCoefficient (lowerData dataSet) cell
      * Beta.power4 (Five.coupling (lowerData dataSet))
localQuarticUpper dataSet cell =
  let
    data = lowerData dataSet
    fourth = Beta.power4 (Five.coupling data)
    pointwise = Beta.sumMonotone
      Five.channels
      (Five.channelRemainder data cell)
      (λ channel → Five.channelCoefficient data cell channel * fourth)
      (channelUpper dataSet cell)

    identify :
      Sums.sumRational Five.channels
        (λ channel → Five.channelCoefficient data cell channel * fourth)
      ≡ Five.localCoefficient data cell * fourth
    identify = trans
      (Sums.sumRationalCong Five.channels
        (λ channel → Five.channelCoefficient data cell channel * fourth)
        (λ channel → fourth * Five.channelCoefficient data cell channel)
        (λ channel → ℚRing.solve-∀ (Five.channelCoefficient data cell channel) fourth))
      (trans
        (Sums.sumRationalScale fourth Five.channels (Five.channelCoefficient data cell))
        (ℚRing.solve-∀ fourth (Five.localCoefficient data cell)))
  in
  subst
    (λ upper → Five.localRemainder data cell ≤ upper)
    identify pointwise

globalQuarticUpper :
  ∀ {Cell} (dataSet : FiveChannelQuarticAbsoluteBetaData Cell) →
  Five.betaInt (lowerData dataSet)
  ≤ Five.coefficientTotal (lowerData dataSet)
      * Beta.power4 (Five.coupling (lowerData dataSet))
globalQuarticUpper dataSet =
  let
    data = lowerData dataSet
    fourth = Beta.power4 (Five.coupling data)
    pointwise = Beta.sumMonotone
      (Five.cells data)
      (Five.localRemainder data)
      (λ cell → Five.localCoefficient data cell * fourth)
      (localQuarticUpper dataSet)

    identify :
      Sums.sumRational (Five.cells data)
        (λ cell → Five.localCoefficient data cell * fourth)
      ≡ Five.coefficientTotal data * fourth
    identify = trans
      (Sums.sumRationalCong (Five.cells data)
        (λ cell → Five.localCoefficient data cell * fourth)
        (λ cell → fourth * Five.localCoefficient data cell)
        (λ cell → ℚRing.solve-∀ (Five.localCoefficient data cell) fourth))
      (trans
        (Sums.sumRationalScale fourth (Five.cells data) (Five.localCoefficient data))
        (ℚRing.solve-∀ fourth (Five.coefficientTotal data)))
  in
  subst (λ upper → Five.betaInt data ≤ upper) identify pointwise

fiveChannelQuarticAbsoluteBetaLevel : ProofLevel
fiveChannelQuarticAbsoluteBetaLevel = machineChecked

-- Source task: instantiate the upper quotient estimates from the SAME analytic
-- channel Taylor/Cauchy data already used for the lower estimates.  This is one
-- absolute majorant theorem, not a new physical beta mechanism.
literalFiveChannelAbsoluteQuotientMajorantLevel : ProofLevel
literalFiveChannelAbsoluteQuotientMajorantLevel = conditional
