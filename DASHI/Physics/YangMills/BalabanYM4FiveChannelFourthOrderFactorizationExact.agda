module DASHI.Physics.YangMills.BalabanYM4FiveChannelFourthOrderFactorizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Lars V. Ahlfors,
-- "Complex Analysis", third edition, McGraw-Hill, 1979. No DOI assigned.
-- Relationship only: Cauchy coefficient/remainder bounds motivate bounding a
-- fourth-order quotient after the lower Taylor coefficients cancel.  No
-- complex-analytic theorem is imported from the book by this module.
--
-- DASHI CONTRIBUTION
--
-- Round56 made the physical H-R_beta channels themselves the atoms consumed by
-- the finite beta theorem, but still asked directly for five inequalities
--
--      -c_(x,a) g^4 <= r_(x,a)(g).
--
-- The higher-alpha analytic target is instead an exact FOURTH-ORDER
-- FACTORIZATION
--
--      r_(x,a)(g) = g^4 q_(x,a)(g)
--
-- plus a common-form quotient majorant
--
--      -c_(x,a) <= q_(x,a)(g),       c_(x,a) >= 0.
--
-- This module proves that those two source-shaped facts construct every
-- Round56 channel inequality and hence the existing global quartic beta
-- enclosure.  A future Cauchy/Taylor theorem now has one precise job: construct
-- and bound q after proving the order-0..3 cancellations.  We do not pretend
-- the repository's current radius-budget records already supply that theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Beta
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five

record FourthOrderFactorizedFiveChannelData (Cell : Set) : Set₁ where
  field
    cells : List Cell
    coupling : ℚ

    -- These are the SAME physical channel remainders consumed by Round56.
    channelRemainder : Cell → Five.PhysicalBetaChannel → ℚ

    -- q_(x,a)(g), evaluated at the same coupling as the remainder.
    fourthOrderQuotient : Cell → Five.PhysicalBetaChannel → ℚ
    coefficient : Cell → Five.PhysicalBetaChannel → ℚ

    -- Exact cancellation/divisibility statement.  Analytically this is where
    -- vanishing Taylor coefficients 0,1,2,3 are converted to a g^4 factor.
    exactFourthOrderFactorization : ∀ cell channel →
      channelRemainder cell channel
      ≡ Beta.power4 coupling * fourthOrderQuotient cell channel

    quotientLower : ∀ cell channel →
      - coefficient cell channel ≤ fourthOrderQuotient cell channel

    coefficientNonnegative : ∀ cell channel →
      0ℚ ≤ coefficient cell channel

open FourthOrderFactorizedFiveChannelData public

power4Nonnegative : ∀ value → 0ℚ ≤ Beta.power4 value
power4Nonnegative value =
  FiniteL2.squareNonnegative (value * value)

factorizedChannelLower :
  ∀ {Cell}
    (dataSet : FourthOrderFactorizedFiveChannelData Cell)
    cell channel →
  - (coefficient dataSet cell channel * Beta.power4 (coupling dataSet))
  ≤ channelRemainder dataSet cell channel
factorizedChannelLower dataSet cell channel =
  let
    fourth = Beta.power4 (coupling dataSet)
    scaled :
      fourth * (- coefficient dataSet cell channel)
      ≤ fourth * fourthOrderQuotient dataSet cell channel
    scaled =
      Norm.scaleNonnegative fourth (power4Nonnegative (coupling dataSet))
        (quotientLower dataSet cell channel)

    lowerIdentity :
      fourth * (- coefficient dataSet cell channel)
      ≡ - (coefficient dataSet cell channel * fourth)
    lowerIdentity = ℚRing.solve-∀ fourth (coefficient dataSet cell channel)
  in
  subst
    (λ lower → lower ≤ channelRemainder dataSet cell channel)
    lowerIdentity
    (subst
      (λ upper →
        fourth * (- coefficient dataSet cell channel) ≤ upper)
      (sym (exactFourthOrderFactorization dataSet cell channel))
      scaled)

asFiveChannelQuarticBetaData :
  ∀ {Cell} →
  FourthOrderFactorizedFiveChannelData Cell →
  Five.FiveChannelQuarticBetaData Cell
asFiveChannelQuarticBetaData dataSet = record
  { Five.FiveChannelQuarticBetaData.cells = cells dataSet
  ; Five.FiveChannelQuarticBetaData.coupling = coupling dataSet
  ; Five.FiveChannelQuarticBetaData.determinantRemainder =
      λ cell → channelRemainder dataSet cell Five.determinant
  ; Five.FiveChannelQuarticBetaData.interactionRemainder =
      λ cell → channelRemainder dataSet cell Five.interaction
  ; Five.FiveChannelQuarticBetaData.chartRemainder =
      λ cell → channelRemainder dataSet cell Five.chart
  ; Five.FiveChannelQuarticBetaData.gaugeRemainder =
      λ cell → channelRemainder dataSet cell Five.gauge
  ; Five.FiveChannelQuarticBetaData.localizationRemainder =
      λ cell → channelRemainder dataSet cell Five.localization
  ; Five.FiveChannelQuarticBetaData.determinantCoefficient =
      λ cell → coefficient dataSet cell Five.determinant
  ; Five.FiveChannelQuarticBetaData.interactionCoefficient =
      λ cell → coefficient dataSet cell Five.interaction
  ; Five.FiveChannelQuarticBetaData.chartCoefficient =
      λ cell → coefficient dataSet cell Five.chart
  ; Five.FiveChannelQuarticBetaData.gaugeCoefficient =
      λ cell → coefficient dataSet cell Five.gauge
  ; Five.FiveChannelQuarticBetaData.localizationCoefficient =
      λ cell → coefficient dataSet cell Five.localization
  ; Five.FiveChannelQuarticBetaData.determinantCoefficientNN =
      λ cell → coefficientNonnegative dataSet cell Five.determinant
  ; Five.FiveChannelQuarticBetaData.interactionCoefficientNN =
      λ cell → coefficientNonnegative dataSet cell Five.interaction
  ; Five.FiveChannelQuarticBetaData.chartCoefficientNN =
      λ cell → coefficientNonnegative dataSet cell Five.chart
  ; Five.FiveChannelQuarticBetaData.gaugeCoefficientNN =
      λ cell → coefficientNonnegative dataSet cell Five.gauge
  ; Five.FiveChannelQuarticBetaData.localizationCoefficientNN =
      λ cell → coefficientNonnegative dataSet cell Five.localization
  ; Five.FiveChannelQuarticBetaData.determinantLower =
      λ cell → factorizedChannelLower dataSet cell Five.determinant
  ; Five.FiveChannelQuarticBetaData.interactionLower =
      λ cell → factorizedChannelLower dataSet cell Five.interaction
  ; Five.FiveChannelQuarticBetaData.chartLower =
      λ cell → factorizedChannelLower dataSet cell Five.chart
  ; Five.FiveChannelQuarticBetaData.gaugeLower =
      λ cell → factorizedChannelLower dataSet cell Five.gauge
  ; Five.FiveChannelQuarticBetaData.localizationLower =
      λ cell → factorizedChannelLower dataSet cell Five.localization
  }

factorizedGlobalQuarticLower :
  ∀ {Cell}
    (dataSet : FourthOrderFactorizedFiveChannelData Cell) →
  - (Five.coefficientTotal (asFiveChannelQuarticBetaData dataSet)
      * Beta.power4 (coupling dataSet))
  ≤ Five.betaInt (asFiveChannelQuarticBetaData dataSet)
factorizedGlobalQuarticLower dataSet =
  Five.globalQuarticLower (asFiveChannelQuarticBetaData dataSet)

fourthOrderFactorizationToFiveChannelBoundsLevel : ProofLevel
fourthOrderFactorizationToFiveChannelBoundsLevel = machineChecked

fourthOrderFactorizationToGlobalBetaBoundLevel : ProofLevel
fourthOrderFactorizationToGlobalBetaBoundLevel = machineChecked

-- Remaining L4 producer, now sharply split into:
--   (1) actual order-0..3 cancellation / exact g^4 factorization for each
--       physical determinant/interaction/chart/gauge/localization remainder;
--   (2) one suitable analytic/localized majorant for the resulting quotients.
-- The current `AnalyticityRadiusCouplingControl` record does not yet construct
-- a complex disk, derivatives, or a Cauchy coefficient estimate.
physicalFiveChannelFourthOrderFactorizationLevel : ProofLevel
physicalFiveChannelFourthOrderFactorizationLevel = conditional

physicalFiveChannelQuotientMajorantLevel : ProofLevel
physicalFiveChannelQuotientMajorantLevel = conditional
