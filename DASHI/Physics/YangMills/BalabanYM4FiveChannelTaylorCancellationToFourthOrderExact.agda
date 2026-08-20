module DASHI.Physics.YangMills.BalabanYM4FiveChannelTaylorCancellationToFourthOrderExact where

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
-- Lars V. Ahlfors, "Complex Analysis", third edition, McGraw-Hill, 1979.
-- No DOI assigned.  Used only as standard Taylor/Cauchy background; the exact
-- finite rational factorization below is proved internally.
--
-- DASHI CONTRIBUTION
--
-- The Round57 five-channel adapter still accepted the desired statement
--
--       r_alpha(g) = g^4 q_alpha(g)
--
-- as a field.  That is stronger than the source-shaped analytic input.  The
-- actual perturbative task is to derive an expansion through order three,
-- prove those four coefficients vanish, and bound the remaining quotient.
--
-- This module removes the direct factorization premise.  From an exact
-- expansion
--
--   r = a0 + g a1 + g^2 a2 + g^3 a3 + g^4 q
--
-- plus a0=a1=a2=a3=0, ring normalization constructs r=g^4 q and feeds the
-- existing five-channel/global quartic beta theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Beta
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five
import DASHI.Physics.YangMills.BalabanYM4FiveChannelFourthOrderFactorizationExact as Fourth

power2 : ℚ → ℚ
power2 g = g * g

power3 : ℚ → ℚ
power3 g = power2 g * g

record FiveChannelTaylorCancellationData (Cell : Set) : Set₁ where
  field
    cells : List Cell
    coupling : ℚ

    -- Same physical channel remainders consumed downstream.
    channelRemainder : Cell → Five.PhysicalBetaChannel → ℚ

    coefficient0 coefficient1 coefficient2 coefficient3 :
      Cell → Five.PhysicalBetaChannel → ℚ
    fourthOrderQuotient : Cell → Five.PhysicalBetaChannel → ℚ

    exactExpansionThroughThirdOrder : ∀ cell channel →
      channelRemainder cell channel
      ≡ coefficient0 cell channel
        + coupling * coefficient1 cell channel
        + power2 coupling * coefficient2 cell channel
        + power3 coupling * coefficient3 cell channel
        + Beta.power4 coupling * fourthOrderQuotient cell channel

    order0Cancels : ∀ cell channel → coefficient0 cell channel ≡ 0ℚ
    order1Cancels : ∀ cell channel → coefficient1 cell channel ≡ 0ℚ
    order2Cancels : ∀ cell channel → coefficient2 cell channel ≡ 0ℚ
    order3Cancels : ∀ cell channel → coefficient3 cell channel ≡ 0ℚ

    majorant : Cell → Five.PhysicalBetaChannel → ℚ
    quotientLower : ∀ cell channel →
      - majorant cell channel ≤ fourthOrderQuotient cell channel
    majorantNonnegative : ∀ cell channel → 0ℚ ≤ majorant cell channel

open FiveChannelTaylorCancellationData public

lowerOrdersVanish :
  ∀ {Cell} (dataSet : FiveChannelTaylorCancellationData Cell)
    cell channel →
  coefficient0 dataSet cell channel
    + coupling dataSet * coefficient1 dataSet cell channel
    + power2 (coupling dataSet) * coefficient2 dataSet cell channel
    + power3 (coupling dataSet) * coefficient3 dataSet cell channel
    + Beta.power4 (coupling dataSet)
        * fourthOrderQuotient dataSet cell channel
  ≡ Beta.power4 (coupling dataSet)
      * fourthOrderQuotient dataSet cell channel
lowerOrdersVanish dataSet cell channel
  rewrite order0Cancels dataSet cell channel
        | order1Cancels dataSet cell channel
        | order2Cancels dataSet cell channel
        | order3Cancels dataSet cell channel =
  ℚRing.solve-∀
    (coupling dataSet)
    (fourthOrderQuotient dataSet cell channel)

exactFourthOrderFactorization :
  ∀ {Cell} (dataSet : FiveChannelTaylorCancellationData Cell)
    cell channel →
  channelRemainder dataSet cell channel
  ≡ Beta.power4 (coupling dataSet)
      * fourthOrderQuotient dataSet cell channel
exactFourthOrderFactorization dataSet cell channel =
  trans
    (exactExpansionThroughThirdOrder dataSet cell channel)
    (lowerOrdersVanish dataSet cell channel)

asFourthOrderFactorizedFiveChannelData :
  ∀ {Cell} → FiveChannelTaylorCancellationData Cell →
  Fourth.FourthOrderFactorizedFiveChannelData Cell
asFourthOrderFactorizedFiveChannelData dataSet = record
  { Fourth.FourthOrderFactorizedFiveChannelData.cells = cells dataSet
  ; Fourth.FourthOrderFactorizedFiveChannelData.coupling = coupling dataSet
  ; Fourth.FourthOrderFactorizedFiveChannelData.channelRemainder =
      channelRemainder dataSet
  ; Fourth.FourthOrderFactorizedFiveChannelData.fourthOrderQuotient =
      fourthOrderQuotient dataSet
  ; Fourth.FourthOrderFactorizedFiveChannelData.coefficient = majorant dataSet
  ; Fourth.FourthOrderFactorizedFiveChannelData.exactFourthOrderFactorization =
      exactFourthOrderFactorization dataSet
  ; Fourth.FourthOrderFactorizedFiveChannelData.quotientLower =
      quotientLower dataSet
  ; Fourth.FourthOrderFactorizedFiveChannelData.coefficientNonnegative =
      majorantNonnegative dataSet
  }

taylorCancellationGlobalQuarticLower :
  ∀ {Cell} (dataSet : FiveChannelTaylorCancellationData Cell) →
  - (Five.coefficientTotal
      (Fourth.asFiveChannelQuarticBetaData
        (asFourthOrderFactorizedFiveChannelData dataSet))
      * Beta.power4 (coupling dataSet))
  ≤ Five.betaInt
      (Fourth.asFiveChannelQuarticBetaData
        (asFourthOrderFactorizedFiveChannelData dataSet))
taylorCancellationGlobalQuarticLower dataSet =
  Fourth.factorizedGlobalQuarticLower
    (asFourthOrderFactorizedFiveChannelData dataSet)

fiveChannelTaylorCancellationToFourthOrderLevel : ProofLevel
fiveChannelTaylorCancellationToFourthOrderLevel = machineChecked

fiveChannelTaylorCancellationToGlobalBetaLevel : ProofLevel
fiveChannelTaylorCancellationToGlobalBetaLevel = machineChecked

-- Remaining physical L4 producer is now source-shaped:
--   (1) construct the actual expansion of each determinant / interaction /
--       chart / gauge / localization remainder through cubic order;
--   (2) prove the four low coefficients vanish in the literal normalization;
--   (3) bound the resulting fourth-order quotient.
-- There is no longer a direct r=g^4 q premise on this route.
physicalFiveChannelTaylorExpansionLevel : ProofLevel
physicalFiveChannelTaylorExpansionLevel = conditional

physicalFiveChannelLowOrderCancellationLevel : ProofLevel
physicalFiveChannelLowOrderCancellationLevel = conditional

physicalFiveChannelFourthOrderQuotientMajorantLevel : ProofLevel
physicalFiveChannelFourthOrderQuotientMajorantLevel = conditional
