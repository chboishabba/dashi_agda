module DASHI.Physics.Closure.NSTriadKNThirdEigenvalueCostCompressionRound79Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir; Eberhard Bodenschatz.
-- Title: "Generation of intense dissipation in high Reynolds number
-- turbulence".
-- Philosophical Transactions of the Royal Society A 380 (2022), 20210088.
-- DOI: 10.1098/rsta.2021.0088.
-- arXiv: 2107.01719.
--
-- ROUND79 / C2 COST-CURRENCY COMPRESSION
--
-- The cited DNS reports that conditioned intense-strain net amplification is
-- produced by the third/most-compressive eigenvalue, while the self-amplifying
-- and vortex-stretching contributions on the other two eigenvalues nearly
-- cancel. That is statistical guidance, not a pointwise theorem.
--
-- The reusable exact consequence is an accounting compression: never ask C2
-- for six separate first/second-eigenvalue estimates if the physical theorem
-- can produce their signed residual directly. For arbitrary eigenvalue-channel
-- contributions, define
--
--   R12 = net1 + net2.
--
-- Then the total is exactly
--
--   total = net3 + R12.
--
-- Thus a source-native C2 proof may spend its sharp estimate on the third
-- channel and control the first-two cancellation residual as one signed cost,
-- without promoting the DNS observation that R12 is universally small.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)

record EigenvalueChannelContributions : Set where
  constructor eigenvalue-channel-contributions
  field
    self1 vortex1 pressure1 : ℚ
    self2 vortex2 pressure2 : ℚ
    self3 vortex3 pressure3 : ℚ

open EigenvalueChannelContributions public

net1 net2 net3 : EigenvalueChannelContributions → ℚ
net1 c = self1 c + vortex1 c + pressure1 c
net2 c = self2 c + vortex2 c + pressure2 c
net3 c = self3 c + vortex3 c + pressure3 c

firstTwoCancellationResidual : EigenvalueChannelContributions → ℚ
firstTwoCancellationResidual c = net1 c + net2 c

totalNetEigenvalueContribution : EigenvalueChannelContributions → ℚ
totalNetEigenvalueContribution c = net1 c + net2 c + net3 c

totalFactorsThroughThirdPlusFirstTwoResidual :
  ∀ c →
  totalNetEigenvalueContribution c
  ≡ net3 c + firstTwoCancellationResidual c
totalFactorsThroughThirdPlusFirstTwoResidual c =
  solve (net1 c ∷ net2 c ∷ net3 c ∷ [])

record ThirdChannelCompressedCost : Set where
  constructor third-channel-compressed-cost
  field
    channels : EigenvalueChannelContributions
    thirdChannelCost : ℚ
    firstTwoResidualCost : ℚ
    thirdChannelMeaning : thirdChannelCost ≡ net3 channels
    firstTwoResidualMeaning :
      firstTwoResidualCost ≡ firstTwoCancellationResidual channels

open ThirdChannelCompressedCost public

round79DNSNearCancellationPromotedToUniversalPointwiseBound : Bool
round79DNSNearCancellationPromotedToUniversalPointwiseBound = false

round79C2MayControlFirstTwoChannelsThroughSignedResidual : Bool
round79C2MayControlFirstTwoChannelsThroughSignedResidual = true

round79C2MayControlFirstTwoChannelsThroughSignedResidualIsTrue :
  round79C2MayControlFirstTwoChannelsThroughSignedResidual ≡ true
round79C2MayControlFirstTwoChannelsThroughSignedResidualIsTrue = refl
