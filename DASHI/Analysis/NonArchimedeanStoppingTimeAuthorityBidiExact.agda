module DASHI.Analysis.NonArchimedeanStoppingTimeAuthorityBidiExact where

------------------------------------------------------------------------
-- STOPPING-TIME AUTHORITY BIDI
--
-- Two source proof routes are now closed-negative as stated:
--
--   * unit-prefactor L2 power norm = 2^(-t/2);
--   * universal survival tail sqrt(|A^c|) 2^(-t/2).
--
-- The second has its own exact n=3 counterexample with A={4}, x0=1, t=3.
-- Downstream moment/concentration statements are therefore reopened at weaker,
-- set-dependent killed-chain producers rather than inherited from the false
-- universal bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data StoppingClaim : Set where
  unitPrefactorL2PowerNorm : StoppingClaim
  prefactoredL2PowerNorm : StoppingClaim
  totalVariationEnvelope : StoppingClaim
  universalInverseSqrtTwoSurvivalTail : StoppingClaim
  setDependentExponentialSurvivalTail : StoppingClaim
  momentGeneratingDomain : StoppingClaim
  polynomialMomentFiniteness : StoppingClaim
  taoStyleConcentration : StoppingClaim


data AuthorityState : Set where
  refuted : AuthorityState
  liveRepair : AuthorityState
  downstreamRepair : AuthorityState
  independentProducerRequired : AuthorityState

claimAuthority : StoppingClaim → AuthorityState
claimAuthority unitPrefactorL2PowerNorm = refuted
claimAuthority prefactoredL2PowerNorm = liveRepair
claimAuthority totalVariationEnvelope = downstreamRepair
claimAuthority universalInverseSqrtTwoSurvivalTail = refuted
claimAuthority setDependentExponentialSurvivalTail = independentProducerRequired
claimAuthority momentGeneratingDomain = downstreamRepair
claimAuthority polynomialMomentFiniteness = downstreamRepair
claimAuthority taoStyleConcentration = independentProducerRequired


data StoppingProducer : Set where
  repairedPrefactoredL2Power : StoppingProducer
  finiteCauchySchwarzTVConsumer : StoppingProducer
  finiteIrreducibleKilledChain : StoppingProducer
  setDependentKilledKernelPowerBound : StoppingProducer
  survivalTailToMGF : StoppingProducer
  survivalTailToMoments : StoppingProducer
  MarkovConcentrationHypotheses : StoppingProducer
  driftStoppingSameObjectWeld : StoppingProducer

reverseRoute : StoppingClaim → List StoppingProducer
reverseRoute unitPrefactorL2PowerNorm = []
reverseRoute prefactoredL2PowerNorm = repairedPrefactoredL2Power ∷ []
reverseRoute totalVariationEnvelope =
  repairedPrefactoredL2Power ∷ finiteCauchySchwarzTVConsumer ∷ []
reverseRoute universalInverseSqrtTwoSurvivalTail = []
reverseRoute setDependentExponentialSurvivalTail =
  finiteIrreducibleKilledChain ∷
  setDependentKilledKernelPowerBound ∷ []
reverseRoute momentGeneratingDomain =
  finiteIrreducibleKilledChain ∷
  setDependentKilledKernelPowerBound ∷
  survivalTailToMGF ∷ []
reverseRoute polynomialMomentFiniteness =
  finiteIrreducibleKilledChain ∷
  setDependentKilledKernelPowerBound ∷
  survivalTailToMoments ∷ []
reverseRoute taoStyleConcentration =
  MarkovConcentrationHypotheses ∷ driftStoppingSameObjectWeld ∷ []

record StoppingAuthorityFirewall : Set where
  constructor stoppingAuthorityFirewall
  field
    falseL2ProducerMayStillSupportDownstreamClaims : Bool
    failedProofRouteAutomaticallyRefutesConclusion : Bool
    universalInverseSqrtTwoSurvivalBoundValid : Bool
    weakerSetDependentTailMayStillHold : Bool
    principalSubmatrixInterlacingAutomaticForNonnormalOperator : Bool
    spectralGapAloneSuppliesStoppingConcentration : Bool
    repairedPrefactorCanFeedTVConsumer : Bool

canonicalStoppingAuthorityFirewall : StoppingAuthorityFirewall
canonicalStoppingAuthorityFirewall =
  stoppingAuthorityFirewall false false false true false false true

universalSurvivalRateClosedNegative :
  StoppingAuthorityFirewall.universalInverseSqrtTwoSurvivalBoundValid
    canonicalStoppingAuthorityFirewall
  ≡ false
universalSurvivalRateClosedNegative = refl

weakerSetDependentTailRemainsOpen :
  StoppingAuthorityFirewall.weakerSetDependentTailMayStillHold
    canonicalStoppingAuthorityFirewall
  ≡ true
weakerSetDependentTailRemainsOpen = refl

failedRouteDoesNotAutoRefuteConclusion :
  StoppingAuthorityFirewall.failedProofRouteAutomaticallyRefutesConclusion
    canonicalStoppingAuthorityFirewall
  ≡ false
failedRouteDoesNotAutoRefuteConclusion = refl

nonnormalKilledKernelNeedsOwnProducer :
  StoppingAuthorityFirewall.principalSubmatrixInterlacingAutomaticForNonnormalOperator
    canonicalStoppingAuthorityFirewall
  ≡ false
nonnormalKilledKernelNeedsOwnProducer = refl

spectralGapDoesNotAutoPromoteTaoConcentration :
  StoppingAuthorityFirewall.spectralGapAloneSuppliesStoppingConcentration
    canonicalStoppingAuthorityFirewall
  ≡ false
spectralGapDoesNotAutoPromoteTaoConcentration = refl
