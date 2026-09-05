module DASHI.Analysis.NonArchimedeanStoppingTimeAuthorityBidiExact where

------------------------------------------------------------------------
-- STOPPING-TIME AUTHORITY BIDI
--
-- The source mixing/stopping document derives several claims downstream from
-- its Theorem 4.2 unit-prefactor L2 norm identity.  That identity is refuted by
-- the exact n=3 witness.  Dependency failure is not the same as statement
-- falsity: each downstream claim is reopened at its own producer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data StoppingClaim : Set where
  unitPrefactorL2PowerNorm : StoppingClaim
  prefactoredL2PowerNorm : StoppingClaim
  totalVariationEnvelope : StoppingClaim
  killedKernelSpectralEnvelope : StoppingClaim
  survivalTail : StoppingClaim
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
claimAuthority killedKernelSpectralEnvelope = independentProducerRequired
claimAuthority survivalTail = independentProducerRequired
claimAuthority momentGeneratingDomain = downstreamRepair
claimAuthority polynomialMomentFiniteness = downstreamRepair
claimAuthority taoStyleConcentration = independentProducerRequired


data StoppingProducer : Set where
  repairedPrefactoredL2Power : StoppingProducer
  finiteCauchySchwarzTVConsumer : StoppingProducer
  killedKernelPowerBound : StoppingProducer
  survivalTailToMGF : StoppingProducer
  survivalTailToMoments : StoppingProducer
  MarkovConcentrationHypotheses : StoppingProducer
  driftStoppingSameObjectWeld : StoppingProducer

reverseRoute : StoppingClaim → List StoppingProducer
reverseRoute unitPrefactorL2PowerNorm = []
reverseRoute prefactoredL2PowerNorm = repairedPrefactoredL2Power ∷ []
reverseRoute totalVariationEnvelope =
  repairedPrefactoredL2Power ∷ finiteCauchySchwarzTVConsumer ∷ []
reverseRoute killedKernelSpectralEnvelope = killedKernelPowerBound ∷ []
reverseRoute survivalTail = killedKernelPowerBound ∷ []
reverseRoute momentGeneratingDomain =
  killedKernelPowerBound ∷ survivalTailToMGF ∷ []
reverseRoute polynomialMomentFiniteness =
  killedKernelPowerBound ∷ survivalTailToMoments ∷ []
reverseRoute taoStyleConcentration =
  MarkovConcentrationHypotheses ∷ driftStoppingSameObjectWeld ∷ []

record StoppingAuthorityFirewall : Set where
  constructor stoppingAuthorityFirewall
  field
    falseL2ProducerMayStillSupportDownstreamClaims : Bool
    failedProofRouteAutomaticallyRefutesConclusion : Bool
    principalSubmatrixInterlacingAutomaticForNonnormalOperator : Bool
    spectralGapAloneSuppliesStoppingConcentration : Bool
    repairedPrefactorCanFeedTVConsumer : Bool

canonicalStoppingAuthorityFirewall : StoppingAuthorityFirewall
canonicalStoppingAuthorityFirewall =
  stoppingAuthorityFirewall false false false false true

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
