module DASHI.Analysis.NonArchimedeanMarkovMixingProofAuditExact where

------------------------------------------------------------------------
-- MARKOV MIXING PROOF AUDIT
--
-- docs/collatz_markov_mixing_stopping_times.md advertises
--
--   ||P_n^t||_{L2_0 -> L2_0} = 2^(-t/2).
--
-- Its proof handles the m=2 shell exactly, but for m>=3 states only
--
--   |2^(-t) W_t(k)| <= C_m 2^(-3t/4)
--
-- and then concludes this is < 2^(-t/2) without discharging C_m.  The exact
-- n=3,t=1 rational counterexample independently refutes the claimed operator
-- norm identity/upper bound.
--
-- Downstream total-variation, survival, moment and concentration statements
-- that cite this theorem lose that producer.  They are not automatically false;
-- they require independent proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)


data MarkovClaim : Set where
  unitPrefactorL2PowerNorm : MarkovClaim
  totalVariationBound : MarkovClaim
  arbitraryStoppingSetSpectralBound : MarkovClaim
  stoppingTimeExponentialTail : MarkovClaim
  allStoppingMomentsFiniteByThisRoute : MarkovClaim
  taoStyleConcentrationByThisRoute : MarkovClaim


data AuditDisposition : Set where
  refuted : AuditDisposition
  proofDependencyBroken : AuditDisposition
  independentProofRequired : AuditDisposition

claimDisposition : MarkovClaim → AuditDisposition
claimDisposition unitPrefactorL2PowerNorm = refuted
claimDisposition totalVariationBound = independentProofRequired
claimDisposition arbitraryStoppingSetSpectralBound = independentProofRequired
claimDisposition stoppingTimeExponentialTail = proofDependencyBroken
claimDisposition allStoppingMomentsFiniteByThisRoute = proofDependencyBroken
claimDisposition taoStyleConcentrationByThisRoute = proofDependencyBroken

record MixingProofFirewall : Set where
  constructor mixingProofFirewall
  field
    shellPrefactorMayBeDroppedWithoutBound : Bool
    eigenvalueModulusAutomaticallyEqualsOperatorNorm : Bool
    refutedUpstreamProofAutomaticallyRefutesDownstreamStatement : Bool
    downstreamStatementMayRetainIndependentProof : Bool

canonicalMixingProofFirewall : MixingProofFirewall
canonicalMixingProofFirewall =
  mixingProofFirewall false false false true

unitPrefactorNormClaimRefuted :
  claimDisposition unitPrefactorL2PowerNorm ≡ refuted
unitPrefactorNormClaimRefuted = refl

downstreamClaimsNeedIndependentReceipts :
  claimDisposition totalVariationBound ≡ independentProofRequired
downstreamClaimsNeedIndependentReceipts = refl

brokenProducerDoesNotMeanFalseConsumer :
  MixingProofFirewall.refutedUpstreamProofAutomaticallyRefutesDownstreamStatement
    canonicalMixingProofFirewall
  ≡ false
brokenProducerDoesNotMeanFalseConsumer = refl
