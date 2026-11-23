module DASHI.Economics.MacroRivalMultiFactor20261121Exact where

open import DASHI.Core.Prelude
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Economics.AIGlobalFundingRegulatorySynthesisExact as Global
import DASHI.Economics.AICapitalOutcomeCompatibility20261016Exact as Outcome
import DASHI.Economics.JPYJGBTreasuryFundingTransmission2026Exact as Yen

-- Public economic axes, distinct from policy intentions and issuers.
-- Not a new monetary ontology: reuse existing source-bounded owners.
data MacroAxis : Set where
  aiCreditExcessSpread terminalCapitalRecovery treasurySupply
  policyRateExpectations energyInputCost foreignFunding
  marketSentiment householdLossIncidence : MacroAxis

data EvidencePolarity : Set where
  stressUp stressDown unchanged unknown : EvidencePolarity

record MacroObservation : Set where
  constructor macroObservation
  field
    credit : EvidencePolarity
    capital : EvidencePolarity
    issuance : EvidencePolarity
    rates : EvidencePolarity
    energy : EvidencePolarity
    foreign : EvidencePolarity
    sentiment : EvidencePolarity
    household : EvidencePolarity

-- Synthetic all-unknown is a negative control, not an economic prediction.
allUnknown : MacroObservation
allUnknown = macroObservation
  unknown unknown unknown unknown unknown unknown unknown unknown

data RivalRegime : Set where
  H0Endogenous H1Tolerated H2Induced H3Selective H4Contagion : RivalRegime

record RivalWorld : Set where
  constructor rivalWorld
  field
    observation : MacroObservation
    regime : RivalRegime

open RivalWorld public

-- Identical public observables do not identify whether a correction was
-- tolerated or merely endogenous. The same applies to a Bessent-intent test.
endogenous : RivalWorld
endogenous = rivalWorld allUnknown H0Endogenous

tolerated : RivalWorld
tolerated = rivalWorld allUnknown H1Tolerated

samePublicObservation : observation endogenous ≡ observation tolerated
samePublicObservation = refl

differentPolicyIntention : regime endogenous ≡ regime tolerated → ⊥
differentPolicyIntention ()

macroNonDescent : Descent.ConsumerNonDescentWitness observation regime
macroNonDescent =
  Descent.consumerNonDescentWitness endogenous tolerated
    samePublicObservation differentPolicyIntention

noTotalIntentClassifier : Descent.FactorsThrough observation regime → ⊥
noTotalIntentClassifier =
  Descent.nonDescentWitnessBlocksFactorization macroNonDescent

record ExistingOwnerProjection : Set where
  field
    coupledState : Global.CoupledState
    candidateYenValve : Yen.YenFundingValve
    partialOutcomeFit : Outcome.OutcomeFit
    alignedEvidence : MacroObservation
    sourceAndHorizonCompared : Bool
    signedUnitNormalizationPaid : Bool
    intentIdentified : Bool

-- The open gates belong to real source admission; these Boolean fields do
-- not manufacture empirical evidence or validate an actor's objective.
