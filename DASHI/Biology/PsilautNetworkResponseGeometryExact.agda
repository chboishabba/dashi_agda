module DASHI.Biology.PsilautNetworkResponseGeometryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥; ¬_)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ContrastiveInterventionResponseExact as Response

------------------------------------------------------------------------
-- PRIMARY PREPRINT
--
-- Tobias P. Whelan; Mihail Dimitrov; Lucas G.S. França; Claire L. Ellis;
-- Francesca Moruzzi; Francesca M. Ponteduro; Johanna Kangas; Nermin Khalil;
-- Yan Ge; Naoise Mulcrone; Glynis Ivin; Dafnis Batallé; Eileen Daly;
-- Ekaterina Malievskaia; Nicolaas A. Puts; Declan G.M. Murphy;
-- Gráinne M. McAlonan (2026),
-- "Distinct response of resting-state brain networks to psilocybin in autism"
-- medRxiv 2026.08.19.26360794.
-- DOI: 10.64898/2026.08.19.26360794
-- Posted 22 August 2026.  Preprint; not peer reviewed at this source version.
--
-- PROTOCOL / MOTIVATION SOURCE
--
-- Tobias P. Whelan et al. (2024),
-- "The 'PSILAUT' protocol: an experimental medicine study of autistic
-- differences in the function of brain serotonin targets of psilocybin",
-- BMC Psychiatry 24:319.
-- DOI: 10.1186/s12888-024-05768-2
--
-- The protocol explicitly motivates a "shiftability" design: experimentally
-- perturb serotonergic targets (principally but not exclusively 5-HT2A-linked
-- pathways) and measure whether neural function shifts differently in autistic
-- and non-autistic adults, rather than relying only on baseline association.
--
-- This module formalizes the group-summary observer logic of the reported
-- resting-state fMRI result.  It does NOT turn group statistics into an
-- individual deterministic law and does NOT identify fMRI functional
-- connectivity with anatomical/synaptic connectivity.
------------------------------------------------------------------------

record SourceAttribution : Set where
  constructor sourceAttribution
  field
    authors : List String
    title : String
    venue : String
    year : Nat
    doi : String
    status : String

open SourceAttribution public

preprintSource : SourceAttribution
preprintSource =
  sourceAttribution
    ("Tobias P. Whelan" ∷
     "Mihail Dimitrov" ∷
     "Lucas G.S. França" ∷
     "Claire L. Ellis" ∷
     "Francesca Moruzzi" ∷
     "Francesca M. Ponteduro" ∷
     "Johanna Kangas" ∷
     "Nermin Khalil" ∷
     "Yan Ge" ∷
     "Naoise Mulcrone" ∷
     "Glynis Ivin" ∷
     "Dafnis Batallé" ∷
     "Eileen Daly" ∷
     "Ekaterina Malievskaia" ∷
     "Nicolaas A. Puts" ∷
     "Declan G.M. Murphy" ∷
     "Gráinne M. McAlonan" ∷ [])
    "Distinct response of resting-state brain networks to psilocybin in autism"
    "medRxiv 2026.08.19.26360794"
    2026
    "10.64898/2026.08.19.26360794"
    "preprint"

protocolSource : SourceAttribution
protocolSource =
  sourceAttribution
    ("Tobias P. Whelan" ∷
     "Eileen Daly" ∷
     "Nicolaas A. Puts" ∷
     "Paula Smith" ∷
     "Carrie Allison" ∷
     "Simon Baron-Cohen" ∷
     "Ekaterina Malievskaia" ∷
     "Declan G.M. Murphy" ∷
     "Gráinne M. McAlonan" ∷ [])
    "The 'PSILAUT' protocol: an experimental medicine study of autistic differences in the function of brain serotonin targets of psilocybin"
    "BMC Psychiatry 24:319"
    2024
    "10.1186/s12888-024-05768-2"
    "peer-reviewed protocol"

------------------------------------------------------------------------
-- Finite group-summary carrier.
--
-- The paper reports no group differences in the baseline placebo network
-- connectivity measures under study, then opposite-direction 5 mg shifts for
-- DMN-FPN and DAN-VAN between-network connectivity.  The equal placebo value
-- below is therefore a GROUP-SUMMARY abstraction of that result, not a claim
-- that every autistic and non-autistic participant had identical baselines.
------------------------------------------------------------------------

data DiagnosticGroup : Set where
  autisticGroup nonAutisticGroup : DiagnosticGroup

data Dose : Set where
  placebo twoMg fiveMg : Dose

data NetworkPair : Set where
  defaultModeFrontoparietal dorsalVentralAttention : NetworkPair

data ConnectivitySummary : Set where
  referenceLevel relativeIncrease relativeDecrease effectNotPromoted : ConnectivitySummary

summaryConnectivity : DiagnosticGroup → Dose → NetworkPair → ConnectivitySummary
summaryConnectivity group placebo pair = referenceLevel
summaryConnectivity group twoMg pair = effectNotPromoted
summaryConnectivity autisticGroup fiveMg pair = relativeIncrease
summaryConnectivity nonAutisticGroup fiveMg pair = relativeDecrease

record GroupSummaryState : Set where
  constructor groupSummaryState
  field
    group : DiagnosticGroup
    networkPair : NetworkPair
    condition : Dose

open GroupSummaryState public

applyDose : Dose → GroupSummaryState → GroupSummaryState
applyDose dose (groupSummaryState group pair oldDose) =
  groupSummaryState group pair dose

observeConnectivity : GroupSummaryState → ConnectivitySummary
observeConnectivity (groupSummaryState group pair dose) =
  summaryConnectivity group dose pair

------------------------------------------------------------------------
-- Response contrast.
------------------------------------------------------------------------

data ConnectivityShift : Set where
  noShift shiftUp shiftDown unresolvedShift : ConnectivityShift

connectivityContrast : ConnectivitySummary → ConnectivitySummary → ConnectivityShift
connectivityContrast referenceLevel referenceLevel = noShift
connectivityContrast referenceLevel relativeIncrease = shiftUp
connectivityContrast referenceLevel relativeDecrease = shiftDown
connectivityContrast referenceLevel effectNotPromoted = unresolvedShift
connectivityContrast otherBaseline otherPost = unresolvedShift

fiveMgResponse : GroupSummaryState → ConnectivityShift
fiveMgResponse state =
  Response.ContrastiveInterventionResponse
    observeConnectivity applyDose placebo connectivityContrast state fiveMg

baselineConnectivityObserver : GroupSummaryState → ConnectivitySummary
baselineConnectivityObserver =
  Response.baselineObserver observeConnectivity applyDose placebo

------------------------------------------------------------------------
-- DMN <-> frontoparietal witness.
------------------------------------------------------------------------

autisticDMNSummary : GroupSummaryState
autisticDMNSummary =
  groupSummaryState autisticGroup defaultModeFrontoparietal placebo

nonAutisticDMNSummary : GroupSummaryState
nonAutisticDMNSummary =
  groupSummaryState nonAutisticGroup defaultModeFrontoparietal placebo

dmnSameBaselineSummary :
  baselineConnectivityObserver autisticDMNSummary
    ≡ baselineConnectivityObserver nonAutisticDMNSummary
dmnSameBaselineSummary = refl

dmnFiveMgResponsesDiffer :
  fiveMgResponse autisticDMNSummary
    ≡ fiveMgResponse nonAutisticDMNSummary → ⊥
dmnFiveMgResponsesDiffer ()

dmnResponseStrictlyRefinesBaselineSummary :
  Observer.StrictRefinement
    baselineConnectivityObserver
    (Response.baselineAndResponseObserver
      observeConnectivity applyDose placebo connectivityContrast fiveMg)
dmnResponseStrictlyRefinesBaselineSummary =
  Response.responseCollisionGivesStrictBaselineRefinement
    observeConnectivity
    applyDose
    placebo
    connectivityContrast
    fiveMg
    autisticDMNSummary
    nonAutisticDMNSummary
    dmnSameBaselineSummary
    dmnFiveMgResponsesDiffer

dmnFiveMgResponseCannotDescendThroughBaselineSummary :
  ¬ Response.ResponseDescendsThroughBaseline
      observeConnectivity applyDose placebo connectivityContrast fiveMg
dmnFiveMgResponseCannotDescendThroughBaselineSummary descent =
  Response.responseCollisionBlocksBaselineDescent
    dmnSameBaselineSummary
    dmnFiveMgResponsesDiffer
    descent

------------------------------------------------------------------------
-- DAN <-> VAN witness.
------------------------------------------------------------------------

autisticAttentionSummary : GroupSummaryState
autisticAttentionSummary =
  groupSummaryState autisticGroup dorsalVentralAttention placebo

nonAutisticAttentionSummary : GroupSummaryState
nonAutisticAttentionSummary =
  groupSummaryState nonAutisticGroup dorsalVentralAttention placebo

attentionSameBaselineSummary :
  baselineConnectivityObserver autisticAttentionSummary
    ≡ baselineConnectivityObserver nonAutisticAttentionSummary
attentionSameBaselineSummary = refl

attentionFiveMgResponsesDiffer :
  fiveMgResponse autisticAttentionSummary
    ≡ fiveMgResponse nonAutisticAttentionSummary → ⊥
attentionFiveMgResponsesDiffer ()

attentionFiveMgResponseCannotDescendThroughBaselineSummary :
  ¬ Response.ResponseDescendsThroughBaseline
      observeConnectivity applyDose placebo connectivityContrast fiveMg
attentionFiveMgResponseCannotDescendThroughBaselineSummary descent =
  Response.responseCollisionBlocksBaselineDescent
    attentionSameBaselineSummary
    attentionFiveMgResponsesDiffer
    descent

------------------------------------------------------------------------
-- Statistical association evidence is represented as evidence metadata, not
-- as a pointwise monotonic theorem over people.
------------------------------------------------------------------------

data AssociationDirection : Set where
  positiveAssociation : AssociationDirection

record ReportedAssociation : Set where
  constructor reportedAssociation
  field
    measure : String
    responseDomain : String
    beta : String
    tStatistic : String
    fdrP : String
    direction : AssociationDirection
    pointwiseMonotonicLawClaimed : Bool
    pointwiseMonotonicLawClaimedIsFalse :
      pointwiseMonotonicLawClaimed ≡ false

open ReportedAssociation public

higherOrderTraitAssociation : ReportedAssociation
higherOrderTraitAssociation =
  reportedAssociation
    "Autism Quotient"
    "psilocybin-induced connectivity increase between higher-order networks"
    "0.33"
    "2.16"
    "0.036"
    positiveAssociation
    false refl

attentionTraitAssociation : ReportedAssociation
attentionTraitAssociation =
  reportedAssociation
    "Autism Quotient"
    "psilocybin-induced connectivity increase between attentional networks"
    "0.36"
    "2.43"
    "0.036"
    positiveAssociation
    false refl

------------------------------------------------------------------------
-- Reported design/result ledger and fail-closed scope.
------------------------------------------------------------------------

record PsilautClaimBoundary : Set where
  constructor psilautClaimBoundary
  field
    crossoverDoubleBlindLowDoseDesignReported : Bool
    crossoverDoubleBlindLowDoseDesignReportedIsTrue :
      crossoverDoubleBlindLowDoseDesignReported ≡ true

    participantsSixtySevenReported : Bool
    participantsSixtySevenReportedIsTrue :
      participantsSixtySevenReported ≡ true

    fiveMgOppositeDirectionNetworkInteractionsReported : Bool
    fiveMgOppositeDirectionNetworkInteractionsReportedIsTrue :
      fiveMgOppositeDirectionNetworkInteractionsReported ≡ true

    traitResponsePositiveAssociationsReported : Bool
    traitResponsePositiveAssociationsReportedIsTrue :
      traitResponsePositiveAssociationsReported ≡ true

    clinicalEfficacyEvaluated : Bool
    clinicalEfficacyEvaluatedIsFalse :
      clinicalEfficacyEvaluated ≡ false

    increasedConnectivityMeansBetterBrain : Bool
    increasedConnectivityMeansBetterBrainIsFalse :
      increasedConnectivityMeansBetterBrain ≡ false

    fMRIConnectivityIsAnatomicalSynapticConnectivity : Bool
    fMRIConnectivityIsAnatomicalSynapticConnectivityIsFalse :
      fMRIConnectivityIsAnatomicalSynapticConnectivity ≡ false

    groupAverageResponseIsDeterministicIndividualLaw : Bool
    groupAverageResponseIsDeterministicIndividualLawIsFalse :
      groupAverageResponseIsDeterministicIndividualLaw ≡ false

    psilocybinIsPerfectlySpecificTo5HT2A : Bool
    psilocybinIsPerfectlySpecificTo5HT2AIsFalse :
      psilocybinIsPerfectlySpecificTo5HT2A ≡ false

    preprintPeerReviewedAtSourceVersion : Bool
    preprintPeerReviewedAtSourceVersionIsFalse :
      preprintPeerReviewedAtSourceVersion ≡ false

canonicalPsilautClaimBoundary : PsilautClaimBoundary
canonicalPsilautClaimBoundary =
  psilautClaimBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
