module DASHI.Environment.LatentEcologyRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Vec using ([]; _∷_)

import DASHI.Environment.FunctionalEcology as Eco
import DASHI.Environment.InversePlanning as Plan
import DASHI.Environment.LatentDepthFormalism as Latent
import DASHI.Foundations.SSPTritCarrier as SSP

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

sampleDepthState : Latent.DepthState three
sampleDepthState =
  SSP.sspNegOne ∷ SSP.sspZero ∷ SSP.sspPosOne ∷ []

sampleSelfAgreement :
  Latent.agreementDepth sampleDepthState sampleDepthState ≡ three
sampleSelfAgreement = Latent.selfAgreementIsDepth sampleDepthState

sampleSelfDistance :
  Latent.depthDistance sampleDepthState sampleDepthState ≡ zero
sampleSelfDistance = Latent.selfDistanceIsZero sampleDepthState

sampleCylinder : Latent.CylinderWitness sampleDepthState sampleDepthState
sampleCylinder = Latent.canonicalCylinderWitness sampleDepthState sampleDepthState

nativePollinatorGroup : Eco.FunctionalGroup
nativePollinatorGroup =
  Eco.mkFunctionalGroup
    "native pollinators"
    (Eco.pollinator ∷ [])

flowerResourceGroup : Eco.FunctionalGroup
flowerResourceGroup =
  Eco.mkFunctionalGroup
    "seasonally continuous flower resources"
    (Eco.producer ∷ Eco.habitatProvider ∷ [])

pollinatorContext : Eco.ContextGate
pollinatorContext =
  Eco.mkContextGate true true true true true true

flowerSupportsNativePollinators : Eco.Interaction
flowerSupportsNativePollinators =
  Eco.mkInteraction
    flowerResourceGroup
    nativePollinatorGroup
    SSP.sspPosOne
    pollinatorContext
    two
    "candidate interaction requiring local phenology and competition evidence"

pollinatorGuild : Eco.Guild
pollinatorGuild =
  Eco.mkGuild
    "native pollinator support guild"
    (flowerResourceGroup ∷ nativePollinatorGroup ∷ [])
    (flowerSupportsNativePollinators ∷ [])
    ("pollination service" ∷ "native-bee persistence" ∷ [])
    ("resource competition and predator response remain context-dependent" ∷ [])

amfCandidate : Eco.MycorrhizalCandidate
amfCandidate =
  Eco.mkMycorrhizalCandidate
    Eco.arbuscularMycorrhizal
    (flowerResourceGroup ∷ [])
    pollinatorContext
    true
    true
    two

amfCandidatePassesGate :
  Eco.mycorrhizalCandidateAdmissible amfCandidate ≡ true
amfCandidatePassesGate = refl

sampleIntervention : Eco.Intervention
sampleIntervention =
  Eco.mkIntervention
    "flowering cover and AMF-compatible host strip"
    Eco.planting
    (flowerResourceGroup ∷ nativePollinatorGroup ∷ [])
    (flowerSupportsNativePollinators ∷ [])
    two
    Latent.pathB-latent
    true

sampleObjective : Plan.Objective
sampleObjective =
  Plan.mkObjective
    "support pollination without net harm to native guilds"
    Plan.nativePollinatorProtection
    SSP.sspPosOne
    three
    true

sampleConstraint : Plan.Constraint
sampleConstraint =
  Plan.mkConstraint
    "local ecological review required"
    true
    true
    "candidate-only formal regression witness"

samplePlan : Plan.Plan
samplePlan =
  Plan.mkPlan
    "pollinator-support candidate"
    (sampleIntervention ∷ [])
    (sampleObjective ∷ [])
    (sampleConstraint ∷ [])
    Latent.pathB-latent
    one
    two
    one
    one

policyEscalation : Latent.EscalationEvidence
policyEscalation =
  Latent.mkEscalationEvidence false false false false true

policyEscalatesLatentToAuthority :
  Latent.chooseLane Latent.pathB-latent policyEscalation
  ≡ Latent.pathC-authoritative
policyEscalatesLatentToAuthority = refl

sampleScreeningReceipt : Plan.PlanningReceipt
sampleScreeningReceipt = Plan.canonicalScreeningReceipt samplePlan
