module DASHI.ComputerScience.SelfReferenceLimitsNamedPhenomenaBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NAMED SELF-REFERENCE / LIMIT / DECISION-THEORY PHENOMENA
--
-- This is a taxonomy/bridge only.  It deliberately does not turn analogy into
-- theorem implication.  The purpose is to keep commonly conflated named
-- results in distinct typed families before later source/formal owners are
-- attached.
------------------------------------------------------------------------

data PhenomenonFamily : Set where
  firstOrderSemanticCompleteness : PhenomenonFamily
  arithmeticIncompleteness : PhenomenonFamily
  computabilityUndecidability : PhenomenonFamily
  fixedPointSelfReference : PhenomenonFamily
  semanticParadox : PhenomenonFamily
  proofLogicSelfReference : PhenomenonFamily
  decisionTheoryThoughtExperiment : PhenomenonFamily
  informationHazardThoughtExperiment : PhenomenonFamily
  complexityGrowthLimit : PhenomenonFamily

data NamedPhenomenon : Set where
  godelCompleteness : NamedPhenomenon
  godelFirstIncompleteness : NamedPhenomenon
  godelSecondIncompleteness : NamedPhenomenon
  diagonalLemma : NamedPhenomenon
  turingHaltingProblem : NamedPhenomenon
  riceTheorem : NamedPhenomenon
  busyBeaver : NamedPhenomenon
  loebTheorem : NamedPhenomenon
  liarParadox : NamedPhenomenon
  curryParadox : NamedPhenomenon
  berryParadox : NamedPhenomenon
  rokoBasilisk : NamedPhenomenon

family : NamedPhenomenon → PhenomenonFamily
family godelCompleteness = firstOrderSemanticCompleteness
family godelFirstIncompleteness = arithmeticIncompleteness
family godelSecondIncompleteness = arithmeticIncompleteness
family diagonalLemma = fixedPointSelfReference
family turingHaltingProblem = computabilityUndecidability
family riceTheorem = computabilityUndecidability
family busyBeaver = complexityGrowthLimit
family loebTheorem = proofLogicSelfReference
family liarParadox = semanticParadox
family curryParadox = semanticParadox
family berryParadox = semanticParadox
family rokoBasilisk = decisionTheoryThoughtExperiment

data RelationStrength : Set where
  exactTheoremDependency : RelationStrength
  sharedConstructionPattern : RelationStrength
  conceptualAnalogyOnly : RelationStrength
  noImplicationRecorded : RelationStrength

-- Curated relations relevant to the current CS/factor-verifier programme.
-- These are intentionally weak unless an actual theorem dependency is owned.

factorVerificationVsDiscoveryToGodel : RelationStrength
factorVerificationVsDiscoveryToGodel = conceptualAnalogyOnly

factorVerificationVsDiscoveryToHalting : RelationStrength
factorVerificationVsDiscoveryToHalting = conceptualAnalogyOnly

selfReferenceToDiagonalLemma : RelationStrength
selfReferenceToDiagonalLemma = sharedConstructionPattern

rokoBasiliskToGodelIncompleteness : RelationStrength
rokoBasiliskToGodelIncompleteness = noImplicationRecorded

rokoBasiliskToDecisionTheory : RelationStrength
rokoBasiliskToDecisionTheory = sharedConstructionPattern

------------------------------------------------------------------------
-- The distinctions that matter most for downstream consumers.
------------------------------------------------------------------------

data CompletenessEqualsIncompleteness : Set where
data VerificationEqualsDiscovery : Set where
data SelfReferenceImpliesUndecidability : Set where
data ThoughtExperimentImpliesMathematicalTheorem : Set where

completenessIsNotIncompleteness : CompletenessEqualsIncompleteness → ⊥
completenessIsNotIncompleteness ()

verificationDoesNotCollapseToDiscovery : VerificationEqualsDiscovery → ⊥
verificationDoesNotCollapseToDiscovery ()

selfReferenceAloneDoesNotYieldUndecidability : SelfReferenceImpliesUndecidability → ⊥
selfReferenceAloneDoesNotYieldUndecidability ()

thoughtExperimentDoesNotBecomeTheoremByAnalogy :
  ThoughtExperimentImpliesMathematicalTheorem → ⊥
thoughtExperimentDoesNotBecomeTheoremByAnalogy ()

record NamedPhenomenaBoundary : Set where
  constructor namedPhenomenaBoundary
  field
    completenessAndIncompletenessDistinct : Bool
    theoremAndThoughtExperimentDistinct : Bool
    selfReferenceAndUndecidabilityDistinct : Bool
    verificationAndDiscoveryDistinct : Bool
    rokoBasiliskClassifiedAsDecisionTheoryThoughtExperiment : Bool
    rokoBasiliskClaimedAsGodelConsequence : Bool
    fullFormalTheoremsConstructedHere : Bool

canonicalNamedPhenomenaBoundary : NamedPhenomenaBoundary
canonicalNamedPhenomenaBoundary =
  namedPhenomenaBoundary true true true true true false false

phenomenonLabel : NamedPhenomenon → String
phenomenonLabel godelCompleteness = "Goedel completeness theorem"
phenomenonLabel godelFirstIncompleteness = "Goedel first incompleteness theorem"
phenomenonLabel godelSecondIncompleteness = "Goedel second incompleteness theorem"
phenomenonLabel diagonalLemma = "diagonal/fixed-point lemma"
phenomenonLabel turingHaltingProblem = "Turing halting problem"
phenomenonLabel riceTheorem = "Rice theorem"
phenomenonLabel busyBeaver = "Busy Beaver"
phenomenonLabel loebTheorem = "Loeb theorem"
phenomenonLabel liarParadox = "liar paradox"
phenomenonLabel curryParadox = "Curry paradox"
phenomenonLabel berryParadox = "Berry paradox"
phenomenonLabel rokoBasilisk = "Roko's Basilisk"
