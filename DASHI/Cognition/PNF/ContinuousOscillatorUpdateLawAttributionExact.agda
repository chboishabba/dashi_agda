module DASHI.Cognition.PNF.ContinuousOscillatorUpdateLawAttributionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Cognition.PNF.ContinuousOscillatorIdentifiabilityReceipt as Ident
import DASHI.Cognition.PNF.LearningUpdateMechanismSeparationExact as Mechanism

------------------------------------------------------------------------
-- SOURCE-BOUND UPDATE-LAW CANDIDATES
--
-- The current synthetic producer uses explicit gradient updates.  Hebbian,
-- Oja, and Kuramoto language therefore remains candidate/comparator language
-- until an actual derivation establishes the relevant equation-level relation.
-- Citation or qualitative resemblance never creates mechanism identity.
------------------------------------------------------------------------

data OscillatorUpdateLawCandidate : Set where
  currentGradientCandidate
  hebbianCandidate
  ojaCandidate
  kuramotoCandidate : OscillatorUpdateLawCandidate

candidateReference : OscillatorUpdateLawCandidate → String
candidateReference currentGradientCandidate =
  "PR #909 explicit gradient descent on amplitude/phase/frequency parameters"
candidateReference hebbianCandidate =
  "Hebb 1949 historical synaptic-learning precedent"
candidateReference ojaCandidate =
  "Oja 1982 normalized linear principal-component learning rule"
candidateReference kuramotoCandidate =
  "Kuramoto 1984 coupled phase-oscillator dynamics"

------------------------------------------------------------------------
-- Primary attribution objects.
------------------------------------------------------------------------

hebbSource : Attribution.AttributedSource
hebbSource = Attribution.mkNoDOISource
  "Donald O. Hebb"
  "The Organization of Behavior: A Neuropsychological Theory"
  "John Wiley & Sons"
  "1949"
  "https://books.google.com/books?id=jvqMAAAAMAAJ"
  Attribution.academicBookSource
  "historical learning/synaptic-plasticity precedent only; does not specify the PR #909 gradient update and does not establish oscillator-memory mechanism identity"
  Attribution.publicAttribution

hebbSnowball : Snowball.SourceRoleSnowballReceipt hebbSource
hebbSnowball = Snowball.canonicalSourceRoleSnowballReceipt hebbSource

ojaSource : Attribution.AttributedSource
ojaSource = Attribution.mkDOISource
  "Erkki Oja"
  "A simplified neuron model as a principal component analyzer"
  "Journal of Mathematical Biology 15(3), 267-273"
  "1982"
  "10.1007/BF00275687"
  "https://doi.org/10.1007/BF00275687"
  Attribution.academicArticleSource
  "source for the Oja comparator family; does not establish that the DASHI oscillator gradient reduces to Oja dynamics"
  Attribution.publicAttribution

ojaSnowball : Snowball.SourceRoleSnowballReceipt ojaSource
ojaSnowball = Snowball.canonicalSourceRoleSnowballReceipt ojaSource

kuramotoSource : Attribution.AttributedSource
kuramotoSource = Attribution.mkDOISource
  "Yoshiki Kuramoto"
  "Chemical Oscillations, Waves, and Turbulence"
  "Springer Series in Synergetics, volume 19"
  "1984"
  "10.1007/978-3-642-69689-3"
  "https://doi.org/10.1007/978-3-642-69689-3"
  Attribution.academicBookSource
  "source for coupled phase-oscillator comparator dynamics; does not establish identity with the DASHI optimizer or with biological neural phase locking"
  Attribution.publicAttribution

kuramotoSnowball : Snowball.SourceRoleSnowballReceipt kuramotoSource
kuramotoSnowball = Snowball.canonicalSourceRoleSnowballReceipt kuramotoSource

updateLawSourceAtlas : Attribution.AttributedSourceAtlas
updateLawSourceAtlas = Attribution.mkSourceAtlas
  "continuous oscillator update-law comparator atlas"
  "DASHI.Cognition.PNF.ContinuousOscillatorUpdateLawAttributionExact"
  (hebbSource ∷ ojaSource ∷ kuramotoSource ∷ [])
  "historical/mathematical comparator sources only; each retains its formalisation role and non-promotion boundary"

------------------------------------------------------------------------
-- Comparison is witness-gated, not lexical.
------------------------------------------------------------------------

record UpdateLawComparisonReceipt
    (candidate : OscillatorUpdateLawCandidate) : Set where
  constructor update-law-comparison-receipt
  field
    derivationReference : String
    sameStateVariablesPaid : Bool
    sameTimeParameterisationPaid : Bool
    sameUpdateEquationPaid : Bool
    sameNormalizationPaid : Bool
    sameNoiseDriveBoundaryPaid : Bool
    exactReductionPaid : Bool
    empiricalMechanismIdentityPaid : Bool
open UpdateLawComparisonReceipt public

comparisonEligibleForExactReduction :
  ∀ {candidate} → UpdateLawComparisonReceipt candidate → Bool
comparisonEligibleForExactReduction receipt = exactReductionPaid receipt

------------------------------------------------------------------------
-- Cross-pollination retains the existing mechanism-separation lesson.
------------------------------------------------------------------------

existingMechanismSeparationBoundary : Mechanism.LearningUpdateMechanismBoundary
existingMechanismSeparationBoundary = Mechanism.canonicalLearningUpdateMechanismBoundary

identifiabilityConsumerRetained : Ident.OscillatorIdentifiabilityQuery
identifiabilityConsumerRetained = Ident.hiddenStateQuery

record OscillatorUpdateLawSourceBoundary : Set where
  constructor oscillator-update-law-source-boundary
  field
    attributedSourceCoreRetained : Bool
    snowballSourceRolesRetained : Bool
    hebbNoDOINotFabricated : Bool
    ojaDOIRetained : Bool
    kuramotoDOIRetained : Bool
    citationImportsProof : Bool
    citationCreatesAuthority : Bool
    comparatorSourceCreatesDashiAuthorship : Bool
open OscillatorUpdateLawSourceBoundary public

canonicalOscillatorUpdateLawSourceBoundary : OscillatorUpdateLawSourceBoundary
canonicalOscillatorUpdateLawSourceBoundary =
  oscillator-update-law-source-boundary
    true true true true true false false false

record OscillatorUpdateLawComparisonBoundary : Set where
  constructor oscillator-update-law-comparison-boundary
  field
    gradientEqualsHebbianByAnalogy : Bool
    gradientEqualsOjaByAnalogy : Bool
    gradientEqualsKuramotoByAnalogy : Bool
    sharedPhaseVariablesCreateKuramotoIdentity : Bool
    sharedLearningLanguageCreatesHebbianIdentity : Bool
    normalizationTermCreatesOjaIdentity : Bool
    exactReductionRequiresDerivation : Bool
    empiricalMechanismIdentityRequiresSeparateEvidence : Bool
    queryAdequacyStillRequiredDownstream : Bool
open OscillatorUpdateLawComparisonBoundary public

canonicalOscillatorUpdateLawComparisonBoundary :
  OscillatorUpdateLawComparisonBoundary
canonicalOscillatorUpdateLawComparisonBoundary =
  oscillator-update-law-comparison-boundary
    false false false false false false true true true
