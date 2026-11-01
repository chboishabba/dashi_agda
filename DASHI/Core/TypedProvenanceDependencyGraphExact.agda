module DASHI.Core.TypedProvenanceDependencyGraphExact where

------------------------------------------------------------------------
-- TYPED PROVENANCE DEPENDENCY GRAPH
--
-- A dependency edge records what a source/module contributes.  Source-family
-- counts are descriptive provenance load only; they are not confidence, truth,
-- authority or ownership percentages.
--
-- The source metadata carrier is reused from AttributedSourceCore rather than
-- replaced by another bibliography schema.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr

------------------------------------------------------------------------
-- Provenance families and edge roles.
------------------------------------------------------------------------

data ProvenanceFamily : Set where
  dashiFormal : ProvenanceFamily
  wikidataData : ProvenanceFamily
  jmdLeanFormal : ProvenanceFamily
  bfoOntology : ProvenanceFamily
  scholarlyLiterature : ProvenanceFamily
  empiricalDataset : ProvenanceFamily
  computedWitness : ProvenanceFamily
  communityCulturalSource : ProvenanceFamily
  runtimeAcquisition : ProvenanceFamily
  otherNamedFamily : String → ProvenanceFamily

data DependencyRole : Set where
  definitionRole : DependencyRole
  theoremRole : DependencyRole
  evidenceRole : DependencyRole
  vocabularyRole : DependencyRole
  projectionRole : DependencyRole
  reconstructionRole : DependencyRole
  residualRole : DependencyRole
  rechartRole : DependencyRole
  counterexampleRole : DependencyRole
  alignmentRole : DependencyRole
  acquisitionRole : DependencyRole
  authorityBoundaryRole : DependencyRole
  validationRole : DependencyRole
  historicalMotivationRole : DependencyRole

record DependencyNode : Set where
  constructor dependencyNode
  field
    nodeLabel : String
    nodeFamily : ProvenanceFamily
    relationship : String
    createsTruthAuthority : Bool

open DependencyNode public

record DependencyEdge : Set where
  constructor dependencyEdge
  field
    sourceNode : DependencyNode
    targetNode : DependencyNode
    role : DependencyRole
    requiredForTarget : Bool
    edgeNote : String

open DependencyEdge public

record TypedDependencyGraph : Set where
  constructor typedDependencyGraph
  field
    graphLabel : String
    nodes : List DependencyNode
    edges : List DependencyEdge

open TypedDependencyGraph public

------------------------------------------------------------------------
-- Literature citation edges keep the canonical AttributedSource object.
------------------------------------------------------------------------

record AttributedDependency : Set where
  constructor attributedDependency
  field
    source : Attr.AttributedSource
    target : DependencyNode
    role : DependencyRole
    requiredForTarget : Bool
    dependencyNote : String

open AttributedDependency public

attributedDependencyCannotImportProofByCitation :
  (dependency : AttributedDependency) →
  Attr.citationImportsProof (source dependency) ≡ false
attributedDependencyCannotImportProofByCitation dependency =
  Attr.citationImportsProofIsFalse (source dependency)

attributedDependencyCannotCreateAuthorityByCitation :
  (dependency : AttributedDependency) →
  Attr.citationCreatesAuthority (source dependency) ≡ false
attributedDependencyCannotCreateAuthorityByCitation dependency =
  Attr.citationCreatesAuthorityIsFalse (source dependency)

------------------------------------------------------------------------
-- Count descriptive provenance load by family.
------------------------------------------------------------------------

sameFamily : ProvenanceFamily → ProvenanceFamily → Bool
sameFamily dashiFormal dashiFormal = true
sameFamily wikidataData wikidataData = true
sameFamily jmdLeanFormal jmdLeanFormal = true
sameFamily bfoOntology bfoOntology = true
sameFamily scholarlyLiterature scholarlyLiterature = true
sameFamily empiricalDataset empiricalDataset = true
sameFamily computedWitness computedWitness = true
sameFamily communityCulturalSource communityCulturalSource = true
sameFamily runtimeAcquisition runtimeAcquisition = true
sameFamily (otherNamedFamily left) (otherNamedFamily right) = false
sameFamily _ _ = false

familyNodeCount : ProvenanceFamily → List DependencyNode → Nat
familyNodeCount family [] = 0
familyNodeCount family (node ∷ rest) with sameFamily family (nodeFamily node)
... | true = suc (familyNodeCount family rest)
... | false = familyNodeCount family rest

nodeCount : List DependencyNode → Nat
nodeCount [] = 0
nodeCount (_ ∷ rest) = suc (nodeCount rest)

edgeCount : List DependencyEdge → Nat
edgeCount [] = 0
edgeCount (_ ∷ rest) = suc (edgeCount rest)

record ProvenanceLoadSummary : Set where
  constructor provenanceLoadSummary
  field
    totalNodes : Nat
    totalEdges : Nat
    dashiNodes : Nat
    wikidataNodes : Nat
    jmdLeanNodes : Nat
    bfoNodes : Nat
    literatureNodes : Nat
    empiricalNodes : Nat
    computedNodes : Nat
    culturalNodes : Nat
    runtimeNodes : Nat

open ProvenanceLoadSummary public

summarizeProvenanceLoad : TypedDependencyGraph → ProvenanceLoadSummary
summarizeProvenanceLoad graph =
  provenanceLoadSummary
    (nodeCount (nodes graph))
    (edgeCount (edges graph))
    (familyNodeCount dashiFormal (nodes graph))
    (familyNodeCount wikidataData (nodes graph))
    (familyNodeCount jmdLeanFormal (nodes graph))
    (familyNodeCount bfoOntology (nodes graph))
    (familyNodeCount scholarlyLiterature (nodes graph))
    (familyNodeCount empiricalDataset (nodes graph))
    (familyNodeCount computedWitness (nodes graph))
    (familyNodeCount communityCulturalSource (nodes graph))
    (familyNodeCount runtimeAcquisition (nodes graph))

------------------------------------------------------------------------
-- Explicit anti-percentage boundary.
------------------------------------------------------------------------

data SourceShareCreatesTruthPercentagePermission : Set where

sourceCountsCannotBecomeTruthPercentages :
  SourceShareCreatesTruthPercentagePermission → ⊥
sourceCountsCannotBecomeTruthPercentages ()

record TypedProvenanceDependencyBoundary : Set where
  constructor typedProvenanceDependencyBoundary
  field
    sourceCountIsTruthWeight : Bool
    citationImportsProof : Bool
    dependencyRoleEqualsSourceFamily : Bool
    graphCanExposeRequiredDependencies : Bool
    graphCanExposeSourceFamilies : Bool

canonicalTypedProvenanceDependencyBoundary :
  TypedProvenanceDependencyBoundary
canonicalTypedProvenanceDependencyBoundary =
  typedProvenanceDependencyBoundary false false false true true
