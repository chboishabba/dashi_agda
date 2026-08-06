module DASHI.Physics.Foundations.ProbabilityDecoratedReebExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- A finite graph-like quotient of connected slice components.  This is a
-- discrete Reeb analogue, not a theorem about a smooth Morse function.

data ReebNode : Set where
  sourceComponent : ReebNode
  leftComponent : ReebNode
  rightComponent : ReebNode
  mergedComponent : ReebNode

data SliceStage : Set where
  beforeSplit : SliceStage
  afterSplit : SliceStage
  afterMerge : SliceStage

nodeStage : ReebNode → SliceStage
nodeStage sourceComponent = beforeSplit
nodeStage leftComponent = afterSplit
nodeStage rightComponent = afterSplit
nodeStage mergedComponent = afterMerge

data ReebEdge : Set where
  sourceToLeft : ReebEdge
  sourceToRight : ReebEdge
  leftToMerge : ReebEdge
  rightToMerge : ReebEdge

edgeSource : ReebEdge → ReebNode
edgeSource sourceToLeft = sourceComponent
edgeSource sourceToRight = sourceComponent
edgeSource leftToMerge = leftComponent
edgeSource rightToMerge = rightComponent

edgeTarget : ReebEdge → ReebNode
edgeTarget sourceToLeft = leftComponent
edgeTarget sourceToRight = rightComponent
edgeTarget leftToMerge = mergedComponent
edgeTarget rightToMerge = mergedComponent

------------------------------------------------------------------------
-- Stage-dependent probability mass in a fixed denominator-six scale.

massBefore : ReebNode → Nat
massBefore sourceComponent = 6
massBefore leftComponent = 0
massBefore rightComponent = 0
massBefore mergedComponent = 0

massSplit : ReebNode → Nat
massSplit sourceComponent = 0
massSplit leftComponent = 2
massSplit rightComponent = 4
massSplit mergedComponent = 0

massMerged : ReebNode → Nat
massMerged sourceComponent = 0
massMerged leftComponent = 0
massMerged rightComponent = 0
massMerged mergedComponent = 6

splitConservesMass :
  massBefore sourceComponent
  ≡
  massSplit leftComponent + massSplit rightComponent
splitConservesMass = refl

mergeConservesMass :
  massSplit leftComponent + massSplit rightComponent
  ≡
  massMerged mergedComponent
mergeConservesMass = refl

------------------------------------------------------------------------
-- Directed probability transport.  The two outgoing currents sum to the
-- source mass and the two incoming currents sum to the merged mass.

edgeCurrent : ReebEdge → Nat
edgeCurrent sourceToLeft = 2
edgeCurrent sourceToRight = 4
edgeCurrent leftToMerge = 2
edgeCurrent rightToMerge = 4

outgoingCurrentConserved :
  edgeCurrent sourceToLeft + edgeCurrent sourceToRight ≡ 6
outgoingCurrentConserved = refl

incomingCurrentConserved :
  edgeCurrent leftToMerge + edgeCurrent rightToMerge ≡ 6
incomingCurrentConserved = refl

------------------------------------------------------------------------
-- Transition semantics are typed separately from topology.  Every canonical
-- graph edge has a declared compatible semantic transition.

data DialecticalLabel : Set where
  undifferentiatedLabel : DialecticalLabel
  differentiatedLeftLabel : DialecticalLabel
  differentiatedRightLabel : DialecticalLabel
  recomposedLabel : DialecticalLabel

nodeLabel : ReebNode → DialecticalLabel
nodeLabel sourceComponent = undifferentiatedLabel
nodeLabel leftComponent = differentiatedLeftLabel
nodeLabel rightComponent = differentiatedRightLabel
nodeLabel mergedComponent = recomposedLabel

data CompatibleTransition : DialecticalLabel → DialecticalLabel → Set where
  differentiateLeft :
    CompatibleTransition undifferentiatedLabel differentiatedLeftLabel
  differentiateRight :
    CompatibleTransition undifferentiatedLabel differentiatedRightLabel
  recomposeLeft :
    CompatibleTransition differentiatedLeftLabel recomposedLabel
  recomposeRight :
    CompatibleTransition differentiatedRightLabel recomposedLabel

canonicalEdgeIsSemanticallyCompatible :
  (edge : ReebEdge) →
  CompatibleTransition
    (nodeLabel (edgeSource edge))
    (nodeLabel (edgeTarget edge))
canonicalEdgeIsSemanticallyCompatible sourceToLeft = differentiateLeft
canonicalEdgeIsSemanticallyCompatible sourceToRight = differentiateRight
canonicalEdgeIsSemanticallyCompatible leftToMerge = recomposeLeft
canonicalEdgeIsSemanticallyCompatible rightToMerge = recomposeRight

------------------------------------------------------------------------
-- A merge is called preserving only after explicit embeddings retain the two
-- incoming features.

data Feature : Set where
  leftFeature : Feature
  rightFeature : Feature

data IncomingComponent : Set where
  incomingLeft : IncomingComponent
  incomingRight : IncomingComponent

incomingFeature : IncomingComponent → Feature
incomingFeature incomingLeft = leftFeature
incomingFeature incomingRight = rightFeature

embedIntoMerge : IncomingComponent → Feature
embedIntoMerge incomingLeft = leftFeature
embedIntoMerge incomingRight = rightFeature

mergePreservesIncomingFeature :
  (component : IncomingComponent) →
  embedIntoMerge component ≡ incomingFeature component
mergePreservesIncomingFeature incomingLeft = refl
mergePreservesIncomingFeature incomingRight = refl

------------------------------------------------------------------------
-- Finite MDL comparison.  Extra topological depth is selected here because
-- the residual reduction exceeds the extra model description cost in the
-- declared table.

data ReebModel : Set where
  shallowReebModel : ReebModel
  splitMergeReebModel : ReebModel

modelCodeLength : ReebModel → Nat
modelCodeLength shallowReebModel = 3
modelCodeLength splitMergeReebModel = 5

residualCodeLength : ReebModel → Nat
residualCodeLength shallowReebModel = 7
residualCodeLength splitMergeReebModel = 2

totalDescriptionLength : ReebModel → Nat
totalDescriptionLength model =
  modelCodeLength model + residualCodeLength model

selectedReebModel : ReebModel
selectedReebModel = splitMergeReebModel

shallowTotalIsTen :
  totalDescriptionLength shallowReebModel ≡ 10
shallowTotalIsTen = refl

selectedTotalIsSeven :
  totalDescriptionLength selectedReebModel ≡ 7
selectedTotalIsSeven = refl

residualSavingIsFive :
  residualCodeLength shallowReebModel
  ≡
  residualCodeLength splitMergeReebModel + 5
residualSavingIsFive = refl

extraModelCostIsTwo :
  modelCodeLength splitMergeReebModel
  ≡
  modelCodeLength shallowReebModel + 2
extraModelCostIsTwo = refl

record ProbabilityDecoratedReebBoundary : Set where
  constructor probabilityDecoratedReebBoundary
  field
    finiteGraphIsAutomaticallySmoothReebSpace : Bool
    finiteGraphIsAutomaticallySmoothReebSpaceIsFalse :
      finiteGraphIsAutomaticallySmoothReebSpace ≡ false

    mergeTopologyAutomaticallyProvesDialecticalSynthesis : Bool
    mergeTopologyAutomaticallyProvesDialecticalSynthesisIsFalse :
      mergeTopologyAutomaticallyProvesDialecticalSynthesis ≡ false

    probabilityMassIsQuantumAmplitude : Bool
    probabilityMassIsQuantumAmplitudeIsFalse :
      probabilityMassIsQuantumAmplitude ≡ false

    threeSixNineThresholdsAreForcedByReebTopology : Bool
    threeSixNineThresholdsAreForcedByReebTopologyIsFalse :
      threeSixNineThresholdsAreForcedByReebTopology ≡ false

open ProbabilityDecoratedReebBoundary public

canonicalProbabilityDecoratedReebBoundary : ProbabilityDecoratedReebBoundary
canonicalProbabilityDecoratedReebBoundary =
  probabilityDecoratedReebBoundary
    false refl
    false refl
    false refl
    false refl
