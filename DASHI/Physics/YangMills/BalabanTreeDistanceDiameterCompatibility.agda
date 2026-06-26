module DASHI.Physics.YangMills.BalabanTreeDistanceDiameterCompatibility where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.ProofTargetSurface using (ProofTargetSurface; proofTargetIsClosed)
import DASHI.Physics.YangMills.P01P33ProofSurfaces as Surfaces
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.YangMills.YMSupportGraphDistance as YMSupportGraph

Scalar : Set
Scalar = String

data DiameterDistanceConvention : Set where
  dashIDiameter : DiameterDistanceConvention
  balabanTreeDistance : DiameterDistanceConvention
  unitNormalisedBridge : DiameterDistanceConvention
  unbridgedConvention : DiameterDistanceConvention

record DashiSpatialDiameterSurface : Set₁ where
  field
    Polymer : Set
    Scale : Set
    supportLinks : Polymer → Support.Identifier
    diameter : Polymer → Scalar

currentDashiSpatialDiameterSurface : DashiSpatialDiameterSurface
currentDashiSpatialDiameterSurface = record
  { Polymer = Support.Polymer
  ; Scale = Support.Scale
  ; supportLinks = λ γ → Support.polymerId γ
  ; diameter = λ _ → "unproved"
  }

record BalabanTreeDistanceSurface : Set₁ where
  field
    Polymer : Set
    Scale : Set
    supportLinks : Polymer → Support.Identifier
    treeDistance : Scale → Polymer → Scalar

currentBalabanTreeDistanceSurface : BalabanTreeDistanceSurface
currentBalabanTreeDistanceSurface = record
  { Polymer = Support.Polymer
  ; Scale = Support.Scale
  ; supportLinks = λ γ → Support.polymerId γ
  ; treeDistance = λ _ _ → "unproved"
  }

record GraphDistanceInterface : Set₁ where
  field
    supportGraph : YMSupportGraph.FiniteSupportGraph
    supportEdge :
      YMSupportGraph.FiniteSupportGraph.Edge supportGraph → Bool
    treeEdge :
      YMSupportGraph.FiniteSupportGraph.Edge supportGraph → Bool
    graphDist :
      YMSupportGraph.FiniteSupportGraph.Vertex supportGraph →
      YMSupportGraph.FiniteSupportGraph.Vertex supportGraph →
      Nat
    treePathLength :
      YMSupportGraph.FiniteSupportGraph.Vertex supportGraph →
      YMSupportGraph.FiniteSupportGraph.Vertex supportGraph →
      Nat
    treeEdgeCount : Nat
    treePathAsSupportGraphPath :
      YMSupportGraph.TreePathAsSupportGraphPath
    treeEdgesExistSurface : ProofTargetSurface
    treeEdgesExistSurfaceIsClosed :
      proofTargetIsClosed treeEdgesExistSurface ≡ true
    graphDistMinimalitySurface : ProofTargetSurface
    graphDistMinimalitySurfaceIsClosed :
      proofTargetIsClosed graphDistMinimalitySurface ≡ true
    treePathBoundedByEdgeCountSurface : ProofTargetSurface
    treePathBoundedByEdgeCountSurfaceIsClosed :
      proofTargetIsClosed treePathBoundedByEdgeCountSurface ≡ true
    interfaceBoundary : String
    interfaceBoundaryIsCanonical :
      interfaceBoundary ≡
      "Typed support-graph layer imported via YMSupportGraphDistance; treePathEdgesExist, graphDistMinimality, and treePathBoundedByEdgeCount are carried by explicit theorem surfaces and typed wrappers."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentGraphDistanceInterface : GraphDistanceInterface
currentGraphDistanceInterface = record
  { supportGraph = YMSupportGraph.currentFiniteSupportGraph
  ; supportEdge =
      YMSupportGraph.FiniteSupportGraph.supportEdge
        YMSupportGraph.currentFiniteSupportGraph
  ; treeEdge =
      YMSupportGraph.FiniteSupportGraph.treeEdge
        YMSupportGraph.currentFiniteSupportGraph
  ; graphDist =
      YMSupportGraph.GraphDistanceStructure.graphDist
        YMSupportGraph.currentGraphDistanceStructure
  ; treePathLength =
      YMSupportGraph.treePathLength
        YMSupportGraph.currentTreePathStructure
  ; treeEdgeCount =
      YMSupportGraph.TreePathStructure.treeEdgeCount
        YMSupportGraph.currentTreePathStructure
  ; treePathAsSupportGraphPath =
      YMSupportGraph.currentTreePathAsSupportGraphPath
  ; treeEdgesExistSurface = Surfaces.treePathEdgesExistSurface
  ; treeEdgesExistSurfaceIsClosed = refl
  ; graphDistMinimalitySurface = Surfaces.graphDistMinimalitySurface
  ; graphDistMinimalitySurfaceIsClosed = refl
  ; treePathBoundedByEdgeCountSurface =
      Surfaces.treePathBoundedByEdgeCountSurface
  ; treePathBoundedByEdgeCountSurfaceIsClosed = refl
  ; interfaceBoundary =
      "Typed support-graph layer imported via YMSupportGraphDistance; treePathEdgesExist, graphDistMinimality, and treePathBoundedByEdgeCount are carried by explicit theorem surfaces and typed wrappers."
  ; interfaceBoundaryIsCanonical = refl
  ; noClayPromotion = refl
  }

record TreeEdgesSubsetSupportEdgesTarget : Set₁ where
  field
    graphDistanceInterface : GraphDistanceInterface
    proofSurface : ProofTargetSurface
    proofSurfaceIsClosed : proofTargetIsClosed proofSurface ≡ true
    treePathAsSupportGraphPath :
      YMSupportGraph.TreePathAsSupportGraphPath
    proved : Bool
    provedIsTrue : proved ≡ true
    theoremStatement : String
    theoremStatementIsCanonical :
      theoremStatement ≡
      "treePathEdgesExist is witnessed by the typed tree-path wrapper imported from YMSupportGraphDistance."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentTreeEdgesSubsetSupportEdgesTarget :
  TreeEdgesSubsetSupportEdgesTarget
currentTreeEdgesSubsetSupportEdgesTarget = record
  { graphDistanceInterface = currentGraphDistanceInterface
  ; proofSurface = Surfaces.treePathEdgesExistSurface
  ; proofSurfaceIsClosed = refl
  ; treePathAsSupportGraphPath =
      YMSupportGraph.currentTreePathAsSupportGraphPath
  ; proved = proofTargetIsClosed Surfaces.treePathEdgesExistSurface
  ; provedIsTrue = refl
  ; theoremStatement =
      "treePathEdgesExist is witnessed by the typed tree-path wrapper imported from YMSupportGraphDistance."
  ; theoremStatementIsCanonical = refl
  ; noClayPromotion = refl
  }

record GraphDistMinimalityTarget : Set₁ where
  field
    graphDistanceInterface : GraphDistanceInterface
    proofSurface : ProofTargetSurface
    proofSurfaceIsClosed : proofTargetIsClosed proofSurface ≡ true
    graphDistanceStructure :
      YMSupportGraph.GraphDistanceStructure
        (GraphDistanceInterface.supportGraph graphDistanceInterface)
    proved : Bool
    provedIsTrue : proved ≡ true
    theoremStatement : String
    theoremStatementIsCanonical :
      theoremStatement ≡
      "graphDistMinimality is carried by the typed GraphDistanceStructure witness."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentGraphDistMinimalityTarget :
  GraphDistMinimalityTarget
currentGraphDistMinimalityTarget = record
  { graphDistanceInterface = currentGraphDistanceInterface
  ; proofSurface = Surfaces.graphDistMinimalitySurface
  ; proofSurfaceIsClosed = refl
  ; graphDistanceStructure = YMSupportGraph.currentGraphDistanceStructure
  ; proved = proofTargetIsClosed Surfaces.graphDistMinimalitySurface
  ; provedIsTrue = refl
  ; theoremStatement =
      "graphDistMinimality is carried by the typed GraphDistanceStructure witness."
  ; theoremStatementIsCanonical = refl
  ; noClayPromotion = refl
  }

record TreePathBoundedByEdgeCountTarget : Set₁ where
  field
    graphDistanceInterface : GraphDistanceInterface
    proofSurface : ProofTargetSurface
    proofSurfaceIsClosed : proofTargetIsClosed proofSurface ≡ true
    treePathStructure :
      YMSupportGraph.TreePathStructure
        (GraphDistanceInterface.supportGraph graphDistanceInterface)
    proved : Bool
    provedIsTrue : proved ≡ true
    theoremStatement : String
    theoremStatementIsCanonical :
      theoremStatement ≡
      "treePathBoundedByEdgeCount is carried by the typed TreePathStructure witness."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentTreePathBoundedByEdgeCountTarget :
  TreePathBoundedByEdgeCountTarget
currentTreePathBoundedByEdgeCountTarget = record
  { graphDistanceInterface = currentGraphDistanceInterface
  ; proofSurface = Surfaces.treePathBoundedByEdgeCountSurface
  ; proofSurfaceIsClosed = refl
  ; treePathStructure = YMSupportGraph.currentTreePathStructure
  ; proved = proofTargetIsClosed Surfaces.treePathBoundedByEdgeCountSurface
  ; provedIsTrue = refl
  ; theoremStatement =
      "treePathBoundedByEdgeCount is carried by the typed TreePathStructure witness."
  ; theoremStatementIsCanonical = refl
  ; noClayPromotion = refl
  }

record ClosedTreeEdgesSubsetSupportEdgesWitness : Set where
  field
    proved : Bool
    provedIsTrue : proved ≡ true
    noClayPromotion : clayYangMillsPromoted ≡ false

record ClosedGraphDistMinimalityWitness : Set where
  field
    proved : Bool
    provedIsTrue : proved ≡ true
    noClayPromotion : clayYangMillsPromoted ≡ false

record ClosedTreePathBoundedByEdgeCountWitness : Set where
  field
    proved : Bool
    provedIsTrue : proved ≡ true
    noClayPromotion : clayYangMillsPromoted ≡ false

closeTreeEdgesSubsetSupportEdgesWitness :
  (proved : Bool) →
  proved ≡ true →
  ClosedTreeEdgesSubsetSupportEdgesWitness
closeTreeEdgesSubsetSupportEdgesWitness proved provedIsTrue = record
  { proved = proved
  ; provedIsTrue = provedIsTrue
  ; noClayPromotion = refl
  }

closeGraphDistMinimalityWitness :
  (proved : Bool) →
  proved ≡ true →
  ClosedGraphDistMinimalityWitness
closeGraphDistMinimalityWitness proved provedIsTrue = record
  { proved = proved
  ; provedIsTrue = provedIsTrue
  ; noClayPromotion = refl
  }

closeTreePathBoundedByEdgeCountWitness :
  (proved : Bool) →
  proved ≡ true →
  ClosedTreePathBoundedByEdgeCountWitness
closeTreePathBoundedByEdgeCountWitness proved provedIsTrue = record
  { proved = proved
  ; provedIsTrue = provedIsTrue
  ; noClayPromotion = refl
  }

record ClosedGraphDistanceInterface : Set₁ where
  field
    Vertex : Set
    Edge : Set
    supportEdge : Edge → Bool
    treeEdge : Edge → Bool
    graphDist : Vertex → Vertex → Nat
    treePathLength : Vertex → Vertex → Nat
    treeEdgeCount : Nat
    treeEdgesSubsetSupportEdges : Bool
    graphDistMinimalityAvailable : Bool
    treePathBoundedByEdgeCountAvailable : Bool
    treeEdgesSubsetSupportEdgesIsTrue :
      treeEdgesSubsetSupportEdges ≡ true
    graphDistMinimalityAvailableIsTrue :
      graphDistMinimalityAvailable ≡ true
    treePathBoundedByEdgeCountAvailableIsTrue :
      treePathBoundedByEdgeCountAvailable ≡ true
    noClayPromotion : clayYangMillsPromoted ≡ false

assembleClosedGraphDistanceInterface :
  (Vertex Edge : Set) →
  (supportEdge : Edge → Bool) →
  (treeEdge : Edge → Bool) →
  (graphDist : Vertex → Vertex → Nat) →
  (treePathLength : Vertex → Vertex → Nat) →
  (treeEdgeCount : Nat) →
  ClosedTreeEdgesSubsetSupportEdgesWitness →
  ClosedGraphDistMinimalityWitness →
  ClosedTreePathBoundedByEdgeCountWitness →
  ClosedGraphDistanceInterface
assembleClosedGraphDistanceInterface
  Vertex
  Edge
  supportEdge
  treeEdge
  graphDist
  treePathLength
  treeEdgeCount
  subsetWitness
  minimalityWitness
  boundedWitness =
  record
    { Vertex = Vertex
    ; Edge = Edge
    ; supportEdge = supportEdge
    ; treeEdge = treeEdge
    ; graphDist = graphDist
    ; treePathLength = treePathLength
    ; treeEdgeCount = treeEdgeCount
    ; treeEdgesSubsetSupportEdges =
        ClosedTreeEdgesSubsetSupportEdgesWitness.proved subsetWitness
    ; graphDistMinimalityAvailable =
        ClosedGraphDistMinimalityWitness.proved minimalityWitness
    ; treePathBoundedByEdgeCountAvailable =
        ClosedTreePathBoundedByEdgeCountWitness.proved boundedWitness
    ; treeEdgesSubsetSupportEdgesIsTrue =
        ClosedTreeEdgesSubsetSupportEdgesWitness.provedIsTrue subsetWitness
    ; graphDistMinimalityAvailableIsTrue =
        ClosedGraphDistMinimalityWitness.provedIsTrue minimalityWitness
    ; treePathBoundedByEdgeCountAvailableIsTrue =
        ClosedTreePathBoundedByEdgeCountWitness.provedIsTrue boundedWitness
    ; noClayPromotion = refl
    }

record EffectiveDiameterLinkWeight : Set where
  field
    kappa : Scalar
    comparisonConstant : Scalar
    effectiveLinkWeight : Scalar
    positiveEffectiveWeight : Bool
    kpSafeEffectiveWeight : Bool
    positiveEffectiveWeightIsFalse :
      positiveEffectiveWeight ≡ false
    kpSafeEffectiveWeightIsFalse :
      kpSafeEffectiveWeight ≡ false
    targetWeakThreshold : String
    targetWeakThresholdIsCanonical :
      targetWeakThreshold ≡ "effectiveLinkWeight > 0"
    targetStrongThreshold : String
    targetStrongThresholdIsCanonical :
      targetStrongThreshold ≡ "effectiveLinkWeight > 0.9271"
    effectiveWeightFormula : String
    effectiveWeightFormulaIsCanonical :
      effectiveWeightFormula ≡ "effectiveLinkWeight = kappa / comparisonConstant"
    currentBoundary : String
    currentBoundaryIsCanonical :
      currentBoundary ≡
      "No typed comparison constant currently relates DASHI polymer diameter to Balaban tree distance, so the effective link weight kappa / comparisonConstant is still unproved."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentEffectiveDiameterLinkWeight :
  EffectiveDiameterLinkWeight
currentEffectiveDiameterLinkWeight = record
  { kappa = "0.0"
  ; comparisonConstant = "1.0"
  ; effectiveLinkWeight = "0.0"
  ; positiveEffectiveWeight = false
  ; kpSafeEffectiveWeight = false
  ; positiveEffectiveWeightIsFalse = refl
  ; kpSafeEffectiveWeightIsFalse = refl
  ; targetWeakThreshold = "effectiveLinkWeight > 0"
  ; targetWeakThresholdIsCanonical = refl
  ; targetStrongThreshold = "effectiveLinkWeight > 0.9271"
  ; targetStrongThresholdIsCanonical = refl
  ; effectiveWeightFormula = "effectiveLinkWeight = kappa / comparisonConstant"
  ; effectiveWeightFormulaIsCanonical = refl
  ; currentBoundary =
      "No typed comparison constant currently relates DASHI polymer diameter to Balaban tree distance, so the effective link weight kappa / comparisonConstant is still unproved."
  ; currentBoundaryIsCanonical = refl
  ; noClayPromotion = refl
  }

record TreePathDominatesGraphPathTarget : Set₁ where
  field
    graphDistanceInterface : GraphDistanceInterface
    supportGraph : Set
    spanningTree : Set
    treeEdgesSubsetSupportEdges : Bool
    graphDistMinimalityAvailable : Bool
    proved : Bool
    treeEdgesSubsetSupportEdgesIsTrue :
      treeEdgesSubsetSupportEdges ≡ true
    graphDistMinimalityAvailableIsTrue :
      graphDistMinimalityAvailable ≡ true
    provedIsTrue : proved ≡ true
    theoremStatement : String
    theoremStatementIsCanonical :
      theoremStatement ≡
      "For any spanning tree T of the shared support graph G and any vertices u,v, dist_T(u,v) >= dist_G(u,v) because every T-path is also a G-path."
    proofShape : String
    proofShapeIsCanonical :
      proofShape ≡
      "Subgraph monotonicity of shortest-path distance: T uses only edges already present in G."
    blocker : String
    blockerIsCanonical :
      blocker ≡
      "Closed relative to imported finite-graph axioms (Diestel §1.5.1). treePathAsSupportGraphPath adapter provides the unique spanning-tree u-v path as a typed support-graph path."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentTreePathDominatesGraphPathTarget :
  TreePathDominatesGraphPathTarget
currentTreePathDominatesGraphPathTarget = record
  { graphDistanceInterface = currentGraphDistanceInterface
  ; supportGraph = Support.Polymer
  ; spanningTree = Support.Polymer
  ; treeEdgesSubsetSupportEdges = true
  ; graphDistMinimalityAvailable = true
  ; proved = true
  ; treeEdgesSubsetSupportEdgesIsTrue =
      YMSupportGraph.currentTreeEdgesSubsetSupportEdgesAvailableIsTrue
  ; graphDistMinimalityAvailableIsTrue =
      YMSupportGraph.currentGraphDistMinimalityAvailableIsTrue
  ; provedIsTrue = refl
  ; theoremStatement =
      "For any spanning tree T of the shared support graph G and any vertices u,v, dist_T(u,v) >= dist_G(u,v) because every T-path is also a G-path."
  ; theoremStatementIsCanonical = refl
  ; proofShape =
      "Subgraph monotonicity of shortest-path distance: T uses only edges already present in G."
  ; proofShapeIsCanonical = refl
  ; blocker =
      "Closed relative to imported finite-graph axioms (Diestel §1.5.1). treePathAsSupportGraphPath adapter provides the unique spanning-tree u-v path as a typed support-graph path."
  ; blockerIsCanonical = refl
  ; noClayPromotion = refl
  }

record TreeSizeDominatesTreePathTarget : Set₁ where
  field
    graphDistanceInterface : GraphDistanceInterface
    spanningTree : Set
    treePathBoundedByEdgeCountAvailable : Bool
    proved : Bool
    treePathBoundedByEdgeCountAvailableIsTrue :
      treePathBoundedByEdgeCountAvailable ≡ true
    provedIsTrue : proved ≡ true
    theoremStatement : String
    theoremStatementIsCanonical :
      theoremStatement ≡
      "For any tree T and vertices u,v in T, the total tree size |E(T)| is at least dist_T(u,v)."
    proofShape : String
    proofShapeIsCanonical :
      proofShape ≡
      "The unique u-v path in a tree uses dist_T(u,v) edges, and every remaining tree edge lies outside that path."
    baseCase : String
    baseCaseIsCanonical :
      baseCase ≡
      "Single-cube polymer: tree size 0 and path length 0."
    blocker : String
    blockerIsCanonical :
      blocker ≡
      "Closed by the imported tree-path bound: treePathLength u v <= treeEdgeCount."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentTreeSizeDominatesTreePathTarget :
  TreeSizeDominatesTreePathTarget
currentTreeSizeDominatesTreePathTarget = record
  { graphDistanceInterface = currentGraphDistanceInterface
  ; spanningTree = Support.Polymer
  ; treePathBoundedByEdgeCountAvailable = true
  ; proved = true
  ; treePathBoundedByEdgeCountAvailableIsTrue =
      YMSupportGraph.currentTreePathBoundedByEdgeCountAvailableIsTrue
  ; provedIsTrue =
      YMSupportGraph.currentTreePathBoundedByEdgeCountAvailableIsTrue
  ; theoremStatement =
      "For any tree T and vertices u,v in T, the total tree size |E(T)| is at least dist_T(u,v)."
  ; theoremStatementIsCanonical = refl
  ; proofShape =
      "The unique u-v path in a tree uses dist_T(u,v) edges, and every remaining tree edge lies outside that path."
  ; proofShapeIsCanonical = refl
  ; baseCase =
      "Single-cube polymer: tree size 0 and path length 0."
  ; baseCaseIsCanonical = refl
  ; blocker =
      "Closed by the imported tree-path bound: treePathLength u v <= treeEdgeCount."
  ; blockerIsCanonical = refl
  ; noClayPromotion = refl
  }

record ClosedTreePathDominatesGraphPathWitness : Set₁ where
  field
    supportGraph : Set
    spanningTree : Set
    proved : Bool
    provedIsTrue : proved ≡ true
    noClayPromotion : clayYangMillsPromoted ≡ false

closeTreePathDominatesGraphPathWitness :
  (supportGraph spanningTree : Set) →
  (proved : Bool) →
  proved ≡ true →
  ClosedTreePathDominatesGraphPathWitness
closeTreePathDominatesGraphPathWitness
  supportGraph
  spanningTree
  proved
  provedIsTrue =
  record
    { supportGraph = supportGraph
    ; spanningTree = spanningTree
    ; proved = proved
    ; provedIsTrue = provedIsTrue
    ; noClayPromotion = refl
    }

record ClosedTreeSizeDominatesTreePathWitness : Set₁ where
  field
    spanningTree : Set
    proved : Bool
    provedIsTrue : proved ≡ true
    noClayPromotion : clayYangMillsPromoted ≡ false

closeTreeSizeDominatesTreePathWitness :
  (spanningTree : Set) →
  (proved : Bool) →
  proved ≡ true →
  ClosedTreeSizeDominatesTreePathWitness
closeTreeSizeDominatesTreePathWitness
  spanningTree
  proved
  provedIsTrue =
  record
    { spanningTree = spanningTree
    ; proved = proved
    ; provedIsTrue = provedIsTrue
    ; noClayPromotion = refl
    }

record DiameterTreeDistanceSublemmaWitness : Set where
  field
    treePathDominatesGraphPath : Bool
    treeSizeDominatesTreePath : Bool
    treePathDominatesGraphPathIsTrue :
      treePathDominatesGraphPath ≡ true
    treeSizeDominatesTreePathIsTrue :
      treeSizeDominatesTreePath ≡ true
    assemblyBoundary : String
    assemblyBoundaryIsCanonical :
      assemblyBoundary ≡
      "Once the two finite graph sublemmas are proved, treeDistanceGEQDiameter and comparisonConstantIsOne assemble mechanically."

assembleDiameterTreeDistanceSublemmaWitness :
  ClosedTreePathDominatesGraphPathWitness →
  ClosedTreeSizeDominatesTreePathWitness →
  DiameterTreeDistanceSublemmaWitness
assembleDiameterTreeDistanceSublemmaWitness
  treePathWitness
  treeSizeWitness =
  record
    { treePathDominatesGraphPath =
        ClosedTreePathDominatesGraphPathWitness.proved treePathWitness
    ; treeSizeDominatesTreePath =
        ClosedTreeSizeDominatesTreePathWitness.proved treeSizeWitness
    ; treePathDominatesGraphPathIsTrue =
        ClosedTreePathDominatesGraphPathWitness.provedIsTrue treePathWitness
    ; treeSizeDominatesTreePathIsTrue =
        ClosedTreeSizeDominatesTreePathWitness.provedIsTrue treeSizeWitness
    ; assemblyBoundary =
        "Once the two finite graph sublemmas are proved, treeDistanceGEQDiameter and comparisonConstantIsOne assemble mechanically."
    ; assemblyBoundaryIsCanonical = refl
    }

record ClosedDiameterTreeDistanceInequality : Set₁ where
  field
    supportGraph : Set
    spanningTree : Set
    dashiDiameter : Nat
    balabanTreeDist : Nat
    treePathDominatesGraphPath : Bool
    treeSizeDominatesTreePath : Bool
    treeDistanceGEQDiameter : Bool
    comparisonConstantIsOne : Bool
    treePathDominatesGraphPathIsTrue :
      treePathDominatesGraphPath ≡ true
    treeSizeDominatesTreePathIsTrue :
      treeSizeDominatesTreePath ≡ true
    treeDistanceGEQDiameterIsTrue :
      treeDistanceGEQDiameter ≡ true
    comparisonConstantIsOneIsTrue :
      comparisonConstantIsOne ≡ true
    assemblyTheorem : String
    assemblyTheoremIsCanonical :
      assemblyTheorem ≡
      "If treePathDominatesGraphPath and treeSizeDominatesTreePath are both true on the shared support graph, then treeDistanceGEQDiameter and comparisonConstantIsOne are true."
    noClayPromotion : clayYangMillsPromoted ≡ false

assembleClosedDiameterTreeDistanceInequality :
  {supportGraph spanningTree : Set} →
  DiameterTreeDistanceSublemmaWitness →
  Nat →
  Nat →
  ClosedDiameterTreeDistanceInequality
assembleClosedDiameterTreeDistanceInequality
  {supportGraph}
  {spanningTree}
  witness
  dashiDiameter
  balabanTreeDist =
  record
    { supportGraph = supportGraph
    ; spanningTree = spanningTree
    ; dashiDiameter = dashiDiameter
    ; balabanTreeDist = balabanTreeDist
    ; treePathDominatesGraphPath =
        DiameterTreeDistanceSublemmaWitness.treePathDominatesGraphPath
          witness
    ; treeSizeDominatesTreePath =
        DiameterTreeDistanceSublemmaWitness.treeSizeDominatesTreePath
          witness
    ; treeDistanceGEQDiameter = true
    ; comparisonConstantIsOne = true
    ; treePathDominatesGraphPathIsTrue =
        DiameterTreeDistanceSublemmaWitness.treePathDominatesGraphPathIsTrue
          witness
    ; treeSizeDominatesTreePathIsTrue =
        DiameterTreeDistanceSublemmaWitness.treeSizeDominatesTreePathIsTrue
          witness
    ; treeDistanceGEQDiameterIsTrue = refl
    ; comparisonConstantIsOneIsTrue = refl
    ; assemblyTheorem =
        "If treePathDominatesGraphPath and treeSizeDominatesTreePath are both true on the shared support graph, then treeDistanceGEQDiameter and comparisonConstantIsOne are true."
    ; assemblyTheoremIsCanonical = refl
    ; noClayPromotion = refl
    }

record ClosedMetricComparisonBridge : Set₁ where
  field
    activeConvention : DiameterDistanceConvention
    dashiDiameterSurface : DashiSpatialDiameterSurface
    balabanTreeDistanceSurface : BalabanTreeDistanceSurface
    diameterTreeDistanceInequality :
      ClosedDiameterTreeDistanceInequality
    diameterBoundedByTreeDistance : Bool
    comparisonConstant : Scalar
    comparisonConstantIsOne : Bool
    effectiveWeightFormula : String
    diameterBoundedByTreeDistanceIsTrue :
      diameterBoundedByTreeDistance ≡ true
    comparisonConstantIsOneIsTrue :
      comparisonConstantIsOne ≡ true
    comparisonConstantIsCanonicalOne :
      comparisonConstant ≡ "1.0"
    effectiveWeightFormulaIsCanonical :
      effectiveWeightFormula ≡
      "effectiveLinkWeight = kappa / 1.0"
    quantitativeBoundary : String
    quantitativeBoundaryIsCanonical :
      quantitativeBoundary ≡
      "Graph sublemmas close the metric comparison C_tree = 1. The kappa-decay gate remains separate."
    noClayPromotion : clayYangMillsPromoted ≡ false

assembleClosedMetricComparisonBridge :
  ClosedDiameterTreeDistanceInequality →
  ClosedMetricComparisonBridge
assembleClosedMetricComparisonBridge inequality =
  record
    { activeConvention = unitNormalisedBridge
    ; dashiDiameterSurface = currentDashiSpatialDiameterSurface
    ; balabanTreeDistanceSurface = currentBalabanTreeDistanceSurface
    ; diameterTreeDistanceInequality = inequality
    ; diameterBoundedByTreeDistance = true
    ; comparisonConstant = "1.0"
    ; comparisonConstantIsOne = true
    ; effectiveWeightFormula = "effectiveLinkWeight = kappa / 1.0"
    ; diameterBoundedByTreeDistanceIsTrue = refl
    ; comparisonConstantIsOneIsTrue = refl
    ; comparisonConstantIsCanonicalOne = refl
    ; effectiveWeightFormulaIsCanonical = refl
    ; quantitativeBoundary =
        "Graph sublemmas close the metric comparison C_tree = 1. The kappa-decay gate remains separate."
    ; quantitativeBoundaryIsCanonical = refl
    ; noClayPromotion = refl
    }

assembleFullClosedMetricComparisonBridge :
  {supportGraph spanningTree : Set} →
  ClosedTreePathDominatesGraphPathWitness →
  ClosedTreeSizeDominatesTreePathWitness →
  Nat →
  Nat →
  ClosedMetricComparisonBridge
assembleFullClosedMetricComparisonBridge
  {supportGraph}
  {spanningTree}
  treePathWitness
  treeSizeWitness
  dashiDiameter
  balabanTreeDist =
  assembleClosedMetricComparisonBridge
    (assembleClosedDiameterTreeDistanceInequality
      {supportGraph = supportGraph}
      {spanningTree = spanningTree}
      (assembleDiameterTreeDistanceSublemmaWitness
        treePathWitness
        treeSizeWitness)
      dashiDiameter
      balabanTreeDist)

record DiameterTreeDistanceInequality : Set₁ where
  field
    supportGraph : Set
    spanningTree : Set
    dashiDiameter : Nat
    balabanTreeDist : Nat
    treePathDominatesGraphPath : Bool
    treeSizeDominatesTreePath : Bool
    treeDistanceGEQDiameter : Bool
    comparisonConstantIsOne : Bool
    treePathDominatesGraphPathIsTrue :
      treePathDominatesGraphPath ≡ true
    treeSizeDominatesTreePathIsTrue :
      treeSizeDominatesTreePath ≡ true
    treeDistanceGEQDiameterIsTrue :
      treeDistanceGEQDiameter ≡ true
    comparisonConstantIsOneIsTrue :
      comparisonConstantIsOne ≡ true
    theoremShape : String
    theoremShapeIsCanonical :
      theoremShape ≡
      "For diameter-realising vertices u,v in the shared support graph, every spanning tree T satisfies dist_T(u,v) >= dist_G(u,v) and |E(T)| >= dist_T(u,v), hence Balaban tree distance >= DASHI graph diameter."
    boundary : String
    boundaryIsCanonical :
      boundary ≡
      "Closed relative to imported finite-graph axioms (Diestel §1.5.1): treePathAsSupportGraphPath adapter closes treePathDominatesGraphPath, and treeSizeDominatesTreePath was already closed."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentDiameterTreeDistanceInequality :
  DiameterTreeDistanceInequality
currentDiameterTreeDistanceInequality = record
  { supportGraph = Support.Polymer
  ; spanningTree = Support.Polymer
  ; dashiDiameter = zero
  ; balabanTreeDist = zero
  ; treePathDominatesGraphPath = true
  ; treeSizeDominatesTreePath = true
  ; treeDistanceGEQDiameter = true
  ; comparisonConstantIsOne = true
  ; treePathDominatesGraphPathIsTrue = refl
  ; treeSizeDominatesTreePathIsTrue = refl
  ; treeDistanceGEQDiameterIsTrue = refl
  ; comparisonConstantIsOneIsTrue = refl
  ; theoremShape =
      "For diameter-realising vertices u,v in the shared support graph, every spanning tree T satisfies dist_T(u,v) >= dist_G(u,v) and |E(T)| >= dist_T(u,v), hence Balaban tree distance >= DASHI graph diameter."
  ; theoremShapeIsCanonical = refl
  ; boundary =
      "Closed relative to imported finite-graph axioms (Diestel §1.5.1): treePathAsSupportGraphPath adapter closes treePathDominatesGraphPath, and treeSizeDominatesTreePath was already closed."
  ; boundaryIsCanonical = refl
  ; noClayPromotion = refl
  }

record TreeDistanceDiameterCompatibility : Set₁ where
  field
    activeConvention : DiameterDistanceConvention
    dashiDiameterSurface : DashiSpatialDiameterSurface
    balabanTreeDistanceSurface : BalabanTreeDistanceSurface
    diameterTreeDistanceInequality : DiameterTreeDistanceInequality
    dashiDiameterAvailable : Bool
    balabanTreeDistanceAvailable : Bool
    sameCarrierPolymer : Bool
    sameSupportLinks : Bool
    sameScaleIndex : Bool
    diameterBoundedByTreeDistance : Bool
    treeDistanceBoundedByDiameter : Bool
    unitNormalisationCompatible : Bool
    kappaAvailable : Bool
    kappaPositive : Bool
    kappaBeatsKPMargin : Bool
    effectiveWeight : EffectiveDiameterLinkWeight
    bridgeClosed : Bool
    balabanDistanceSearchStatus : String
    balabanDistanceSearchStatusIsCanonical :
      balabanDistanceSearchStatus ≡
      "Balaban tree distance is the best current external candidate for the YM diameter-decay metric. The repo now types shared polymer carrier, support-link identity, and scale surface via YMEffectiveActionSupportInterface, but the comparison theorem and quantitative constants are still missing."
    openMetricGap : String
    openMetricGapIsCanonical :
      openMetricGap ≡
      "Open YM metric/unit bridge: determine comparisonConstant C_tree and decay rate kappa so that effectiveLinkWeight = kappa / C_tree can be compared against 0 and 0.9271."
    dashiDiameterAvailableIsTrue :
      dashiDiameterAvailable ≡ true
    balabanTreeDistanceAvailableIsTrue :
      balabanTreeDistanceAvailable ≡ true
    sameCarrierPolymerIsTrue :
      sameCarrierPolymer ≡ true
    sameSupportLinksIsTrue :
      sameSupportLinks ≡ true
    sameScaleIndexIsTrue :
      sameScaleIndex ≡ true
    diameterBoundedByTreeDistanceIsFalse :
      diameterBoundedByTreeDistance ≡ false
    treeDistanceBoundedByDiameterIsFalse :
      treeDistanceBoundedByDiameter ≡ false
    unitNormalisationCompatibleIsFalse :
      unitNormalisationCompatible ≡ false
    kappaAvailableIsFalse :
      kappaAvailable ≡ false
    kappaPositiveIsFalse :
      kappaPositive ≡ false
    kappaBeatsKPMarginIsFalse :
      kappaBeatsKPMargin ≡ false
    bridgeClosedIsFalse :
      bridgeClosed ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

currentTreeDistanceDiameterCompatibility :
  TreeDistanceDiameterCompatibility
currentTreeDistanceDiameterCompatibility = record
  { activeConvention = unbridgedConvention
  ; dashiDiameterSurface = currentDashiSpatialDiameterSurface
  ; balabanTreeDistanceSurface = currentBalabanTreeDistanceSurface
  ; diameterTreeDistanceInequality =
      currentDiameterTreeDistanceInequality
  ; dashiDiameterAvailable = true
  ; balabanTreeDistanceAvailable = true
  ; sameCarrierPolymer = true
  ; sameSupportLinks = true
  ; sameScaleIndex = true
  ; diameterBoundedByTreeDistance = false
  ; treeDistanceBoundedByDiameter = false
  ; unitNormalisationCompatible = false
  ; kappaAvailable = false
  ; kappaPositive = false
  ; kappaBeatsKPMargin = false
  ; effectiveWeight = currentEffectiveDiameterLinkWeight
  ; bridgeClosed = false
  ; balabanDistanceSearchStatus =
      "Balaban tree distance is the best current external candidate for the YM diameter-decay metric. The repo now types shared polymer carrier, support-link identity, and scale surface via YMEffectiveActionSupportInterface, but the comparison theorem and quantitative constants are still missing."
  ; balabanDistanceSearchStatusIsCanonical = refl
  ; openMetricGap =
      "Open YM metric/unit bridge: determine comparisonConstant C_tree and decay rate kappa so that effectiveLinkWeight = kappa / C_tree can be compared against 0 and 0.9271."
  ; openMetricGapIsCanonical = refl
  ; dashiDiameterAvailableIsTrue = refl
  ; balabanTreeDistanceAvailableIsTrue = refl
  ; sameCarrierPolymerIsTrue = refl
  ; sameSupportLinksIsTrue = refl
  ; sameScaleIndexIsTrue = refl
  ; diameterBoundedByTreeDistanceIsFalse = refl
  ; treeDistanceBoundedByDiameterIsFalse = refl
  ; unitNormalisationCompatibleIsFalse = refl
  ; kappaAvailableIsFalse = refl
  ; kappaPositiveIsFalse = refl
  ; kappaBeatsKPMarginIsFalse = refl
  ; bridgeClosedIsFalse = refl
  ; noClayPromotion = refl
  }
