module DASHI.Physics.YangMills.BalabanClayGate4RCanonicalRepositoryTraceReuseExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2RepositoryBreadthFirstTreeInstanceExact as BFS
import DASHI.Physics.YangMills.BalabanClayT2RepositoryConnectedPolymerExtractionExact as Extraction
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayGate4CountingAndLocalizationReuseExact as Reuse

------------------------------------------------------------------------
-- Primary provenance.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Roberto Fernández and Aldo Procacci,
-- "Cluster Expansion for Abstract Polymer Models. New Bounds from an Old
-- Approach", Communications in Mathematical Physics 274 (2007), 123--140.
-- DOI: 10.1007/s00220-007-0279-2.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- The literature requires connected rooted polymers.  The least root,
-- breadth-first parent tree, fixed-order depth-first word and decoder are the
-- existing DASHI implementation; this module only binds an R-expression to it.
------------------------------------------------------------------------

record RCanonicalRepositoryTrace
    (RExpression Polymer Block Tree Traversal Scale Volume : Set) : Set₁ where
  field
    breadthFirstData :
      BFS.RepositoryBreadthFirstTreeData Polymer Block Tree Traversal

    expressionPolymer : RExpression → Polymer
    scaleOf : RExpression → Scale
    volumeOf : RExpression → Volume
    familyMass : RExpression → ℚ

open RCanonicalRepositoryTrace public

repositoryCarrier :
  ∀ {RExpression Polymer Block Tree Traversal Scale Volume} →
  RCanonicalRepositoryTrace
    RExpression Polymer Block Tree Traversal Scale Volume →
  Extraction.RepositoryConnectedBlockCarrier Polymer Block Tree Traversal
repositoryCarrier dataSet =
  BFS.asRepositoryConnectedBlockCarrier (breadthFirstData dataSet)

rCanonicalRoot :
  ∀ {RExpression Polymer Block Tree Traversal Scale Volume} →
  RCanonicalRepositoryTrace
    RExpression Polymer Block Tree Traversal Scale Volume →
  RExpression → Block
rCanonicalRoot dataSet expression =
  BFS.leastBlock (breadthFirstData dataSet)
    (expressionPolymer dataSet expression)

rCanonicalWord :
  ∀ {RExpression Polymer Block Tree Traversal Scale Volume} →
  RCanonicalRepositoryTrace
    RExpression Polymer Block Tree Traversal Scale Volume →
  RExpression → Agda.Builtin.List.List
    DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact.SignedAxis4
rCanonicalWord dataSet expression =
  BFS.canonicalDirectionWord (breadthFirstData dataSet)
    (expressionPolymer dataSet expression)

rCanonicalDepth :
  ∀ {RExpression Polymer Block Tree Traversal Scale Volume} →
  RCanonicalRepositoryTrace
    RExpression Polymer Block Tree Traversal Scale Volume →
  RExpression → Nat
rCanonicalDepth dataSet expression = length (rCanonicalWord dataSet expression)

record RCanonicalShellIdentification
    {RExpression Polymer Block Tree Traversal Scale Volume : Set}
    (trace : RCanonicalRepositoryTrace
      RExpression Polymer Block Tree Traversal Scale Volume)
    (shellData : Shell.TraversalShellData Scale Volume Block) : Set₁ where
  field
    familyMassIsRootedShell : ∀ expression →
      familyMass trace expression
      ≡ Shell.rootedShell shellData
          (scaleOf trace expression)
          (volumeOf trace expression)
          (rCanonicalRoot trace expression)
          (rCanonicalDepth trace expression)

open RCanonicalShellIdentification public

asExactRootedFamilyRepresentation :
  ∀ {RExpression Polymer Block Tree Traversal Scale Volume}
    {trace : RCanonicalRepositoryTrace
      RExpression Polymer Block Tree Traversal Scale Volume}
    {shellData : Shell.TraversalShellData Scale Volume Block} →
  RCanonicalShellIdentification trace shellData →
  Reuse.ExactRootedFamilyRepresentation Scale Volume Block shellData
asExactRootedFamilyRepresentation {trace = trace} identification = record
  { Reuse.ExactRootedFamilyRepresentation.Family = _
  ; Reuse.ExactRootedFamilyRepresentation.scaleOf = scaleOf trace
  ; Reuse.ExactRootedFamilyRepresentation.volumeOf = volumeOf trace
  ; Reuse.ExactRootedFamilyRepresentation.rootOf = rCanonicalRoot trace
  ; Reuse.ExactRootedFamilyRepresentation.depthOf = rCanonicalDepth trace
  ; Reuse.ExactRootedFamilyRepresentation.familyMass = familyMass trace
  ; Reuse.ExactRootedFamilyRepresentation.familyMassDefinition =
      familyMassIsRootedShell identification
  }

rCanonicalCountingBound :
  ∀ {RExpression Polymer Block Tree Traversal Scale Volume}
    {trace : RCanonicalRepositoryTrace
      RExpression Polymer Block Tree Traversal Scale Volume}
    {shellData : Shell.TraversalShellData Scale Volume Block}
    (identification : RCanonicalShellIdentification trace shellData)
    expression →
  familyMass trace expression
  Shell.≤ Shell.quarter * Shell.halfPower (rCanonicalDepth trace expression)
rCanonicalCountingBound identification =
  Reuse.exactRootedFamilyCounting
    (asExactRootedFamilyRepresentation identification)

record RExpressionPolymerFaithfulness
    {RExpression Polymer Block Tree Traversal Scale Volume : Set}
    (trace : RCanonicalRepositoryTrace
      RExpression Polymer Block Tree Traversal Scale Volume) : Set₁ where
  field
    expressionPolymerInjective : ∀ {left right} →
      expressionPolymer trace left ≡ expressionPolymer trace right →
      left ≡ right

open RExpressionPolymerFaithfulness public

rRootAndWordInjective :
  ∀ {RExpression Polymer Block Tree Traversal Scale Volume}
    {trace : RCanonicalRepositoryTrace
      RExpression Polymer Block Tree Traversal Scale Volume} →
  RExpressionPolymerFaithfulness trace →
  ∀ {left right} →
  rCanonicalRoot trace left ≡ rCanonicalRoot trace right →
  rCanonicalWord trace left ≡ rCanonicalWord trace right →
  left ≡ right
rRootAndWordInjective {trace = trace} faithful rootEqual wordEqual =
  expressionPolymerInjective faithful
    (BFS.canonicalTraceInjective (breadthFirstData trace)
      rootEqual wordEqual)

rCanonicalRepositoryTraceReuseLevel : ProofLevel
rCanonicalRepositoryTraceReuseLevel = machineChecked

rCanonicalRootWordInjectivityLevel : ProofLevel
rCanonicalRootWordInjectivityLevel = machineChecked

rCanonicalCountingAssemblyLevel : ProofLevel
rCanonicalCountingAssemblyLevel = machineChecked

physicalRExpressionPolymerIdentificationInputsLevel : ProofLevel
physicalRExpressionPolymerIdentificationInputsLevel = conditional

physicalRFamilyMassRootedShellInputsLevel : ProofLevel
physicalRFamilyMassRootedShellInputsLevel = conditional

repositoryBreadthFirstTreeInputsLevel : ProofLevel
repositoryBreadthFirstTreeInputsLevel = conditional
