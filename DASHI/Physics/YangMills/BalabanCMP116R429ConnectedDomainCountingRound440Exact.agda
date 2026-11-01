{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R429ConnectedDomainCountingRound440Exact where

------------------------------------------------------------------------
-- B / ROUND440: INJECT THE LITERAL R429 DOMAIN FAMILY INTO THE EXISTING
-- CANONICAL ROOTED TRACE / TREE COUNTING MACHINE.
--
-- The repository already proves the combinatorial part:
--
--   least root + canonical BFS tree + fixed DFS word + decoder
--       -> injective rooted trace
--       -> family mass <= 1/4 * (1/2)^traceDepth.
--
-- For Goal 1 we should not restate that theorem for CMP116.  The only
-- genuinely source-specific geometric payment is to identify each literal
-- R429 domain with such a connected polymer and prove that the canonical
-- trace depth is the literal R429/YM support-tree depth.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _≤_; _*_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph

import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRationalConstantsExact as Constants
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geometric
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayGate4RCanonicalRepositoryTraceReuseExact as Trace

record R429CanonicalConnectedDomainCounting
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (Polymer Block Tree Traversal Scale Volume : Set)
    : Set₁ where
  field
    trace :
      Trace.RCanonicalRepositoryTrace
        (R429.Domain fourStage)
        Polymer Block Tree Traversal Scale Volume

    shellData :
      Shell.TraversalShellData Scale Volume Block

    literalDomainIsRootedShell :
      Trace.RCanonicalShellIdentification trace shellData

    literalDomainPolymerFaithful :
      Trace.RExpressionPolymerFaithfulness trace

    -- This is the actual R429 -> rooted-trace geometric seam.
    -- R438 already made CMP116's source tree coordinate definitionally
    -- Graph.ymTreeEdgeCount, so no second source-distance identification
    -- remains after this field.
    canonicalTraceDepthIsR429TreeDepth :
      ∀ domain →
      Trace.rCanonicalDepth trace domain ≡ Graph.ymTreeEdgeCount

open R429CanonicalConnectedDomainCounting public

r429DomainCountingBound :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    {Polymer Block Tree Traversal Scale Volume}
    (counting :
      R429CanonicalConnectedDomainCounting
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage Polymer Block Tree Traversal Scale Volume)
    domain →
  Trace.familyMass (trace counting) domain
    ≤
  Constants.quarter * Geometric.halfPower Graph.ymTreeEdgeCount
r429DomainCountingBound counting domain =
  subst
    (λ depth →
      Trace.familyMass (trace counting) domain
        ≤ Constants.quarter * Geometric.halfPower depth)
    (canonicalTraceDepthIsR429TreeDepth counting domain)
    (Trace.rCanonicalCountingBound
      (literalDomainIsRootedShell counting)
      domain)

r429RootAndTraceWordInjective :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    {Polymer Block Tree Traversal Scale Volume}
    (counting :
      R429CanonicalConnectedDomainCounting
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage Polymer Block Tree Traversal Scale Volume)
    {left right} →
  Trace.rCanonicalRoot (trace counting) left
    ≡ Trace.rCanonicalRoot (trace counting) right →
  Trace.rCanonicalWord (trace counting) left
    ≡ Trace.rCanonicalWord (trace counting) right →
  left ≡ right
r429RootAndTraceWordInjective counting =
  Trace.rRootAndWordInjective
    (literalDomainPolymerFaithful counting)

round440RepositoryTraceCountingReuseLevel : ProofLevel
round440RepositoryTraceCountingReuseLevel = machineChecked

round440R429RootWordInjectionCompilerLevel : ProofLevel
round440R429RootWordInjectionCompilerLevel = machineChecked

-- The generic connected-domain combinatorics are now reused theorem-for-theorem.
-- What remains source-specific is exactly the construction of the four fields
-- above for the literal CMP116/R429 domain family.  In particular there is no
-- longer a separate "prove a connected-domain counting theorem" obligation.
literalRound440R429ConnectedDomainInstantiationLevel : ProofLevel
literalRound440R429ConnectedDomainInstantiationLevel = conditional
