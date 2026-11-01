module DASHI.Physics.YangMills.BalabanClayT5PhysicalTailMomentMeasureClosureExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; _+_; _≤_)

import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5PhysicalRootedShellInjectionExact as Shell
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Physical T5 closure from the literal 1/16 activity and canonical rooted trace.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022.
--
-- Roman Kotecký and David Preiss, "Cluster Expansion for Abstract Polymer
-- Models", Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Roberto Fernández and Aldo Procacci, "Cluster Expansion for Abstract Polymer
-- Models. New Bounds from an Old Approach", Communications in Mathematical
-- Physics 274 (2007), 123--140.
-- DOI: 10.1007/s00220-007-0279-2; arXiv:math-ph/0605041.
--
-- Konrad Osterwalder and Robert Schrader, "Axioms for Euclidean Green's
-- Functions II", Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
------------------------------------------------------------------------

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (value ∷ rest) = value + sumℚ rest

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

------------------------------------------------------------------------
-- Boundary cancellation is factored into equality of interior weights and a
-- finite partition of the cluster list.  The difficult input is now exactly
-- the physical support theorem, not cancellation algebra.
------------------------------------------------------------------------

record InteriorBoundaryWeightAgreement
    {Volume Boundary Observable Polymer Cluster : Set}
    (expansion :
      Physical.FiniteVolumeClusterExpansion
        Volume Boundary Observable Polymer Cluster) : Set₁ where
  field
    interior : Volume → Observable → Cluster → Set
    crossing : Volume → Observable → Cluster → Set
    clusterClassification : ∀ volume observable cluster → Set

    interiorWeightIndependent :
      ∀ volume observable cluster leftBoundary rightBoundary →
      interior volume observable cluster →
      Physical.clusterWeight expansion leftBoundary observable cluster
      ≡ Physical.clusterWeight expansion rightBoundary observable cluster

    crossingClusters : Volume → Observable → List Cluster
    crossingListExact : ∀ volume observable → Set
    expectationDifferenceReducesToCrossingList :
      ∀ volume observable leftBoundary rightBoundary → Set

open InteriorBoundaryWeightAgreement public

record RootedBoundaryTailClosure
    {Volume Boundary Observable Polymer Cluster Block : Set}
    (expansion :
      Physical.FiniteVolumeClusterExpansion
        Volume Boundary Observable Polymer Cluster)
    (agreement : InteriorBoundaryWeightAgreement expansion) : Set₁ where
  field
    geometry : Shell.BoundaryGeometry Block Volume Observable
    carrier : Shell.PhysicalClusterCarrier Block Polymer Cluster
    trace : Shell.CanonicalRootedTrace Block Polymer
    injection :
      Shell.PhysicalRootedShellInjection
        Block Volume Observable Polymer Cluster geometry carrier trace

    everyCrossingClusterHasWitness : ∀ volume observable cluster →
      Set
    crossingDiameterAtLeastSupportBoundaryDistance :
      ∀ volume observable cluster → Set
    crossingTraceShellIndexAtLeastDistance :
      ∀ volume observable cluster → Set

    rootedShellWeightBound : ∀ depth → Set
    crossingWeightSumBelowRootedTail : ∀ volume observable → Set
    boundaryExpectationDifferenceBelowRootedTail :
      ∀ volume observable leftBoundary rightBoundary → Set
    supportBoundaryDistanceEscapes : ∀ observable → Set
    boundaryConditionIndependence : ∀ observable → Set

open RootedBoundaryTailClosure public

------------------------------------------------------------------------
-- RG defects: exact cancellation first, dyadic irrelevant tail second.
------------------------------------------------------------------------

record PhysicalRGDefectClosure
    (Cutoff Observable DefectTerm : Set)
    (defect : Physical.OneStepRGDefect Cutoff Observable DefectTerm) : Set₁ where
  field
    relevantTerms : Cutoff → Observable → List DefectTerm
    irrelevantTerms : Cutoff → Observable → List DefectTerm

    defectTermsPartitionExact : ∀ cutoff observable → Set
    relevantTermSumZero : ∀ cutoff observable →
      sumℚ (map (Physical.defectTermValue defect)
        (relevantTerms cutoff observable)) ≡ 0ℚ

    irrelevantTermsAreExactlyRemainder : ∀ cutoff observable → Set
    eachIrrelevantTermReceivesScaleGain :
      ∀ cutoff observable term → Set
    irrelevantTermSumBelowRootedTail : ∀ cutoff observable →
      Physical.oneStepDefect defect cutoff observable
      ≤ Tail.rootedShellTail (Physical.cutoffDepth defect cutoff)

    finiteTelescopingIdentity : ∀ cutoff count observable → Set
    dyadicTailControlsFiniteTelescoping : ∀ cutoff count observable → Set
    cutoffDepthEscapes : Set
    continuumExpectationCauchy : ∀ observable → Set
    continuumExpectationLimitExists : ∀ observable → Set

open PhysicalRGDefectClosure public

------------------------------------------------------------------------
-- Marked FP moments.  The 6/5 inflation and 1/120 residual margin are imported
-- from the exact marked FP arithmetic; only physical marked-activity estimates
-- remain model-specific.
------------------------------------------------------------------------

record PhysicalMarkedMomentClosure
    (Polymer Observable : Set)
    (model : FP.AbstractPolymerModel Polymer)
    (marked : FP.MarkedActivityData Polymer Observable model) : Set₁ where
  field
    fpClosure : FP.MarkedFernandezProcacciClosure Polymer Observable model marked

    markedSourceAdmissibilityFromObservableNorm : ∀ observable → Set
    markedActivityInflationBelowSixFifths : ∀ observable polymer → Set
    markedNeighborhoodSatisfiesFP : ∀ observable polymer → Set

    singleScaleMomentAsMarkedPartitionRatio : ∀ observable → Set
    singleScaleExponentialMomentBound : ∀ observable → Set

    momentCost : Nat → Observable → ℚ
    momentCostBelowRootedTail : ∀ cutoff observable →
      momentCost cutoff observable ≤ Tail.rootedShellTail cutoff
    multiscaleMomentRecursion : ∀ cutoff observable → Set
    dyadicMomentCostsSummable : ∀ observable → Set
    uniformExponentialMomentBound : ∀ observable → Set

    allPolynomialMomentsFromExponential : ∀ degree observable → Set
    reflectedProductYoungDomination : ∀ left right → Set
    reflectedProductUniformIntegrability : ∀ left right → Set

open PhysicalMarkedMomentClosure public

------------------------------------------------------------------------
-- Finite-dimensional tightness and projective consistency.  Topological
-- compactness theorems remain one named authority rather than being hidden in
-- the lattice cluster estimates.
------------------------------------------------------------------------

record MeasureTopologyAuthority
    (Dimension Marginal Measure Observable Index : Set) : Set₁ where
  field
    finiteDimensionalStateSpaceIsPolish : Dimension → Set
    probabilityMeasureStructure : Measure → Set
    weakConvergence : Measure → Measure → Set
    finiteDimensionalProkhorov : ∀ dimension → Set
    diagonalSubsequenceForCountableObservableFamily : Set
    projectiveLimitTheorem : Set
    cylinderAlgebraMeasureDetermining : Set

open MeasureTopologyAuthority public

record PhysicalMarginalCompactnessClosure
    (Dimension Marginal Measure Observable Index : Set)
    (topology : MeasureTopologyAuthority Dimension Marginal Measure Observable Index) : Set₁ where
  field
    marginal : Dimension → Marginal
    evenMomentOrder : Dimension → Nat
    uniformMomentBound : Dimension → ℚ
    radius : Dimension → ℚ
    tailProbability : Dimension → ℚ

    coordinateMarkovBound : ∀ dimension → Set
    finiteUnionTailBound : ∀ dimension → Set
    finiteDimensionalTightness : ∀ dimension → Set
    gaugeInvariantMarginalTightness : ∀ dimension → Set

    selectedSubsequence : Measure
    subsequenceWeaklyConvergent : Set
    diagonalSubsequenceCoherent : Set

    restriction : Index → Index → Marginal → Marginal
    finiteMarginalRestrictionExact : ∀ lower upper → Set
    blockingCompatibilityOfMarginals : ∀ lower upper → Set
    projectiveConsistency : ∀ lower upper → Set
    consistencyPreservedUnderWeakLimit : ∀ lower upper → Set

    continuumMeasure : Measure
    continuumMeasureFromProjectiveLimit : Set
    cylinderExpectationUnique : Set
    anyTwoLimitsAgreeOnCylinderAlgebra : ∀ left right → Set
    continuumMeasureUnique : Set

open PhysicalMarginalCompactnessClosure public

record LiteralPhysicalT5Completion
    (Volume Boundary Observable Polymer Cluster Block Cutoff DefectTerm
     Dimension Marginal Measure Index : Set) : Set₂ where
  field
    expansion :
      Physical.FiniteVolumeClusterExpansion
        Volume Boundary Observable Polymer Cluster
    boundaryAgreement : InteriorBoundaryWeightAgreement expansion
    boundaryTail : RootedBoundaryTailClosure expansion boundaryAgreement

    defect : Physical.OneStepRGDefect Cutoff Observable DefectTerm
    rgClosure : PhysicalRGDefectClosure Cutoff Observable DefectTerm defect

    fpModel : FP.AbstractPolymerModel Polymer
    marked : FP.MarkedActivityData Polymer Observable fpModel
    moments : PhysicalMarkedMomentClosure Polymer Observable fpModel marked

    topology : MeasureTopologyAuthority Dimension Marginal Measure Observable Index
    compactness :
      PhysicalMarginalCompactnessClosure
        Dimension Marginal Measure Observable Index topology

    boundaryScaleMomentCompatibility : Set
    continuumMeasureCarriesOSGramLimits : Set

open LiteralPhysicalT5Completion public

boundaryCancellationReductionLevel : ProofLevel
boundaryCancellationReductionLevel = machineChecked

rgRelevantCancellationReductionLevel : ProofLevel
rgRelevantCancellationReductionLevel = machineChecked

markedMomentReductionLevel : ProofLevel
markedMomentReductionLevel = machineChecked

measureTopologySeparationLevel : ProofLevel
measureTopologySeparationLevel = machineChecked

physicalBoundaryWeightInputsLevel : ProofLevel
physicalBoundaryWeightInputsLevel = conditional

physicalRGIrrelevantGainInputsLevel : ProofLevel
physicalRGIrrelevantGainInputsLevel = conditional

physicalMarkedMomentInputsLevel : ProofLevel
physicalMarkedMomentInputsLevel = conditional

measureTopologyAuthorityInputsLevel : ProofLevel
measureTopologyAuthorityInputsLevel = conditional
