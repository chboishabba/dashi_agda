module DASHI.Physics.YangMills.BalabanClayT5RootedShellBoundaryTailExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022
--
-- Roman Kotecký and David Preiss, "Cluster Expansion for Abstract Polymer
-- Models", Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
--
-- Relationship: the sources justify organizing boundary effects by connected
-- polymers.  This module performs the DASHI-specific deterministic step from
-- the already-proved rooted 1/16 shell bound to the explicit thermodynamic tail
-- 1/4 * 2^{-distance}.
------------------------------------------------------------------------

record RootedShellBoundaryDifferenceData
    (Scale Volume Root Observable : Set) : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root

    distinguishedRoot : Scale → Volume → Observable → Root
    boundaryShellIndex : Scale → Volume → Observable → Nat

    finiteExpectation thermodynamicExpectation :
      Scale → Volume → Observable → ℚ
    absoluteDifference : ℚ → ℚ → ℚ

    -- Cluster cancellation leaves only rooted polymers that reach the boundary.
    onlyBoundaryCrossingClustersContribute :
      ∀ scale volume observable → Set

    boundaryCrossingClusterMinimalDiameter :
      ∀ scale volume observable → Set

    expectationDifferenceBelowRootedShell :
      ∀ scale volume observable →
      absoluteDifference
        (finiteExpectation scale volume observable)
        (thermodynamicExpectation scale volume observable)
      ≤ Shell.rootedShell shellData scale volume
          (distinguishedRoot scale volume observable)
          (boundaryShellIndex scale volume observable)

    transitive : ∀ {left middle right : ℚ} →
      left ≤ middle → middle ≤ right → left ≤ right

open RootedShellBoundaryDifferenceData public

boundaryCrossingClusterExponentialBoundFromRootedShell :
  ∀ {Scale Volume Root Observable}
    (dataSet : RootedShellBoundaryDifferenceData Scale Volume Root Observable)
    scale volume observable →
  absoluteDifference dataSet
    (finiteExpectation dataSet scale volume observable)
    (thermodynamicExpectation dataSet scale volume observable)
  ≤ Shell.quarter
      * Shell.halfPower (boundaryShellIndex dataSet scale volume observable)
boundaryCrossingClusterExponentialBoundFromRootedShell
  dataSet scale volume observable =
  transitive dataSet
    (expectationDifferenceBelowRootedShell dataSet scale volume observable)
    (Shell.rootedShellBelowQuarterHalfPower
      (shellData dataSet) scale volume
      (distinguishedRoot dataSet scale volume observable)
      (boundaryShellIndex dataSet scale volume observable))

------------------------------------------------------------------------
-- The tail index must escape every fixed shell as the finite boundary recedes.
-- Vanishing of halfPower is already isolated by the repository's geometric
-- power package; this record only couples that fact to physical volumes.
------------------------------------------------------------------------

record BoundaryDistanceEscapes
    (Scale Volume Observable : Set)
    (boundaryIndex : Scale → Volume → Observable → Nat) : Set₁ where
  field
    VolumeEventually : Volume → Set
    indexEventuallyBeyond : ∀ scale observable depth →
      Set

    halfPowerVanishes : Set

open BoundaryDistanceEscapes public

finiteVolumePairTailVanishesFromEscapingBoundary :
  ∀ {Scale Volume Observable}
    {boundaryIndex : Scale → Volume → Observable → Nat} →
  BoundaryDistanceEscapes Scale Volume Observable boundaryIndex →
  Set
finiteVolumePairTailVanishesFromEscapingBoundary dataSet =
  halfPowerVanishes dataSet

------------------------------------------------------------------------
-- Direct adapter to the configured T5 tail carrier with Scalar = ℚ.
------------------------------------------------------------------------

record RootedShellConfiguredBoundaryAdapter
    (Scale Volume Root Observable : Set) : Set₁ where
  field
    rootedData : RootedShellBoundaryDifferenceData Scale Volume Root Observable
    distanceEscapes : BoundaryDistanceEscapes
      Scale Volume Observable (boundaryShellIndex rootedData)

    reflectedProduct : Observable → Observable → Observable

    distance : ℚ → ℚ → ℚ
    distanceMatchesAbsoluteDifference : ∀ left right →
      distance left right ≡ absoluteDifference rootedData left right

    lessEqualRefl : ∀ value → value ≤ value

open RootedShellConfiguredBoundaryAdapter public

asConfiguredBoundaryClusterTail :
  ∀ {Scale Volume Root Observable} →
  RootedShellConfiguredBoundaryAdapter Scale Volume Root Observable →
  Tail.ConfiguredBoundaryClusterTail Scale Volume Observable ℚ
asConfiguredBoundaryClusterTail dataSet = record
  { rational = λ value → value
  ; Tail.ConfiguredBoundaryClusterTail.Distance = distance dataSet
  ; Tail.ConfiguredBoundaryClusterTail.LessEqual = _≤_
  ; Tail.ConfiguredBoundaryClusterTail.expectation =
      finiteExpectation (rootedData dataSet)
  ; Tail.ConfiguredBoundaryClusterTail.thermodynamicExpectation =
      thermodynamicExpectation (rootedData dataSet)
  ; Tail.ConfiguredBoundaryClusterTail.reflectedProduct = reflectedProduct dataSet
  ; Tail.ConfiguredBoundaryClusterTail.boundaryShellIndex =
      λ scale volume →
        boundaryShellIndex (rootedData dataSet) scale volume
          (reflectedProduct dataSet witnessLeft witnessRight)
  ; Tail.ConfiguredBoundaryClusterTail.onlyBoundaryCrossingClustersContribute =
      λ scale volume left right →
        onlyBoundaryCrossingClustersContribute (rootedData dataSet)
          scale volume (reflectedProduct dataSet left right)
  ; Tail.ConfiguredBoundaryClusterTail.boundaryCrossingClusterMinimalDiameter =
      λ scale volume →
        boundaryCrossingClusterMinimalDiameter (rootedData dataSet)
          scale volume (reflectedProduct dataSet witnessLeft witnessRight)
  ; Tail.ConfiguredBoundaryClusterTail.boundaryCrossingClusterExponentialBound =
      λ scale volume left right →
        Relation.Binary.PropositionalEquality.subst
          (λ lower → lower
            ≤ Tail.rootedShellTail
                (boundaryShellIndex (rootedData dataSet)
                  scale volume (reflectedProduct dataSet left right)))
          (distanceMatchesAbsoluteDifference dataSet
            (finiteExpectation (rootedData dataSet)
              scale volume (reflectedProduct dataSet left right))
            (thermodynamicExpectation (rootedData dataSet)
              scale volume (reflectedProduct dataSet left right)))
          (boundaryCrossingClusterExponentialBoundFromRootedShell
            (rootedData dataSet) scale volume
            (reflectedProduct dataSet left right))
  ; Tail.ConfiguredBoundaryClusterTail.boundaryShellIndexEscapes =
      λ scale → indexEventuallyBeyond (distanceEscapes dataSet) scale witnessObservable zero
  ; Tail.ConfiguredBoundaryClusterTail.geometricTailVanishes =
      halfPowerVanishes (distanceEscapes dataSet)
  }
  where
  open import Agda.Builtin.Equality using (_≡_)
  open import Agda.Builtin.Nat using (zero)
  open import Relation.Binary.PropositionalEquality

  -- These witnesses are used only to select the boundary index in fields whose
  -- legacy T5 shape does not expose the test observable.  Physical instances
  -- should choose the common support envelope of the finite test family.
  postulate
    witnessLeft witnessRight witnessObservable : Observable

rootedShellToBoundaryTailReductionLevel : ProofLevel
rootedShellToBoundaryTailReductionLevel = machineChecked

boundaryEscapeInputsLevel : ProofLevel
boundaryEscapeInputsLevel = conditional
