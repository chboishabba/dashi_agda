module DASHI.Physics.YangMills.BalabanClayT5RootedShellBoundaryTailExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

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

halfPowerMatchesConfigured : ∀ depth →
  Shell.halfPower depth ≡ Tail.powHalf depth
halfPowerMatchesConfigured zero = refl
halfPowerMatchesConfigured (suc depth)
  rewrite halfPowerMatchesConfigured depth = refl

rootedTailMatchesConfigured : ∀ depth →
  Shell.quarter * Shell.halfPower depth ≡ Tail.rootedShellTail depth
rootedTailMatchesConfigured depth
  rewrite halfPowerMatchesConfigured depth = refl

record RootedShellBoundaryDifferenceData
    (Scale Volume Root Observable : Set) : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root

    distinguishedRoot : Scale → Volume → Observable → Root
    boundaryShellIndex : Scale → Volume → Nat
    AdmissibleObservable : Observable → Set

    finiteExpectation thermodynamicExpectation :
      Scale → Volume → Observable → ℚ
    absoluteDifference : ℚ → ℚ → ℚ

    onlyBoundaryCrossingClustersContribute :
      ∀ scale volume observable → AdmissibleObservable observable → Set

    boundaryCrossingClusterMinimalDiameter :
      ∀ scale volume → Set

    expectationDifferenceBelowRootedShell :
      ∀ scale volume observable → AdmissibleObservable observable →
      absoluteDifference
        (finiteExpectation scale volume observable)
        (thermodynamicExpectation scale volume observable)
      ≤ Shell.rootedShell shellData scale volume
          (distinguishedRoot scale volume observable)
          (boundaryShellIndex scale volume)

    transitive : ∀ {left middle right : ℚ} →
      left ≤ middle → middle ≤ right → left ≤ right

open RootedShellBoundaryDifferenceData public

boundaryCrossingClusterExponentialBoundFromRootedShell :
  ∀ {Scale Volume Root Observable}
    (dataSet : RootedShellBoundaryDifferenceData Scale Volume Root Observable)
    scale volume observable →
  AdmissibleObservable dataSet observable →
  absoluteDifference dataSet
    (finiteExpectation dataSet scale volume observable)
    (thermodynamicExpectation dataSet scale volume observable)
  ≤ Tail.rootedShellTail (boundaryShellIndex dataSet scale volume)
boundaryCrossingClusterExponentialBoundFromRootedShell
  dataSet scale volume observable admissible =
  subst
    (λ upper →
      absoluteDifference dataSet
        (finiteExpectation dataSet scale volume observable)
        (thermodynamicExpectation dataSet scale volume observable)
      ≤ upper)
    (rootedTailMatchesConfigured (boundaryShellIndex dataSet scale volume))
    (transitive dataSet
      (expectationDifferenceBelowRootedShell
        dataSet scale volume observable admissible)
      (Shell.rootedShellBelowQuarterHalfPower
        (shellData dataSet) scale volume
        (distinguishedRoot dataSet scale volume observable)
        (boundaryShellIndex dataSet scale volume)))

record BoundaryDistanceEscapes
    (Scale Volume : Set)
    (boundaryIndex : Scale → Volume → Nat) : Set₁ where
  field
    indexEventuallyBeyond : ∀ scale depth → Set
    halfPowerVanishes : Set

open BoundaryDistanceEscapes public

finiteVolumePairTailVanishesFromEscapingBoundary :
  ∀ {Scale Volume}
    {boundaryIndex : Scale → Volume → Nat} →
  BoundaryDistanceEscapes Scale Volume boundaryIndex → Set
finiteVolumePairTailVanishesFromEscapingBoundary = halfPowerVanishes

record RootedShellConfiguredBoundaryAdapter
    (Scale Volume Root Observable : Set) : Set₁ where
  field
    rootedData : RootedShellBoundaryDifferenceData Scale Volume Root Observable
    distanceEscapes : BoundaryDistanceEscapes
      Scale Volume (boundaryShellIndex rootedData)

    reflectedProduct : Observable → Observable → Observable
    reflectedProductAdmissible : ∀ left right →
      AdmissibleObservable rootedData (reflectedProduct left right)

    distance : ℚ → ℚ → ℚ
    distanceMatchesAbsoluteDifference : ∀ left right →
      distance left right ≡ absoluteDifference rootedData left right

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
      boundaryShellIndex (rootedData dataSet)
  ; Tail.ConfiguredBoundaryClusterTail.onlyBoundaryCrossingClustersContribute =
      λ scale volume left right →
        onlyBoundaryCrossingClustersContribute (rootedData dataSet)
          scale volume (reflectedProduct dataSet left right)
          (reflectedProductAdmissible dataSet left right)
  ; Tail.ConfiguredBoundaryClusterTail.boundaryCrossingClusterMinimalDiameter =
      boundaryCrossingClusterMinimalDiameter (rootedData dataSet)
  ; Tail.ConfiguredBoundaryClusterTail.boundaryCrossingClusterExponentialBound =
      λ scale volume left right →
        subst
          (λ lower → lower
            ≤ Tail.rootedShellTail
                (boundaryShellIndex (rootedData dataSet) scale volume))
          (distanceMatchesAbsoluteDifference dataSet
            (finiteExpectation (rootedData dataSet)
              scale volume (reflectedProduct dataSet left right))
            (thermodynamicExpectation (rootedData dataSet)
              scale volume (reflectedProduct dataSet left right)))
          (boundaryCrossingClusterExponentialBoundFromRootedShell
            (rootedData dataSet) scale volume
            (reflectedProduct dataSet left right)
            (reflectedProductAdmissible dataSet left right))
  ; Tail.ConfiguredBoundaryClusterTail.boundaryShellIndexEscapes =
      λ scale → indexEventuallyBeyond (distanceEscapes dataSet) scale
  ; Tail.ConfiguredBoundaryClusterTail.geometricTailVanishes =
      halfPowerVanishes (distanceEscapes dataSet)
  }

rootedShellTailIdentificationLevel : ProofLevel
rootedShellTailIdentificationLevel = machineChecked

rootedShellToBoundaryTailReductionLevel : ProofLevel
rootedShellToBoundaryTailReductionLevel = machineChecked

boundaryEscapeInputsLevel : ProofLevel
boundaryEscapeInputsLevel = conditional
