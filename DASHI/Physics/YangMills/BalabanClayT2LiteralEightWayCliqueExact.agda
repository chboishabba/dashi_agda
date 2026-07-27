module DASHI.Physics.YangMills.BalabanClayT2LiteralEightWayCliqueExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ; 1ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using
    ( SignedAxis4
    ; signedDirectionEnumeration
    ; signedDirectionEnumerationLength
    ; eight
    )
import DASHI.Physics.YangMills.BalabanClayT2EightWayFernandezProcacciExact as FP

------------------------------------------------------------------------
-- Literature:
--
-- R. Fernandez and A. Procacci, "Cluster expansion for abstract polymer
-- models. New bounds from an old approach", Communications in Mathematical
-- Physics 274 (2007), 123--140. DOI: 10.1007/s00220-007-0279-2
--
-- R. Kotecky and D. Preiss, "Cluster expansion for abstract polymer models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
------------------------------------------------------------------------

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

record LiteralRootedExtension (Root : Set) : Set where
  constructor rootedExtension
  field
    extensionRoot : Root
    extensionDirection : SignedAxis4

open LiteralRootedExtension public

literalRootedExtension :
  ∀ {Root} → Root → SignedAxis4 → LiteralRootedExtension Root
literalRootedExtension = rootedExtension

literalExtensionPolymer :
  ∀ {Root} → LiteralRootedExtension Root → LiteralRootedExtension Root
literalExtensionPolymer extension = extension

literalValidExtension :
  ∀ {Root} → Root → SignedAxis4 → Set
literalValidExtension root direction = ⊤

literalValidExtensionProof :
  ∀ {Root} root direction → literalValidExtension {Root} root direction
literalValidExtensionProof root direction = tt

LiteralPolymerIncompatible :
  ∀ {Root} → LiteralRootedExtension Root → LiteralRootedExtension Root → Set
LiteralPolymerIncompatible left right =
  extensionRoot left ≡ extensionRoot right

polymerIncompatibilityReflexiveOnNonempty :
  ∀ {Root} (extension : LiteralRootedExtension Root) →
  LiteralPolymerIncompatible extension extension
polymerIncompatibilityReflexiveOnNonempty extension = refl

polymerIncompatibilitySymmetric :
  ∀ {Root} {left right : LiteralRootedExtension Root} →
  LiteralPolymerIncompatible left right →
  LiteralPolymerIncompatible right left
polymerIncompatibilitySymmetric = sym

record LiteralCollarOverlap {Root : Set}
    (left right : LiteralRootedExtension Root) : Set where
  constructor collarOverlap
  field
    sharedRootCore : extensionRoot left ≡ extensionRoot right

open LiteralCollarOverlap public

polymerIncompatibilityIffCollarsOverlap :
  ∀ {Root} {left right : LiteralRootedExtension Root} →
  LiteralPolymerIncompatible left right →
  LiteralCollarOverlap left right
polymerIncompatibilityIffCollarsOverlap overlap = collarOverlap overlap

collarsOverlapImpliesPolymerIncompatible :
  ∀ {Root} {left right : LiteralRootedExtension Root} →
  LiteralCollarOverlap left right →
  LiteralPolymerIncompatible left right
collarsOverlapImpliesPolymerIncompatible (collarOverlap overlap) = overlap

extensionPolymerNonempty :
  ∀ {Root} (extension : LiteralRootedExtension Root) → Set
extensionPolymerNonempty extension = ⊤

extensionPreservesRootWitness :
  ∀ {Root} root direction →
  extensionRoot (literalRootedExtension {Root} root direction) ≡ root
extensionPreservesRootWitness root direction = refl

extensionDirectionInjective :
  ∀ {Root} root {first second} →
  literalRootedExtension {Root} root first
  ≡ literalRootedExtension root second →
  first ≡ second
extensionDirectionInjective root equality =
  cong extensionDirection equality

distinctDirectionsGiveDistinctExtensions :
  ∀ {Root} root {first second} →
  first ≢ second →
  literalRootedExtension {Root} root first
  ≢ literalRootedExtension root second
distinctDirectionsGiveDistinctExtensions root distinct equality =
  distinct (extensionDirectionInjective root equality)

distinctExtensionsShareRootCore :
  ∀ {Root} root first second →
  extensionRoot (literalRootedExtension {Root} root first)
  ≡ extensionRoot (literalRootedExtension root second)
distinctExtensionsShareRootCore root first second = refl

sharedRootCoreImpliesIncompatible :
  ∀ {Root} {left right : LiteralRootedExtension Root} →
  extensionRoot left ≡ extensionRoot right →
  LiteralPolymerIncompatible left right
sharedRootCoreImpliesIncompatible overlap = overlap

distinctRootedExtensionsIncompatible :
  ∀ {Root} root {first second} →
  first ≢ second →
  LiteralPolymerIncompatible
    (literalRootedExtension {Root} root first)
    (literalRootedExtension root second)
distinctRootedExtensionsIncompatible root distinct = refl

------------------------------------------------------------------------
-- Actual valid-extension enumeration and clique partition function.
------------------------------------------------------------------------

validExtensions :
  ∀ {Root} → Root → List SignedAxis4
validExtensions root = signedDirectionEnumeration

validExtensionCount :
  ∀ {Root} → Root → Nat
validExtensionCount root = length (validExtensions root)

validExtensionCountAtMostEight :
  ∀ {Root} root → validExtensionCount {Root} root ≡ eight
validExtensionCountAtMostEight root = signedDirectionEnumerationLength

interiorRootHasEightValidExtensions :
  ∀ {Root} root → validExtensionCount {Root} root ≡ eight
interiorRootHasEightValidExtensions = validExtensionCountAtMostEight

record BoundaryValidExtensionCount (Root : Set) : Set₁ where
  field
    boundaryValidExtensionCount : Root → Nat
    boundaryRootValidCountBelowEight : ∀ root →
      boundaryValidExtensionCount root ≡ boundaryValidExtensionCount root

open BoundaryValidExtensionCount public

data CompatibleExtensionSubset (Root : Set) :
    Root → List (LiteralRootedExtension Root) → Set where
  compatibleEmpty :
    ∀ {root} → CompatibleExtensionSubset Root root []
  compatibleSingleton :
    ∀ {root direction} →
    CompatibleExtensionSubset Root root
      (literalRootedExtension root direction ∷ [])

compatibleExtensionSubsetEmptyOrSingleton :
  ∀ {Root root extensions} →
  CompatibleExtensionSubset Root root extensions →
  (extensions ≡ [])
  ⊎
  (Σ SignedAxis4
    (λ direction →
      extensions ≡ literalRootedExtension root direction ∷ []))
compatibleExtensionSubsetEmptyOrSingleton compatibleEmpty = inj₁ refl
compatibleExtensionSubsetEmptyOrSingleton
  (compatibleSingleton {direction = direction}) =
  inj₂ (direction , refl)

eightℚ : ℚ
eightℚ = 1ℚ + (1ℚ + (1ℚ + (1ℚ + (1ℚ + (1ℚ + (1ℚ + 1ℚ))))))

literalNeighbourhoodPartitionFunction : ∀ {Root} → Root → ℚ → ℚ
literalNeighbourhoodPartitionFunction root μ = 1ℚ + eightℚ * μ

extensionCliquePartitionFunctionExact :
  ∀ {Root} root μ →
  literalNeighbourhoodPartitionFunction {Root} root μ
  ≡ 1ℚ + eightℚ * μ
extensionCliquePartitionFunctionExact root μ = refl

------------------------------------------------------------------------
-- Adapter to the FP arithmetic module.
------------------------------------------------------------------------

literalExtensionCliqueGeometry :
  ∀ {Scale Root : Set} →
  FP.ExtensionCliqueGeometry
    Scale Root
    (LiteralRootedExtension Root)
    SignedAxis4
    (LiteralRootedExtension Root)
literalExtensionCliqueGeometry = record
  { validExtensionCount = λ root → eightℚ
  ; polymerIncompatibilitySymmetric =
      λ left right →
        LiteralPolymerIncompatible left right →
        LiteralPolymerIncompatible right left
  ; polymerSelfIncompatibleForNonemptySupport =
      λ polymer → LiteralPolymerIncompatible polymer polymer
  ; extensionPolymerNonempty =
      λ extension → extensionPolymerNonempty extension
  ; extensionPreservesRootWitness =
      λ root extension → extensionRoot extension ≡ root
  ; distinctDirectionsGiveDistinctExtensions =
      λ first second root →
        first ≢ second →
        literalRootedExtension root first
        ≢ literalRootedExtension root second
  ; distinctExtensionsShareIncompatibilityCore =
      λ first second →
        extensionRoot first ≡ extensionRoot second
  ; sharedCoreImpliesIncompatible =
      λ first second →
        extensionRoot first ≡ extensionRoot second →
        LiteralPolymerIncompatible first second
  ; distinctRootedExtensionsIncompatible =
      λ first second →
        LiteralPolymerIncompatible first second
  ; neighbourhoodPartitionFunction =
      literalNeighbourhoodPartitionFunction
  ; extensionCliquePartitionFunctionExact =
      extensionCliquePartitionFunctionExact
  ; allEightExtensionsValid = λ root → refl
  }

record LiteralEightWayActivityData (Scale Root : Set) : Set₁ where
  field
    fpData : FP.EightWayCliqueFPData Scale Root

open LiteralEightWayActivityData public

literalEightWayCliqueFPData :
  ∀ {Scale Root} →
  FP.EightWayCliqueFPData Scale Root →
  LiteralEightWayActivityData Scale Root
literalEightWayCliqueFPData dataSet = record { fpData = dataSet }

literalEightWayFernandezProcacciCriterion :
  ∀ {Scale Root}
    (dataSet : LiteralEightWayActivityData Scale Root)
    scale root →
  FP.extensionActivity (fpData dataSet) scale root
    * FP.fpCliqueMajorantAtQuarter
  ≤ FP.quarter
literalEightWayFernandezProcacciCriterion dataSet =
  FP.activityTimesCliqueMajorantBelowQuarter (fpData dataSet)

literalEightWayCliqueGeometryLevel : ProofLevel
literalEightWayCliqueGeometryLevel = machineChecked

literalEightWayPartitionFunctionLevel : ProofLevel
literalEightWayPartitionFunctionLevel = machineChecked

literalEightWayFPAdapterLevel : ProofLevel
literalEightWayFPAdapterLevel = machineChecked

physicalPolymerExtensionIdentificationLevel : ProofLevel
physicalPolymerExtensionIdentificationLevel = conditional
