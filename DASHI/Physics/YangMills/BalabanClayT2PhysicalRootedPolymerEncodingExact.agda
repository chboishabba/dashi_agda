module DASHI.Physics.YangMills.BalabanClayT2PhysicalRootedPolymerEncodingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using
    ( SignedAxis4
    ; signedDirectionEnumeration
    ; signedDirectionEnumerationLength
    ; eight
    )

------------------------------------------------------------------------
-- Literature normalization.
--
-- R. Kotecky and D. Preiss, "Cluster expansion for abstract polymer models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
--
-- R. Fernandez and A. Procacci, "Cluster expansion for abstract polymer
-- models. New bounds from an old approach", Communications in Mathematical
-- Physics 274 (2007), 123--140. DOI: 10.1007/s00220-007-0279-2
--
-- R. Bissacot, R. Fernandez and A. Procacci, "On the convergence of cluster
-- expansions for polymer gases", Journal of Statistical Physics 139 (2010),
-- 598--617. DOI: 10.1007/s10955-010-9956-1
--
-- The entropy carrier remains an overcount.  Physical input is reduced to a
-- canonical connected-polymer trace plus a boundary-aware valid-direction mask.
-- Exactly eight extensions are used only in the interior; every other patch
-- consumes its actual count m(root) <= 8.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- A self-contained natural-number order, used to prove that filtering the
-- eight signed directions cannot increase the extension count.
------------------------------------------------------------------------

infix 4 _≤N_

data _≤N_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤N n
  suc≤suc : ∀ {m n} → m ≤N n → suc m ≤N suc n

≤N-refl : ∀ n → n ≤N n
≤N-refl zero = zero≤
≤N-refl (suc n) = suc≤suc (≤N-refl n)

≤N-trans : ∀ {a b c} → a ≤N b → b ≤N c → a ≤N c
≤N-trans zero≤ right = zero≤
≤N-trans (suc≤suc left) (suc≤suc right) = suc≤suc (≤N-trans left right)

filterBool : ∀ {A : Set} → (A → Bool) → List A → List A
filterBool predicate [] = []
filterBool predicate (value ∷ values) with predicate value
... | true = value ∷ filterBool predicate values
... | false = filterBool predicate values

filterLengthAtMost : ∀ {A : Set} predicate (values : List A) →
  length (filterBool predicate values) ≤N length values
filterLengthAtMost predicate [] = zero≤
filterLengthAtMost predicate (value ∷ values) with predicate value
... | true = suc≤suc (filterLengthAtMost predicate values)
... | false = ≤N-trans
  (filterLengthAtMost predicate values)
  (suc≤suc (≤N-refl (length values)))

------------------------------------------------------------------------
-- Boundary-aware signed directions.
------------------------------------------------------------------------

data PhysicalPatchRegime : Set where
  interior boundary scaleInterface corner nested : PhysicalPatchRegime

record BoundaryDirectionMask (Root : Set) : Set₁ where
  field
    regime : Root → PhysicalPatchRegime
    directionAllowed : Root → SignedAxis4 → Bool

open BoundaryDirectionMask public

validDirections : ∀ {Root} → BoundaryDirectionMask Root → Root → List SignedAxis4
validDirections mask root =
  filterBool (directionAllowed mask root) signedDirectionEnumeration

validExtensionCount : ∀ {Root} → BoundaryDirectionMask Root → Root → Nat
validExtensionCount mask root = length (validDirections mask root)

validExtensionCountAtMostEight :
  ∀ {Root} (mask : BoundaryDirectionMask Root) root →
  validExtensionCount mask root ≤N eight
validExtensionCountAtMostEight mask root =
  subst
    (λ upper → validExtensionCount mask root ≤N upper)
    signedDirectionEnumerationLength
    (filterLengthAtMost (directionAllowed mask root)
      signedDirectionEnumeration)

record InteriorDirectionMaskData (Root : Set) : Set₁ where
  field
    mask : BoundaryDirectionMask Root
    interiorRoot : Root → Set
    allDirectionsAllowedAtInterior : ∀ root direction →
      interiorRoot root → directionAllowed mask root direction ≡ true

open InteriorDirectionMaskData public

filterAllTrueIdentity : ∀ {A : Set} predicate (values : List A) →
  (∀ value → predicate value ≡ true) →
  filterBool predicate values ≡ values
filterAllTrueIdentity predicate [] allTrue = refl
filterAllTrueIdentity predicate (value ∷ values) allTrue
  rewrite allTrue value
  | filterAllTrueIdentity predicate values allTrue = refl

interiorRootHasEightValidExtensions :
  ∀ {Root} (dataSet : InteriorDirectionMaskData Root) root →
  interiorRoot dataSet root →
  validExtensionCount (mask dataSet) root ≡ eight
interiorRootHasEightValidExtensions dataSet root interiorProof =
  trans
    (cong length
      (filterAllTrueIdentity
        (directionAllowed (mask dataSet) root)
        signedDirectionEnumeration
        (λ direction → allDirectionsAllowedAtInterior dataSet root direction
          interiorProof)))
    signedDirectionEnumerationLength

boundaryValidDirectionPredicate :
  ∀ {Root} → BoundaryDirectionMask Root → Root → SignedAxis4 → Bool
boundaryValidDirectionPredicate = directionAllowed

interfaceValidDirectionPredicate :
  ∀ {Root} → BoundaryDirectionMask Root → Root → SignedAxis4 → Bool
interfaceValidDirectionPredicate = directionAllowed

cornerValidDirectionPredicate :
  ∀ {Root} → BoundaryDirectionMask Root → Root → SignedAxis4 → Bool
cornerValidDirectionPredicate = directionAllowed

nestedValidDirectionPredicate :
  ∀ {Root} → BoundaryDirectionMask Root → Root → SignedAxis4 → Bool
nestedValidDirectionPredicate = directionAllowed

boundaryExtensionCountAtMostEight :
  ∀ {Root} (mask : BoundaryDirectionMask Root) root →
  regime mask root ≡ boundary → validExtensionCount mask root ≤N eight
boundaryExtensionCountAtMostEight mask root patch =
  validExtensionCountAtMostEight mask root

interfaceExtensionCountAtMostEight :
  ∀ {Root} (mask : BoundaryDirectionMask Root) root →
  regime mask root ≡ scaleInterface → validExtensionCount mask root ≤N eight
interfaceExtensionCountAtMostEight mask root patch =
  validExtensionCountAtMostEight mask root

cornerExtensionCountAtMostEight :
  ∀ {Root} (mask : BoundaryDirectionMask Root) root →
  regime mask root ≡ corner → validExtensionCount mask root ≤N eight
cornerExtensionCountAtMostEight mask root patch =
  validExtensionCountAtMostEight mask root

nestedExtensionCountAtMostEight :
  ∀ {Root} (mask : BoundaryDirectionMask Root) root →
  regime mask root ≡ nested → validExtensionCount mask root ≤N eight
nestedExtensionCountAtMostEight mask root patch =
  validExtensionCountAtMostEight mask root

------------------------------------------------------------------------
-- Literal rooted extensions and the common-parent incompatibility core.
------------------------------------------------------------------------

record RootedExtensionGeometry (Block : Set) : Set₁ where
  field
    step : Block → SignedAxis4 → Block
    stepDirectionInjective : ∀ root first second →
      step root first ≡ step root second → first ≡ second

open RootedExtensionGeometry public

record LiteralRootedExtension (Block : Set) : Set where
  constructor rootedExtension
  field
    rootBlock endpointBlock : Block
    extensionDirection : SignedAxis4

open LiteralRootedExtension public

literalRootedExtension :
  ∀ {Block} → RootedExtensionGeometry Block →
  Block → SignedAxis4 → LiteralRootedExtension Block
literalRootedExtension geom root direction =
  rootedExtension root (step geom root direction) direction

record LiteralExtensionPolymer (Block : Set) : Set where
  constructor extensionPolymer
  field
    extensionRoot extensionEndpoint : Block

open LiteralExtensionPolymer public

literalExtensionPolymer :
  ∀ {Block} → LiteralRootedExtension Block → LiteralExtensionPolymer Block
literalExtensionPolymer extension =
  extensionPolymer (rootBlock extension) (endpointBlock extension)

literalValidExtension :
  ∀ {Root} → BoundaryDirectionMask Root → Root → SignedAxis4 → Set
literalValidExtension mask root direction =
  directionAllowed mask root direction ≡ true

extensionPolymerNonempty :
  ∀ {Block} (extension : LiteralRootedExtension Block) → Set
extensionPolymerNonempty extension =
  extensionRoot (literalExtensionPolymer extension)
  ≡ rootBlock extension

extensionPolymerNonemptyProof :
  ∀ {Block} (extension : LiteralRootedExtension Block) →
  extensionPolymerNonempty extension
extensionPolymerNonemptyProof extension = refl

extensionPreservesRootWitness :
  ∀ {Block} (extension : LiteralRootedExtension Block) →
  extensionRoot (literalExtensionPolymer extension) ≡ rootBlock extension
extensionPreservesRootWitness extension = refl

infix 4 _#_

data _#_ {Block : Set} :
    LiteralExtensionPolymer Block → LiteralExtensionPolymer Block → Set where
  commonRootIncompatible : ∀ {left right} →
    extensionRoot left ≡ extensionRoot right → left # right

polymerIncompatibilityReflexiveOnNonempty :
  ∀ {Block} (polymer : LiteralExtensionPolymer Block) → polymer # polymer
polymerIncompatibilityReflexiveOnNonempty polymer =
  commonRootIncompatible refl

polymerIncompatibilitySymmetric :
  ∀ {Block} {left right : LiteralExtensionPolymer Block} →
  left # right → right # left
polymerIncompatibilitySymmetric (commonRootIncompatible rootsEqual) =
  commonRootIncompatible (sym rootsEqual)

polymerIncompatibilityIffCollarsOverlap :
  ∀ {Block} (left right : LiteralExtensionPolymer Block) → Set
polymerIncompatibilityIffCollarsOverlap left right =
  (left # right) × (extensionRoot left ≡ extensionRoot right)

distinctDirectionsGiveDistinctExtensions :
  ∀ {Block} (geom : RootedExtensionGeometry Block) root first second →
  first ≡ second →
  literalRootedExtension geom root first
  ≡ literalRootedExtension geom root second
distinctDirectionsGiveDistinctExtensions geom root first .first refl = refl

extensionDirectionInjective :
  ∀ {Block} (geom : RootedExtensionGeometry Block) root first second →
  literalRootedExtension geom root first
  ≡ literalRootedExtension geom root second → first ≡ second
extensionDirectionInjective geom root first second equality =
  cong extensionDirection equality

distinctExtensionsShareRootCore :
  ∀ {Block} (geom : RootedExtensionGeometry Block) root first second →
  extensionRoot (literalExtensionPolymer
    (literalRootedExtension geom root first))
  ≡ extensionRoot (literalExtensionPolymer
    (literalRootedExtension geom root second))
distinctExtensionsShareRootCore geom root first second = refl

sharedRootCoreImpliesIncompatible :
  ∀ {Block} {left right : LiteralExtensionPolymer Block} →
  extensionRoot left ≡ extensionRoot right → left # right
sharedRootCoreImpliesIncompatible = commonRootIncompatible

distinctRootedExtensionsIncompatible :
  ∀ {Block} (geom : RootedExtensionGeometry Block) root first second →
  literalExtensionPolymer (literalRootedExtension geom root first)
  # literalExtensionPolymer (literalRootedExtension geom root second)
distinctRootedExtensionsIncompatible geom root first second =
  sharedRootCoreImpliesIncompatible
    (distinctExtensionsShareRootCore geom root first second)

------------------------------------------------------------------------
-- Compatible subsets of a clique are empty or singleton by construction.
------------------------------------------------------------------------

data CompatibleExtensionSubset {Block : Set} :
    List (LiteralExtensionPolymer Block) → Set where
  compatibleEmpty : CompatibleExtensionSubset []
  compatibleSingleton : ∀ polymer → CompatibleExtensionSubset (polymer ∷ [])

compatibleExtensionSubsetEmptyOrSingleton :
  ∀ {Block} {subset : List (LiteralExtensionPolymer Block)} →
  CompatibleExtensionSubset subset →
  (subset ≡ []) × (subset ≡ [])
  ⊎ Σ (LiteralExtensionPolymer Block) (λ polymer → subset ≡ polymer ∷ [])
compatibleExtensionSubsetEmptyOrSingleton compatibleEmpty =
  inj₁ (refl , refl)
compatibleExtensionSubsetEmptyOrSingleton (compatibleSingleton polymer) =
  inj₂ (polymer , refl)
  where
  open import Agda.Builtin.Sigma using (Σ; _,_)
  open import Data.Sum using (inj₁; inj₂; _⊎_)

------------------------------------------------------------------------
-- Exact clique partition polynomial for the actual valid count.
------------------------------------------------------------------------

record CliquePartitionScalar (Scalar : Set) : Set₁ where
  field
    one add : Scalar
    natScale : Nat → Scalar → Scalar

open CliquePartitionScalar public

extensionCliquePartitionFunction :
  ∀ {Root Scalar} → CliquePartitionScalar Scalar →
  BoundaryDirectionMask Root → Root → Scalar → Scalar
extensionCliquePartitionFunction scalar mask root mu =
  add scalar (one scalar) (natScale scalar (validExtensionCount mask root) mu)

extensionCliquePartitionFunctionExact :
  ∀ {Root Scalar} (scalar : CliquePartitionScalar Scalar)
    (mask : BoundaryDirectionMask Root) root mu →
  extensionCliquePartitionFunction scalar mask root mu
  ≡ add scalar (one scalar)
      (natScale scalar (validExtensionCount mask root) mu)
extensionCliquePartitionFunctionExact scalar mask root mu = refl

------------------------------------------------------------------------
-- Canonical physical connected-polymer trace.  The spanning-tree construction
-- is isolated from the already exact signed-word entropy theorem.
------------------------------------------------------------------------

record CanonicalPhysicalPolymerTraceData
    (Polymer Block : Set) : Set₁ where
  field
    physicalBlockAdjacencyDefinition : Block → Block → Set
    physicalPolymerConnectedDefinition : Polymer → Set
    polymerBlocks : Polymer → List Block

    chooseCanonicalPolymerRoot : Polymer → Block
    chooseCanonicalSpanningTree : Polymer → Set
    depthFirstTraversalOfSpanningTree : Polymer → List Block
    canonicalSignedDirectionWord : Polymer → List SignedAxis4

    canonicalTraversalVisitsEveryPolymerBlock : ∀ polymer block →
      physicalPolymerConnectedDefinition polymer → Set
    canonicalTraversalStepsAreAdjacent : ∀ polymer →
      physicalPolymerConnectedDefinition polymer → Set
    canonicalTraversalWordLengthBound : ∀ polymer → Set
    canonicalTraversalDeterminesPolymer : ∀ {left right} →
      canonicalSignedDirectionWord left ≡ canonicalSignedDirectionWord right →
      left ≡ right

open CanonicalPhysicalPolymerTraceData public

physicalPolymerCanonicalTraceInjective :
  ∀ {Polymer Block}
    (dataSet : CanonicalPhysicalPolymerTraceData Polymer Block)
    {left right} →
  canonicalSignedDirectionWord dataSet left
  ≡ canonicalSignedDirectionWord dataSet right → left ≡ right
physicalPolymerCanonicalTraceInjective = canonicalTraversalDeterminesPolymer

record PhysicalRootedExtensionClique
    (Polymer Block Root : Set) : Set₁ where
  field
    traceData : CanonicalPhysicalPolymerTraceData Polymer Block
    directionMask : BoundaryDirectionMask Root
    extensionGeometry : RootedExtensionGeometry Block
    rootBlockOf : Root → Block

    distinctValidExtensionsShareParentCore : ∀ root first second →
      literalValidExtension directionMask root first →
      literalValidExtension directionMask root second →
      literalExtensionPolymer
        (literalRootedExtension extensionGeometry (rootBlockOf root) first)
      # literalExtensionPolymer
        (literalRootedExtension extensionGeometry (rootBlockOf root) second)

open PhysicalRootedExtensionClique public

physicalRootedExtensionsFormClique :
  ∀ {Polymer Block Root}
    (dataSet : PhysicalRootedExtensionClique Polymer Block Root)
    root first second →
  literalValidExtension (directionMask dataSet) root first →
  literalValidExtension (directionMask dataSet) root second →
  literalExtensionPolymer
    (literalRootedExtension (extensionGeometry dataSet)
      (rootBlockOf dataSet root) first)
  # literalExtensionPolymer
    (literalRootedExtension (extensionGeometry dataSet)
      (rootBlockOf dataSet root) second)
physicalRootedExtensionsFormClique = distinctValidExtensionsShareParentCore

boundaryAwareDirectionCountLevel : ProofLevel
boundaryAwareDirectionCountLevel = machineChecked

literalCommonRootCliqueLevel : ProofLevel
literalCommonRootCliqueLevel = machineChecked

actualCountPartitionFunctionLevel : ProofLevel
actualCountPartitionFunctionLevel = machineChecked

canonicalPhysicalTraceReductionLevel : ProofLevel
canonicalPhysicalTraceReductionLevel = machineChecked

physicalSpanningTreeConstructionInputsLevel : ProofLevel
physicalSpanningTreeConstructionInputsLevel = conditional

physicalPatchDirectionMaskInputsLevel : ProofLevel
physicalPatchDirectionMaskInputsLevel = conditional
