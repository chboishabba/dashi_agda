module DASHI.ComputerScience.RSA260BidiAStarEncodingGeneratorCollisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiProjectionIndexedGeneratorSignatureExact as Signature
import DASHI.ComputerScience.RSA260ProjectionMatrixGeneratorExact as MatrixGenerator

------------------------------------------------------------------------
-- RSA-260 BIDI A* ENCODING / GENERATOR-IDENTITY COLLISION
--
-- Runtime probe fixes the same BASEX/BASEY projection pair and varies only
-- the prepared-operator adapter.  The compact production-shaped encoding
--
--   (d, row-extension, column-extension, square-extension, rank H[d,d])
--
-- collides for identity and rotate1:
--
--   identity : (17,0,0,0,127)
--   rotate1  : (17,0,0,0,127)
--
-- while the recovered shared matrix-generator coefficient blobs have distinct
-- SHA-256 digests.  Hence the compact encoding does not determine generator
-- identity even after the projection pair is frozen.
--
-- This is a finite synthetic obstruction only.  It does not identify a
-- canonical minimal generator and does not claim RSA-260 production identity.
------------------------------------------------------------------------

signatureBoundary : Signature.ProjectionIndexedGeneratorBoundary
signatureBoundary = Signature.canonicalProjectionIndexedGeneratorBoundary

matrixGeneratorBoundary : MatrixGenerator.RSA260MatrixGeneratorRoadmapBoundary
matrixGeneratorBoundary = MatrixGenerator.currentRSA260MatrixGeneratorRoadmapBoundary

record EncodingCollisionRuntimeReceipt : Set where
  constructor encoding-collision-runtime-receipt
  field
    runtimePath : String
    runtimeGitBlob : String
    runtimeSHA256 : String
    outputSHA256 : String
    projectionPairLabel : String
    checkedAdapters : Nat
    projectionPairHeldFixed : Bool
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open EncodingCollisionRuntimeReceipt public

currentEncodingCollisionRuntimeReceipt : EncodingCollisionRuntimeReceipt
currentEncodingCollisionRuntimeReceipt =
  encoding-collision-runtime-receipt
    "/mnt/data/rsa260_astar_encoding_collision_probe.py"
    "16ca62e1c9e209e3a14b42d7a2fd7e87734cdc3d"
    "0ebe6b944b19c1e43a1085dcfd603acc45bfd98c2cabec0b3ca3a9f2f672bbb7"
    "cbee0d040e0bd9b03bdf5f6061884235782e12ccc87f7e494f356cef182274c0"
    "BASEX/BASEY fixed"
    4
    true
    true
    false

record CompactAStarEncoding : Set where
  constructor compact-astar-encoding
  field
    projectedGeneratorDegree : Nat
    rowExtension : Nat
    columnExtension : Nat
    squareExtension : Nat
    hankelRankDD : Nat
open CompactAStarEncoding public

identityCompactEncoding : CompactAStarEncoding
identityCompactEncoding = compact-astar-encoding 17 0 0 0 127

rotate1CompactEncoding : CompactAStarEncoding
rotate1CompactEncoding = compact-astar-encoding 17 0 0 0 127

record GeneratorDigestReceipt : Set where
  constructor generator-digest-receipt
  field
    adapterLabel : String
    generatorSHA256 : String
    sequenceSHA256 : String
open GeneratorDigestReceipt public

identityGeneratorDigest : GeneratorDigestReceipt
identityGeneratorDigest = generator-digest-receipt
  "identity"
  "cc06dfc1a4731e638c0b161d0bc34bcf5053d4d6e5483e634dede0b034ed1bdf"
  "5f676109353994f0bc2a584b4486c261cb9213cc6cc26b9e6287e8468bde7954"

rotate1GeneratorDigest : GeneratorDigestReceipt
rotate1GeneratorDigest = generator-digest-receipt
  "rotate1"
  "c655a8f2d23472850c059b416da865b44d874ec2096ce404d8945f8bc1250c59"
  "6c2fe8ff55a9293f834b49bfd57fe93099a6151930d40580c6fae15a6c6531f9"

------------------------------------------------------------------------
-- Exact query-indexed obstruction.
------------------------------------------------------------------------

data EncodingWorld : Set where
  identityWorld : EncodingWorld
  rotate1World : EncodingWorld

data CompactEncodingSurface : Set where
  degree17ZeroExtensionRank127 : CompactEncodingSurface

data RefinedGeneratorSurface : Set where
  identityGeneratorSurface : RefinedGeneratorSurface
  rotate1GeneratorSurface : RefinedGeneratorSurface

data GeneratorQuery : Set where
  recoveredSharedGeneratorIdentity : GeneratorQuery

data GeneratorAnswer : Set where
  identityGeneratorAnswer : GeneratorAnswer
  rotate1GeneratorAnswer : GeneratorAnswer

compactObserve : EncodingWorld → CompactEncodingSurface
compactObserve _ = degree17ZeroExtensionRank127

refinedGeneratorObserve : EncodingWorld → RefinedGeneratorSurface
refinedGeneratorObserve identityWorld = identityGeneratorSurface
refinedGeneratorObserve rotate1World = rotate1GeneratorSurface

generatorAnswer : GeneratorQuery → EncodingWorld → GeneratorAnswer
generatorAnswer recoveredSharedGeneratorIdentity identityWorld = identityGeneratorAnswer
generatorAnswer recoveredSharedGeneratorIdentity rotate1World = rotate1GeneratorAnswer

generatorSemantics :
  Query.QuerySemantics EncodingWorld GeneratorQuery GeneratorAnswer
generatorSemantics = Query.querySemantics generatorAnswer

CoarseEncodingAdequacyDefect : Set₁
CoarseEncodingAdequacyDefect =
  Query.QueryAdequacyDefect
    compactObserve
    generatorSemantics
    recoveredSharedGeneratorIdentity

compactEncodingCannotDetermineGeneratorIdentity :
  CoarseEncodingAdequacyDefect
compactEncodingCannotDetermineGeneratorIdentity =
  Query.queryAdequacyDefect
    identityWorld
    rotate1World
    refl
    (λ ())

compactEncodingNotAdequateForGeneratorIdentity :
  Query.AdequateFor
    compactObserve
    generatorSemantics
    recoveredSharedGeneratorIdentity → ⊥
compactEncodingNotAdequateForGeneratorIdentity =
  Query.queryAdequacyDefectBlocksFactorisation
    compactEncodingCannotDetermineGeneratorIdentity

generatorFromRefinedSurface : RefinedGeneratorSurface → GeneratorAnswer
generatorFromRefinedSurface identityGeneratorSurface = identityGeneratorAnswer
generatorFromRefinedSurface rotate1GeneratorSurface = rotate1GeneratorAnswer

refinedGeneratorFactorisation :
  (world : EncodingWorld) →
  generatorAnswer recoveredSharedGeneratorIdentity world
    ≡ generatorFromRefinedSurface (refinedGeneratorObserve world)
refinedGeneratorFactorisation identityWorld = refl
refinedGeneratorFactorisation rotate1World = refl

RefinedGeneratorAdequacy : Set₁
RefinedGeneratorAdequacy =
  Query.AdequateFor
    refinedGeneratorObserve
    generatorSemantics
    recoveredSharedGeneratorIdentity

generatorIdentityFactorsThroughRefinedObserver : RefinedGeneratorAdequacy
generatorIdentityFactorsThroughRefinedObserver =
  Query.factorsForQuery generatorFromRefinedSurface refinedGeneratorFactorisation

------------------------------------------------------------------------
-- Interpretation boundary and roadmap.
------------------------------------------------------------------------

record AStarEncodingCollisionBoundary : Set where
  constructor astar-encoding-collision-boundary
  field
    sameProjectionPairPaid : Bool
    projectedDegreeSame : Bool
    rectangularExtensionSame : Bool
    hankelRankDDSame : Bool
    generatorCoefficientDigestDifferent : Bool
    compactEncodingDeterminesGeneratorIdentity : Bool
    concreteAdequacyDefectPaid : Bool
    refinedGeneratorObserverAdequateOnWitness : Bool
    collisionProvesCanonicalMinimalGeneratorDifference : Bool
    collisionUsesProductionRSA260AStar : Bool
    runtimeCommittedToProducerRepository : Bool
open AStarEncodingCollisionBoundary public

canonicalAStarEncodingCollisionBoundary : AStarEncodingCollisionBoundary
canonicalAStarEncodingCollisionBoundary =
  astar-encoding-collision-boundary
    true
    true
    true
    true
    true
    false
    true
    true
    false
    false
    false

data AStarEncodingCollisionResidual : Set where
  testRelationSpaceAugmentedEncoding : AStarEncodingCollisionResidual
  testShiftedRankAugmentedEncoding : AStarEncodingCollisionResidual
  searchCoefficientResidualCompression : AStarEncodingCollisionResidual
  compileProductionShapedAStarDecoder : AStarEncodingCollisionResidual
  acquireSameObjectProjectedAStarBytes : AStarEncodingCollisionResidual
  fallbackToSameObjectFSolsIfAStarUnavailable : AStarEncodingCollisionResidual

firstAStarEncodingCollisionResidual : AStarEncodingCollisionResidual
firstAStarEncodingCollisionResidual = testRelationSpaceAugmentedEncoding

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SameCompactEncodingMeansSameGenerator : Set where
data DifferentSyntheticGeneratorDigestMeansCanonicalMinimalDifference : Set where
data SyntheticCollisionMeansProductionCollision : Set where

defaultEncodingDoesNotCreateGeneratorIdentity :
  SameCompactEncodingMeansSameGenerator → ⊥
defaultEncodingDoesNotCreateGeneratorIdentity ()

digestDifferenceDoesNotCreateCanonicalMinimalDifference :
  DifferentSyntheticGeneratorDigestMeansCanonicalMinimalDifference → ⊥
digestDifferenceDoesNotCreateCanonicalMinimalDifference ()

syntheticCollisionDoesNotCreateProductionCollision :
  SyntheticCollisionMeansProductionCollision → ⊥
syntheticCollisionDoesNotCreateProductionCollision ()
