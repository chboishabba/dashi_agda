module DASHI.ComputerScience.RSA260BidiAStarRelationAugmentedEncodingCollisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.ComputerScience.RSA260BidiAStarEncodingGeneratorCollisionExact as Coarse

------------------------------------------------------------------------
-- RSA-260 BIDI RELATION-AUGMENTED A* ENCODING COLLISION
--
-- After the compact encoding failed, we added two already-measured Krylov
-- coordinates:
--
--   relation-space dimension
--   shifted Krylov rank.
--
-- With BASEX/BASEY still fixed, the ten-adapter runtime portfolio contains
-- multiple collisions.  In particular rotate3 and affine7 both expose
--
--   d = 17
--   rectangular extension = (0,0,0)
--   rank H[d,d] = 128
--   relation-space dimension = 16
--   shifted rank = 120
--
-- but recover distinct shared matrix-generator coefficient digests.
-- Therefore scalar/rank augmentation still does not determine generator
-- identity.  The next repair should retain coefficient-level residual data
-- rather than continue accumulating unrelated scalar summaries.
------------------------------------------------------------------------

coarseBoundary : Coarse.AStarEncodingCollisionBoundary
coarseBoundary = Coarse.canonicalAStarEncodingCollisionBoundary

record RelationAugmentedRuntimeReceipt : Set where
  constructor relation-augmented-runtime-receipt
  field
    runtimePath : String
    runtimeGitBlob : String
    runtimeSHA256 : String
    outputSHA256 : String
    checkedAdapters : Nat
    projectionPairHeldFixed : Bool
    exactLocalRuntimeExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open RelationAugmentedRuntimeReceipt public

currentRelationAugmentedRuntimeReceipt : RelationAugmentedRuntimeReceipt
currentRelationAugmentedRuntimeReceipt =
  relation-augmented-runtime-receipt
    "/mnt/data/rsa260_astar_relation_augmented_collision_probe.py"
    "02bf7bf85277747c2ba06a5c4b75991f68000bd7"
    "ea29ca2f1982d22b9b5b9f176f79b6c116de3526eb2cfc5021f573d947746612"
    "197e0afe8c2b260b19337fb40ddedb17c1fe752209c8a26371e3274e756cc859"
    10
    true
    true
    false

record RelationAugmentedEncoding : Set where
  constructor relation-augmented-encoding
  field
    projectedGeneratorDegree : Nat
    rowExtension : Nat
    columnExtension : Nat
    squareExtension : Nat
    hankelRankDD : Nat
    relationSpaceDimension : Nat
    shiftedKrylovRank : Nat
open RelationAugmentedEncoding public

rotate3Encoding : RelationAugmentedEncoding
rotate3Encoding = relation-augmented-encoding 17 0 0 0 128 16 120

affine7Encoding : RelationAugmentedEncoding
affine7Encoding = relation-augmented-encoding 17 0 0 0 128 16 120

record RelationAugmentedGeneratorReceipt : Set where
  constructor relation-augmented-generator-receipt
  field
    adapterLabel : String
    generatorSHA256 : String
open RelationAugmentedGeneratorReceipt public

rotate3GeneratorReceipt : RelationAugmentedGeneratorReceipt
rotate3GeneratorReceipt = relation-augmented-generator-receipt
  "rotate3"
  "d8e0497723b7fedd2c0a4d87cc6f25aa0917b3f732a6355ccca9a6afd7454f84"

affine7GeneratorReceipt : RelationAugmentedGeneratorReceipt
affine7GeneratorReceipt = relation-augmented-generator-receipt
  "affine7"
  "9a72e66bcb9c863e0f600651740924c3b517d389b47753ada38968c707af20c4"

------------------------------------------------------------------------
-- Exact finite obstruction.
------------------------------------------------------------------------

data RelationWorld : Set where
  rotate3World : RelationWorld
  affine7World : RelationWorld

data RelationAugmentedSurface : Set where
  degree17ZeroExtensionRank128Rel16Shift120 : RelationAugmentedSurface

data GeneratorIdentitySurface : Set where
  rotate3GeneratorSurface : GeneratorIdentitySurface
  affine7GeneratorSurface : GeneratorIdentitySurface

data GeneratorIdentityQuery : Set where
  sharedMatrixGeneratorIdentity : GeneratorIdentityQuery

data GeneratorIdentityAnswer : Set where
  rotate3GeneratorAnswer : GeneratorIdentityAnswer
  affine7GeneratorAnswer : GeneratorIdentityAnswer

relationAugmentedObserve : RelationWorld → RelationAugmentedSurface
relationAugmentedObserve _ = degree17ZeroExtensionRank128Rel16Shift120

generatorIdentityObserve : RelationWorld → GeneratorIdentitySurface
generatorIdentityObserve rotate3World = rotate3GeneratorSurface
generatorIdentityObserve affine7World = affine7GeneratorSurface

generatorIdentityAnswer :
  GeneratorIdentityQuery → RelationWorld → GeneratorIdentityAnswer
generatorIdentityAnswer sharedMatrixGeneratorIdentity rotate3World = rotate3GeneratorAnswer
generatorIdentityAnswer sharedMatrixGeneratorIdentity affine7World = affine7GeneratorAnswer

generatorIdentitySemantics :
  Query.QuerySemantics RelationWorld GeneratorIdentityQuery GeneratorIdentityAnswer
generatorIdentitySemantics = Query.querySemantics generatorIdentityAnswer

RelationAugmentedAdequacyDefect : Set₁
RelationAugmentedAdequacyDefect =
  Query.QueryAdequacyDefect
    relationAugmentedObserve
    generatorIdentitySemantics
    sharedMatrixGeneratorIdentity

relationAugmentedEncodingCannotDetermineGeneratorIdentity :
  RelationAugmentedAdequacyDefect
relationAugmentedEncodingCannotDetermineGeneratorIdentity =
  Query.queryAdequacyDefect
    rotate3World
    affine7World
    refl
    (λ ())

relationAugmentedEncodingNotAdequateForGeneratorIdentity :
  Query.AdequateFor
    relationAugmentedObserve
    generatorIdentitySemantics
    sharedMatrixGeneratorIdentity → ⊥
relationAugmentedEncodingNotAdequateForGeneratorIdentity =
  Query.queryAdequacyDefectBlocksFactorisation
    relationAugmentedEncodingCannotDetermineGeneratorIdentity

answerFromGeneratorIdentity : GeneratorIdentitySurface → GeneratorIdentityAnswer
answerFromGeneratorIdentity rotate3GeneratorSurface = rotate3GeneratorAnswer
answerFromGeneratorIdentity affine7GeneratorSurface = affine7GeneratorAnswer

generatorIdentityFactorisation :
  (world : RelationWorld) →
  generatorIdentityAnswer sharedMatrixGeneratorIdentity world
    ≡ answerFromGeneratorIdentity (generatorIdentityObserve world)
generatorIdentityFactorisation rotate3World = refl
generatorIdentityFactorisation affine7World = refl

GeneratorIdentityAdequacy : Set₁
GeneratorIdentityAdequacy =
  Query.AdequateFor
    generatorIdentityObserve
    generatorIdentitySemantics
    sharedMatrixGeneratorIdentity

generatorIdentityFactorsThroughCoefficientResidual : GeneratorIdentityAdequacy
generatorIdentityFactorsThroughCoefficientResidual =
  Query.factorsForQuery answerFromGeneratorIdentity generatorIdentityFactorisation

------------------------------------------------------------------------
-- Boundary and roadmap.
------------------------------------------------------------------------

record RelationAugmentedEncodingBoundary : Set where
  constructor relation-augmented-encoding-boundary
  field
    compactEncodingFailureInherited : Bool
    relationSpaceDimensionAdded : Bool
    shiftedKrylovRankAdded : Bool
    sameProjectionPairPaid : Bool
    concreteAugmentedCollisionPaid : Bool
    augmentedEncodingDeterminesGeneratorIdentity : Bool
    coefficientLevelResidualRepairsFiniteWitness : Bool
    scalarRankAccumulationNowDominated : Bool
    collisionProvesAlgebraicGeneratorInequivalence : Bool
    collisionUsesProductionRSA260AStar : Bool
open RelationAugmentedEncodingBoundary public

canonicalRelationAugmentedEncodingBoundary : RelationAugmentedEncodingBoundary
canonicalRelationAugmentedEncodingBoundary =
  relation-augmented-encoding-boundary
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

data RelationAugmentedEncodingResidual : Set where
  retainGeneratorCoefficientResidual : RelationAugmentedEncodingResidual
  testCoefficientResidualCompression : RelationAugmentedEncodingResidual
  compileProductionShapedAStarDecoder : RelationAugmentedEncodingResidual
  acquireSameObjectProjectedAStarBytes : RelationAugmentedEncodingResidual
  fallbackToSameObjectFSolsIfAStarUnavailable : RelationAugmentedEncodingResidual

firstRelationAugmentedEncodingResidual : RelationAugmentedEncodingResidual
firstRelationAugmentedEncodingResidual = retainGeneratorCoefficientResidual

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data MoreScalarRanksMeanGeneratorIdentity : Set where
data DifferentCoefficientDigestMeansAlgebraicInequivalence : Set where
data SyntheticPortfolioCollisionMeansProductionCollision : Set where

scalarAccumulationDoesNotCreateGeneratorIdentity :
  MoreScalarRanksMeanGeneratorIdentity → ⊥
scalarAccumulationDoesNotCreateGeneratorIdentity ()

digestDifferenceDoesNotCreateAlgebraicInequivalence :
  DifferentCoefficientDigestMeansAlgebraicInequivalence → ⊥
digestDifferenceDoesNotCreateAlgebraicInequivalence ()

syntheticCollisionDoesNotCreateProductionCollision :
  SyntheticPortfolioCollisionMeansProductionCollision → ⊥
syntheticCollisionDoesNotCreateProductionCollision ()
