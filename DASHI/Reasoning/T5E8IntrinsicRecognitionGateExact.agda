module DASHI.Reasoning.T5E8IntrinsicRecognitionGateExact where

------------------------------------------------------------------------
-- INTRINSIC-GEOMETRY GATE FOR T5 / E8 RECOGNITION
--
-- DASHI CONTRIBUTION
--
-- A cardinality bijection plus an action transported *through that same
-- bijection* is not independent evidence that the target carrier possessed E8
-- geometry beforehand.  This owner strengthens the recognition discipline:
--
--   pre-existing target relation/geometry
--   + independently justified provenance
--   + relation-preserving same-object map
--   -> admissible intrinsic recognition candidate.
--
-- The Lean mirror source-writes a finite obstruction for the naive standard-F3
-- orthogonality graph: literal E8 root-addition degree 56 versus a concrete T5
-- orthogonality witness of degree 77.  Agda records that result at cross-language
-- evidence grade only until an exact-head kernel receipt exists.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.T5E8RelativeComplementCandidateExact as Relative

------------------------------------------------------------------------
-- 1. Generic stronger recognition socket.
------------------------------------------------------------------------

record IntrinsicTargetGeometry : Set₁ where
  constructor intrinsic-target-geometry
  field
    State : Set
    Relation : State → State → Set
    provenance : String
    fixedBeforeRecognitionMap : Bool
    fixedBeforeRecognitionMapIsTrue : fixedBeforeRecognitionMap ≡ true

open IntrinsicTargetGeometry public

record IntrinsicRecognition
    (source : IntrinsicTargetGeometry)
    (target : IntrinsicTargetGeometry) : Set₁ where
  constructor intrinsic-recognition
  field
    forward : State source → State target
    backward : State target → State source
    forwardBackward : (y : State target) → forward (backward y) ≡ y
    backwardForward : (x : State source) → backward (forward x) ≡ x
    preservesRelation :
      (x y : State source) →
      Relation source x y →
      Relation target (forward x) (forward y)
    reflectsRelation :
      (x y : State source) →
      Relation target (forward x) (forward y) →
      Relation source x y
    recognitionProvenance : String

------------------------------------------------------------------------
-- 2. Transported geometry is classified separately.
------------------------------------------------------------------------

record TransportedGeometryDefinition : Set₁ where
  constructor transported-geometry-definition
  field
    Source Target : Set
    sourceRelation : Source → Source → Set
    map : Source → Target
    inverse : Target → Source
    transportedRelation : Target → Target → Set
    definitionWitness :
      (x y : Target) →
      transportedRelation x y ≡ sourceRelation (inverse x) (inverse y)
    createdAfterMapChosen : Bool
    createdAfterMapChosenIsTrue : createdAfterMapChosen ≡ true

open TransportedGeometryDefinition public

------------------------------------------------------------------------
-- 3. Cross-language naive-orthogonality obstruction receipt.
------------------------------------------------------------------------

record NaiveOrthogonalityObstructionReceipt : Set where
  constructor naive-orthogonality-obstruction-receipt
  field
    pythonLiteralE8RootCount : Bool
    pythonE8UniformDegree56 : Bool
    pythonRelativeT5WitnessDegree77 : Bool
    leanLiteralE8CarrierSourceWritten : Bool
    leanDegreeObstructionSourceWritten : Bool
    leanKernelVerified : Bool
    agdaLiteralGraphEnumerationProvedHere : Bool
    note : String

canonicalNaiveOrthogonalityObstructionReceipt :
  NaiveOrthogonalityObstructionReceipt
canonicalNaiveOrthogonalityObstructionReceipt =
  naive-orthogonality-obstruction-receipt
    true true true
    true true false false
    "Python exhaustively checked the 240-root E8 degree and the T5 degree witness. Lean finite owners are source-written; no exact-head kernel receipt is available in this session."

------------------------------------------------------------------------
-- 4. Claim boundary.
------------------------------------------------------------------------

record IntrinsicRecognitionBoundary : Set where
  constructor intrinsic-recognition-boundary
  field
    targetGeometryMustPreexistRecognition : Bool
    relationPreservationAndReflectionRequired : Bool
    transportedGeometryCountsAsIndependentEvidence : Bool
    naiveOrthogonalityCandidateRejectedByLeanSource : Bool
    otherIntrinsicTargetGeometriesRemainOpen : Bool
    intrinsicRecognitionCreatesPhysicalMechanism : Bool
    leanKernelVerified : Bool

open IntrinsicRecognitionBoundary public

canonicalIntrinsicRecognitionBoundary : IntrinsicRecognitionBoundary
canonicalIntrinsicRecognitionBoundary =
  intrinsic-recognition-boundary
    true true false true true false false

reflTargetPreexists :
  targetGeometryMustPreexistRecognition canonicalIntrinsicRecognitionBoundary ≡ true
reflTargetPreexists = refl

reflTransportNotEvidence :
  transportedGeometryCountsAsIndependentEvidence canonicalIntrinsicRecognitionBoundary ≡ false
reflTransportNotEvidence = refl

reflNaiveRejected :
  naiveOrthogonalityCandidateRejectedByLeanSource canonicalIntrinsicRecognitionBoundary ≡ true
reflNaiveRejected = refl

reflLeanKernelUnverified :
  leanKernelVerified canonicalIntrinsicRecognitionBoundary ≡ false
reflLeanKernelUnverified = refl
