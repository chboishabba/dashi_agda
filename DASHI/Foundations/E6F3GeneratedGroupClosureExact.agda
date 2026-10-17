module DASHI.Foundations.E6F3GeneratedGroupClosureExact where

------------------------------------------------------------------------
-- E6 MOD-3 GENERATED-GROUP CLOSURE RECEIPT
--
-- DASHI CONTRIBUTION
--
-- Lean PR #47 now source-writes the finite closure producer for the six
-- five-dimensional E6 generators: 51,840 generated transformations and a
-- selected Q=2/root stabilizer of order 720.  This Agda owner does not pretend
-- that a cross-prover source file is an Agda kernel theorem.  Instead it types
-- the exact receipt that a local Agda producer or an imported verified receipt
-- must inhabit, while preserving the existing no-cardinality-promotion rules.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.E6F3ExteriorSquareRecognitionExact as E6

record GeneratedE6ImageReceipt : Set₁ where
  field
    Matrix : Set
    generatedMatrix : Matrix → Set
    rootStabilizerMatrix : Matrix → Set

    generatedImageOrder : Nat
    rootStabilizerOrder : Nat

    generatedImageOrderIs51840 : generatedImageOrder ≡ 51840
    rootStabilizerOrderIs720 : rootStabilizerOrder ≡ 720

    closureUnderSixSimpleGenerators : Set
    q2RootOrbitTransitivity : Set
    orbitStabilizerCompatibility : Set
open GeneratedE6ImageReceipt public

record ExplicitS6StabilizerRecognition
  (G : GeneratedE6ImageReceipt) : Set₁ where
  field
    SixObject : Set
    sixObjectCardinalityReceipt : Set
    stabilizerAction : Matrix G → SixObject → SixObject
    faithfulActionReceipt : Set
    ontoPermutationActionReceipt : Set
open ExplicitS6StabilizerRecognition public

record GeneratedGroupBoundary : Set where
  constructor generated-group-boundary
  field
    generatedImageOrder51840ReceiptTyped : Bool
    rootStabilizerOrder720ReceiptTyped : Bool
    orbitStabilizerCompatibilityReceiptTyped : Bool

    leanGeneratedGroupProducerSourceWritten : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaGeneratedGroupProducerKernelPaidHere : Bool

    fullPGSp4WE6EqualityKernelPaidInAgda : Bool
    stabilizerPromotedToS6FromOrderAlone : Bool
    explicitS6RecognitionStillRequiresAction : Bool
open GeneratedGroupBoundary public

canonicalGeneratedGroupBoundary : GeneratedGroupBoundary
canonicalGeneratedGroupBoundary =
  generated-group-boundary
    true true true
    true false false
    false false true

-- Order equality is evidence for the expected W(A5)/S6 stabilizer shape only.
-- It is not itself an isomorphism theorem.
record StabilizerOrderFirewall : Set where
  constructor stabilizer-order-firewall
  field
    order720DoesNotCreateS6Isomorphism : Bool
    explicitSixObjectActionRequired : Bool
open StabilizerOrderFirewall public

canonicalStabilizerOrderFirewall : StabilizerOrderFirewall
canonicalStabilizerOrderFirewall = stabilizer-order-firewall true true

-- The older PGSp4/W(E6) recognition socket remains the correct promotion gate:
-- a full matrix-group equality must supply two-sided actor recovery and action
-- intertwining, not merely the common finite order 51,840.
record GeneratedGroupToRecognitionBridge
  (G : GeneratedE6ImageReceipt)
  (M : E6.E6Mod3QuadraticModel) : Set₁ where
  field
    sameActorRecognition : E6.PGSp4WE6Recognition M
    generatedImageMatchesRecognizedActor : Set
    matrixActionAgreement : Set
open GeneratedGroupToRecognitionBridge public
