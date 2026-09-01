module DASHI.Cognition.PNF.ConsumerRelationSheetFractranQuotientBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context

------------------------------------------------------------------------
-- Three-role complete relation sheet.
-- This is a semantic comparison object.  It is not identified with cyclic C9
-- merely because it has nine cells.
------------------------------------------------------------------------

data Role3 : Set where
  roleA roleB roleC : Role3

record RelationSheet3 : Set where
  constructor relationSheet3
  field
    relation : Role3 → Role3 → Trit.SSPTrit
    diagonalA : relation roleA roleA ≡ Trit.sspZero
    diagonalB : relation roleB roleB ≡ Trit.sspZero
    diagonalC : relation roleC roleC ≡ Trit.sspZero

open RelationSheet3 public

record ConsumerAObservation : Set where
  constructor consumerAObservation
  field
    aToB : Trit.SSPTrit
    aToC : Trit.SSPTrit

open ConsumerAObservation public

observeA : RelationSheet3 → ConsumerAObservation
observeA sheet =
  consumerAObservation
    (relation sheet roleA roleB)
    (relation sheet roleA roleC)

------------------------------------------------------------------------
-- A concrete pair: both worlds answer the A-facing consumer identically while
-- retaining opposite B/C tail orientation in the complete sheet.
------------------------------------------------------------------------

abcRelation : Role3 → Role3 → Trit.SSPTrit
abcRelation roleA roleA = Trit.sspZero
abcRelation roleA roleB = Trit.sspNegOne
abcRelation roleA roleC = Trit.sspNegOne
abcRelation roleB roleA = Trit.sspPosOne
abcRelation roleB roleB = Trit.sspZero
abcRelation roleB roleC = Trit.sspNegOne
abcRelation roleC roleA = Trit.sspPosOne
abcRelation roleC roleB = Trit.sspPosOne
abcRelation roleC roleC = Trit.sspZero

acbRelation : Role3 → Role3 → Trit.SSPTrit
acbRelation roleA roleA = Trit.sspZero
acbRelation roleA roleB = Trit.sspNegOne
acbRelation roleA roleC = Trit.sspNegOne
acbRelation roleB roleA = Trit.sspPosOne
acbRelation roleB roleB = Trit.sspZero
acbRelation roleB roleC = Trit.sspPosOne
acbRelation roleC roleA = Trit.sspPosOne
acbRelation roleC roleB = Trit.sspNegOne
acbRelation roleC roleC = Trit.sspZero

abcSheet : RelationSheet3
abcSheet = relationSheet3 abcRelation refl refl refl

acbSheet : RelationSheet3
acbSheet = relationSheet3 acbRelation refl refl refl

consumerCannotDistinguishTailSwap :
  observeA abcSheet ≡ observeA acbSheet
consumerCannotDistinguishTailSwap = refl

tailOrientationDiffers :
  relation abcSheet roleB roleC ≡ relation acbSheet roleB roleC → ⊥
tailOrientationDiffers ()

------------------------------------------------------------------------
-- Typed relation-sheet transpose/sign inversion.  This is an oriented-relation
-- operation; a semantic role inversion must still carry an admissibility receipt.
------------------------------------------------------------------------

negateTrit : Trit.SSPTrit → Trit.SSPTrit
negateTrit Trit.sspNegOne = Trit.sspPosOne
negateTrit Trit.sspZero = Trit.sspZero
negateTrit Trit.sspPosOne = Trit.sspNegOne

record AntisymmetricSheet : Set where
  constructor antisymmetricSheet
  field
    sheet : RelationSheet3
    converseNegates :
      (left right : Role3) →
      relation sheet left right ≡ negateTrit (relation sheet right left)

open AntisymmetricSheet public

------------------------------------------------------------------------
-- FRACTRAN observation of a selected relation cell.  The selected prime lane
-- carries executable signed multiplicity; the trit is its coarse observation.
------------------------------------------------------------------------

record RelationCellFractranView : Set where
  constructor relationCellFractranView
  field
    roles : Context.OrientedRolePair
    prime : Signed.SSPPrime
    multiplicity : Signed.SignedMultiplicity
    observed : Trit.SSPTrit
    observedIsCoarse : observed ≡ Context.coarseSSPTrit multiplicity

open RelationCellFractranView public

record ConsumerRelationBoundary : Set where
  constructor consumerRelationBoundary
  field
    completeNineCellSheetIsCyclicC9 : Bool
    sixLinearExtensionsAreCyclicC6 : Bool
    consumerEqualityErasesTailFibre : Bool
    relationConverseAlwaysSemanticInverse : Bool
    relationCellCanProjectToSignedFractranLane : Bool

canonicalConsumerRelationBoundary : ConsumerRelationBoundary
canonicalConsumerRelationBoundary =
  consumerRelationBoundary false false false false true
