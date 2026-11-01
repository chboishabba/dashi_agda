module DASHI.ComputerScience.RSA260BidiMksolActionSparseObserverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.ComputerScience.RSA260BidiSeparatingCoordinateHypergraphExact as Hyper

------------------------------------------------------------------------
-- SPARSE OBSERVER RELATIVE TO THE SYNTHETIC MKSOL-STYLE ACTION CONSUMER
--
-- The active consumer is no longer generator receipt identity.  It is the
-- finite synthetic action already exercised in this tranche:
--
--     A(F;M,V) = XOR_{l<d} M^l V F_l.
--
-- Degree is retained separately.  Among equal-degree worlds, every pair with
-- different action output induces a constraint edge.  Runtime exhaustive search
-- on the existing 12-world cross-validation family found that ranks F2 and F10
-- hit all such edges, while neither rank alone does.
--
-- This is a finite synthetic adequacy receipt.  It is NOT exact CADO mksol
-- semantics and does not imply production sufficiency.
------------------------------------------------------------------------

record MksolActionSparseObserverRuntimeReceipt : Set where
  constructor mksol-action-sparse-observer-runtime-receipt
  field
    worldCount : Nat
    equalDegreeDistinctActionPairCount : Nat
    selectedRank0 : Nat
    selectedRank1 : Nat
    minimumRankCoordinateCountFound : Nat
    minimumSizeSolutionCountFound : Nat
    degreePlusSelectedRanksSeparateAllCurrentActions : Bool
    eitherSelectedRankAloneSuffices : Bool
    exhaustiveFiniteSubsetSearchRun : Bool
    exactCADOMksolSemanticsUsed : Bool
    productionRSA260CarrierUsed : Bool
    receiptReference : String

open MksolActionSparseObserverRuntimeReceipt public

currentMksolActionSparseObserverRuntimeReceipt :
  MksolActionSparseObserverRuntimeReceipt
currentMksolActionSparseObserverRuntimeReceipt =
  mksol-action-sparse-observer-runtime-receipt
    12
    31
    2
    10
    2
    1
    true
    false
    true
    false
    false
    "rsa260_bidi_mksol_style_consumer_diagnostic.json + finite hitting-set search"

------------------------------------------------------------------------
-- Relation to the generic sparse-coordinate interpretation.
------------------------------------------------------------------------

hypergraphBoundary : Hyper.SeparatingCoordinateHypergraphBoundary
hypergraphBoundary = Hyper.canonicalSeparatingCoordinateHypergraphBoundary

record MksolActionSparseObserverBoundary : Set where
  constructor mksol-action-sparse-observer-boundary
  field
    consumerChangedFromReceiptIdentityToAction : Bool
    sparseObserverUsesDegreeRankF2RankF10 : Bool
    twoRanksSufficientOnCurrentTwelveWorldFamily : Bool
    oneRankSufficientOnCurrentTwelveWorldFamily : Bool
    currentFiniteSearchKernelProved : Bool
    exactReplayStillStrongerAndSeparatelyAvailable : Bool
    nextStepIsStressAcrossBroaderContextFamily : Bool
    exactCADOMksolAdequacyPaid : Bool

open MksolActionSparseObserverBoundary public

canonicalMksolActionSparseObserverBoundary : MksolActionSparseObserverBoundary
canonicalMksolActionSparseObserverBoundary =
  mksol-action-sparse-observer-boundary
    true
    true
    true
    false
    false
    true
    true
    false
