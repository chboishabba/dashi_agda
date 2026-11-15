module DASHI.Moonshine.Monster3BAtlasSelectedHeisenbergLiftReceiptExact where

------------------------------------------------------------------------
-- SELECTED MONSTER-3B SOURCE WORD -> REPOSITORY HEISENBERG LIFT RECEIPT
--
-- Companion exact finite producer:
--   scripts/verify_monster3b_selected_heisenberg_lift.py
--
-- The producer consumes the vendored ATLAS 2.Suz / 2.Suz:2 12-dimensional
-- GF(3) matrices, recomputes the repository symplectic basis X6 + X6*, and
-- evaluates the already-selected field-producing source word
--
--   g2 g1 g2^-1 g1 g2^-1.
--
-- For its normalized 12x12 action M the producer checks exactly:
--
-- * symplectic multiplier = 1;
-- * the X6 compression is the previously selected degree-six receipt;
-- * for the repository asymmetric Heisenberg cocycle matrix C,
--     D = M^T C M - C
--   is symmetric and has rank 12;
-- * over GF(3), q(x)=2 x^T D x has polarization D;
-- * hence the central-correction identity
--     q(x+y)+c(x,y)=q(x)+q(y)+c(Mx,My)
--   holds algebraically.
--
-- This is a selected-word exact matrix receipt.  It does NOT promote the full
-- 2.Suz:2 normalizer to a completely instantiated Heisenberg action, does not
-- pay Monster orbit/stabilizer semantics, and does not establish any physical
-- realization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record SelectedHeisenbergLiftReceipt : Set where
  constructor selected-heisenberg-lift-receipt
  field
    producerPath : String
    selectedSourceWord : String
    carrierDimension : Nat
    lagrangianDimension : Nat
    fieldDegree : Nat
    symplecticMultiplier : Nat
    cocycleDefectRank : Nat
    compressionMatchesSelectedFieldReceipt : Bool
    cocycleDefectSymmetric : Bool
    quadraticPolarizationIdentity : Bool
    heisenbergCoboundaryIdentity : Bool
    bruteForcePairEnumerationUsed : Bool
open SelectedHeisenbergLiftReceipt public

canonicalSelectedHeisenbergLiftReceipt : SelectedHeisenbergLiftReceipt
canonicalSelectedHeisenbergLiftReceipt =
  selected-heisenberg-lift-receipt
    "scripts/verify_monster3b_selected_heisenberg_lift.py"
    "g2 g1 g2^-1 g1 g2^-1"
    12 6 6 1 12
    true true true true false

record Boundary : Set where
  constructor boundary
  field
    vendoredAtlasMatricesConsumed : Bool
    sameRepositorySymplecticBasisRecomputed : Bool
    selectedWordMatrixRuntimePaid : Bool
    selectedWordStrictSymplecticPaid : Bool
    selectedWordCompressionSameReceiptPaid : Bool
    selectedWordQuadraticCentralCorrectionPaid : Bool
    selectedWordHeisenbergLiftRuntimePaid : Bool
    selectedWordAgdaKernelMatrixProofPaid : Bool
    fullNormalizerHeisenbergActionPaid : Bool
    fullMonsterOrbitStabilizerRecognitionPaid : Bool
    physicalNormalizerRealizationPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true true true true true true true
    false false false false
