module DASHI.Analysis.BishopRadixCellQuantisationExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE BISHOP-REAL RADIX CELL QUANTISATION
--
-- A globally total floor operation is not required for the climbing-gym
-- observer and is not constructively available merely from an ordered-real
-- interface.  The useful proof-relevant object is instead a certificate that
-- a Bishop real lies strictly inside one finite radix cell
--
--       j / N < x < (j + 1) / N,       N = p^depth.
--
-- Such a witness excludes the ambiguous grid-boundary case and determines the
-- existing finite RadialTreeAddress exactly.  The cell index is compiled by
-- the repository's Nat -> radial-tree codec; no second radix semantics and no
-- classical excluded-middle floor are introduced.
--
-- SOURCE / CARRIER PROVENANCE
-- The ordinary `Real` module is the repository's git-pinned vendored Bishop
-- implementation.  Its rational embedding `_⋆`, strict order and constructive
-- positivity are theorem-bearing vendor code, not a citation-only substitute.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (NonZero)
open import Data.Nat using (_<_)
open import Data.Rational.Unnormalised using (_/_)

import Real as BishopReal

import DASHI.Foundations.BishopVendoredSubmoduleProvenanceExact as BishopProvenance
import DASHI.Foundations.NatRadialTreeCodecExact as NatRadix
import DASHI.Foundations.RadixValuationStageBridge as Radix

------------------------------------------------------------------------
-- Exact rational grid boundary embedded in the Bishop real carrier.
------------------------------------------------------------------------

radixCellCount : Radix.RadixChart → Nat → Nat
radixCellCount chart depth =
  Radix.radixPower (Radix.radix chart) depth

rationalGridBoundary :
  (cells index : Nat) →
  {{cellsNonZero : NonZero cells}} →
  BishopReal.ℝ
rationalGridBoundary cells index =
  BishopReal._⋆ (+ index / cells)

------------------------------------------------------------------------
-- Proof-relevant non-boundary cell location.
------------------------------------------------------------------------

record CertifiedOpenRadixCell
    (chart : Radix.RadixChart)
    (depth : Nat)
    (x : BishopReal.ℝ) : Set where
  constructor certified-open-radix-cell
  field
    cellsNonZero : NonZero (radixCellCount chart depth)
    cellIndex : Nat
    cellIndexInRange : cellIndex < radixCellCount chart depth

    lowerStrict :
      BishopReal._<_
        (rationalGridBoundary
          (radixCellCount chart depth)
          cellIndex
          {{cellsNonZero}})
        x

    upperStrict :
      BishopReal._<_
        x
        (rationalGridBoundary
          (radixCellCount chart depth)
          (suc cellIndex)
          {{cellsNonZero}})

open CertifiedOpenRadixCell public

------------------------------------------------------------------------
-- The certified cell index determines the existing radial address.
------------------------------------------------------------------------

certifiedRadialAddress :
  ∀ {chart depth x} →
  CertifiedOpenRadixCell chart depth x →
  Radix.RadialTreeAddress chart depth
certifiedRadialAddress {chart} {depth} certificate =
  NatRadix.natRadialAddress chart depth (cellIndex certificate)

certifiedRadialValue :
  ∀ {chart depth x} →
  CertifiedOpenRadixCell chart depth x →
  Nat
certifiedRadialValue {chart} certificate =
  NatRadix.radialValue chart (certifiedRadialAddress certificate)

------------------------------------------------------------------------
-- Boundary / authority accounting.
------------------------------------------------------------------------

record BishopRadixCellQuantisationBoundary : Set where
  constructor bishop-radix-cell-quantisation-boundary
  field
    vendoredBishopRealCarrierReused : Bool
    exactRationalGridEmbedded : Bool
    strictOpenCellCertificateDefined : Bool
    certifiedNonBoundaryCellToAddressClosed : Bool
    existingNatRadialCodecReused : Bool

    totalConstructiveRealFloorConstructed : Bool
    radixBoundaryEqualityDecidableForEveryBishopReal : Bool
    excludedMiddleImportedForQuantisation : Bool
    certificateConstructsZetaZeroProof : Bool
    certificateConstructsMonsterSpecificity : Bool

open BishopRadixCellQuantisationBoundary public

canonicalBishopRadixCellQuantisationBoundary :
  BishopRadixCellQuantisationBoundary
canonicalBishopRadixCellQuantisationBoundary =
  bishop-radix-cell-quantisation-boundary
    true true true true true
    false false false false false

bishopSubmodulePinRetained : String
bishopSubmodulePinRetained = BishopProvenance.bishopSubmodulePinnedCommit
