module DASHI.Analysis.DyadicPhaseCellCertificateExact where

------------------------------------------------------------------------
-- EXACT DYADIC ENCLOSURE -> EXISTING RADIAL-TREE CELL
--
-- External rigorous numerics naturally return dyadic interval endpoints.
-- This owner performs only the small kernel-side arithmetic payment needed by
-- the climbing-gym consumer.  If an entire dyadic interval lies strictly
-- inside one j/N radix cell, then that cell index deterministically compiles to
-- the repository's existing `RadialTreeAddress`.
--
-- Crucially, this module does NOT assert where the interval came from.  A
-- FLINT/Arb calculation, a hand proof, or any other producer must separately
-- establish that the analytic quantity of interest is enclosed by the supplied
-- interval.  Checked cell arithmetic cannot promote producer provenance into
-- zeta-zero truth or Monster authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_≤_; _<_)
import Data.Nat.Properties as NatP
open NatP using (_≤?_; _<?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Foundations.NatRadialTreeCodecExact as NatRadix
import DASHI.Foundations.RadixValuationStageBridge as Radix

------------------------------------------------------------------------
-- Nonnegative dyadic interval [lower / 2^k, upper / 2^k].
------------------------------------------------------------------------

twoPower : Nat → Nat
twoPower zero = 1
twoPower (suc exponent) = 2 * twoPower exponent

record DyadicInterval : Set where
  constructor dyadic-interval
  field
    denominatorExponent : Nat
    lowerNumerator : Nat
    upperNumerator : Nat
    ordered : lowerNumerator ≤ upperNumerator

open DyadicInterval public

dyadicDenominator : DyadicInterval → Nat
dyadicDenominator interval = twoPower (denominatorExponent interval)

radixCellCount : Radix.RadixChart → Nat → Nat
radixCellCount chart depth =
  Radix.radixPower (Radix.radix chart) depth

------------------------------------------------------------------------
-- Whole-interval strict containment in one open radix cell.
--
--   j/N < lower/2^k <= upper/2^k < (j+1)/N
--
-- is checked without division by cross-multiplication over Nat.
------------------------------------------------------------------------

record CertifiedDyadicRadixCell
    (chart : Radix.RadixChart)
    (depth : Nat)
    (interval : DyadicInterval) : Set where
  constructor certified-dyadic-radix-cell
  field
    cellIndex : Nat
    cellIndexInRange : cellIndex < radixCellCount chart depth

    lowerStrictInside :
      cellIndex * dyadicDenominator interval
      < radixCellCount chart depth * lowerNumerator interval

    upperStrictInside :
      radixCellCount chart depth * upperNumerator interval
      < suc cellIndex * dyadicDenominator interval

open CertifiedDyadicRadixCell public

certifiedRadialAddress :
  ∀ {chart depth interval} →
  CertifiedDyadicRadixCell chart depth interval →
  Radix.RadialTreeAddress chart depth
certifiedRadialAddress {chart} {depth} certificate =
  NatRadix.natRadialAddress chart depth (cellIndex certificate)

certifiedRadialValue :
  ∀ {chart depth interval} →
  CertifiedDyadicRadixCell chart depth interval →
  Nat
certifiedRadialValue {chart} certificate =
  NatRadix.radialValue chart (certifiedRadialAddress certificate)

------------------------------------------------------------------------
-- Small executable-by-normalisation fixture.
--
-- [9/16,10/16] lies strictly inside binary depth-one cell j=1 = (1/2,1).
------------------------------------------------------------------------

binaryInteriorInterval : DyadicInterval
binaryInteriorInterval =
  dyadic-interval 4 9 10
    (toWitness {a? = 9 ≤? 10} _)

binaryInteriorCertificate :
  CertifiedDyadicRadixCell Radix.binaryChart 1 binaryInteriorInterval
binaryInteriorCertificate =
  certified-dyadic-radix-cell
    1
    (toWitness {a? = 1 <? 2} _)
    (toWitness {a? = 16 <? 18} _)
    (toWitness {a? = 20 <? 32} _)

binaryInteriorAddressValue :
  certifiedRadialValue binaryInteriorCertificate ≡ 1
binaryInteriorAddressValue = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record DyadicPhaseCellBoundary : Set where
  constructor dyadic-phase-cell-boundary
  field
    exactDyadicIntervalCarrierDefined : Bool
    strictCellContainmentCheckedByNatArithmetic : Bool
    existingRadialTreeReused : Bool
    certifiedDyadicCellToRadialAddressClosed : Bool

    producerEnclosureTruthCreatedByChecker : Bool
    totalConstructiveRealFloorRequired : Bool
    certificateProvesZetaZero : Bool
    certificateProvesMonsterSpecificity : Bool

open DyadicPhaseCellBoundary public

canonicalDyadicPhaseCellBoundary : DyadicPhaseCellBoundary
canonicalDyadicPhaseCellBoundary =
  dyadic-phase-cell-boundary
    true true true true
    false false false false
