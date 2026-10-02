module DASHI.ComputerScience.TekumSourceAttributionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record SourceRecord : Set where
  constructor sourceRecord
  field
    author : String
    title : String
    year : Nat
    locator : String
    importedClaim : String
    excludedPromotion : String
open SourceRecord public

hunholdTekumSource : SourceRecord
hunholdTekumSource =
  sourceRecord
    "Laslo Hunhold"
    "Tekum: Balanced Ternary Tapered Precision Real Arithmetic"
    2025
    "arXiv:2512.10964"
    "Balanced-ternary integer mapping, anchor anc_n(t)=|t|-11...1, three-trit regime, tapered exponent count, Tekum encoding, injectivity, negation, monotonicity and truncation-as-rounding."
    "The source does not identify Tekum fields with DASHI SSP15 or FRACTRAN semantics; any such bridge is a separate DASHI construction."

schloeglFeySource : SourceRecord
schloeglFeySource =
  sourceRecord
    "Thomas Schloegl; Dietmar Fey"
    "Ternary Signed Digit Addition on Field Programmable Gate Arrays"
    2026
    "DOI:10.1007/978-3-032-03281-2_3"
    "Binary-coded ternary signed-digit FPGA addition; LUT and carry-chain implementations; reported width-independent addition clock behaviour and approximately 50 percent LUT reduction versus the naive LUT design."
    "The abstract/result receipt is empirical hardware evidence, not a kernel proof of a particular gate-level netlist."

record AttributionBoundary : Set where
  constructor attributionBoundary
  field
    sourceClaimsSeparatedFromDASHIBridges : Bool
    empiricalHardwareClaimsSeparatedFromProof : Bool

canonicalAttributionBoundary : AttributionBoundary
canonicalAttributionBoundary = attributionBoundary true true
