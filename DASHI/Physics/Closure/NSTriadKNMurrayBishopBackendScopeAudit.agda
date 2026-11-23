module DASHI.Physics.Closure.NSTriadKNMurrayBishopBackendScopeAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Martín Hötzel Escardó; Fredrik
-- Nordvall Forsberg; Chuangjie Xu; Zachary Murray; Viktor Csimma; Loukas
-- Grafakos; Rodolfo H. Torres; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Formalising Real Numbers in Homotopy Type
-- Theory"; "Constructive Analysis in the Agda Proof Assistant"; "A
-- Multilinear Schur Test and Multiplier Operators"; and "Murray--Bishop
-- backend and transcendental-scope audit for output relocation".
-- Venue/year: Springer, 1985; CPP 2017; Dalhousie University/arXiv, 2022;
-- Journal of Functional Analysis 187 (2001), 1--24; DASHI formal development,
-- 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.1145/3018610.3018614;
-- 10.48550/arXiv.2205.08354; 10.1006/jfan.2001.3804; the repository audit has
-- no DOI.
-- Source pin: viktorcsimma/bishop commit
-- 582c6afcdf805d06730c8c0aa970f4a6e033b611.
-- Uses: the concrete Murray regular-sequence setoid, exact rational dyadic
-- anchors, the concrete Sobolev exponent 11/4, and the direct-canonical
-- 128/93 theorem.
-- Relationship: records why a total exp/log package and literal quotient
-- completeness are not proof-critical for this archetype.  It leaves only the
-- literal Navier--Stokes coefficient-to-canonical-kernel bridge fail-closed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MurrayBishopSetoidBackend as Backend
import DASHI.Physics.Closure.NSTriadKNSetoidDirectCanonicalEnvelopeClosure as Direct
import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
import DASHI.Physics.Closure.NSTriadKNMurrayBishopCanonicalDyadicAnchors as Anchors
import DASHI.Physics.Closure.NSTriadKNMurrayBishopSobolevElevenFourths as Sobolev

bishopSourceRepository : String
bishopSourceRepository = "viktorcsimma/bishop"

bishopSourceCommit : String
bishopSourceCommit = "582c6afcdf805d06730c8c0aa970f4a6e033b611"

bishopSourcePinned : Bool
bishopSourcePinned = true

murrayBishopSetoidBackendClosed : Bool
murrayBishopSetoidBackendClosed = true

arbitraryLiteralQuotientSequenceCompletenessClaimed : Bool
arbitraryLiteralQuotientSequenceCompletenessClaimed = false

setoidCompletenessAvoidsRepresentativeChoice : Bool
setoidCompletenessAvoidsRepresentativeChoice = true

globalRealExpLogPackageInhabited : Bool
globalRealExpLogPackageInhabited = false

globalRealExpLogRequiredForThisArchetype : Bool
globalRealExpLogRequiredForThisArchetype = false

exactCanonicalDyadicAnchorsInhabited : Bool
exactCanonicalDyadicAnchorsInhabited = true

concreteSobolevElevenFourthsInhabited : Bool
concreteSobolevElevenFourthsInhabited = true

setoidDirectCanonical128Over93Closed : Bool
setoidDirectCanonical128Over93Closed = true

literalNavierStokesDirectCanonicalCoefficientBridgeClosed : Bool
literalNavierStokesDirectCanonicalCoefficientBridgeClosed = false

bishopSourcePinnedIsTrue : bishopSourcePinned ≡ true
bishopSourcePinnedIsTrue = refl

murrayBishopSetoidBackendClosedIsTrue :
  murrayBishopSetoidBackendClosed ≡ true
murrayBishopSetoidBackendClosedIsTrue =
  Backend.murrayBishopSetoidCompletenessClosedIsTrue

arbitraryLiteralQuotientSequenceCompletenessClaimedIsFalse :
  arbitraryLiteralQuotientSequenceCompletenessClaimed ≡ false
arbitraryLiteralQuotientSequenceCompletenessClaimedIsFalse = refl

setoidCompletenessAvoidsRepresentativeChoiceIsTrue :
  setoidCompletenessAvoidsRepresentativeChoice ≡ true
setoidCompletenessAvoidsRepresentativeChoiceIsTrue =
  Backend.literalQuotientCompletenessNotUsedIsTrue

globalRealExpLogPackageInhabitedIsFalse :
  globalRealExpLogPackageInhabited ≡ false
globalRealExpLogPackageInhabitedIsFalse = refl

globalRealExpLogRequiredForThisArchetypeIsFalse :
  globalRealExpLogRequiredForThisArchetype ≡ false
globalRealExpLogRequiredForThisArchetypeIsFalse =
  Direct.setoidDirectCanonicalExpLogIndependentIsTrue

exactCanonicalDyadicAnchorsInhabitedIsTrue :
  exactCanonicalDyadicAnchorsInhabited ≡ true
exactCanonicalDyadicAnchorsInhabitedIsTrue =
  Anchors.murrayBishopExactIntegerAnchorsClosedIsTrue

concreteSobolevElevenFourthsInhabitedIsTrue :
  concreteSobolevElevenFourthsInhabited ≡ true
concreteSobolevElevenFourthsInhabitedIsTrue =
  Sobolev.murrayBishopConcreteSobolevIntervalClosedIsTrue

setoidDirectCanonical128Over93ClosedIsTrue :
  setoidDirectCanonical128Over93Closed ≡ true
setoidDirectCanonical128Over93ClosedIsTrue =
  Carrier.murrayBishopDirectCanonical128Over93ClosedIsTrue

literalNavierStokesDirectCanonicalCoefficientBridgeClosedIsFalse :
  literalNavierStokesDirectCanonicalCoefficientBridgeClosed ≡ false
literalNavierStokesDirectCanonicalCoefficientBridgeClosedIsFalse = refl
