module DASHI.Physics.Closure.NSTriadKNStage3MurrayBishopConcreteBackendIntegration where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Martín Hötzel Escardó; Fredrik
-- Nordvall Forsberg; Chuangjie Xu; Zachary Murray; Viktor Csimma; Jean-Michel
-- Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Loukas Grafakos;
-- Rodolfo H. Torres; DASHI repository contributors.
-- Title: "Constructive Analysis"; "Formalising Real Numbers in Homotopy Type
-- Theory"; "Constructive Analysis in the Agda Proof Assistant"; "Fourier
-- Analysis and Nonlinear Partial Differential Equations"; "A Multilinear
-- Schur Test and Multiplier Operators"; and "Stage-3 Murray--Bishop concrete
-- backend integration".
-- Venue/year: Springer, 1985 and 2011; CPP 2017; Dalhousie University/arXiv,
-- 2022; Journal of Functional Analysis 187 (2001), 1--24; DASHI formal
-- development, 2026.
-- DOI: 10.1007/978-3-642-61667-9; 10.1145/3018610.3018614;
-- 10.48550/arXiv.2205.08354; 10.1007/978-3-642-16830-7;
-- 10.1006/jfan.2001.3804; the repository integration receipt has no DOI.
-- Source pin: viktorcsimma/bishop commit
-- 582c6afcdf805d06730c8c0aa970f4a6e033b611.
-- Uses: the concrete complete setoid backend, exact rational embedding,
-- canonical dyadic anchors, s = 11/4 and the setoid direct-canonical 128/93
-- theorem.
-- Relationship: supersedes the former generic-backend frontier for this
-- archetype.  Total real exp/log remains a separate library objective, not an
-- input to output relocation.  The sole open physical seam is the literal
-- coefficient sandwich against the embedded canonical kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.MurrayBishopSetoidBackend as Backend
import DASHI.Physics.Closure.NSTriadKNSetoidDirectCanonicalEnvelopeClosure as Direct
import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
import DASHI.Physics.Closure.NSTriadKNMurrayBishopCanonicalDyadicAnchors as Anchors
import DASHI.Physics.Closure.NSTriadKNMurrayBishopSobolevElevenFourths as Sobolev
import DASHI.Physics.Closure.NSTriadKNMurrayBishopBackendScopeAudit as Scope

record Stage3MurrayBishopConcreteBackendReceipt : Set where
  constructor receipt
  field
    sourcePinned : Scope.bishopSourcePinned ≡ true
    carrierNondegenerate : Backend.murrayBishopCarrierNondegenerate ≡ true
    setoidCompletenessClosed :
      Backend.murrayBishopSetoidCompletenessClosed ≡ true
    quotientChoiceNotImported :
      Backend.literalQuotientCompletenessNotUsed ≡ true
    rationalEnvelopeCarrierClosed :
      Carrier.murrayBishopRationalEnvelopeCarrierClosed ≡ true
    directCanonicalSummationClosed :
      Direct.setoidDirectCanonicalSummationClosed ≡ true
    directCanonical128Over93Closed :
      Carrier.murrayBishopDirectCanonical128Over93Closed ≡ true
    exactIntegerAnchorsClosed :
      Anchors.murrayBishopExactIntegerAnchorsClosed ≡ true
    totalExpLogNotRequired :
      Direct.setoidDirectCanonicalExpLogIndependent ≡ true
    concreteSobolevIntervalClosed :
      Sobolev.murrayBishopConcreteSobolevIntervalClosed ≡ true
    concreteDecayArithmeticClosed :
      Sobolev.murrayBishopConcreteDecayArithmeticClosed ≡ true
    literalCoefficientBridgeStillOpen :
      Scope.literalNavierStokesDirectCanonicalCoefficientBridgeClosed ≡ false

open Stage3MurrayBishopConcreteBackendReceipt public

stage3MurrayBishopConcreteBackendReceipt :
  Stage3MurrayBishopConcreteBackendReceipt
stage3MurrayBishopConcreteBackendReceipt = receipt
  Scope.bishopSourcePinnedIsTrue
  Backend.murrayBishopCarrierNondegenerateIsTrue
  Backend.murrayBishopSetoidCompletenessClosedIsTrue
  Backend.literalQuotientCompletenessNotUsedIsTrue
  Carrier.murrayBishopRationalEnvelopeCarrierClosedIsTrue
  Direct.setoidDirectCanonicalSummationClosedIsTrue
  Carrier.murrayBishopDirectCanonical128Over93ClosedIsTrue
  Anchors.murrayBishopExactIntegerAnchorsClosedIsTrue
  Direct.setoidDirectCanonicalExpLogIndependentIsTrue
  Sobolev.murrayBishopConcreteSobolevIntervalClosedIsTrue
  Sobolev.murrayBishopConcreteDecayArithmeticClosedIsTrue
  Scope.literalNavierStokesDirectCanonicalCoefficientBridgeClosedIsFalse

outputRelocationGenericBackendComplete : Bool
outputRelocationGenericBackendComplete = true

outputRelocationConcreteSobolevChoiceComplete : Bool
outputRelocationConcreteSobolevChoiceComplete = true

outputRelocationGlobalExpLogDependencyRetired : Bool
outputRelocationGlobalExpLogDependencyRetired = true

outputRelocationLiteralPhysicalCoefficientBridgeComplete : Bool
outputRelocationLiteralPhysicalCoefficientBridgeComplete = false

outputRelocationGenericBackendCompleteIsTrue :
  outputRelocationGenericBackendComplete ≡ true
outputRelocationGenericBackendCompleteIsTrue = refl

outputRelocationConcreteSobolevChoiceCompleteIsTrue :
  outputRelocationConcreteSobolevChoiceComplete ≡ true
outputRelocationConcreteSobolevChoiceCompleteIsTrue = refl

outputRelocationGlobalExpLogDependencyRetiredIsTrue :
  outputRelocationGlobalExpLogDependencyRetired ≡ true
outputRelocationGlobalExpLogDependencyRetiredIsTrue = refl

outputRelocationLiteralPhysicalCoefficientBridgeCompleteIsFalse :
  outputRelocationLiteralPhysicalCoefficientBridgeComplete ≡ false
outputRelocationLiteralPhysicalCoefficientBridgeCompleteIsFalse = refl
