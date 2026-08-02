module DASHI.Physics.Closure.NSTriadKNQuarticLyapunovStage3OrderedL2Bridge where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Quartic-Lyapunov bridge for the Stage-3 ordered l2 analytic path".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a repository-original dependency bridge.
-- Uses: the exact vector-adjoint layer, ordered-l2 analytic integration,
-- canonical hard-shell geometry, component profiles and finite-overlap counts.
-- Relationship: makes the ordinary theorem path visible to the eight-stage
-- aggregate without importing the optional Stage-3 369 status adapters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNStage3OrderedL2AnalyticIntegration as Stage3

stage3OrderedL2PathRepresented : Bool
stage3OrderedL2PathRepresented = Stage3.stage3OrderedL2AnalyticPathRepresented

stage3OrderedL2PathRepresentedIsTrue :
  stage3OrderedL2PathRepresented ≡ true
stage3OrderedL2PathRepresentedIsTrue =
  Stage3.stage3OrderedL2AnalyticPathRepresentedIsTrue

stage3OrderedL2PathAnalyticallyClosed : Bool
stage3OrderedL2PathAnalyticallyClosed = Stage3.stage3OrderedL2AnalyticallyClosed

stage3OrderedL2PathAnalyticallyClosedIsFalse :
  stage3OrderedL2PathAnalyticallyClosed ≡ false
stage3OrderedL2PathAnalyticallyClosedIsFalse =
  Stage3.stage3OrderedL2AnalyticallyClosedIsFalse
