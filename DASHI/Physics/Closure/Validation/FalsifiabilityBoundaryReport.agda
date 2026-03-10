module DASHI.Physics.Closure.Validation.FalsifiabilityBoundaryReport where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.Validation.FalsifiabilityBoundary as FB

record FalsifiabilityBoundaryReport : Setω where
  field
    harness : FB.FalsifiabilityBoundaryHarness
    facts : FB.FalsifiabilityBoundaryFacts harness
    verdict : FB.FalsifiabilityBoundaryVerdict

buildReport :
  FB.FalsifiabilityBoundaryHarness →
  FalsifiabilityBoundaryReport
buildReport harness =
  let facts = FB.computeFacts harness
  in
  record
    { harness = harness
    ; facts = facts
    ; verdict = FB.classify facts
    }
