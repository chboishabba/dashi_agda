module DASHI.Physics.Closure.Validation.FejerOverChiSquaredReport where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.Validation.FejerOverChiSquared as FCS

record FejerOverChi2Report : Setω where
  field
    harness : FCS.FejerOverChi2Harness
    facts : FCS.FejerOverChi2Facts
    verdict : FCS.FejerBenchmarkVerdict

buildReport : FCS.FejerOverChi2Harness → FejerOverChi2Report
buildReport harness =
  let facts = FCS.computeFacts harness
  in
  record
    { harness = harness
    ; facts = facts
    ; verdict = FCS.classify facts
    }

