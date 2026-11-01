module DASHI.Physics.Closure.Validation.ObservableCollapseReport where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.Validation.ObservableCollapse as OC

record ObservableCollapseReport : Setω where
  field
    harness : OC.ObservableCollapseHarness
    facts : OC.ObservableCollapseFacts harness
    verdict : OC.ObservableCollapseVerdict

buildReport : OC.ObservableCollapseHarness → ObservableCollapseReport
buildReport harness =
  let facts = OC.computeFacts harness
  in
  record
    { harness = harness
    ; facts = facts
    ; verdict = OC.classify facts
    }
