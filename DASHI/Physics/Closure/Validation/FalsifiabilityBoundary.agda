module DASHI.Physics.Closure.Validation.FalsifiabilityBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import DASHI.Physics.OrbitSignatureDiscriminant as OSD

data FalsifiabilityBoundaryVerdict : Set where
  boundaryEstablished : FalsifiabilityBoundaryVerdict

record FalsifiabilityBoundaryHarness : Setω where
  field
    label : String
    falsifySig40 : OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig40
    falsifySig22 : OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig22
    falsifyMirror : OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig13
    falsifySig04 : OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig04

record FalsifiabilityBoundaryFacts
  (harness : FalsifiabilityBoundaryHarness) : Setω where
  field
    sig40Exclusion :
      OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig40
    sig22Exclusion :
      OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig22
    mirrorExclusion :
      OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig13
    sig04Exclusion :
      OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig04

computeFacts :
  (harness : FalsifiabilityBoundaryHarness) →
  FalsifiabilityBoundaryFacts harness
computeFacts harness =
  record
    { sig40Exclusion = FalsifiabilityBoundaryHarness.falsifySig40 harness
    ; sig22Exclusion = FalsifiabilityBoundaryHarness.falsifySig22 harness
    ; mirrorExclusion = FalsifiabilityBoundaryHarness.falsifyMirror harness
    ; sig04Exclusion = FalsifiabilityBoundaryHarness.falsifySig04 harness
    }

classify :
  ∀ {harness} →
  FalsifiabilityBoundaryFacts harness →
  FalsifiabilityBoundaryVerdict
classify _ = boundaryEstablished
