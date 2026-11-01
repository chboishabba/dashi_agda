module DASHI.Physics.Closure.CanonicalObservableConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalGeometryConsumer as CGC
open import DASHI.Physics.Closure.KnownLimitsRecoveredObservablesTheorem as KLRO
open import DASHI.Physics.Closure.Validation.ObservableCollapseReport as OCR
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record ObservableConsumerFromMinimal
  (C : MCPC.MinimalCrediblePhysicsClosure) : Setω where
  field
    geometryConsumer : CGC.GeometryConsumerFromMinimal C
    recoveredObservables : KLRO.KnownLimitsRecoveredObservablesTheorem
    observableCollapse : OCR.ObservableCollapseReport

canonicalObservableConsumer :
  ObservableConsumerFromMinimal MCCSI.minimumCredibleClosureShift
canonicalObservableConsumer =
  record
    { geometryConsumer = CGC.canonicalGeometryConsumer
    ; recoveredObservables = KLRO.canonicalKnownLimitsRecoveredObservablesTheorem
    ; observableCollapse =
        KLRO.KnownLimitsRecoveredObservablesTheorem.observableCollapse
          KLRO.canonicalKnownLimitsRecoveredObservablesTheorem
    }
