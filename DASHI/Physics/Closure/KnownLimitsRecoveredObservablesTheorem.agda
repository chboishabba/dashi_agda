module DASHI.Physics.Closure.KnownLimitsRecoveredObservablesTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalGeometryConsumer as CGC
open import DASHI.Physics.Closure.KnownLimitsRecoveredDynamicsTheorem as KLRD
open import DASHI.Physics.Closure.Validation.ObservableCollapseReport as OCR
open import DASHI.Physics.Closure.Validation.ObservableCollapseShift as OCS
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI

record KnownLimitsRecoveredObservablesTheorem : Setω where
  field
    recoveredDynamics : KLRD.KnownLimitsRecoveredDynamicsTheorem
    geometryConsumer :
      CGC.GeometryConsumerFromMinimal MCCSI.minimumCredibleClosureShift
    observableCollapse : OCR.ObservableCollapseReport

canonicalKnownLimitsRecoveredObservablesTheorem :
  KnownLimitsRecoveredObservablesTheorem
canonicalKnownLimitsRecoveredObservablesTheorem =
  record
    { recoveredDynamics = KLRD.canonicalKnownLimitsRecoveredDynamicsTheorem
    ; geometryConsumer = CGC.canonicalGeometryConsumer
    ; observableCollapse = OCS.shiftReport
    }
