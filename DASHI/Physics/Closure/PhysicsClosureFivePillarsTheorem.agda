module DASHI.Physics.Closure.PhysicsClosureFivePillarsTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.CanonicalDynamicsLawTheorem as CDLT
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW
open import DASHI.Physics.Closure.KnownLimitsFullMatterGaugeTheorem as KLMGFT

record PhysicsClosureFivePillarsTheorem : Setω where
  field
    naturalPhysicalDynamicsLaw : CDLT.CanonicalDynamicsLawTheorem
    conservedPhysicalQuantity :
      DCS.DynamicalClosureStatus.monotoneQuantity
        (CDLT.CanonicalDynamicsLawTheorem.canonicalDynamicsStatus
          naturalPhysicalDynamicsLaw)
      ≡ DCS.mdlLyapunovAndFejer
    continuumLimitTheorem :
      DCS.DynamicalClosureStatus.effectiveGeometry
        (CDLT.CanonicalDynamicsLawTheorem.canonicalDynamicsStatus
          naturalPhysicalDynamicsLaw)
      ≡ DCS.quadraticPolarizationAndOrthogonality
    realizationIndependentProof : DCW.DynamicalClosureWitness
    fullGaugeMatterRecoveryTheorem : KLMGFT.KnownLimitsFullMatterGaugeTheorem

canonicalPhysicsClosureFivePillarsTheorem :
  PhysicsClosureFivePillarsTheorem
canonicalPhysicsClosureFivePillarsTheorem =
  record
    { naturalPhysicalDynamicsLaw = CDLT.canonicalDynamicsLawTheorem
    ; conservedPhysicalQuantity =
        CDLT.CanonicalDynamicsLawTheorem.conservedQuantityLaw
          CDLT.canonicalDynamicsLawTheorem
    ; continuumLimitTheorem =
        CDLT.CanonicalDynamicsLawTheorem.continuumLimitLaw
          CDLT.canonicalDynamicsLawTheorem
    ; realizationIndependentProof =
        CDLT.CanonicalDynamicsLawTheorem.realizationIndependentProofShape
          CDLT.canonicalDynamicsLawTheorem
    ; fullGaugeMatterRecoveryTheorem =
        KLMGFT.canonicalKnownLimitsFullMatterGaugeTheorem
    }
