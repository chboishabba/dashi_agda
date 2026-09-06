module DASHI.Physics.YangMills.MassGapSpectralStatement where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

------------------------------------------------------------------------
-- Physical spectral statement.
--
-- Historical source-intake/finite-carrier gap claims are now separated from
-- the literal physical continuum statement.  Both the sibling Lean bounded
-- strong-limit compiler and the pre-existing Agda vacuum-recovery compiler are
-- consumed here; neither is promoted without its physical producer.
------------------------------------------------------------------------

record MassGapSpectralStatement : Set₁ where
  field
    physicalHamiltonianAvailable : Bool
    physicalVacuumEigenvalueZeroEstablished : Bool
    physicalVacuumMultiplicityOneEstablished : Bool
    physicalContinuumSpectralGapPositive : Bool

    boundedStrongLimitFormGapTransportAvailable : Bool
    vacuumOrthogonalRecoveryGapCompilerAvailable : Bool
    denseCoreSpectralExclusionCompilerAvailable : Bool

    genuinePartialDomainHamiltonianAvailable : Bool
    physicalVacuumRecoverySystemAvailable : Bool
    physicalDenseCoreProducerAvailable : Bool
    physicalClosedFormOrResolventIdentificationAvailable : Bool

    gapBound : String
    clayPromoted : Bool

    physicalHamiltonianAvailableIsFalse : physicalHamiltonianAvailable ≡ false
    physicalVacuumEigenvalueZeroEstablishedIsFalse :
      physicalVacuumEigenvalueZeroEstablished ≡ false
    physicalVacuumMultiplicityOneEstablishedIsFalse :
      physicalVacuumMultiplicityOneEstablished ≡ false
    physicalContinuumSpectralGapPositiveIsFalse :
      physicalContinuumSpectralGapPositive ≡ false
    boundedStrongLimitFormGapTransportAvailableIsTrue :
      boundedStrongLimitFormGapTransportAvailable ≡ true
    vacuumOrthogonalRecoveryGapCompilerAvailableIsTrue :
      vacuumOrthogonalRecoveryGapCompilerAvailable ≡ true
    denseCoreSpectralExclusionCompilerAvailableIsTrue :
      denseCoreSpectralExclusionCompilerAvailable ≡ true
    genuinePartialDomainHamiltonianAvailableIsFalse :
      genuinePartialDomainHamiltonianAvailable ≡ false
    physicalVacuumRecoverySystemAvailableIsFalse :
      physicalVacuumRecoverySystemAvailable ≡ false
    physicalDenseCoreProducerAvailableIsFalse :
      physicalDenseCoreProducerAvailable ≡ false
    physicalClosedFormOrResolventIdentificationAvailableIsFalse :
      physicalClosedFormOrResolventIdentificationAvailable ≡ false
    clayPromotedIsFalse : clayPromoted ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalMassGapSpectralStatement : MassGapSpectralStatement
canonicalMassGapSpectralStatement = record
  { physicalHamiltonianAvailable =
      Frontier.genuinePartialDomainHamiltonianFormalized
        Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalVacuumEigenvalueZeroEstablished = false
  ; physicalVacuumMultiplicityOneEstablished = false
  ; physicalContinuumSpectralGapPositive = false
  ; boundedStrongLimitFormGapTransportAvailable =
      Frontier.boundedStrongLimitFormGapTransportClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; vacuumOrthogonalRecoveryGapCompilerAvailable =
      Frontier.vacuumOrthogonalRecoveryGapCompilerClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; denseCoreSpectralExclusionCompilerAvailable =
      Frontier.denseCoreSpectralExclusionCompilerClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; genuinePartialDomainHamiltonianAvailable =
      Frontier.genuinePartialDomainHamiltonianFormalized
        Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalVacuumRecoverySystemAvailable =
      Frontier.physicalVacuumRecoverySystemConstructed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalDenseCoreProducerAvailable =
      Frontier.physicalDenseCoreClusteringContinuityProducerClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; physicalClosedFormOrResolventIdentificationAvailable =
      Frontier.physicalClosedFormOrResolventIdentificationClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; gapBound =
      "Two generic compilers are closed: Lean bounded pointwise-strong-limit form-gap transport and Agda vacuum-orthogonal recovery gap transport; Agda also closes dense-core spectral exclusion. The physical continuum YM gap remains open until the domain-aware Hamiltonian, vacuum-orthogonal recovery/dense-core producers, and physical continuum identification are supplied."
  ; clayPromoted = false
  ; physicalHamiltonianAvailableIsFalse = refl
  ; physicalVacuumEigenvalueZeroEstablishedIsFalse = refl
  ; physicalVacuumMultiplicityOneEstablishedIsFalse = refl
  ; physicalContinuumSpectralGapPositiveIsFalse = refl
  ; boundedStrongLimitFormGapTransportAvailableIsTrue = refl
  ; vacuumOrthogonalRecoveryGapCompilerAvailableIsTrue = refl
  ; denseCoreSpectralExclusionCompilerAvailableIsTrue = refl
  ; genuinePartialDomainHamiltonianAvailableIsFalse = refl
  ; physicalVacuumRecoverySystemAvailableIsFalse = refl
  ; physicalDenseCoreProducerAvailableIsFalse = refl
  ; physicalClosedFormOrResolventIdentificationAvailableIsFalse = refl
  ; clayPromotedIsFalse = refl
  ; noClayPromotion = refl
  }
