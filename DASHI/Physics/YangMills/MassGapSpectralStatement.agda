module DASHI.Physics.YangMills.MassGapSpectralStatement where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

------------------------------------------------------------------------
-- Physical spectral statement.
--
-- This owner used to mark the physical Hamiltonian and positive continuum
-- spectral gap as already available.  The 2026 Lean/Agda bidirectional audit
-- shows that this conflated a source-intake/finite-carrier route with the
-- literal domain-theoretic continuum Hamiltonian.  The existing owner is now
-- fail-closed at the physical level and consumes the actual frontier.
------------------------------------------------------------------------

record MassGapSpectralStatement : Set₁ where
  field
    physicalHamiltonianAvailable : Bool
    physicalVacuumEigenvalueZeroEstablished : Bool
    physicalVacuumMultiplicityOneEstablished : Bool
    physicalContinuumSpectralGapPositive : Bool

    -- Generic theorem now genuinely available from the sibling Lean tranche.
    boundedStrongLimitFormGapTransportAvailable : Bool

    -- Missing operator/form bridge needed before the generic theorem can be
    -- promoted to the physical continuum Hamiltonian.
    genuinePartialDomainHamiltonianAvailable : Bool
    unboundedContinuumGapTransportAvailable : Bool

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
    genuinePartialDomainHamiltonianAvailableIsFalse :
      genuinePartialDomainHamiltonianAvailable ≡ false
    unboundedContinuumGapTransportAvailableIsFalse :
      unboundedContinuumGapTransportAvailable ≡ false
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
  ; genuinePartialDomainHamiltonianAvailable =
      Frontier.genuinePartialDomainHamiltonianFormalized
        Frontier.canonicalYMOperatorContinuumFrontier
  ; unboundedContinuumGapTransportAvailable =
      Frontier.unboundedClosedFormOrResolventGapTransportClosed
        Frontier.canonicalYMOperatorContinuumFrontier
  ; gapBound =
      "Lean proves bounded pointwise-strong-limit quadratic-form lower-bound transport. A physical continuum YM mass gap is not promoted until a genuine domain-aware Hamiltonian, vacuum identification, and closed-form/resolvent continuum transport are constructed."
  ; clayPromoted = false
  ; physicalHamiltonianAvailableIsFalse = refl
  ; physicalVacuumEigenvalueZeroEstablishedIsFalse = refl
  ; physicalVacuumMultiplicityOneEstablishedIsFalse = refl
  ; physicalContinuumSpectralGapPositiveIsFalse = refl
  ; boundedStrongLimitFormGapTransportAvailableIsTrue = refl
  ; genuinePartialDomainHamiltonianAvailableIsFalse = refl
  ; unboundedContinuumGapTransportAvailableIsFalse = refl
  ; clayPromotedIsFalse = refl
  ; noClayPromotion = refl
  }
