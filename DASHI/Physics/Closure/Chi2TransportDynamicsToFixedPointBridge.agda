module DASHI.Physics.Closure.Chi2TransportDynamicsToFixedPointBridge where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_)
open import Data.Product using (Σ)

open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.Closure.Chi2CanonicalPoolObservationCandidate as CHI2POOL
open import DASHI.Physics.Closure.Chi2ToShiftPressureTransportCandidate as CHI2SHIFT
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- W3 local transport-dynamics bridge.
--
-- This composes the local chi2-pool -> shift-pressure transport with the
-- existing two-step absorption of shift-pressure dynamics into the held point.
-- It is still non-empirical: no observation target and no
-- `obs(fixedPoint) = empirical` bridge is supplied here.

chi2PoolTransportConvergesWithin2 :
  (case : CHI2POOL.CanonicalChi2PoolCase) →
  Σ Nat
    (λ n →
      Σ (n ≤ suc (suc zero))
        (λ _ →
          DDSI.iterate
            n
            DDSI.shiftPressureAdvance
            (CHI2SHIFT.chi2PoolToShiftPressurePoint case)
          ≡
          SPTI.shiftHeldExitPoint))
chi2PoolTransportConvergesWithin2 case =
  DDSI.shiftConvergesToHeldWithin2
    (CHI2SHIFT.chi2PoolToShiftPressurePoint case)

data Chi2TransportDynamicsBoundary : Set where
  localTransportDynamicsOnly : Chi2TransportDynamicsBoundary
  nonEmpiricalDynamicsOnly : Chi2TransportDynamicsBoundary
  nonPromotingDynamicsOnly : Chi2TransportDynamicsBoundary
  noEmpiricalObservationTarget : Chi2TransportDynamicsBoundary
  noObsFixedPointEqualsEmpiricalClaim : Chi2TransportDynamicsBoundary

record Chi2TransportDynamicsToFixedPointBridge : Set₁ where
  field
    transportCandidate :
      CHI2SHIFT.Chi2ToShiftPressureTransportCandidate

    dynamics :
      DDSI.ShiftConvergesToHeldWithin2

    transportedDynamics :
      (case : CHI2POOL.CanonicalChi2PoolCase) →
      Σ Nat
        (λ n →
          Σ (n ≤ suc (suc zero))
            (λ _ →
              DDSI.iterate
                n
                DDSI.shiftPressureAdvance
                (CHI2SHIFT.Chi2ToShiftPressureTransportCandidate.transport
                  transportCandidate
                  case)
              ≡
              SPTI.shiftHeldExitPoint))

    boundary :
      List Chi2TransportDynamicsBoundary

    remainingW3Gaps :
      List String

canonicalChi2TransportDynamicsToFixedPointBridge :
  Chi2TransportDynamicsToFixedPointBridge
canonicalChi2TransportDynamicsToFixedPointBridge =
  record
    { transportCandidate =
        CHI2SHIFT.canonicalChi2ToShiftPressureTransportCandidate
    ; dynamics =
        DDSI.shiftConvergesToHeldWithin2
    ; transportedDynamics =
        chi2PoolTransportConvergesWithin2
    ; boundary =
        localTransportDynamicsOnly
        ∷ nonEmpiricalDynamicsOnly
        ∷ nonPromotingDynamicsOnly
        ∷ noEmpiricalObservationTarget
        ∷ noObsFixedPointEqualsEmpiricalClaim
        ∷ []
    ; remainingW3Gaps =
        "supply an empirical observation target over the transported chi2 pool"
        ∷ "supply a promotion bridge from local chi2 transport to empirical adequacy"
        ∷ "promote empirical B4 validation beyond standaloneOnly"
        ∷ "promote the origin observation receipt beyond empiricalBlocked"
        ∷ []
    }
