module DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance where

-- Assumptions:
-- - concrete PhysicsClosureFull instance
-- - concrete observable-prediction package
--
-- Output:
-- - canonical minimal-credible closure instance for Stage C surfaces.
--
-- Classification:
-- - minimal credible

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.PhysicsClosureFullInstance as PCFI
open import DASHI.Physics.Closure.ObservablePredictionPackage as OPP
open import DASHI.Physics.Closure.ShiftObservablePredictionInstance as SOPI
open import DASHI.Physics.Signature31Canonical as S31C

minimumCredibleClosureFromProvider :
  (provider : S31C.IntrinsicCoreProvider) →
  (providerSignatureMatches :
    S31C.signature31FromProvider provider
    ≡ OPP.ObservablePredictionPackage.provedSignature
        SOPI.shiftObservablePrediction) →
  MCPC.MinimalCrediblePhysicsClosure
minimumCredibleClosureFromProvider provider providerSignatureMatches =
  record
    { full = PCFI.physicsClosureFullFromLegacyProvider provider
    ; observables = SOPI.shiftObservablePrediction
    ; closureSignatureMatchesPrediction = providerSignatureMatches
    }

minimumCredibleClosureShift : MCPC.MinimalCrediblePhysicsClosure
minimumCredibleClosureShift =
  minimumCredibleClosureFromProvider
    S31C.shiftCoreProvider
    refl

minimumCredibleClosureSyntheticWithProof :
  (syntheticSignatureMatches :
    S31C.signature31FromProvider S31C.syntheticCoreProvider
    ≡ OPP.ObservablePredictionPackage.provedSignature
        SOPI.shiftObservablePrediction) →
  MCPC.MinimalCrediblePhysicsClosure
minimumCredibleClosureSyntheticWithProof syntheticSignatureMatches =
  minimumCredibleClosureFromProvider
    S31C.syntheticCoreProvider
    syntheticSignatureMatches

minimumCredibleClosureSynthetic : MCPC.MinimalCrediblePhysicsClosure
minimumCredibleClosureSynthetic =
  minimumCredibleClosureSyntheticWithProof
    S31C.syntheticSignatureMatchesCanonical
