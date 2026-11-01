module DASHI.Physics.QFT where

-- QFT-side adapter boundary: placeholders expressed as parameters.

open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Bridge using (BridgeSurface)
open import DASHI.Physics.CliffordBridge using (CliffordAdapter)
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.ObservablePredictionPackage as OPP
open import DASHI.Physics.Closure.ShiftObservablePredictionInstance as SOPI
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.RealClosureKit as RK
open import DASHI.Physics.Signature31Canonical as S31C

record QFTAdapter : Set₁ where
  field
    bridge    : BridgeSurface
    clifford  : CliffordAdapter

open QFTAdapter public

qftBridgeSurface : MCPC.MinimalCrediblePhysicsClosure -> BridgeSurface
qftBridgeSurface C =
  record
    { A = RK.closureAxioms (PCF.PhysicsClosureFull.kit (MCPC.MinimalCrediblePhysicsClosure.full C)) }

canonicalQFTAdapterFromMinimal : MCPC.MinimalCrediblePhysicsClosure -> QFTAdapter
canonicalQFTAdapterFromMinimal C =
  record
    { bridge = qftBridgeSurface C
    ; clifford = record { bridge = qftBridgeSurface C}
    }

canonicalQFTAdapter : QFTAdapter
canonicalQFTAdapter = canonicalQFTAdapterFromMinimal MCCSI.minimumCredibleClosureShift

canonicalQFTAdapterFromProvider :
  (provider : S31C.IntrinsicCoreProvider) →
  (providerSignatureMatches :
    S31C.signature31FromProvider provider
    ≡ OPP.ObservablePredictionPackage.provedSignature
        SOPI.shiftObservablePrediction) →
  QFTAdapter
canonicalQFTAdapterFromProvider provider providerSignatureMatches =
  canonicalQFTAdapterFromMinimal
    (MCCSI.minimumCredibleClosureFromProvider provider providerSignatureMatches)
