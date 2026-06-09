module DASHI.Physics.GR where

-- GR-side adapter boundary: placeholders expressed as parameters.

import DASHI.Physics.GR.RiemannTensor
import DASHI.Physics.GR.EinsteinTensor
import DASHI.Physics.GR.StressEnergyCompatibility

open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Bridge using (BridgeSurface)
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureShiftInstance as MCCSI
open import DASHI.Physics.Closure.ObservablePredictionPackage as OPP
open import DASHI.Physics.Closure.ShiftObservablePredictionInstance as SOPI
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.RealClosureKit as RK
open import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.LorentzBridge using (LorentzAdapter)

open import DASHI.Physics.LorentzBridge as LB

record GRAdapter : Set₁ where
  field
    bridge  : BridgeSurface
    lorentz : LorentzAdapter

open GRAdapter public

-- Thin projections so GR can cite the canonical signature seam without
-- importing the underlying signature modules.

grSignature31 : GRAdapter -> _
grSignature31 A = LorentzAdapter.signature31Tag (GRAdapter.lorentz A)

grSignature31Theorem : GRAdapter -> _
grSignature31Theorem A = LorentzAdapter.signature31Theorem (GRAdapter.lorentz A)

grBridgeSurface : MCPC.MinimalCrediblePhysicsClosure -> BridgeSurface
grBridgeSurface C =
  record
    { A = RK.closureAxioms (PCF.PhysicsClosureFull.kit (MCPC.MinimalCrediblePhysicsClosure.full C)) }

canonicalGRAdapterFromMinimal : MCPC.MinimalCrediblePhysicsClosure -> GRAdapter
canonicalGRAdapterFromMinimal C =
  record
    { bridge = grBridgeSurface C
    ; lorentz = LB.canonicalLorentzAdapter (grBridgeSurface C)
    }

canonicalGRAdapter : GRAdapter
canonicalGRAdapter = canonicalGRAdapterFromMinimal MCCSI.minimumCredibleClosureShift

canonicalGRAdapterFromProvider :
  (provider : S31C.IntrinsicCoreProvider) →
  (providerSignatureMatches :
    S31C.signature31FromProvider provider
    ≡ OPP.ObservablePredictionPackage.provedSignature
        SOPI.shiftObservablePrediction) →
  GRAdapter
canonicalGRAdapterFromProvider provider providerSignatureMatches =
  canonicalGRAdapterFromMinimal
    (MCCSI.minimumCredibleClosureFromProvider provider providerSignatureMatches)
