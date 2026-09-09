module DASHI.Physics.GR where

-- GR-side adapter boundary: placeholders expressed as parameters.

import DASHI.Physics.GR.RiemannTensor
import DASHI.Physics.GR.EinsteinTensor
import DASHI.Physics.GR.StressEnergyCompatibility
import DASHI.Physics.GR.GravitationalObservationSourceAtlasExact
import DASHI.Physics.GR.GravitationalObservationBidiExact
import DASHI.Physics.GR.GravitationalWaveTheoryTestBidiExact
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact
import DASHI.Physics.GR.GravitationalMultiScaleTheoryFingerprintBidiExact
import DASHI.Physics.GR.GravitationalEpistemicLineageExact
import DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact
import DASHI.Physics.GR.GravitationalAttributedMultiScaleFingerprintBidiExact
import DASHI.Physics.GR.GravitationalWavePolarizationSourceAttributionExact
import DASHI.Physics.GR.GravitationalWavePolarizationSignBidiExact
import DASHI.Physics.GR.GravitationalWavePhaseSignBidiExact
import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact
import DASHI.Physics.GR.SignedEinsteinCouplingSourceDegeneracyBidiExact
import DASHI.Physics.GR.SignedGRNormalizationBidiExact
import DASHI.Physics.GR.SignedNewtonianLimitBidiExact
import DASHI.Physics.GR.SignedGravitationalWaveCouplingBidiExact
import DASHI.Physics.GR.SignedCosmologicalMatterCouplingBidiExact
import DASHI.Physics.GR.UniversalSignedGCrossScaleFingerprintBidiExact
import DASHI.Physics.GR.NegativeGPredictionAuthorityExact
import DASHI.Physics.GR.SignedGSourceDynamicsBidiExact

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
