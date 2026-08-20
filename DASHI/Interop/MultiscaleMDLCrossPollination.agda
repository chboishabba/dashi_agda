module DASHI.Interop.MultiscaleMDLCrossPollination where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import DASHI.Core.MultiscaleMDL
open import DASHI.Foundations.SSPTritCarrier

------------------------------------------------------------------------
-- Cross-pollination surface.
--
-- The exact shared machine is:
--
--   carrier at scale j
--     -> coarse projection + gated residual
--     -> exact reconstruction
--     -> symmetry/orbit witness
--     -> kernel naturality
--     -> explicit MDL/admissibility receipt.
--
-- Codec, DNA, wave, Lie-action, and sparse-twist readings instantiate this
-- machine differently.  This module records the common interfaces and the
-- non-identifications needed to prevent one lane's semantics or authority from
-- leaking into another.

------------------------------------------------------------------------
-- Exact support/sign factorisation of the canonical SSP trit.

record SupportSign : Set where
  constructor support-sign
  field
    support : Bool
    negative : Bool
open SupportSign public

factorSSPTrit : SSPTrit → SupportSign
factorSSPTrit sspNegOne = support-sign true true
factorSSPTrit sspZero = support-sign false false
factorSSPTrit sspPosOne = support-sign true false

decodeSupportSign : SupportSign → SSPTrit
decodeSupportSign (support-sign false _) = sspZero
decodeSupportSign (support-sign true true) = sspNegOne
decodeSupportSign (support-sign true false) = sspPosOne

support-sign-roundtrip : ∀ t → decodeSupportSign (factorSSPTrit t) ≡ t
support-sign-roundtrip sspNegOne = refl
support-sign-roundtrip sspZero = refl
support-sign-roundtrip sspPosOne = refl

-- Sign is a gated fibre: its value is semantically irrelevant when support is
-- false.  Canonicalisation removes that redundant bit.

canonicaliseSupportSign : SupportSign → SupportSign
canonicaliseSupportSign (support-sign false _) = support-sign false false
canonicaliseSupportSign (support-sign true sign) = support-sign true sign

decode-canonicalise : ∀ x → decodeSupportSign (canonicaliseSupportSign x) ≡ decodeSupportSign x
decode-canonicalise (support-sign false false) = refl
decode-canonicalise (support-sign false true) = refl
decode-canonicalise (support-sign true false) = refl
decode-canonicalise (support-sign true true) = refl

------------------------------------------------------------------------
-- Domain roles.  These are interpretations of one formal machine, not proofs
-- that the domains are identical.

data CrossPollinationLane : Set where
  codecLane : CrossPollinationLane
  dnaLane : CrossPollinationLane
  waveLane : CrossPollinationLane
  lieActionLane : CrossPollinationLane
  sparseTwistLane : CrossPollinationLane

laneCarrierReading : CrossPollinationLane → String
laneCarrierReading codecLane = "balanced-trit residual planes or structured symbol blocks"
laneCarrierReading dnaLane = "admissible CAGT traces with biochemical state context"
laneCarrierReading waveLane = "phase/coherence amplitudes over a selected wave carrier"
laneCarrierReading lieActionLane = "states carrying a typed finite or Lie-group action"
laneCarrierReading sparseTwistLane = "sparse support plus signed orientation/twist payload"

laneResidualReading : CrossPollinationLane → String
laneResidualReading codecLane = "mask, gated sign, and unresolved prediction detail"
laneResidualReading dnaLane = "fine sequence choice beyond the projected admissible state"
laneResidualReading waveLane = "phase/coherence detail omitted by coarse observation"
laneResidualReading lieActionLane = "orbit-local coordinate or representation detail"
laneResidualReading sparseTwistLane = "unresolved filament, circulation, or orientation detail"

laneSymmetryReading : CrossPollinationLane → String
laneSymmetryReading codecLane = "sign involution, spatial transform, or dictionary equivalence"
laneSymmetryReading dnaLane = "complement, reverse-complement, or admissible grammar symmetry"
laneSymmetryReading waveLane = "phase action or reversible evolution on a coherent sector"
laneSymmetryReading lieActionLane = "explicit group action and orbit witness"
laneSymmetryReading sparseTwistLane = "orientation reversal, frame action, or local twist transport"

------------------------------------------------------------------------
-- Typed adapter from any domain lane into the exact core.

record LaneAdapter (lane : CrossPollinationLane) : Set₁ where
  constructor lane-adapter
  field
    tower : MultiscaleCarrier
    codec : ResidualCodec tower
    kernelTower : KernelTower tower
    symmetry : SymmetryAction tower
    carrierReading : String
    carrierReadingIsCanonical : carrierReading ≡ laneCarrierReading lane
    residualReading : String
    residualReadingIsCanonical : residualReading ≡ laneResidualReading lane
    symmetryReading : String
    symmetryReadingIsCanonical : symmetryReading ≡ laneSymmetryReading lane
open LaneAdapter public

------------------------------------------------------------------------
-- Cross-lane transport requires an explicit map and exact compatibility.
-- Sharing vocabulary alone never licenses transport.

record CrossLaneTransport
  {source target : CrossPollinationLane}
  (from : LaneAdapter source)
  (to : LaneAdapter target) : Set₁ where
  field
    mapState : ∀ j → Carrier (tower from) j → Carrier (tower to) j
    project-compatible :
      ∀ {j} (x : Carrier (tower from) (suc j)) →
      mapState j (project (tower from) x) ≡
      project (tower to) (mapState (suc j) x)
    kernel-compatible :
      ∀ j (x : Carrier (tower from) j) →
      mapState j (kernel (kernelTower from) j x) ≡
      kernel (kernelTower to) j (mapState j x)
open CrossLaneTransport public

------------------------------------------------------------------------
-- Authority is intentionally lane-local.

data AuthorityKind : Set where
  exactFormalAuthority : AuthorityKind
  codecBenchmarkAuthority : AuthorityKind
  biochemicalAuthority : AuthorityKind
  wavePhysicsAuthority : AuthorityKind
  geometricGroupAuthority : AuthorityKind
  fluidDynamicsAuthority : AuthorityKind

laneEmpiricalAuthority : CrossPollinationLane → AuthorityKind
laneEmpiricalAuthority codecLane = codecBenchmarkAuthority
laneEmpiricalAuthority dnaLane = biochemicalAuthority
laneEmpiricalAuthority waveLane = wavePhysicsAuthority
laneEmpiricalAuthority lieActionLane = geometricGroupAuthority
laneEmpiricalAuthority sparseTwistLane = fluidDynamicsAuthority

record CrossPollinationBoundary : Set where
  constructor cross-pollination-boundary
  field
    exactCoreShared : Bool
    exactCoreSharedIsTrue : exactCoreShared ≡ true
    laneSemanticsIdentical : Bool
    laneSemanticsIdenticalIsFalse : laneSemanticsIdentical ≡ false
    empiricalAuthorityTransfersAutomatically : Bool
    empiricalAuthorityTransfersAutomaticallyIsFalse :
      empiricalAuthorityTransfersAutomatically ≡ false
    mdlEqualsPhysicalActionAutomatically : Bool
    mdlEqualsPhysicalActionAutomaticallyIsFalse :
      mdlEqualsPhysicalActionAutomatically ≡ false
    waveLiftMakesEveryKernelUnitary : Bool
    waveLiftMakesEveryKernelUnitaryIsFalse :
      waveLiftMakesEveryKernelUnitary ≡ false
    sparseTwistProxyProvesVorticityClosure : Bool
    sparseTwistProxyProvesVorticityClosureIsFalse :
      sparseTwistProxyProvesVorticityClosure ≡ false
open CrossPollinationBoundary public

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  cross-pollination-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

canonicalLanes : List CrossPollinationLane
canonicalLanes =
  codecLane ∷ dnaLane ∷ waveLane ∷ lieActionLane ∷ sparseTwistLane ∷ []
