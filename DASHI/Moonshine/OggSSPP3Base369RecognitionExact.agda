module DASHI.Moonshine.OggSSPP3Base369RecognitionExact where

------------------------------------------------------------------------
-- p=3 OGG/SSP SOURCE GROUPOID -> INDEPENDENT BASE369 TARGET RECOGNITION
--
-- DASHI CONTRIBUTION
--
-- Source presentation:
--   OggSSPSmallCharacteristicResidualGroupoidExact
--   State = KernelTrit
--   C2 acts by KernelTrit sign inversion.
--
-- Target presentation:
--   Base369P3ConstantTernaryActionGroupoidExact
--   State = canonical SSPTrit
--   C2 acts by SSP sign inversion.
--
-- This module proves an actual same-object recognition theorem between the two
-- typed presentations:
--
--   * exact two-sided state rechart;
--   * exact symmetry/action equivariance;
--   * exact orbit correspondence;
--   * pi0 injectivity + surjectivity;
--   * stabilizer preservation + reflection;
--   * exact provenance preservation.
--
-- External monstrous-exponent arithmetic remains attributed upstream.  The
-- recognition theorem itself is DASHI mathematics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Kernel
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Core.ProvenancePreservingRecognitionFunctorExact as Provenance
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Moonshine.Base369P3ConstantTernaryActionGroupoidExact as Target
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Source
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Exact carrier rechart.
------------------------------------------------------------------------

kernelToSSP :
  Kernel.KernelTrit ->
  SSP.SSPTrit
kernelToSSP Kernel.negativeTrit = SSP.sspNegOne
kernelToSSP Kernel.zeroTrit = SSP.sspZero
kernelToSSP Kernel.positiveTrit = SSP.sspPosOne

sspToKernel :
  SSP.SSPTrit ->
  Kernel.KernelTrit
sspToKernel SSP.sspNegOne = Kernel.negativeTrit
sspToKernel SSP.sspZero = Kernel.zeroTrit
sspToKernel SSP.sspPosOne = Kernel.positiveTrit

kernelRoundTrip :
  (state : Kernel.KernelTrit) ->
  sspToKernel (kernelToSSP state) ≡ state
kernelRoundTrip Kernel.negativeTrit = refl
kernelRoundTrip Kernel.zeroTrit = refl
kernelRoundTrip Kernel.positiveTrit = refl

sspRoundTrip :
  (state : SSP.SSPTrit) ->
  kernelToSSP (sspToKernel state) ≡ state
sspRoundTrip SSP.sspNegOne = refl
sspRoundTrip SSP.sspZero = refl
sspRoundTrip SSP.sspPosOne = refl

------------------------------------------------------------------------
-- 2. The rechart intertwines sign inversion.
------------------------------------------------------------------------

kernelToSSPCommutesWithNegation :
  (state : Kernel.KernelTrit) ->
  kernelToSSP (Kernel.negateTrit state)
  ≡ Target.negateSSP (kernelToSSP state)
kernelToSSPCommutesWithNegation Kernel.negativeTrit = refl
kernelToSSPCommutesWithNegation Kernel.zeroTrit = refl
kernelToSSPCommutesWithNegation Kernel.positiveTrit = refl

p3ActionRecognition :
  Recognition.ActionRecognitionFunctor
    Source.constantC2Action
    Target.p3C2Action
p3ActionRecognition =
  Recognition.action-recognition-functor
    kernelToSSP
    (λ g -> g)
    refl
    (λ g h -> refl)
    (λ g -> refl)
    equivariant
  where
    equivariant :
      (g : C2.C2) ->
      (state : Kernel.KernelTrit) ->
      kernelToSSP (Source.actConstantC2 g state)
      ≡ Target.actP3C2 g (kernelToSSP state)
    equivariant C2.identity state = refl
    equivariant C2.flip state =
      kernelToSSPCommutesWithNegation state

------------------------------------------------------------------------
-- 3. Exact orbit correspondence.
------------------------------------------------------------------------

sourceOrbitToTarget :
  Source.ConstantTernaryOrbit ->
  Target.P3Orbit
sourceOrbitToTarget Source.zeroConstantOrbit = Target.zeroOrbit
sourceOrbitToTarget Source.nonzeroConstantOrbit = Target.nonzeroOrbit

targetOrbitToSource :
  Target.P3Orbit ->
  Source.ConstantTernaryOrbit
targetOrbitToSource Target.zeroOrbit = Source.zeroConstantOrbit
targetOrbitToSource Target.nonzeroOrbit = Source.nonzeroConstantOrbit

sourceTargetOrbitRoundTrip :
  (orbit : Source.ConstantTernaryOrbit) ->
  targetOrbitToSource (sourceOrbitToTarget orbit) ≡ orbit
sourceTargetOrbitRoundTrip Source.zeroConstantOrbit = refl
sourceTargetOrbitRoundTrip Source.nonzeroConstantOrbit = refl

targetSourceOrbitRoundTrip :
  (orbit : Target.P3Orbit) ->
  sourceOrbitToTarget (targetOrbitToSource orbit) ≡ orbit
targetSourceOrbitRoundTrip Target.zeroOrbit = refl
targetSourceOrbitRoundTrip Target.nonzeroOrbit = refl

p3OrbitRecognition :
  Recognition.OrbitRecognition
    p3ActionRecognition
    Source.constantTernaryOrbitPresentation
    Target.p3OrbitPresentation
p3OrbitRecognition =
  Recognition.orbit-recognition
    sourceOrbitToTarget
    orbitExact
  where
    orbitExact :
      (state : Kernel.KernelTrit) ->
      Target.orbitOf (kernelToSSP state)
      ≡ sourceOrbitToTarget (Source.constantOrbitOf state)
    orbitExact Kernel.negativeTrit = refl
    orbitExact Kernel.zeroTrit = refl
    orbitExact Kernel.positiveTrit = refl

p3Pi0Embedding :
  Recognition.Pi0Embedding p3OrbitRecognition
p3Pi0Embedding =
  Recognition.pi0-embedding reflect
  where
    reflect :
      {left right : Source.ConstantTernaryOrbit} ->
      sourceOrbitToTarget left ≡ sourceOrbitToTarget right ->
      left ≡ right
    reflect {Source.zeroConstantOrbit} {Source.zeroConstantOrbit} same = refl
    reflect {Source.zeroConstantOrbit} {Source.nonzeroConstantOrbit} ()
    reflect {Source.nonzeroConstantOrbit} {Source.zeroConstantOrbit} ()
    reflect {Source.nonzeroConstantOrbit} {Source.nonzeroConstantOrbit} same = refl

p3Pi0Surjection :
  Recognition.Pi0Surjection p3OrbitRecognition
p3Pi0Surjection =
  Recognition.pi0-surjection
    targetOrbitToSource
    targetSourceOrbitRoundTrip

------------------------------------------------------------------------
-- 4. Stabilizer preservation and reflection.
------------------------------------------------------------------------

p3StabilizerRecognition :
  Recognition.StabilizerRecognition p3OrbitRecognition
p3StabilizerRecognition =
  Recognition.stabilizer-recognition
    representativeCompatibility
    preserves
    reflects
  where
    representativeCompatibility :
      (orbit : Source.ConstantTernaryOrbit) ->
      kernelToSSP
        (Orbit.representative
          Source.constantTernaryOrbitPresentation
          orbit)
      ≡
      Orbit.representative
        Target.p3OrbitPresentation
        (sourceOrbitToTarget orbit)
    representativeCompatibility Source.zeroConstantOrbit = refl
    representativeCompatibility Source.nonzeroConstantOrbit = refl

    preserves :
      (orbit : Source.ConstantTernaryOrbit) ->
      (g : C2.C2) ->
      Action.act Source.constantC2Action g
        (Orbit.representative
          Source.constantTernaryOrbitPresentation orbit)
      ≡
      Orbit.representative
        Source.constantTernaryOrbitPresentation orbit
      ->
      Action.act Target.p3C2Action g
        (Orbit.representative
          Target.p3OrbitPresentation
          (sourceOrbitToTarget orbit))
      ≡
      Orbit.representative
        Target.p3OrbitPresentation
        (sourceOrbitToTarget orbit)
    preserves Source.zeroConstantOrbit C2.identity same = refl
    preserves Source.zeroConstantOrbit C2.flip same = refl
    preserves Source.nonzeroConstantOrbit C2.identity same = refl
    preserves Source.nonzeroConstantOrbit C2.flip ()

    reflects :
      (orbit : Source.ConstantTernaryOrbit) ->
      (g : C2.C2) ->
      Action.act Target.p3C2Action g
        (Orbit.representative
          Target.p3OrbitPresentation
          (sourceOrbitToTarget orbit))
      ≡
      Orbit.representative
        Target.p3OrbitPresentation
        (sourceOrbitToTarget orbit)
      ->
      Action.act Source.constantC2Action g
        (Orbit.representative
          Source.constantTernaryOrbitPresentation orbit)
      ≡
      Orbit.representative
        Source.constantTernaryOrbitPresentation orbit
    reflects Source.zeroConstantOrbit C2.identity same = refl
    reflects Source.zeroConstantOrbit C2.flip same = refl
    reflects Source.nonzeroConstantOrbit C2.identity same = refl
    reflects Source.nonzeroConstantOrbit C2.flip ()

p3FullRecognition :
  Recognition.OrbitStabilizerRecognition
    p3ActionRecognition
    Source.constantTernaryOrbitPresentation
    Target.p3OrbitPresentation
p3FullRecognition =
  Recognition.orbit-stabilizer-recognition
    p3OrbitRecognition
    p3Pi0Embedding
    p3Pi0Surjection
    p3StabilizerRecognition

------------------------------------------------------------------------
-- 5. Exact state provenance preservation.
--
-- Provenance is deliberately finer than orbit class here: the source retains
-- the exact KernelTrit and the target retains the exact SSPTrit.
------------------------------------------------------------------------

SourceProvenance : Set
SourceProvenance = Kernel.KernelTrit

TargetProvenance : Set
TargetProvenance = SSP.SSPTrit

sourceProvenance :
  Kernel.KernelTrit ->
  SourceProvenance
sourceProvenance state = state

targetProvenance :
  SSP.SSPTrit ->
  TargetProvenance
targetProvenance state = state

kernelToSSPInjective :
  {left right : Kernel.KernelTrit} ->
  kernelToSSP left ≡ kernelToSSP right ->
  left ≡ right
kernelToSSPInjective {left} {right} same =
  trans
    (sym (kernelRoundTrip left))
    (trans
      (cong sspToKernel same)
      (kernelRoundTrip right))

p3ProvenanceActionRecognition :
  Provenance.ProvenancePreservingActionRecognition
    Source.constantC2Action
    Target.p3C2Action
    sourceProvenance
    targetProvenance
p3ProvenanceActionRecognition =
  Provenance.provenance-preserving-action-recognition
    p3ActionRecognition
    kernelToSSP
    (λ state -> refl)
    kernelToSSPInjective

p3ProvenanceOrbitRecognition :
  Provenance.ProvenancePreservingOrbitRecognition
    p3ProvenanceActionRecognition
    Source.constantTernaryOrbitPresentation
    Target.p3OrbitPresentation
p3ProvenanceOrbitRecognition =
  Provenance.provenance-preserving-orbit-recognition
    p3OrbitRecognition
    p3Pi0Embedding
    p3Pi0Surjection
    p3StabilizerRecognition

------------------------------------------------------------------------
-- 6. Recognition consequences.
------------------------------------------------------------------------

zeroOrbitRecognisedExactly :
  Recognition.mapOrbit p3OrbitRecognition Source.zeroConstantOrbit
  ≡ Target.zeroOrbit
zeroOrbitRecognisedExactly = refl

nonzeroOrbitRecognisedExactly :
  Recognition.mapOrbit p3OrbitRecognition Source.nonzeroConstantOrbit
  ≡ Target.nonzeroOrbit
nonzeroOrbitRecognisedExactly = refl

zeroFlipStabilizerRecognised :
  Action.act Target.p3C2Action C2.flip
    (Orbit.representative Target.p3OrbitPresentation Target.zeroOrbit)
  ≡
  Orbit.representative Target.p3OrbitPresentation Target.zeroOrbit
zeroFlipStabilizerRecognised = refl

nonzeroFlipNotStabilizer :
  Action.act Target.p3C2Action C2.flip
    (Orbit.representative Target.p3OrbitPresentation Target.nonzeroOrbit)
  ≡
  Orbit.representative Target.p3OrbitPresentation Target.nonzeroOrbit
  ->
  ⊥
nonzeroFlipNotStabilizer =
  Target.nonzeroNotFixedByFlip

recognitionClaimOrigin : Attribution.ClaimOrigin
recognitionClaimOrigin =
  Attribution.repositoryNewExtension

record OggSSPP3Base369RecognitionBoundary : Set where
  constructor ogg-ssp-p3-base369-recognition-boundary
  field
    sourceAndTargetCarriersDefinitionallySame : Bool
    exactTwoSidedRechartProved : Bool
    c2ActionEquivarianceProved : Bool
    pi0BijectionProved : Bool
    stabilizerPreservationReflectionProved : Bool
    exactStateProvenancePreserved : Bool
    arithmeticResidualCountUsedToConstructFunctor : Bool
    sameObjectRecognitionPaidAtP3 : Bool
    duncanSwisherCreditedWithRecognitionTheorem : Bool

canonicalOggSSPP3Base369RecognitionBoundary :
  OggSSPP3Base369RecognitionBoundary
canonicalOggSSPP3Base369RecognitionBoundary =
  ogg-ssp-p3-base369-recognition-boundary
    false true true true true true false true false
