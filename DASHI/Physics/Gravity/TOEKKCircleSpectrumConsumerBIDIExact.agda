module DASHI.Physics.Gravity.TOEKKCircleSpectrumConsumerBIDIExact where

------------------------------------------------------------------------
-- TOE HYPERFABRIC x COMPACT KK S1 / CASIMIR CONSUMERS
--
-- EXACT FINITE non-descent: counting 27 sites cannot determine which
-- lattice operator is meant, and a finite Fourier character aliases
-- continuum KK mode 0 and mode 27. The analytic sine-error and
-- Wilson-link lattice calculation lives in the same-PR Python test.
--
-- REUSE: canonical DASHI FormalClaimTransport/ConsumerDescent.
-- PRIOR ART: standard cycle Fourier theory; Arkani-Hamed,
-- Cohen, Georgi (2001) PRL 86, 4757, DOI 10.1103/PhysRevLett.86.4757.
-- The PR #1249 P3^3 vs C3^3 theorem is a SIBLING DONOR, not a
-- typed same-branch import or a claimed local proof.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair

data TwentySevenSiteOperator : Set where
  pathCube27 periodicTorus27 periodicCircle27 : TwentySevenSiteOperator

siteCount : TwentySevenSiteOperator → Nat
siteCount pathCube27 = 27
siteCount periodicTorus27 = 27
siteCount periodicCircle27 = 27

data SelectedLaplacian : Set where
  pathProductLaplacian : SelectedLaplacian
  torusProductLaplacian : SelectedLaplacian
  oneDimensionalCycleLaplacian : SelectedLaplacian

selectedOperator : TwentySevenSiteOperator → SelectedLaplacian
selectedOperator pathCube27 = pathProductLaplacian
selectedOperator periodicTorus27 = torusProductLaplacian
selectedOperator periodicCircle27 = oneDimensionalCycleLaplacian

pathNotCycle :
  pathProductLaplacian ≡ oneDimensionalCycleLaplacian → ⊥
pathNotCycle ()

cardinalityDoesNotRecoverLaplacian :
  Transport.ClaimNonTransportWitness siteCount selectedOperator
cardinalityDoesNotRecoverLaplacian =
  Descent.consumerNonDescentWitness
    pathCube27 periodicCircle27 refl pathNotCycle

noPhysicsFromTwentySevenAlone :
  Transport.ClaimTransport siteCount selectedOperator → ⊥
noPhysicsFromTwentySevenAlone =
  Transport.claimNonTransportWitnessBlocksTransport
    cardinalityDoesNotRecoverLaplacian

-- A finite C27 character aliases periodic momentum labels 0 and 27.
-- At unit radius the SMOOTH S1 masses squared are 0 and 27^2=729.
-- The actual character exp(2*pi*i*n*j/27) is verified by the
-- accompanying executable; the finite Agda observer is its quotient.
data ContinuumCircleMode : Set where
  smoothMode0 smoothMode27 : ContinuumCircleMode

sampledC27FourierCharacter : ContinuumCircleMode → Bool
sampledC27FourierCharacter smoothMode0 = true
sampledC27FourierCharacter smoothMode27 = true

smoothKKMassSquaredAtUnitRadius : ContinuumCircleMode → Nat
smoothKKMassSquaredAtUnitRadius smoothMode0 = 0
smoothKKMassSquaredAtUnitRadius smoothMode27 = 729

zeroNot729 : 0 ≡ 729 → ⊥
zeroNot729 ()

finiteC27CannotDetermineFullKKMassTower :
  Transport.ClaimNonTransportWitness
    sampledC27FourierCharacter
    smoothKKMassSquaredAtUnitRadius
finiteC27CannotDetermineFullKKMassTower =
  Descent.consumerNonDescentWitness
    smoothMode0 smoothMode27 refl zeroNot729

noFullKKMassClaimFromFiniteFourier :
  Transport.ClaimTransport
    sampledC27FourierCharacter
    smoothKKMassSquaredAtUnitRadius → ⊥
noFullKKMassClaimFromFiniteFourier =
  Transport.claimNonTransportWitnessBlocksTransport
    finiteC27CannotDetermineFullKKMassTower

modeRepairMustSeparateAlias :
  (refine : ContinuumCircleMode → Bool) →
  Repair.RefinementRepairs
    sampledC27FourierCharacter refine
    smoothKKMassSquaredAtUnitRadius →
  refine smoothMode0 ≡ refine smoothMode27 → ⊥
modeRepairMustSeparateAlias refine adequate same =
  Repair.refinementRepairSeparatesWitness
    finiteC27CannotDetermineFullKKMassTower adequate same

-- Failure for an UNBOUNDED continuum consumer cannot invalidate
-- the correctly represented, declared finite Fourier consumer.
finiteFourierCanAnswerItself :
  Transport.ClaimTransport
    sampledC27FourierCharacter sampledC27FourierCharacter
finiteFourierCanAnswerItself =
  Transport.identityClaimTransport sampledC27FourierCharacter
