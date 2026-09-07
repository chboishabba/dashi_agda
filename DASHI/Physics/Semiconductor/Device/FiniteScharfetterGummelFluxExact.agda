{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.FiniteScharfetterGummelFluxExact where

------------------------------------------------------------------------
-- SCIENTIFIC SOURCE
--
-- D. L. Scharfetter and H. K. Gummel,
-- "Large-signal analysis of a silicon Read diode oscillator",
-- IEEE Transactions on Electron Devices 16 (1969), 64-77.
-- DOI: 10.1109/T-ED.1969.16566.
--
-- SOURCE / DASHI BOUNDARY
--
-- Scharfetter and Gummel own the semiconductor exponential-fitting context.
-- The finite Nat-valued Bernoulli calibration, nodal profiles, and exact
-- executable fixture below are DASHI constructions.  In particular, the
-- weights 2 and 1 below are NOT attributed to the paper and are NOT asserted
-- to equal the physical Bernoulli function B(psi)=psi/(exp(psi)-1).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_∸_)

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell

------------------------------------------------------------------------
-- Four nodes / three faces for the existing two-control-volume fixture.
------------------------------------------------------------------------

data SGNode : Set where
  node0 node1 node2 node3 : SGNode

data SGFace : Set where
  face01 face12 face23 : SGFace

leftNode : SGFace → SGNode
leftNode face01 = node0
leftNode face12 = node1
leftNode face23 = node2

rightNode : SGFace → SGNode
rightNode face01 = node1
rightNode face12 = node2
rightNode face23 = node3

nodeOffset : SGNode → Nat
nodeOffset node0 = 0
nodeOffset node1 = 1
nodeOffset node2 = 2
nodeOffset node3 = 3

-- The potential profile is downstream of the already-computed device centre
-- potential.  Every admitted face therefore has one finite potential step.
nodePotential : Cell.SourceCharge → SGNode → Nat
nodePotential q node = Cell.centrePotential q + nodeOffset node

q1PotentialProfile :
  nodePotential Cell.q1 node0 ≡ 3
  × nodePotential Cell.q1 node1 ≡ 4
  × nodePotential Cell.q1 node2 ≡ 5
  × nodePotential Cell.q1 node3 ≡ 6
q1PotentialProfile = refl , refl , refl , refl

------------------------------------------------------------------------
-- Finite Bernoulli calibration.
--
-- This is a deliberately small exact surrogate for the two oriented weights
-- consumed by an exponential-fitting face balance.  Physical promotion still
-- requires a real exponential/Bernoulli implementation and unit calibration.
------------------------------------------------------------------------

data PotentialDropClass : Set where
  unitForwardDrop : PotentialDropClass

forwardBernoulliWeight : PotentialDropClass → Nat
forwardBernoulliWeight unitForwardDrop = 2

backwardBernoulliWeight : PotentialDropClass → Nat
backwardBernoulliWeight unitForwardDrop = 1

faceDropClass :
  (q : Cell.SourceCharge) →
  (face : SGFace) →
  PotentialDropClass
faceDropClass q face = unitForwardDrop

------------------------------------------------------------------------
-- Nodal carrier profiles.
--
-- node0 is tied to the already-computed carrier state; downstream nodal values
-- are finite calibration data chosen to expose exact flux production across all
-- three faces.  They are not physical carrier densities.
------------------------------------------------------------------------

electronPopulationAt : Cell.SourceCharge → SGNode → Nat
electronPopulationAt Cell.q1 node0 = 20
electronPopulationAt Cell.q1 node1 = 26
electronPopulationAt Cell.q1 node2 = 40
electronPopulationAt Cell.q1 node3 = 70
electronPopulationAt Cell.q3 node0 = 19
electronPopulationAt Cell.q3 node1 = 26
electronPopulationAt Cell.q3 node2 = 41
electronPopulationAt Cell.q3 node3 = 72
electronPopulationAt Cell.q5 node0 = 18
electronPopulationAt Cell.q5 node1 = 26
electronPopulationAt Cell.q5 node2 = 42
electronPopulationAt Cell.q5 node3 = 74

holePopulationAt : Cell.SourceCharge → SGNode → Nat
holePopulationAt Cell.q1 node0 = 3
holePopulationAt Cell.q1 node1 = 5
holePopulationAt Cell.q1 node2 = 8
holePopulationAt Cell.q1 node3 = 13
holePopulationAt Cell.q3 node0 = 4
holePopulationAt Cell.q3 node1 = 6
holePopulationAt Cell.q3 node2 = 10
holePopulationAt Cell.q3 node3 = 17
holePopulationAt Cell.q5 node0 = 5
holePopulationAt Cell.q5 node1 = 7
holePopulationAt Cell.q5 node2 = 11
holePopulationAt Cell.q5 node3 = 19

-- Left boundary populations are explicit functions of the already-computed
-- one-cell populations, so the spatial carrier is not completely detached from
-- the previous same-object state.
electronNode0MatchesComputedPopulation :
  (q : Cell.SourceCharge) →
  electronPopulationAt q node0 ≡ Cell.electronPopulation q + 13
electronNode0MatchesComputedPopulation Cell.q1 = refl
electronNode0MatchesComputedPopulation Cell.q3 = refl
electronNode0MatchesComputedPopulation Cell.q5 = refl

holeNode0MatchesComputedPopulation :
  (q : Cell.SourceCharge) →
  holePopulationAt q node0 ≡ Cell.holePopulation q + 2
holeNode0MatchesComputedPopulation Cell.q1 = refl
holeNode0MatchesComputedPopulation Cell.q3 = refl
holeNode0MatchesComputedPopulation Cell.q5 = refl

------------------------------------------------------------------------
-- Oriented finite SG-style face producer.
--
-- For the admitted orientation the forward weighted term exceeds the backward
-- weighted term, so Nat monus is exact on this fixture:
--
--   J_face = u_L * B_forward - u_R * B_backward.
--
-- This is computationally downstream of nodal populations and the finite
-- Bernoulli calibration; there is no separately supplied face-current table.
------------------------------------------------------------------------

weightedForward : Nat → Nat
weightedForward population =
  population * forwardBernoulliWeight unitForwardDrop

weightedBackward : Nat → Nat
weightedBackward population =
  population * backwardBernoulliWeight unitForwardDrop

electronFaceFlux : Cell.SourceCharge → SGFace → Nat
electronFaceFlux q face =
  weightedForward (electronPopulationAt q (leftNode face))
  ∸ weightedBackward (electronPopulationAt q (rightNode face))

holeFaceFlux : Cell.SourceCharge → SGFace → Nat
holeFaceFlux q face =
  weightedForward (holePopulationAt q (leftNode face))
  ∸ weightedBackward (holePopulationAt q (rightNode face))

------------------------------------------------------------------------
-- Exact executable outputs.
------------------------------------------------------------------------

q1ElectronFace01 : electronFaceFlux Cell.q1 face01 ≡ 14
q1ElectronFace01 = refl
q1ElectronFace12 : electronFaceFlux Cell.q1 face12 ≡ 12
q1ElectronFace12 = refl
q1ElectronFace23 : electronFaceFlux Cell.q1 face23 ≡ 10
q1ElectronFace23 = refl

q3ElectronFace01 : electronFaceFlux Cell.q3 face01 ≡ 12
q3ElectronFace01 = refl
q3ElectronFace12 : electronFaceFlux Cell.q3 face12 ≡ 11
q3ElectronFace12 = refl
q3ElectronFace23 : electronFaceFlux Cell.q3 face23 ≡ 10
q3ElectronFace23 = refl

q5ElectronFace01 : electronFaceFlux Cell.q5 face01 ≡ 10
q5ElectronFace01 = refl
q5ElectronFace12 : electronFaceFlux Cell.q5 face12 ≡ 10
q5ElectronFace12 = refl
q5ElectronFace23 : electronFaceFlux Cell.q5 face23 ≡ 10
q5ElectronFace23 = refl

q1HoleFace01 : holeFaceFlux Cell.q1 face01 ≡ 1
q1HoleFace01 = refl
q1HoleFace12 : holeFaceFlux Cell.q1 face12 ≡ 2
q1HoleFace12 = refl
q1HoleFace23 : holeFaceFlux Cell.q1 face23 ≡ 3
q1HoleFace23 = refl

q3HoleFace01 : holeFaceFlux Cell.q3 face01 ≡ 2
q3HoleFace01 = refl
q3HoleFace12 : holeFaceFlux Cell.q3 face12 ≡ 2
q3HoleFace12 = refl
q3HoleFace23 : holeFaceFlux Cell.q3 face23 ≡ 3
q3HoleFace23 = refl

q5HoleFace01 : holeFaceFlux Cell.q5 face01 ≡ 3
q5HoleFace01 = refl
q5HoleFace12 : holeFaceFlux Cell.q5 face12 ≡ 3
q5HoleFace12 = refl
q5HoleFace23 : holeFaceFlux Cell.q5 face23 ≡ 3
q5HoleFace23 = refl

-- The left boundary face recovers the earlier computed transport current as a
-- theorem rather than taking that current as an input to this face producer.
electronLeftFaceRecoversComputedCurrent :
  (q : Cell.SourceCharge) →
  electronFaceFlux q face01 ≡ Cell.electronCurrent q
electronLeftFaceRecoversComputedCurrent Cell.q1 = refl
electronLeftFaceRecoversComputedCurrent Cell.q3 = refl
electronLeftFaceRecoversComputedCurrent Cell.q5 = refl

holeLeftFaceRecoversComputedCurrent :
  (q : Cell.SourceCharge) →
  holeFaceFlux q face01 ≡ Cell.holeCurrent q
holeLeftFaceRecoversComputedCurrent Cell.q1 = refl
holeLeftFaceRecoversComputedCurrent Cell.q3 = refl
holeLeftFaceRecoversComputedCurrent Cell.q5 = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data PhysicalSGLeaf : Set where
  SignedFluxCarrier : PhysicalSGLeaf
  PhysicalBernoulliFunction : PhysicalSGLeaf
  PhysicalExponential : PhysicalSGLeaf
  ThermalVoltageScaling : PhysicalSGLeaf
  MobilityDiffusivityPrefactor : PhysicalSGLeaf
  FaceAreaMetric : PhysicalSGLeaf
  MeshSpacingMetric : PhysicalSGLeaf
  PhysicalCarrierDensity : PhysicalSGLeaf
  NonuniformPotentialDrop : PhysicalSGLeaf
  PositivityOrientationProof : PhysicalSGLeaf
  PhysicalScharfetterGummelFlux : PhysicalSGLeaf

-- Firewalls:
-- finite weights (2,1) != physical Bernoulli-function evaluation.
-- Nat monus is valid only on the admitted positive orientation; it is not a
-- signed-current implementation.
-- finite nodal population tables != physical carrier-statistics solution.
-- exact face fluxes on this tiny mesh != production Scharfetter-Gummel transport.
