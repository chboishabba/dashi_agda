{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Device.SpatialContinuityRecombinationExact where

------------------------------------------------------------------------
-- SCIENTIFIC SOURCES
--
-- Siegfried Selberherr,
-- "Analysis and Simulation of Semiconductor Devices",
-- Springer Vienna (1984), DOI 10.1007/978-3-7091-8752-4.
--
-- D. L. Scharfetter and H. K. Gummel,
-- "Large-signal analysis of a silicon Read diode oscillator",
-- IEEE Transactions on Electron Devices 16 (1969), 64-77,
-- DOI 10.1109/T-ED.1969.16566.
--
-- The cited literature owns semiconductor transport/continuity numerical
-- context.  The finite Nat fixture and exact residual decomposition below are
-- DASHI constructions, not numerical values attributed to those sources.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Physics.Semiconductor.Device.ComputedFiniteDeviceCellExact as Cell
import DASHI.Biology.Physical.FiniteReactionDiffusionConservationExact as RD
import DASHI.Physics.Laws.ContinuumMaterialLaws as Continuum
import DASHI.Biology.Morphogenesis.ReactionDiffusionHodgeBridge as Hodge

------------------------------------------------------------------------
-- Minimal spatial semiconductor mesh.
--
-- Three nodes induce one interior control volume and two oriented faces:
--
--   left node ---- left face | interior | right face ---- right node
--
-- The current values are normalized codes.  Electron and hole equations are
-- kept separate because their conventional-current continuity signs differ.
------------------------------------------------------------------------

data MeshNode : Set where
  leftNode interiorNode rightNode : MeshNode

data MeshFace : Set where
  leftFace rightFace : MeshFace

record InteriorCarrierFluxState : Set where
  constructor interiorCarrierFluxState
  field
    electronLeftFace  : Nat
    electronRightFace : Nat
    holeLeftFace      : Nat
    holeRightFace     : Nat
    generationCode    : Nat
    recombinationCode : Nat

open InteriorCarrierFluxState public

------------------------------------------------------------------------
-- Same-object spatial state generated from the already-computed device cell.
--
-- Existing cell electron/hole currents become the left-face currents.  The
-- right-face values are fixed finite boundary data for this admitted fixture.
-- Generation and recombination are both one, so their net contribution is zero
-- here while remaining explicit coordinates of the balance law.
------------------------------------------------------------------------

spatialFluxState : Cell.SourceCharge → InteriorCarrierFluxState
spatialFluxState Cell.q1 = interiorCarrierFluxState 14 10 1 3 1 1
spatialFluxState Cell.q3 = interiorCarrierFluxState 12 10 2 3 1 1
spatialFluxState Cell.q5 = interiorCarrierFluxState 10 10 3 3 1 1

electronLeftMatchesComputedCurrent :
  (q : Cell.SourceCharge) →
  electronLeftFace (spatialFluxState q) ≡ Cell.electronCurrent q
electronLeftMatchesComputedCurrent Cell.q1 = refl
electronLeftMatchesComputedCurrent Cell.q3 = refl
electronLeftMatchesComputedCurrent Cell.q5 = refl

holeLeftMatchesComputedCurrent :
  (q : Cell.SourceCharge) →
  holeLeftFace (spatialFluxState q) ≡ Cell.holeCurrent q
holeLeftMatchesComputedCurrent Cell.q1 = refl
holeLeftMatchesComputedCurrent Cell.q3 = refl
holeLeftMatchesComputedCurrent Cell.q5 = refl

------------------------------------------------------------------------
-- Discrete steady-state continuity residual.
--
-- With normalized charge factor one and left-to-right orientation, the target
-- balance surfaces are written subtraction-free as:
--
-- electron: Jn_right + R = Jn_left + G
-- hole:     Jp_left  + G = Jp_right + R
--
-- Residual coordinates pay the one-sided mismatch of these exact balances on
-- the admitted fixture.
------------------------------------------------------------------------

record SpatialContinuityResidual : Set where
  constructor spatialContinuityResidual
  field
    electronDivergenceResidual : Nat
    holeDivergenceResidual     : Nat

open SpatialContinuityResidual public

spatialResidual : Cell.SourceCharge → SpatialContinuityResidual
spatialResidual Cell.q1 = spatialContinuityResidual 4 2
spatialResidual Cell.q3 = spatialContinuityResidual 2 1
spatialResidual Cell.q5 = spatialContinuityResidual 0 0

electronSpatialAccounting :
  (q : Cell.SourceCharge) →
  electronRightFace (spatialFluxState q)
    + recombinationCode (spatialFluxState q)
    + electronDivergenceResidual (spatialResidual q)
  ≡ electronLeftFace (spatialFluxState q)
    + generationCode (spatialFluxState q)
electronSpatialAccounting Cell.q1 = refl
electronSpatialAccounting Cell.q3 = refl
electronSpatialAccounting Cell.q5 = refl

holeSpatialAccounting :
  (q : Cell.SourceCharge) →
  holeLeftFace (spatialFluxState q)
    + generationCode (spatialFluxState q)
    + holeDivergenceResidual (spatialResidual q)
  ≡ holeRightFace (spatialFluxState q)
    + recombinationCode (spatialFluxState q)
holeSpatialAccounting Cell.q1 = refl
holeSpatialAccounting Cell.q3 = refl
holeSpatialAccounting Cell.q5 = refl

spatialResidualScore : Cell.SourceCharge → Nat
spatialResidualScore q =
  electronDivergenceResidual (spatialResidual q)
  + holeDivergenceResidual (spatialResidual q)

q1SpatialResidualScore : spatialResidualScore Cell.q1 ≡ 6
q1SpatialResidualScore = refl

q3SpatialResidualScore : spatialResidualScore Cell.q3 ≡ 3
q3SpatialResidualScore = refl

q5SpatialResidualScore : spatialResidualScore Cell.q5 ≡ 0
q5SpatialResidualScore = refl

------------------------------------------------------------------------
-- Coordinate-wise closure.
------------------------------------------------------------------------

data SpatialContinuityClosed : Cell.SourceCharge → Set where
  q5SpatialContinuityClosed : SpatialContinuityClosed Cell.q5

closedElectronSpatialResidualZero :
  (q : Cell.SourceCharge) →
  SpatialContinuityClosed q →
  electronDivergenceResidual (spatialResidual q) ≡ 0
closedElectronSpatialResidualZero Cell.q5 q5SpatialContinuityClosed = refl

closedHoleSpatialResidualZero :
  (q : Cell.SourceCharge) →
  SpatialContinuityClosed q →
  holeDivergenceResidual (spatialResidual q) ≡ 0
closedHoleSpatialResidualZero Cell.q5 q5SpatialContinuityClosed = refl

closedSpatialScoreZero :
  (q : Cell.SourceCharge) →
  SpatialContinuityClosed q →
  spatialResidualScore q ≡ 0
closedSpatialScoreZero Cell.q5 q5SpatialContinuityClosed = refl

------------------------------------------------------------------------
-- Cross-pollination with existing conservation / continuum / Hodge owners.
--
-- RD owns a finite transport-conservation theorem.  We re-export that theorem
-- here as the generic conservation donor.  It does NOT identify biological
-- concentration quanta with semiconductor carriers.
------------------------------------------------------------------------

reactionDiffusionConservationDonor :
  (x : RD.TwoCompartment) →
  RD.totalMaterial (RD.diffuseLeftToRight x) ≡ RD.totalMaterial x
reactionDiffusionConservationDonor = RD.diffusionConservesTotal

record ExistingSpatialPhysicsSurface : Set₁ where
  field
    continuumReactionDiffusionLawAvailable : Set₁
    hodgeIdentificationAvailable : Set₁
    finiteConservationCarrierAvailable : Set

existingSpatialPhysicsSurface : ExistingSpatialPhysicsSurface
existingSpatialPhysicsSurface = record
  { continuumReactionDiffusionLawAvailable = Continuum.ReactionDiffusionLaw
  ; hodgeIdentificationAvailable =
      Hodge.ReactionDiffusionHodgeIdentification
  ; finiteConservationCarrierAvailable = RD.TwoCompartment
  }

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

data PhysicalSpatialContinuityLeaf : Set where
  SignedCurrentUnits : PhysicalSpatialContinuityLeaf
  PhysicalCellVolume : PhysicalSpatialContinuityLeaf
  PhysicalFaceArea : PhysicalSpatialContinuityLeaf
  PhysicalMeshSpacing : PhysicalSpatialContinuityLeaf
  ChargeFactor : PhysicalSpatialContinuityLeaf
  GenerationModel : PhysicalSpatialContinuityLeaf
  RecombinationModel : PhysicalSpatialContinuityLeaf
  ScharfetterGummelFaceFlux : PhysicalSpatialContinuityLeaf
  TimeDerivativeStorage : PhysicalSpatialContinuityLeaf
  MultiCellAssembly : PhysicalSpatialContinuityLeaf
  PhysicalBoundaryConditions : PhysicalSpatialContinuityLeaf

-- Firewalls:
-- finite face-current codes != SI current density.
-- G=R=1 fixture != physical recombination kinetics.
-- one interior control volume != a production transistor mesh.
-- reaction-diffusion conservation architecture != semiconductor constitutive law.
-- Hodge coercivity availability != physical semiconductor convergence proof.
