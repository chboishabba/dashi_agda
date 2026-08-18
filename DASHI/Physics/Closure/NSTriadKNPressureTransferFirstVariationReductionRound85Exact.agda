module DASHI.Physics.Closure.NSTriadKNPressureTransferFirstVariationReductionRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND85 / PRESSURE SHARE OF THE TRANSFER FIRST VARIATION
--
-- Round84 proved that the literal pressure tangent P is longitudinal on each
-- retained output mode.  The literal Galerkin nonlinearity N(u) is Leray
-- projected and therefore transverse on the same nonzero mode.  Consequently
-- the first product-rule slot in the pressure transfer variation vanishes:
--
--   <P_K , N_K(u)> = 0.
--
-- Hence the entire pressure share of qdot is exactly the second slot
--
--   qdot_P = Re <u_K , DN(u)[P]_K>.
--
-- Together with the retained-packet theorem Ddot_P=0 this sharpens the C4
-- pressure relative-growth scalar to
--
--   R_P = D * Re <u_K , DN(u)[P]_K>.
--
-- This is the high-alpha form for the next physical-space calculation: opening
-- DN(u)[P] gives the pressure-gradient advection term and the derivative of the
-- pressure gradient, the latter being the actual pressure Hessian.  No sign or
-- estimate is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Literal
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact as NTrans
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Drift
import DASHI.Physics.Closure.NSTriadKNNonlinearRelativeGrowthAdvectivePressureSplitRound84Exact as Split
import DASHI.Physics.Closure.NSTriadKNPressureDirectionHermitianOrthogonalityRound84Exact as Orth

------------------------------------------------------------------------
-- Pointwise pressure/base-nonlinearity orthogonality on a retained packet.
------------------------------------------------------------------------

pressurePacketAgainstBaseNonlinearityZero :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : Orth.RetainedPressurePacketDatum datum)
    mode → mode Cube.∈ Drift.packetModes datum →
  C3.hermitianPairing3
    (Packet.packetField model (Drift.shell datum) (Split.pressureRHS datum) mode)
    (Packet.packetBaseNonlinearity model
      (Drift.finiteSystem datum) (Drift.shell datum) mode)
  ≡ C3.complexZero (LP.realField model)
pressurePacketAgainstBaseNonlinearityZero {model = model}
    datum retained mode member
  with LP.shellSelect model (Drift.shell datum) mode
... | true =
  let
    retainedMember = Orth.packetModesAreRetained retained mode member
    nonzero = Literal.retainedModeNonzero
      (Drift.physicalSystem datum) mode retainedMember
    transverseN = NTrans.projectedNonlinearityTransverseExact
      (Drift.finiteSystem datum) mode nonzero
  in
  Orth.pressureRHSOrthogonalLeftToTransverse
    (Drift.finiteSystem datum) mode
    (Audit.projectedNonlinearity (Drift.finiteSystem datum) mode)
    transverseN
... | false =
  Orth.hermitianZeroLeft (C3.complex3Zero (LP.realField model))

pressureTransferFirstSlotZero :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : Orth.RetainedPressurePacketDatum datum) →
  Packet.finiteHermitianPairing
    (Drift.packetModes datum)
    (Packet.packetPerturbation model (Drift.shell datum) (Split.pressureRHS datum))
    (Packet.packetBaseNonlinearity model
      (Drift.finiteSystem datum) (Drift.shell datum))
  ≡ C3.complexZero (LP.realField model)
pressureTransferFirstSlotZero {model = model} datum retained =
  go (Drift.packetModes datum)
    (λ mode member → pressurePacketAgainstBaseNonlinearityZero
      datum retained mode member)
  where
  F = LP.realField model

  go :
    (modes : List Z3.FourierMode) →
    (∀ mode → mode Cube.∈ modes →
      C3.hermitianPairing3
        (Packet.packetPerturbation model (Drift.shell datum)
          (Split.pressureRHS datum) mode)
        (Packet.packetBaseNonlinearity model
          (Drift.finiteSystem datum) (Drift.shell datum) mode)
      ≡ C3.complexZero F) →
    Packet.finiteHermitianPairing modes
      (Packet.packetPerturbation model (Drift.shell datum) (Split.pressureRHS datum))
      (Packet.packetBaseNonlinearity model
        (Drift.finiteSystem datum) (Drift.shell datum))
    ≡ C3.complexZero F
  go [] pointwise = refl
  go (mode ∷ modes) pointwise =
    trans
      (cong₂ C3.complexAdd
        (pointwise mode (Cube.here refl))
        (go modes
          (λ selected selectedMember →
            pointwise selected (Cube.there selectedMember))))
      (Field.complexAddZeroLeft (C3.complexZero F))

------------------------------------------------------------------------
-- qdot_P is only the DN(u)[P] slot.
------------------------------------------------------------------------

pressureTransferSecondSlot :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model →
  C3.Complex (LP.realField model)
pressureTransferSecondSlot {model = model} datum =
  Packet.finiteHermitianPairing
    (Drift.packetModes datum)
    (Packet.packetBaseVelocity model
      (Drift.finiteSystem datum) (Drift.shell datum))
    (Packet.packetNonlinearityFirstVariation model
      (Drift.finiteSystem datum) (Drift.shell datum) (Split.pressureRHS datum))

complexPressureTransferTangentReducesToDN :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : Orth.RetainedPressurePacketDatum datum) →
  Split.complexTransferTangentPressure datum
  ≡ pressureTransferSecondSlot datum
complexPressureTransferTangentReducesToDN {model = model} datum retained =
  trans
    (cong₂ C3.complexAdd
      (pressureTransferFirstSlotZero datum retained)
      refl)
    (Field.complexAddZeroLeft (pressureTransferSecondSlot datum))

rawPressureTransferTangentReducesToDN :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : Orth.RetainedPressurePacketDatum datum) →
  Split.rawTransferTangentPressure datum
  ≡ C3.real (pressureTransferSecondSlot datum)
rawPressureTransferTangentReducesToDN datum retained =
  cong C3.real (complexPressureTransferTangentReducesToDN datum retained)

pressureRelativeGrowthIsDissipationTimesDNPressureWork :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : Orth.RetainedPressurePacketDatum datum) →
  Split.pressureRelativeGrowthCore datum
  ≡ C3.multiply (LP.realField model)
      (C3.real (pressureTransferSecondSlot datum))
      (Drift.rawDissipation datum)
pressureRelativeGrowthIsDissipationTimesDNPressureWork {model = model}
    datum retained =
  trans
    (Orth.pressureRelativeGrowthReducesToTransferTimesDissipation datum retained)
    (cong
      (λ qdot → C3.multiply (LP.realField model) qdot (Drift.rawDissipation datum))
      (rawPressureTransferTangentReducesToDN datum retained))

round85PressureTransferFirstSlotZero : Bool
round85PressureTransferFirstSlotZero = true

round85PressureTransferTangentReducesToDNPressureSlot : Bool
round85PressureTransferTangentReducesToDNPressureSlot = true

round85PressureRelativeGrowthIsDissipationTimesDNPressureWork : Bool
round85PressureRelativeGrowthIsDissipationTimesDNPressureWork = true

round85PressureTransferTangentReducesToDNPressureSlotIsTrue :
  round85PressureTransferTangentReducesToDNPressureSlot ≡ true
round85PressureTransferTangentReducesToDNPressureSlotIsTrue = refl
