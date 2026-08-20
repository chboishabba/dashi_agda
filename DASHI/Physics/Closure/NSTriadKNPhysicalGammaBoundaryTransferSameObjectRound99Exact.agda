module DASHI.Physics.Closure.NSTriadKNPhysicalGammaBoundaryTransferSameObjectRound99Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- ROUND99 / PHYSICAL GAMMA <-> BOUNDARY-TRANSFER SAME-OBJECT WELD
--
-- The compact-Gamma datum historically accepted an arbitrary `packetModes`
-- list even though its packet field is selected by the literal hard shell.
-- For the physical same-object theorem we canonicalize ONLY that bookkeeping
-- list to the finite Galerkin cutoff cube.  No velocity, shell, viscosity,
-- Fourier geometry, or nonlinearity is changed.
--
-- On that canonical datum,
--
--   rawTransfer = Re sum_k <u_K(k), N_K(u)(k)>
--
-- is literally the real part of the selected projected Galerkin pairing in
-- the repaired generic Round98 factor-six theorem.  Therefore
--
--   Re(three-leg boundary sum) = 6 * rawTransfer
--
-- in the additive generic-carrier sense.  This is the division-free physical
-- normalization weld needed by the compact-Gamma/off-packet sign audit.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Drift
import DASHI.Physics.Closure.NSTriadKNGenericPacketBoundaryFluxFactorSixRound98Exact as FactorSix

canonicalCompactGammaDatum :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model →
  Drift.LiteralPhysicalCompactTransferDatum model
canonicalCompactGammaDatum datum = record
  { physicalSystem = Drift.physicalSystem datum
  ; shell = Drift.shell datum
  ; packetModes = Cube.cutoffModes (Audit.cutoff (Drift.finiteSystem datum))
  }

canonicalDatumPreservesFiniteSystem :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Drift.finiteSystem (canonicalCompactGammaDatum datum) ≡ Drift.finiteSystem datum
canonicalDatumPreservesFiniteSystem datum = refl

canonicalDatumPreservesShell :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Drift.shell (canonicalCompactGammaDatum datum) ≡ Drift.shell datum
canonicalDatumPreservesShell datum = refl

selectedModePairingReal :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E}
    (system : Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I)
    (shell : Agda.Builtin.Nat.Nat)
    (output : Z3.FourierMode) →
  C3.real
    (C3.hermitianPairing3
      (Packet.packetField model shell (Audit.velocity system) output)
      (Packet.packetField model shell (Audit.projectedNonlinearity system) output))
  ≡ C3.real
    (FactorSix.selectedProjectedOutputPower system
      (LP.shellSelect model shell) output)
selectedModePairingReal model system shell output
  with LP.shellSelect model shell output
... | true = refl
... | false =
  cong C3.real
    (FactorSix.hermitianZeroRight
      (C3.complex3Zero (LP.realField model)))

canonicalPacketPairingRealEqualsSelectedProjectedReal :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E}
    (system : Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I)
    (shell : Agda.Builtin.Nat.Nat)
    (modes : List Z3.FourierMode) →
  C3.real
    (Packet.finiteHermitianPairing modes
      (Packet.packetField model shell (Audit.velocity system))
      (Packet.packetField model shell (Audit.projectedNonlinearity system)))
  ≡ C3.real
    (FactorSix.sumSelectedProjectedPowers system
      (LP.shellSelect model shell) modes)
canonicalPacketPairingRealEqualsSelectedProjectedReal model system shell [] = refl
canonicalPacketPairingRealEqualsSelectedProjectedReal model system shell (output ∷ rest) =
  cong₂ (C3.add (LP.realField model))
    (selectedModePairingReal model system shell output)
    (canonicalPacketPairingRealEqualsSelectedProjectedReal model system shell rest)

rawTransferCanonicalEqualsLiteralSelectedProjectedReal :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Drift.rawTransfer (canonicalCompactGammaDatum datum)
  ≡ C3.real
      (FactorSix.literalSelectedProjectedPairing
        (Drift.finiteSystem datum)
        (LP.shellSelect model (Drift.shell datum)))
rawTransferCanonicalEqualsLiteralSelectedProjectedReal {model = model} datum =
  canonicalPacketPairingRealEqualsSelectedProjectedReal
    model (Drift.finiteSystem datum) (Drift.shell datum)
    (Cube.cutoffModes (Audit.cutoff (Drift.finiteSystem datum)))

sixReal : ∀ {r} (F : C3.RealField r) → C3.Carrier F → C3.Carrier F
sixReal F value =
  C3.add F
    (C3.add F (C3.add F value value) (C3.add F value value))
    (C3.add F value value)

realSixFold : ∀ {r} {F : C3.RealField r} (value : C3.Complex F) →
  C3.real (FactorSix.sixFold value) ≡ sixReal F (C3.real value)
realSixFold value = refl

PhysicalGammaBoundaryTransferSameObjectIdentification :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Reality.RealityCondition (Audit.velocity (Drift.finiteSystem datum)) →
  Reality.DivergenceFreeCondition
    (Audit.integerEmbedding (Drift.finiteSystem datum))
    (Audit.velocity (Drift.finiteSystem datum)) →
  C3.real
    (FactorSix.sumBoundaryTransfer
      (Audit.integerEmbedding (Drift.finiteSystem datum))
      (Audit.inverseSquare (Drift.finiteSystem datum))
      (LP.shellSelect model (Drift.shell datum))
      (Audit.velocity (Drift.finiteSystem datum))
      (Physical.physicalTriadEnumeration
        (Audit.cutoff (Drift.finiteSystem datum))))
  ≡ sixReal (LP.realField model)
      (Drift.rawTransfer (canonicalCompactGammaDatum datum))
PhysicalGammaBoundaryTransferSameObjectIdentification {model = model}
    datum reality divergenceFree =
  let
    system = Drift.finiteSystem datum
    selected = LP.shellSelect model (Drift.shell datum)
    factorSix =
      FactorSix.PhysicalPacketBoundaryFluxFactorSixIdentification
        system selected reality divergenceFree
  in
  trans
    (cong C3.real factorSix)
    (trans
      (realSixFold (FactorSix.literalSelectedProjectedPairing system selected))
      (cong (sixReal (LP.realField model))
        (sym (rawTransferCanonicalEqualsLiteralSelectedProjectedReal datum))))

round99PhysicalGammaBoundaryTransferSameObjectWeldClosed : Bool
round99PhysicalGammaBoundaryTransferSameObjectWeldClosed = true

round99CompactGammaPacketModesCanonicalizedWithoutChangingSystem : Bool
round99CompactGammaPacketModesCanonicalizedWithoutChangingSystem = true

round99GenericBoundaryFluxEqualsSixRawTransfer : Bool
round99GenericBoundaryFluxEqualsSixRawTransfer = true
