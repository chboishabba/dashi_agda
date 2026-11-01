module DASHI.Physics.Closure.NSTriadKNPressureRelativeGrowthThreeWayRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- Authors: Jinhee Jeong; Fazle Hussain.
-- Title: "On the identification of a vortex".
-- DOI: 10.1017/S0022112095000462.
--
-- Author: Marco Cannone.
-- Title: "Harmonic Analysis Tools for Solving the Incompressible
-- Navier-Stokes Equations".
-- DOI: 10.1016/S1874-5792(05)80006-0.
--
-- ROUND85 / THREE-WAY PRESSURE SHARE OF THE COMPACT-TRANSFER DRIFT
--
-- The previous Round85 modules prove, on the literal pressure tangent,
--
--   Ddot_P = 0,
--   qdot_P = Re <u_K , DN(u)[P]_K>,
--
-- and the exact output-fibre decomposition
--
--   DN(u)[P]
--     = HessianFold
--       + RelocatedPacketDerivativeFold
--       + PoissonSourceFold.
--
-- This file pushes that identity through the ACTUAL hard-shell selector and
-- finite Hermitian pairing.  Therefore
--
--   qdot_P = qdot_H + qdot_R + qdot_Q,
--
-- and, because Ddot_P=0,
--
--   R_P = D qdot_H + D qdot_R + D qdot_Q.
--
-- The three remaining quantitative pressure tasks are now explicit:
--
--   * Hessian share: consume Round78--81 pressure geometry;
--   * relocated share: localization/commutator absorption;
--   * Poisson share: consume -Delta p = -2Q with the exact Round85
--     normalization, without pretending global mean-Q zero is shell-local.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Drift
import DASHI.Physics.Closure.NSTriadKNLiteralRHSRelativeGrowthSplitRound83Exact as R83
import DASHI.Physics.Closure.NSTriadKNNonlinearRelativeGrowthAdvectivePressureSplitRound84Exact as Split
import DASHI.Physics.Closure.NSTriadKNPressureDirectionHermitianOrthogonalityRound84Exact as Orth
import DASHI.Physics.Closure.NSTriadKNPressureTransferFirstVariationReductionRound85Exact as TransferReduction
import DASHI.Physics.Closure.NSTriadKNDNPressureHessianTransportSplitRound85Exact as HessianSplit
import DASHI.Physics.Closure.NSTriadKNPressureTransportPoissonSplitRound85Exact as TransportSplit

hessianField :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → Packet.TotalField model
hessianField datum = HessianSplit.pressureHessianFold (Drift.finiteSystem datum)

relocatedField :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → Packet.TotalField model
relocatedField datum = TransportSplit.pressureRelocatedFold (Drift.finiteSystem datum)

poissonField :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → Packet.TotalField model
poissonField datum = TransportSplit.pressurePoissonFold (Drift.finiteSystem datum)

packetDNPressureThreeWayPointwise :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) mode →
  Packet.packetNonlinearityFirstVariation model
    (Drift.finiteSystem datum) (Drift.shell datum) (Split.pressureRHS datum) mode
  ≡ First.fieldAdd
      (Packet.packetField model (Drift.shell datum) (hessianField datum))
      (First.fieldAdd
        (Packet.packetField model (Drift.shell datum) (relocatedField datum))
        (Packet.packetField model (Drift.shell datum) (poissonField datum)))
      mode
packetDNPressureThreeWayPointwise {model = model} datum mode
  with LP.shellSelect model (Drift.shell datum) mode
... | true =
  TransportSplit.projectedNonlinearityPressureVariationThreeWay
    (Drift.finiteSystem datum) mode
... | false =
  sym
    (trans
      (First.complex3AddZeroLeft
        (C3.complex3Add
          (C3.complex3Zero (LP.realField model))
          (C3.complex3Zero (LP.realField model))))
      (First.complex3AddZeroLeft (C3.complex3Zero (LP.realField model))))

hessianPressureTransferShare :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Complex (LP.realField model)
hessianPressureTransferShare {model = model} datum =
  Packet.finiteHermitianPairing
    (Drift.packetModes datum)
    (Packet.packetBaseVelocity model
      (Drift.finiteSystem datum) (Drift.shell datum))
    (Packet.packetField model (Drift.shell datum) (hessianField datum))

relocatedPressureTransferShare :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Complex (LP.realField model)
relocatedPressureTransferShare {model = model} datum =
  Packet.finiteHermitianPairing
    (Drift.packetModes datum)
    (Packet.packetBaseVelocity model
      (Drift.finiteSystem datum) (Drift.shell datum))
    (Packet.packetField model (Drift.shell datum) (relocatedField datum))

poissonPressureTransferShare :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Complex (LP.realField model)
poissonPressureTransferShare {model = model} datum =
  Packet.finiteHermitianPairing
    (Drift.packetModes datum)
    (Packet.packetBaseVelocity model
      (Drift.finiteSystem datum) (Drift.shell datum))
    (Packet.packetField model (Drift.shell datum) (poissonField datum))

pressureTransferSecondSlotSplitsThreeWay :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  TransferReduction.pressureTransferSecondSlot datum
  ≡ C3.complexAdd
      (hessianPressureTransferShare datum)
      (C3.complexAdd
        (relocatedPressureTransferShare datum)
        (poissonPressureTransferShare datum))
pressureTransferSecondSlotSplitsThreeWay {model = model} datum =
  trans
    (R83.finiteHermitianPairingCongRight
      (Drift.packetModes datum)
      (Packet.packetBaseVelocity model
        (Drift.finiteSystem datum) (Drift.shell datum))
      (Packet.packetNonlinearityFirstVariation model
        (Drift.finiteSystem datum) (Drift.shell datum) (Split.pressureRHS datum))
      (First.fieldAdd
        (Packet.packetField model (Drift.shell datum) (hessianField datum))
        (First.fieldAdd
          (Packet.packetField model (Drift.shell datum) (relocatedField datum))
          (Packet.packetField model (Drift.shell datum) (poissonField datum))))
      (packetDNPressureThreeWayPointwise datum))
    (trans
      (Packet.finiteHermitianPairingAddRight
        (Drift.packetModes datum)
        (Packet.packetBaseVelocity model
          (Drift.finiteSystem datum) (Drift.shell datum))
        (Packet.packetField model (Drift.shell datum) (hessianField datum))
        (First.fieldAdd
          (Packet.packetField model (Drift.shell datum) (relocatedField datum))
          (Packet.packetField model (Drift.shell datum) (poissonField datum))))
      (cong
        (C3.complexAdd (hessianPressureTransferShare datum))
        (Packet.finiteHermitianPairingAddRight
          (Drift.packetModes datum)
          (Packet.packetBaseVelocity model
            (Drift.finiteSystem datum) (Drift.shell datum))
          (Packet.packetField model (Drift.shell datum) (relocatedField datum))
          (Packet.packetField model (Drift.shell datum) (poissonField datum)))))

rawHessianPressureTransferShare :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawHessianPressureTransferShare datum = C3.real (hessianPressureTransferShare datum)

rawRelocatedPressureTransferShare :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawRelocatedPressureTransferShare datum = C3.real (relocatedPressureTransferShare datum)

rawPoissonPressureTransferShare :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawPoissonPressureTransferShare datum = C3.real (poissonPressureTransferShare datum)

rawPressureTransferTangentSplitsThreeWay :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : Orth.RetainedPressurePacketDatum datum) →
  Split.rawTransferTangentPressure datum
  ≡ C3.add (LP.realField model)
      (rawHessianPressureTransferShare datum)
      (C3.add (LP.realField model)
        (rawRelocatedPressureTransferShare datum)
        (rawPoissonPressureTransferShare datum))
rawPressureTransferTangentSplitsThreeWay datum retained =
  trans
    (TransferReduction.rawPressureTransferTangentReducesToDN datum retained)
    (trans
      (cong C3.real (pressureTransferSecondSlotSplitsThreeWay datum))
      (trans
        (R83.realOfComplexAdd
          (hessianPressureTransferShare datum)
          (C3.complexAdd
            (relocatedPressureTransferShare datum)
            (poissonPressureTransferShare datum)))
        (cong
          (C3.add (LP.realField _) (rawHessianPressureTransferShare datum))
          (R83.realOfComplexAdd
            (relocatedPressureTransferShare datum)
            (poissonPressureTransferShare datum))))))

hessianPressureRelativeGrowthShare :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
hessianPressureRelativeGrowthShare {model = model} datum =
  C3.multiply (LP.realField model)
    (rawHessianPressureTransferShare datum) (Drift.rawDissipation datum)

relocatedPressureRelativeGrowthShare :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
relocatedPressureRelativeGrowthShare {model = model} datum =
  C3.multiply (LP.realField model)
    (rawRelocatedPressureTransferShare datum) (Drift.rawDissipation datum)

poissonPressureRelativeGrowthShare :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
poissonPressureRelativeGrowthShare {model = model} datum =
  C3.multiply (LP.realField model)
    (rawPoissonPressureTransferShare datum) (Drift.rawDissipation datum)

pressureRelativeGrowthSplitsThreeWay :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (retained : Orth.RetainedPressurePacketDatum datum) →
  Split.pressureRelativeGrowthCore datum
  ≡ C3.add (LP.realField model)
      (hessianPressureRelativeGrowthShare datum)
      (C3.add (LP.realField model)
        (relocatedPressureRelativeGrowthShare datum)
        (poissonPressureRelativeGrowthShare datum))
pressureRelativeGrowthSplitsThreeWay {model = model} datum retained =
  trans
    (Orth.pressureRelativeGrowthReducesToTransferTimesDissipation datum retained)
    (trans
      (cong
        (λ qdot → C3.multiply (LP.realField model) qdot (Drift.rawDissipation datum))
        (rawPressureTransferTangentSplitsThreeWay datum retained))
      (P.R.solve 4
        (λ h r q d →
          ((h P.R.⊕ (r P.R.⊕ q)) P.R.⊗ d)
          P.R.⊜
          ((h P.R.⊗ d)
            P.R.⊕ ((r P.R.⊗ d) P.R.⊕ (q P.R.⊗ d))))
        refl
        (rawHessianPressureTransferShare datum)
        (rawRelocatedPressureTransferShare datum)
        (rawPoissonPressureTransferShare datum)
        (Drift.rawDissipation datum)))
  where module P = Field.Polynomial (LP.realField model)

round85PressureTransferSecondSlotSplitsThreeWay : Bool
round85PressureTransferSecondSlotSplitsThreeWay = true

round85PressureRelativeGrowthSplitsHessianRelocatedPoisson : Bool
round85PressureRelativeGrowthSplitsHessianRelocatedPoisson = true

round85HessianPressureShareEstimated : Bool
round85HessianPressureShareEstimated = false

round85RelocatedPressureShareAbsorbed : Bool
round85RelocatedPressureShareAbsorbed = false

round85PoissonQPressureShareEstimated : Bool
round85PoissonQPressureShareEstimated = false

round85PressureRelativeGrowthSplitsHessianRelocatedPoissonIsTrue :
  round85PressureRelativeGrowthSplitsHessianRelocatedPoisson ≡ true
round85PressureRelativeGrowthSplitsHessianRelocatedPoissonIsTrue = refl
