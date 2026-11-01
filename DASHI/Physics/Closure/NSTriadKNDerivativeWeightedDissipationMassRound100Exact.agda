module DASHI.Physics.Closure.NSTriadKNDerivativeWeightedDissipationMassRound100Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- ROUND100 / DISSIPATION-MASS SAME-OBJECT WELD
--
-- Round89 moved the dangerous p.q geometry inside a tensor with one Fourier
-- derivative on each high input.  The two L2 masses required by the closed
-- finite HH->low theorem must therefore be the SAME derivative mass as the
-- compact-Gamma denominator, not a newly supplied norm.
--
-- On every packet mode k this file proves algebraically over the generic
-- repository RealField
--
--   Re <u_K(k), |k|^2 u_K(k)>
--      = |k|^2 ||u_K(k)||_2^2.
--
-- Finite summation over the canonical packet list then identifies the literal
-- `rawDissipation` exactly with the derivative-weighted packet mass.  No
-- positivity, square root, Parseval constant, or replacement norm is added.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3EuclideanSelfPairing as Self
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as Euclidean
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Drift

realOfRealScalarProduct :
  ∀ {r} {F : C3.RealField r}
    (weight : C3.Carrier F) (value : C3.Complex F) →
  C3.real (C3.complexMultiply (C3.realEmbed F weight) value)
  ≡ C3.multiply F weight (C3.real value)
realOfRealScalarProduct {F = F} weight (C3.complex vr vi) =
  P.R.solve 3
    (λ w vr vi →
      ((w P.R.⊗ vr) P.R.⊕ P.R.⊝ (P.R.K (C3.zero F) P.R.⊗ vi))
      P.R.⊜ (w P.R.⊗ vr))
    refl weight vr vi
  where module P = Field.Polynomial F

modeDerivativeMass :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Z3.FourierMode → C3.Carrier (LP.realField model)
modeDerivativeMass {model = model} datum mode =
  C3.multiply (LP.realField model)
    (C3.normSquared
      (Audit.inverseSquare (Drift.finiteSystem datum)) mode)
    (Euclidean.complex3NormSquared
      (Drift.packetVelocity datum mode))

modeLiteralDissipationPairing :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Z3.FourierMode → C3.Carrier (LP.realField model)
modeLiteralDissipationPairing datum mode =
  C3.real
    (C3.hermitianPairing3
      (Drift.packetVelocity datum mode)
      (Drift.weightedPacketField datum
        (Audit.velocity (Drift.finiteSystem datum)) mode))

modeLiteralDissipationIsDerivativeMass :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (mode : Z3.FourierMode) →
  modeLiteralDissipationPairing datum mode ≡ modeDerivativeMass datum mode
modeLiteralDissipationIsDerivativeMass {model = model} datum mode =
  let
    F = LP.realField model
    uK = Drift.packetVelocity datum mode
    weight = C3.normSquared (Audit.inverseSquare (Drift.finiteSystem datum)) mode
    scaled = Scaling.hermitianPairingScaleRight
      (C3.realEmbed F weight) uK uK
  in
  trans
    (cong C3.real scaled)
    (trans
      (realOfRealScalarProduct weight (C3.hermitianPairing3 uK uK))
      (cong (C3.multiply F weight)
        (Self.complex3SelfPairingRealPartIsNormSquared uK)))

sumDerivativeMass :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model →
  List Z3.FourierMode → C3.Carrier (LP.realField model)
sumDerivativeMass {model = model} datum [] = C3.zero (LP.realField model)
sumDerivativeMass {model = model} datum (mode ∷ rest) =
  C3.add (LP.realField model)
    (modeDerivativeMass datum mode)
    (sumDerivativeMass datum rest)

realFiniteDissipationPairingIsDerivativeMass :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (modes : List Z3.FourierMode) →
  C3.real
    (Packet.finiteHermitianPairing modes
      (Drift.packetVelocity datum)
      (Drift.weightedPacketField datum
        (Audit.velocity (Drift.finiteSystem datum))))
  ≡ sumDerivativeMass datum modes
realFiniteDissipationPairingIsDerivativeMass {model = model} datum [] = refl
realFiniteDissipationPairingIsDerivativeMass {model = model} datum (mode ∷ rest) =
  cong₂ (C3.add (LP.realField model))
    (modeLiteralDissipationIsDerivativeMass datum mode)
    (realFiniteDissipationPairingIsDerivativeMass datum rest)

rawDissipationIsDerivativeWeightedPacketMass :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Drift.rawDissipation datum
  ≡ sumDerivativeMass datum (Drift.packetModes datum)
rawDissipationIsDerivativeWeightedPacketMass datum =
  realFiniteDissipationPairingIsDerivativeMass datum (Drift.packetModes datum)

round100DissipationMassesWeldedToDerivativeTensorInputs : Bool
round100DissipationMassesWeldedToDerivativeTensorInputs = true

round100NoIndependentHHInputMassReceiptRequired : Bool
round100NoIndependentHHInputMassReceiptRequired = true

round100DissipationMassesWeldedToDerivativeTensorInputsIsTrue :
  round100DissipationMassesWeldedToDerivativeTensorInputs ≡ true
round100DissipationMassesWeldedToDerivativeTensorInputsIsTrue = refl
