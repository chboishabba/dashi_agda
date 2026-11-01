module DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND82 / SAME-OBJECT PHYSICAL COMPACT-TRANSFER DRIFT
--
-- This module repairs the last provenance gap in the generic Round82 transfer
-- derivative surface.  The selected tangent is not an arbitrary perturbation:
-- it is exactly the repository's literal finite-mode Navier--Stokes RHS
--
--   F_N(u)(k) = -nu |k|^2 u(k) + N_k(u),
--
-- from `LiteralViscousQuadraticCoefficientRound30Exact`.
--
-- Likewise the dissipation denominator is NOT defined through the abstract
-- `PeriodicHardShellFourierPDE.derivativeMultiplier`.  It is built directly
-- from the SAME `normSquared` entering the literal viscous coefficient:
--
--   D_K = Re sum_{k in packet K} <u_k, |k|^2 u_k>.
--
-- Its first variation along the literal RHS is
--
--   Ddot_K = Re sum [<F_k,|k|^2 u_k> + <u_k,|k|^2 F_k>].
--
-- The transfer side is also same-object:
--
--   q_K    = Re <u_K,N_K(u)>,
--   qdot_K = Re (<F_K,N_K(u)> + <u_K,DN_K(u)[F]>).
--
-- With Q=s_K q, V=(2nu)D, the exact relative-growth numerator factors as
--
--   Qdot V - Q Vdot = s_K (2nu) (qdot D - q Ddot).
--
-- Thus the remaining C4 theorem is now literally an inequality on the actual
-- selected finite-Galerkin Navier--Stokes tangent; no arbitrary tangent,
-- derivative-multiplier, quotient, or viscosity-identification field remains.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Literal
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralCompactTransferDriftDataRound82Exact as Scale

record LiteralPhysicalCompactTransferDatum
    {r : Level}
    (model : LP.PeriodicHardShellFourierPDE {r}) : Set (lsuc r) where
  field
    physicalSystem :
      Literal.PhysicalFiniteComplex3GalerkinSystem (LP.realField model)
    shell : Nat
    packetModes : List Z3.FourierMode

open LiteralPhysicalCompactTransferDatum public

finiteSystem :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : LiteralPhysicalCompactTransferDatum model) →
  Audit.FiniteComplex3GalerkinSystem
    (LP.realField model)
    (Literal.physicalEmbedding (physicalSystem datum))
    (Literal.physicalInverseSquare (physicalSystem datum))
finiteSystem datum = Literal.finiteSystem (physicalSystem datum)

literalRHS :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model →
  Packet.TotalField model
literalRHS datum =
  Literal.literalViscousQuadraticCoefficient (physicalSystem datum)

packetVelocity :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model →
  Packet.TotalField model
packetVelocity {model = model} datum =
  Packet.packetField model (shell datum) (Audit.velocity (finiteSystem datum))

packetRHS :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model →
  Packet.TotalField model
packetRHS {model = model} datum =
  Packet.packetField model (shell datum) (literalRHS datum)

modeDissipationWeight :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model →
  Z3.FourierMode → C3.Complex (LP.realField model)
modeDissipationWeight {model = model} datum mode =
  C3.realEmbed (LP.realField model)
    (C3.normSquared
      (Literal.physicalInverseSquare (physicalSystem datum)) mode)

weightedPacketField :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  (datum : LiteralPhysicalCompactTransferDatum model) →
  Packet.TotalField model → Packet.TotalField model
weightedPacketField {model = model} datum field mode =
  C3.complex3Scale
    (modeDissipationWeight datum mode)
    (Packet.packetField model (shell datum) field mode)

weightedPacketFieldAdd :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : LiteralPhysicalCompactTransferDatum model)
    (left right : Packet.TotalField model)
    (mode : Z3.FourierMode) →
  weightedPacketField datum (First.fieldAdd left right) mode
  ≡ First.fieldAdd
      (weightedPacketField datum left)
      (weightedPacketField datum right)
      mode
weightedPacketFieldAdd {model = model} datum left right mode =
  trans
    (cong
      (C3.complex3Scale (modeDissipationWeight datum mode))
      (Packet.packetFieldAdd model (shell datum) left right mode))
    (First.complex3ScaleVectorAdd
      (modeDissipationWeight datum mode)
      (Packet.packetField model (shell datum) left mode)
      (Packet.packetField model (shell datum) right mode))

rawTransfer :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawTransfer {model = model} datum =
  C3.real
    (Packet.packetTransferPairing
      model (finiteSystem datum) (shell datum) (packetModes datum))

rawTransferTangent :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawTransferTangent {model = model} datum =
  C3.real
    (Packet.packetTransferPairingFirstVariation
      model (finiteSystem datum) (shell datum) (packetModes datum)
      (literalRHS datum))

rawDissipation :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawDissipation datum =
  C3.real
    (Packet.finiteHermitianPairing
      (packetModes datum)
      (packetVelocity datum)
      (weightedPacketField datum (Audit.velocity (finiteSystem datum))))

rawDissipationTangent :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawDissipationTangent datum =
  C3.real
    (C3.complexAdd
      (Packet.finiteHermitianPairing
        (packetModes datum)
        (packetRHS datum)
        (weightedPacketField datum (Audit.velocity (finiteSystem datum))))
      (Packet.finiteHermitianPairing
        (packetModes datum)
        (packetVelocity datum)
        (weightedPacketField datum (literalRHS datum))))

rawRelativeGrowthCore :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
rawRelativeGrowthCore {model = model} datum =
  Scale.realSubtract (LP.realField model)
    (C3.multiply (LP.realField model)
      (rawTransferTangent datum) (rawDissipation datum))
    (C3.multiply (LP.realField model)
      (rawTransfer datum) (rawDissipationTangent datum))

transferScale :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
transferScale {model = model} datum =
  Scale.shellTransferScale (LP.realField model) (shell datum)

viscousFactor :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
viscousFactor {model = model} datum =
  C3.multiply (LP.realField model)
    (Scale.twoCarrier (LP.realField model))
    (Literal.viscosity (physicalSystem datum))

physicalTransfer :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
physicalTransfer {model = model} datum =
  C3.multiply (LP.realField model) (transferScale datum) (rawTransfer datum)

physicalTransferTangent :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
physicalTransferTangent {model = model} datum =
  C3.multiply (LP.realField model)
    (transferScale datum) (rawTransferTangent datum)

physicalViscousDenominator :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
physicalViscousDenominator {model = model} datum =
  C3.multiply (LP.realField model)
    (viscousFactor datum) (rawDissipation datum)

physicalViscousDenominatorTangent :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
physicalViscousDenominatorTangent {model = model} datum =
  C3.multiply (LP.realField model)
    (viscousFactor datum) (rawDissipationTangent datum)

physicalRelativeGrowthNumerator :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  LiteralPhysicalCompactTransferDatum model → C3.Carrier (LP.realField model)
physicalRelativeGrowthNumerator {model = model} datum =
  Scale.realSubtract (LP.realField model)
    (C3.multiply (LP.realField model)
      (physicalTransferTangent datum)
      (physicalViscousDenominator datum))
    (C3.multiply (LP.realField model)
      (physicalTransfer datum)
      (physicalViscousDenominatorTangent datum))

physicalRelativeGrowthFactorsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : LiteralPhysicalCompactTransferDatum model) →
  physicalRelativeGrowthNumerator datum
  ≡
  C3.multiply (LP.realField model)
    (C3.multiply (LP.realField model)
      (transferScale datum) (viscousFactor datum))
    (rawRelativeGrowthCore datum)
physicalRelativeGrowthFactorsExactly {model = model} datum =
  P.R.solve 6
    (λ s c q qdot d ddot →
      ((s P.R.⊗ qdot) P.R.⊗ (c P.R.⊗ d))
        P.R.⊕ P.R.⊝ ((s P.R.⊗ q) P.R.⊗ (c P.R.⊗ ddot))
      P.R.⊜
      (s P.R.⊗ c) P.R.⊗
        ((qdot P.R.⊗ d) P.R.⊕ P.R.⊝ (q P.R.⊗ ddot)))
    refl
    (transferScale datum)
    (viscousFactor datum)
    (rawTransfer datum)
    (rawTransferTangent datum)
    (rawDissipation datum)
    (rawDissipationTangent datum)
  where
  module P = Field.Polynomial (LP.realField model)

round82SelectedTangentIsLiteralViscousPlusQuadraticRHS : Bool
round82SelectedTangentIsLiteralViscousPlusQuadraticRHS = true

round82SelectedDissipationUsesSameNormSquaredAsViscousRHS : Bool
round82SelectedDissipationUsesSameNormSquaredAsViscousRHS = true

round82SameObjectPhysicalCompactTransferDriftConstructed : Bool
round82SameObjectPhysicalCompactTransferDriftConstructed = true

round82PhysicalRelativeGrowthInequalityConstructed : Bool
round82PhysicalRelativeGrowthInequalityConstructed = false

round82SameObjectPhysicalCompactTransferDriftConstructedIsTrue :
  round82SameObjectPhysicalCompactTransferDriftConstructed ≡ true
round82SameObjectPhysicalCompactTransferDriftConstructedIsTrue = refl
