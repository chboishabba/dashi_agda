module DASHI.Physics.Closure.NSTriadKNPressureDNPacketPrincipalTailRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND85 / SELECTED-PACKET PRINCIPAL PRESSURE BLOCK VS CROSS-SHELL TAIL
--
-- The compact-transfer derivative tests DN(u)[P] against the selected hard
-- shell u_K.  Decompose the literal Galerkin velocity exactly as
--
--   u = u_K + u_C,
--
-- where u_C is the Boolean hard-shell complement.  Bilinearity then gives
--
--   DN(u)[P]
--     = B(u_K,P) + B(P,u_K)
--       + B(u_C,P) + B(P,u_C).
--
-- We call the first line the selected-packet principal pressure block and the
-- second line the cross-shell tail.  This matters because the principal block
-- is the place where periodic integration by parts combines Hessian and
-- Poisson source into
--
--   H - (1/2) Delta p I = H^D - (1/3) Q I,
--
-- while every failure of that same-field identity is now explicitly attached
-- to an off-packet velocity leg.  No analytic bound is asserted here; this file
-- establishes the exact source partition consumed by the Bony/first-adjoint
-- tail machinery.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Drift
import DASHI.Physics.Closure.NSTriadKNLiteralAdvectivePressureRHSSplitRound84Exact as AP
import DASHI.Physics.Closure.NSTriadKNNonlinearRelativeGrowthAdvectivePressureSplitRound84Exact as Split

packetComplement :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  (shell : Agda.Builtin.Nat.Nat) → Packet.TotalField model → Packet.TotalField model
packetComplement model shell field mode with LP.shellSelect model shell mode
... | true = C3.complex3Zero (LP.realField model)
... | false = field mode

packetPlusComplementPointwise :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    shell (field : Packet.TotalField model) mode →
  First.fieldAdd
    (Packet.packetField model shell field)
    (packetComplement model shell field)
    mode
  ≡ field mode
packetPlusComplementPointwise model shell field mode
  with LP.shellSelect model shell mode
... | true = Field.complex3AddZeroRight (field mode)
... | false = First.complex3AddZeroLeft (field mode)

------------------------------------------------------------------------
-- Finite bilinearity of the mixed projected nonlinearity.
------------------------------------------------------------------------

sumMixedAddLeft :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left₁ left₂ right : First.VelocityField F)
    (incidences : List Physical.PhysicalTriadIncidence) →
  Audit.sumVectors
    (First.mixedTerms system (First.fieldAdd left₁ left₂) right incidences)
  ≡ C3.complex3Add
      (Audit.sumVectors (First.mixedTerms system left₁ right incidences))
      (Audit.sumVectors (First.mixedTerms system left₂ right incidences))
sumMixedAddLeft {F = F} system left₁ left₂ right [] =
  sym (First.complex3AddZeroLeft (C3.complex3Zero F))
sumMixedAddLeft system left₁ left₂ right (incidence ∷ rest) =
  trans
    (cong₂ C3.complex3Add
      (First.orderedInteractionAddLeft
        (Audit.integerEmbedding system) (Audit.inverseSquare system)
        (Physical.k incidence) (Physical.p incidence) (Physical.q incidence)
        (left₁ (Physical.p incidence))
        (left₂ (Physical.p incidence))
        (right (Physical.q incidence)))
      (sumMixedAddLeft system left₁ left₂ right rest))
    (First.complex3Interchange
      (First.mixedProjectedOrderedTerm system left₁ right incidence)
      (First.mixedProjectedOrderedTerm system left₂ right incidence)
      (Audit.sumVectors (First.mixedTerms system left₁ right rest))
      (Audit.sumVectors (First.mixedTerms system left₂ right rest)))

sumMixedAddRight :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left right₁ right₂ : First.VelocityField F)
    (incidences : List Physical.PhysicalTriadIncidence) →
  Audit.sumVectors
    (First.mixedTerms system left (First.fieldAdd right₁ right₂) incidences)
  ≡ C3.complex3Add
      (Audit.sumVectors (First.mixedTerms system left right₁ incidences))
      (Audit.sumVectors (First.mixedTerms system left right₂ incidences))
sumMixedAddRight {F = F} system left right₁ right₂ [] =
  sym (First.complex3AddZeroLeft (C3.complex3Zero F))
sumMixedAddRight system left right₁ right₂ (incidence ∷ rest) =
  trans
    (cong₂ C3.complex3Add
      (First.orderedInteractionAddRight
        (Audit.integerEmbedding system) (Audit.inverseSquare system)
        (Physical.k incidence) (Physical.p incidence) (Physical.q incidence)
        (left (Physical.p incidence))
        (right₁ (Physical.q incidence))
        (right₂ (Physical.q incidence)))
      (sumMixedAddRight system left right₁ right₂ rest))
    (First.complex3Interchange
      (First.mixedProjectedOrderedTerm system left right₁ incidence)
      (First.mixedProjectedOrderedTerm system left right₂ incidence)
      (Audit.sumVectors (First.mixedTerms system left right₁ rest))
      (Audit.sumVectors (First.mixedTerms system left right₂ rest)))

mixedProjectedNonlinearityAddLeft :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left₁ left₂ right : First.VelocityField F) output →
  First.mixedProjectedNonlinearity system (First.fieldAdd left₁ left₂) right output
  ≡ C3.complex3Add
      (First.mixedProjectedNonlinearity system left₁ right output)
      (First.mixedProjectedNonlinearity system left₂ right output)
mixedProjectedNonlinearityAddLeft system left₁ left₂ right output =
  sumMixedAddLeft system left₁ left₂ right (Audit.concreteTriadsAt system output)

mixedProjectedNonlinearityAddRight :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left right₁ right₂ : First.VelocityField F) output →
  First.mixedProjectedNonlinearity system left (First.fieldAdd right₁ right₂) output
  ≡ C3.complex3Add
      (First.mixedProjectedNonlinearity system left right₁ output)
      (First.mixedProjectedNonlinearity system left right₂ output)
mixedProjectedNonlinearityAddRight system left right₁ right₂ output =
  sumMixedAddRight system left right₁ right₂ (Audit.concreteTriadsAt system output)

------------------------------------------------------------------------
-- Exact pressure DN principal/tail split on a literal compact-transfer datum.
------------------------------------------------------------------------

selectedVelocity :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → Packet.TotalField model
selectedVelocity {model = model} datum =
  Packet.packetField model (Drift.shell datum)
    (Audit.velocity (Drift.finiteSystem datum))

complementVelocity :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → Packet.TotalField model
complementVelocity {model = model} datum =
  packetComplement model (Drift.shell datum)
    (Audit.velocity (Drift.finiteSystem datum))

principalPressureVariation :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → Packet.TotalField model
principalPressureVariation datum output =
  C3.complex3Add
    (First.mixedProjectedNonlinearity
      (Drift.finiteSystem datum) (selectedVelocity datum) (Split.pressureRHS datum) output)
    (First.mixedProjectedNonlinearity
      (Drift.finiteSystem datum) (Split.pressureRHS datum) (selectedVelocity datum) output)

crossShellPressureVariation :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model → Packet.TotalField model
crossShellPressureVariation datum output =
  C3.complex3Add
    (First.mixedProjectedNonlinearity
      (Drift.finiteSystem datum) (complementVelocity datum) (Split.pressureRHS datum) output)
    (First.mixedProjectedNonlinearity
      (Drift.finiteSystem datum) (Split.pressureRHS datum) (complementVelocity datum) output)

pressureVariationSplitsPrincipalCrossShell :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) output →
  First.projectedNonlinearityFirstVariation
    (Drift.finiteSystem datum) (Split.pressureRHS datum) output
  ≡ C3.complex3Add
      (principalPressureVariation datum output)
      (crossShellPressureVariation datum output)
pressureVariationSplitsPrincipalCrossShell {model = model} datum output =
  let
    system = Drift.finiteSystem datum
    u = Audit.velocity system
    uK = selectedVelocity datum
    uC = complementVelocity datum
    P = Split.pressureRHS datum

    uAsSplit : ∀ mode → u mode ≡ First.fieldAdd uK uC mode
    uAsSplit mode = sym
      (packetPlusComplementPointwise model (Drift.shell datum) u mode)

    leftCong =
      Split.mixedProjectedNonlinearityCongLeft
        system u (First.fieldAdd uK uC) P uAsSplit output
    rightCong =
      Split.mixedProjectedNonlinearityCongRight
        system P u (First.fieldAdd uK uC) uAsSplit output
  in
  trans
    (cong₂ C3.complex3Add leftCong rightCong)
    (trans
      (cong₂ C3.complex3Add
        (mixedProjectedNonlinearityAddLeft system uK uC P output)
        (mixedProjectedNonlinearityAddRight system P uK uC output))
      (First.complex3Interchange
        (First.mixedProjectedNonlinearity system uK P output)
        (First.mixedProjectedNonlinearity system uC P output)
        (First.mixedProjectedNonlinearity system P uK output)
        (First.mixedProjectedNonlinearity system P uC output)))

round85PressureDNSplitsSelectedPrincipalAndCrossShellTail : Bool
round85PressureDNSplitsSelectedPrincipalAndCrossShellTail = true

round85PrincipalPressureBlockHasSameSelectedVelocityLegs : Bool
round85PrincipalPressureBlockHasSameSelectedVelocityLegs = true

round85CrossShellPressureTailUniformlyAbsorbed : Bool
round85CrossShellPressureTailUniformlyAbsorbed = false

round85PressureDNSplitsSelectedPrincipalAndCrossShellTailIsTrue :
  round85PressureDNSplitsSelectedPrincipalAndCrossShellTail ≡ true
round85PressureDNSplitsSelectedPrincipalAndCrossShellTailIsTrue = refl
