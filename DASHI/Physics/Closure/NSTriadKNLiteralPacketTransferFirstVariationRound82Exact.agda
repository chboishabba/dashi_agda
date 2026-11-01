module DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact where

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
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- ROUND82 / LITERAL PACKET TRANSFER FIRST VARIATION
--
-- The compact-transfer executable lane uses
--
--   Q_K = 2^(K+1) Re <u_K , N_K(u)>,
--   D_K = <grad u_K , grad u_K>,
--
-- and differentiates them along a finite Galerkin tangent v.  Round82 already
-- proved the exact literal nonlinearity polarization
--
--   DN(u)[v] = B(u,v) + B(v,u).
--
-- This module now proves the corresponding finite-packet product-rule algebra
-- on the exact Fourier carrier.  It uses the same Boolean hard shell selection
-- as `PeriodicHardShellFourierPDE`, represented on the total Galerkin field by
-- zero outside the selected shell.
--
-- The unscaled complex transfer first variation is exactly
--
--   <v_K,N_K(u)> + <u_K,DN_K(u)[v]>.
--
-- The derivative-weighted quadratic first variation is exactly
--
--   <grad v_K,grad u_K> + <grad u_K,grad v_K>.
--
-- The physical real-part, dyadic factor 2^(K+1), viscosity factor, and the
-- final inequality on Qdot V - Q Vdot remain separate source-facing steps.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First

TotalField :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) → Set r
TotalField model = Z3.FourierMode → C3.Complex3 (LP.realField model)

packetField :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  Nat → TotalField model → TotalField model
packetField model shell field mode with LP.shellSelect model shell mode
... | true = field mode
... | false = C3.complex3Zero (LP.realField model)

packetFieldAdd :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (shell : Nat)
    (left right : TotalField model)
    (mode : Z3.FourierMode) →
  packetField model shell (First.fieldAdd left right) mode
  ≡ First.fieldAdd
      (packetField model shell left)
      (packetField model shell right)
      mode
packetFieldAdd model shell left right mode
  with LP.shellSelect model shell mode
... | true = refl
... | false =
  sym (First.complex3AddZeroLeft (C3.complex3Zero (LP.realField model)))

complexInterchange :
  ∀ {r} {F : C3.RealField r}
    (a b c d : C3.Complex F) →
  C3.complexAdd (C3.complexAdd a b) (C3.complexAdd c d)
  ≡ C3.complexAdd (C3.complexAdd a c) (C3.complexAdd b d)
complexInterchange a b c d =
  trans
    (Field.complexAddAssociative a b (C3.complexAdd c d))
    (trans
      (cong (C3.complexAdd a)
        (sym (Field.complexAddAssociative b c d)))
      (trans
        (cong (C3.complexAdd a)
          (cong (λ middle → C3.complexAdd middle d)
            (Field.complexAddCommutative b c)))
        (trans
          (cong (C3.complexAdd a)
            (Field.complexAddAssociative c b d))
          (sym (Field.complexAddAssociative a c (C3.complexAdd b d))))))

finiteHermitianPairing :
  ∀ {r} {F : C3.RealField r} →
  List Z3.FourierMode →
  (Z3.FourierMode → C3.Complex3 F) →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
finiteHermitianPairing {F = F} [] left right = C3.complexZero F
finiteHermitianPairing (mode ∷ modes) left right =
  C3.complexAdd
    (C3.hermitianPairing3 (left mode) (right mode))
    (finiteHermitianPairing modes left right)

finiteHermitianPairingAddLeft :
  ∀ {r} {F : C3.RealField r}
    (modes : List Z3.FourierMode)
    (left₁ left₂ right : Z3.FourierMode → C3.Complex3 F) →
  finiteHermitianPairing modes (First.fieldAdd left₁ left₂) right
  ≡ C3.complexAdd
      (finiteHermitianPairing modes left₁ right)
      (finiteHermitianPairing modes left₂ right)
finiteHermitianPairingAddLeft {F = F} [] left₁ left₂ right =
  sym (Field.complexAddZeroLeft (C3.complexZero F))
finiteHermitianPairingAddLeft (mode ∷ modes) left₁ left₂ right =
  let
    a = C3.hermitianPairing3 (left₁ mode) (right mode)
    b = C3.hermitianPairing3 (left₂ mode) (right mode)
    tail₁ = finiteHermitianPairing modes left₁ right
    tail₂ = finiteHermitianPairing modes left₂ right
  in
  trans
    (cong₂ C3.complexAdd
      (Additive.hermitianPairingAddLeft
        (left₁ mode) (left₂ mode) (right mode))
      (finiteHermitianPairingAddLeft modes left₁ left₂ right))
    (complexInterchange a b tail₁ tail₂)

finiteHermitianPairingAddRight :
  ∀ {r} {F : C3.RealField r}
    (modes : List Z3.FourierMode)
    (left right₁ right₂ : Z3.FourierMode → C3.Complex3 F) →
  finiteHermitianPairing modes left (First.fieldAdd right₁ right₂)
  ≡ C3.complexAdd
      (finiteHermitianPairing modes left right₁)
      (finiteHermitianPairing modes left right₂)
finiteHermitianPairingAddRight {F = F} [] left right₁ right₂ =
  sym (Field.complexAddZeroLeft (C3.complexZero F))
finiteHermitianPairingAddRight (mode ∷ modes) left right₁ right₂ =
  let
    a = C3.hermitianPairing3 (left mode) (right₁ mode)
    b = C3.hermitianPairing3 (left mode) (right₂ mode)
    tail₁ = finiteHermitianPairing modes left right₁
    tail₂ = finiteHermitianPairing modes left right₂
  in
  trans
    (cong₂ C3.complexAdd
      (Additive.hermitianPairingAddRight
        (left mode) (right₁ mode) (right₂ mode))
      (finiteHermitianPairingAddRight modes left right₁ right₂))
    (complexInterchange a b tail₁ tail₂)

finiteHermitianPairingAddThreeRight :
  ∀ {r} {F : C3.RealField r}
    (modes : List Z3.FourierMode)
    (left first second third : Z3.FourierMode → C3.Complex3 F) →
  finiteHermitianPairing modes left
    (First.fieldAdd (First.fieldAdd first second) third)
  ≡ C3.complexAdd
      (C3.complexAdd
        (finiteHermitianPairing modes left first)
        (finiteHermitianPairing modes left second))
      (finiteHermitianPairing modes left third)
finiteHermitianPairingAddThreeRight modes left first second third =
  trans
    (finiteHermitianPairingAddRight
      modes left (First.fieldAdd first second) third)
    (cong
      (λ pair →
        C3.complexAdd pair (finiteHermitianPairing modes left third))
      (finiteHermitianPairingAddRight modes left first second))

packetBaseVelocity :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E} →
  Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I →
  Nat → TotalField model
packetBaseVelocity model system shell =
  packetField model shell (Audit.velocity system)

packetPerturbation :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  Nat → TotalField model → TotalField model
packetPerturbation = packetField

packetBaseNonlinearity :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E} →
  Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I →
  Nat → TotalField model
packetBaseNonlinearity model system shell =
  packetField model shell (Audit.projectedNonlinearity system)

packetNonlinearityFirstVariation :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E} →
  Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I →
  Nat → TotalField model → TotalField model
packetNonlinearityFirstVariation model system shell perturbation =
  packetField model shell
    (First.projectedNonlinearityFirstVariation system perturbation)

packetNonlinearityQuadraticRemainder :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E} →
  Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I →
  Nat → TotalField model → TotalField model
packetNonlinearityQuadraticRemainder model system shell perturbation =
  packetField model shell
    (First.projectedNonlinearityQuadraticRemainder system perturbation)

packetNonlinearityPolarizationPointwise :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E}
    (system : Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I)
    (shell : Nat)
    (perturbation : TotalField model)
    (mode : Z3.FourierMode) →
  packetField model shell
    (First.mixedProjectedNonlinearity system
      (First.fieldAdd (Audit.velocity system) perturbation)
      (First.fieldAdd (Audit.velocity system) perturbation)) mode
  ≡
  First.fieldAdd
    (First.fieldAdd
      (packetBaseNonlinearity model system shell)
      (packetNonlinearityFirstVariation model system shell perturbation))
    (packetNonlinearityQuadraticRemainder model system shell perturbation)
    mode
packetNonlinearityPolarizationPointwise model system shell perturbation mode
  with LP.shellSelect model shell mode
... | true = First.projectedNonlinearityPolarizationExact system perturbation mode
... | false =
  sym
    (trans
      (Field.complex3AddZeroRight
        (C3.complex3Add
          (C3.complex3Zero (LP.realField model))
          (C3.complex3Zero (LP.realField model))))
      (First.complex3AddZeroLeft
        (C3.complex3Zero (LP.realField model))))

packetTransferPairing :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E} →
  Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I →
  Nat → List Z3.FourierMode → C3.Complex (LP.realField model)
packetTransferPairing model system shell modes =
  finiteHermitianPairing modes
    (packetBaseVelocity model system shell)
    (packetBaseNonlinearity model system shell)

packetTransferPairingFirstVariation :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E} →
  Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I →
  Nat → List Z3.FourierMode → TotalField model →
  C3.Complex (LP.realField model)
packetTransferPairingFirstVariation model system shell modes perturbation =
  C3.complexAdd
    (finiteHermitianPairing modes
      (packetPerturbation model shell perturbation)
      (packetBaseNonlinearity model system shell))
    (finiteHermitianPairing modes
      (packetBaseVelocity model system shell)
      (packetNonlinearityFirstVariation model system shell perturbation))

packetTransferSixTermExpansion :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    {E : C3.IntegerEmbedding (LP.realField model)}
    {I : C3.ModeInverseSquare (LP.realField model) E}
    (system : Audit.FiniteComplex3GalerkinSystem (LP.realField model) E I)
    (shell : Nat)
    (modes : List Z3.FourierMode)
    (perturbation : TotalField model) →
  finiteHermitianPairing modes
    (First.fieldAdd
      (packetBaseVelocity model system shell)
      (packetPerturbation model shell perturbation))
    (First.fieldAdd
      (First.fieldAdd
        (packetBaseNonlinearity model system shell)
        (packetNonlinearityFirstVariation model system shell perturbation))
      (packetNonlinearityQuadraticRemainder model system shell perturbation))
  ≡
  C3.complexAdd
    (C3.complexAdd
      (C3.complexAdd
        (finiteHermitianPairing modes
          (packetBaseVelocity model system shell)
          (packetBaseNonlinearity model system shell))
        (finiteHermitianPairing modes
          (packetBaseVelocity model system shell)
          (packetNonlinearityFirstVariation model system shell perturbation)))
      (finiteHermitianPairing modes
        (packetBaseVelocity model system shell)
        (packetNonlinearityQuadraticRemainder model system shell perturbation)))
    (C3.complexAdd
      (C3.complexAdd
        (finiteHermitianPairing modes
          (packetPerturbation model shell perturbation)
          (packetBaseNonlinearity model system shell))
        (finiteHermitianPairing modes
          (packetPerturbation model shell perturbation)
          (packetNonlinearityFirstVariation model system shell perturbation)))
      (finiteHermitianPairing modes
        (packetPerturbation model shell perturbation)
        (packetNonlinearityQuadraticRemainder model system shell perturbation)))
packetTransferSixTermExpansion model system shell modes perturbation =
  trans
    (finiteHermitianPairingAddLeft
      modes
      (packetBaseVelocity model system shell)
      (packetPerturbation model shell perturbation)
      nonlinearExpansion)
    (cong₂ C3.complexAdd
      (finiteHermitianPairingAddThreeRight modes
        (packetBaseVelocity model system shell)
        (packetBaseNonlinearity model system shell)
        (packetNonlinearityFirstVariation model system shell perturbation)
        (packetNonlinearityQuadraticRemainder model system shell perturbation))
      (finiteHermitianPairingAddThreeRight modes
        (packetPerturbation model shell perturbation)
        (packetBaseNonlinearity model system shell)
        (packetNonlinearityFirstVariation model system shell perturbation)
        (packetNonlinearityQuadraticRemainder model system shell perturbation)))
  where
  nonlinearExpansion =
    First.fieldAdd
      (First.fieldAdd
        (packetBaseNonlinearity model system shell)
        (packetNonlinearityFirstVariation model system shell perturbation))
      (packetNonlinearityQuadraticRemainder model system shell perturbation)

finiteHermitianQuadraticFirstVariation :
  ∀ {r} {F : C3.RealField r} →
  List Z3.FourierMode →
  (Z3.FourierMode → C3.Complex3 F) →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
finiteHermitianQuadraticFirstVariation modes base tangent =
  C3.complexAdd
    (finiteHermitianPairing modes tangent base)
    (finiteHermitianPairing modes base tangent)

finiteHermitianQuadraticExpansion :
  ∀ {r} {F : C3.RealField r}
    (modes : List Z3.FourierMode)
    (base tangent : Z3.FourierMode → C3.Complex3 F) →
  finiteHermitianPairing modes
    (First.fieldAdd base tangent)
    (First.fieldAdd base tangent)
  ≡
  C3.complexAdd
    (C3.complexAdd
      (finiteHermitianPairing modes base base)
      (finiteHermitianPairing modes base tangent))
    (C3.complexAdd
      (finiteHermitianPairing modes tangent base)
      (finiteHermitianPairing modes tangent tangent))
finiteHermitianQuadraticExpansion modes base tangent =
  trans
    (finiteHermitianPairingAddLeft
      modes base tangent (First.fieldAdd base tangent))
    (cong₂ C3.complexAdd
      (finiteHermitianPairingAddRight modes base base tangent)
      (finiteHermitianPairingAddRight modes tangent base tangent))

packetDerivativeField :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  Nat → TotalField model → TotalField model
packetDerivativeField model shell field mode =
  C3.complex3Scale
    (LP.derivativeMultiplier model mode)
    (packetField model shell field mode)

packetDissipationPairingFirstVariation :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r}) →
  Nat → List Z3.FourierMode →
  TotalField model → TotalField model →
  C3.Complex (LP.realField model)
packetDissipationPairingFirstVariation model shell modes base tangent =
  finiteHermitianQuadraticFirstVariation modes
    (packetDerivativeField model shell base)
    (packetDerivativeField model shell tangent)

round82LiteralPacketTransferFirstVariationConstructed : Bool
round82LiteralPacketTransferFirstVariationConstructed = true

round82LiteralPacketDissipationFirstVariationConstructed : Bool
round82LiteralPacketDissipationFirstVariationConstructed = true

round82LiteralPacketProductRuleAlgebraConstructed : Bool
round82LiteralPacketProductRuleAlgebraConstructed = true

round82LiteralPacketProductRuleAlgebraConstructedIsTrue :
  round82LiteralPacketProductRuleAlgebraConstructed ≡ true
round82LiteralPacketProductRuleAlgebraConstructedIsTrue = refl
