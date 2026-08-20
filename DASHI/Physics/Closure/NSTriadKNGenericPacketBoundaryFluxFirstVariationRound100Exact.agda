module DASHI.Physics.Closure.NSTriadKNGenericPacketBoundaryFluxFirstVariationRound100Exact where

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
-- ROUND100 / DIFFERENTIATE THE WHOLE FACTOR-SIX THEOREM
--
-- Round99 constructed the dual-number RealField F[eps]/(eps^2) and used it to
-- differentiate exact triad energy cancellation.  Round100 applies the same
-- idea one level higher: the repaired generic packet-boundary theorem already
-- holds over EVERY repository RealField, hence it holds over the dual lift.
--
-- Evaluating the factor-six identity at u + eps h and taking the eps
-- coordinate proves directly
--
--   d(boundary three-leg flux)[u;h]
--      = sixFold ( d selected-projected-pairing[u;h] ).
--
-- This avoids a second membership/partition proof for differentiated internal
-- triads.  Internal first variations have already cancelled inside the generic
-- boundary theorem before the tangent coordinate is projected.  The only
-- surviving differentiated transfer is therefore packet-boundary transfer.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNDualRealFieldTriadFirstVariationRound99Exact as Dual
import DASHI.Physics.Closure.NSTriadKNGenericPacketBoundaryFluxFactorSixRound98Exact as FactorSix

liftFiniteSystem :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (perturbation : Z3.FourierMode → C3.Complex3 F) →
  Audit.FiniteComplex3GalerkinSystem
    (Dual.dualRealField F)
    (Dual.dualIntegerEmbedding E)
    (Dual.dualModeInverseSquare E I)
liftFiniteSystem system perturbation = record
  { cutoff = Audit.cutoff system
  ; modes = Audit.modes system
  ; triads = Audit.triads system
  ; velocity = λ mode → Dual.liftComplex3 (Audit.velocity system mode) (perturbation mode)
  ; viscosity = Dual.constantDual (Audit.viscosity system)
  ; modeListed = Audit.modeListed system
  ; triadListed = Audit.triadListed system
  ; modesAreLiteralCutoff = Audit.modesAreLiteralCutoff system
  ; triadsAreLiteralEnumeration = Audit.triadsAreLiteralEnumeration system
  ; zeroModeExcluded = Audit.zeroModeExcluded system
  ; realityClosed = Audit.realityClosed system
  }

liftFiniteSystemCutoff :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (perturbation : Z3.FourierMode → C3.Complex3 F) →
  Audit.cutoff (liftFiniteSystem system perturbation) ≡ Audit.cutoff system
liftFiniteSystemCutoff system perturbation = refl

boundaryFirstVariation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
boundaryFirstVariation {E = E} {I = I} system selected perturbation =
  Dual.complexTangent
    (FactorSix.sumBoundaryTransfer
      (Dual.dualIntegerEmbedding E)
      (Dual.dualModeInverseSquare E I)
      selected
      (Audit.velocity (liftFiniteSystem system perturbation))
      (Physical.physicalTriadEnumeration (Audit.cutoff system)))

selectedProjectedPairingFirstVariation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Complex F
selectedProjectedPairingFirstVariation system selected perturbation =
  Dual.complexTangent
    (FactorSix.literalSelectedProjectedPairing
      (liftFiniteSystem system perturbation) selected)

complexTangentSixFold :
  ∀ {r} {F : C3.RealField r}
    (value : C3.Complex (Dual.dualRealField F)) →
  Dual.complexTangent (FactorSix.sixFold value)
  ≡ FactorSix.sixFold (Dual.complexTangent value)
complexTangentSixFold value = refl

PhysicalPacketBoundaryFluxFirstVariationFactorSix :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (selected : Z3.FourierMode → Bool)
    (perturbation : Z3.FourierMode → C3.Complex3 F) →
  Reality.RealityCondition (Audit.velocity system) →
  Reality.RealityCondition perturbation →
  Reality.DivergenceFreeCondition E (Audit.velocity system) →
  Reality.DivergenceFreeCondition E perturbation →
  boundaryFirstVariation system selected perturbation
  ≡ FactorSix.sixFold
      (selectedProjectedPairingFirstVariation system selected perturbation)
PhysicalPacketBoundaryFluxFirstVariationFactorSix {F = F} {E = E} {I = I}
    system selected perturbation velocityReality perturbationReality
    velocityDivergenceFree perturbationDivergenceFree =
  let
    lifted = liftFiniteSystem system perturbation
    liftedReality =
      Dual.liftedReality
        (Audit.velocity system) perturbation
        velocityReality perturbationReality
    liftedDivergenceFree =
      Dual.liftedDivergenceFree E
        (Audit.velocity system) perturbation
        velocityDivergenceFree perturbationDivergenceFree
    factorSix =
      FactorSix.PhysicalPacketBoundaryFluxFactorSixIdentification
        lifted selected liftedReality liftedDivergenceFree
  in
  trans
    (cong Dual.complexTangent factorSix)
    (complexTangentSixFold
      (FactorSix.literalSelectedProjectedPairing lifted selected))
  where
  open import Relation.Binary.PropositionalEquality using (cong; trans)

round100GenericPacketBoundaryFirstVariationFactorSixClosed : Bool
round100GenericPacketBoundaryFirstVariationFactorSixClosed = true

round100DifferentiatedInternalTriadsNeedSeparateEstimate : Bool
round100DifferentiatedInternalTriadsNeedSeparateEstimate = false

round100GenericPacketBoundaryFirstVariationFactorSixClosedIsTrue :
  round100GenericPacketBoundaryFirstVariationFactorSixClosed ≡ true
round100GenericPacketBoundaryFirstVariationFactorSixClosedIsTrue = refl
