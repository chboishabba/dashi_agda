module DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadExternalReplenishmentIdentityRound95Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND95 / EXTERNAL REPLENISHMENT IDENTITY
--
-- On each of the k,p,q legs, the actual projected Galerkin forcing is exactly
-- self+external. Hermitian pairing and real-part extraction are additive.
-- Round95 already proved the selected triad's self three-leg energy sum is
-- zero. Therefore the complete three-leg nonlinear energy increment equals
-- the external-network three-leg increment exactly:
--
--   T_k^full + T_p^full + T_q^full
--     = T_k^ext + T_p^ext + T_q^ext.
--
-- This is the exact same-object replenishment identity needed by the compact-
-- Gamma route. The remaining Clay-scale estimate is quantitative: control the
-- positive external packet flux by absorbed dissipation plus a fixed remainder.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Galerkin
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as Split
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadSelfEnergyNonreplenishmentRound95Exact as Self

fullPowerK :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
fullPowerK system tau =
  C3.complexRealPart
    (C3.hermitianPairing3
      (Galerkin.velocityAt system (Physical.k tau))
      (Split.fullForcingK system tau))

fullPowerP :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
fullPowerP system tau =
  C3.complexRealPart
    (C3.hermitianPairing3
      (Galerkin.velocityAt system (Physical.p tau))
      (Split.fullForcingP system tau))

fullPowerQ :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
fullPowerQ system tau =
  C3.complexRealPart
    (C3.hermitianPairing3
      (Galerkin.velocityAt system (Physical.q tau))
      (Split.fullForcingQ system tau))

selfPowerK :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
selfPowerK system tau =
  C3.complexRealPart
    (C3.hermitianPairing3
      (Galerkin.velocityAt system (Physical.k tau))
      (Split.selfForcingK system tau))

selfPowerP :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
selfPowerP system tau =
  C3.complexRealPart
    (C3.hermitianPairing3
      (Galerkin.velocityAt system (Physical.p tau))
      (Split.selfForcingP system tau))

selfPowerQ :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
selfPowerQ system tau =
  C3.complexRealPart
    (C3.hermitianPairing3
      (Galerkin.velocityAt system (Physical.q tau))
      (Split.selfForcingQ system tau))

externalPowerK :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
externalPowerK system tau =
  C3.complexRealPart
    (C3.hermitianPairing3
      (Galerkin.velocityAt system (Physical.k tau))
      (Split.externalForcingK system tau))

externalPowerP :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
externalPowerP system tau =
  C3.complexRealPart
    (C3.hermitianPairing3
      (Galerkin.velocityAt system (Physical.p tau))
      (Split.externalForcingP system tau))

externalPowerQ :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
externalPowerQ system tau =
  C3.complexRealPart
    (C3.hermitianPairing3
      (Galerkin.velocityAt system (Physical.q tau))
      (Split.externalForcingQ system tau))

powerSplits :
  ∀ {r} {F : C3.RealField r}
    (u self external : C3.Complex3 F) →
  u ≡ u →
  C3.complex3Add self external ≡ C3.complex3Add self external →
  C3.complexRealPart
    (C3.hermitianPairing3 u (C3.complex3Add self external))
  ≡
  C3.complexAdd
    (C3.complexRealPart (C3.hermitianPairing3 u self))
    (C3.complexRealPart (C3.hermitianPairing3 u external))
powerSplits u self external refl refl =
  trans
    (cong C3.complexRealPart
      (Additive.hermitianPairingAddRight u self external))
    (Algebra.complexRealPartAdd
      (C3.hermitianPairing3 u self)
      (C3.hermitianPairing3 u external))

fullPowerKSplits :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  fullPowerK system tau ≡ C3.complexAdd (selfPowerK system tau) (externalPowerK system tau)
fullPowerKSplits system tau
  rewrite Split.fullKIsSelfPlusExternal system tau =
  powerSplits
    (Galerkin.velocityAt system (Physical.k tau))
    (Split.selfForcingK system tau) (Split.externalForcingK system tau) refl refl

fullPowerPSplits :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  fullPowerP system tau ≡ C3.complexAdd (selfPowerP system tau) (externalPowerP system tau)
fullPowerPSplits system tau
  rewrite Split.fullPIsSelfPlusExternal system tau =
  powerSplits
    (Galerkin.velocityAt system (Physical.p tau))
    (Split.selfForcingP system tau) (Split.externalForcingP system tau) refl refl

fullPowerQSplits :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  fullPowerQ system tau ≡ C3.complexAdd (selfPowerQ system tau) (externalPowerQ system tau)
fullPowerQSplits system tau
  rewrite Split.fullQIsSelfPlusExternal system tau =
  powerSplits
    (Galerkin.velocityAt system (Physical.q tau))
    (Split.selfForcingQ system tau) (Split.externalForcingQ system tau) refl refl

totalFullPower totalSelfPower totalExternalPower :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  Galerkin.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
totalFullPower system tau =
  C3.complexAdd (C3.complexAdd (fullPowerK system tau) (fullPowerP system tau))
    (fullPowerQ system tau)
totalSelfPower system tau =
  C3.complexAdd (C3.complexAdd (selfPowerK system tau) (selfPowerP system tau))
    (selfPowerQ system tau)
totalExternalPower system tau =
  C3.complexAdd (C3.complexAdd (externalPowerK system tau) (externalPowerP system tau))
    (externalPowerQ system tau)

totalFullSplitsSelfExternal :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  totalFullPower system tau
  ≡ C3.complexAdd (totalSelfPower system tau) (totalExternalPower system tau)
totalFullSplitsSelfExternal {F = F} system tau
  rewrite fullPowerKSplits system tau
        | fullPowerPSplits system tau
        | fullPowerQSplits system tau =
  R.solve 6
    (λ sk ek sp ep sq eq →
      (((sk R.⊕ ek) R.⊕ (sp R.⊕ ep)) R.⊕ (sq R.⊕ eq))
      R.⊜ (((sk R.⊕ sp) R.⊕ sq) R.⊕ ((ek R.⊕ ep) R.⊕ eq)))
    refl
    (selfPowerK system tau) (externalPowerK system tau)
    (selfPowerP system tau) (externalPowerP system tau)
    (selfPowerQ system tau) (externalPowerQ system tau)
  where module R = Ring.Solver F

totalSelfPowerAgreesWithSelectedSelfOrbit :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  totalSelfPower system tau ≡ Self.selectedTriadSelfEnergyPower system tau
totalSelfPowerAgreesWithSelectedSelfOrbit system tau = refl

fullThreeLegReplenishmentIsExternalNetwork :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Audit.RealityCondition (Galerkin.velocityAt system) →
  Audit.DivergenceFreeCondition E (Galerkin.velocityAt system) →
  totalFullPower system tau ≡ totalExternalPower system tau
fullThreeLegReplenishmentIsExternalNetwork {F = F} system tau reality divergenceFree =
  trans
    (totalFullSplitsSelfExternal system tau)
    (trans
      (cong (λ self → C3.complexAdd self (totalExternalPower system tau))
        (trans
          (totalSelfPowerAgreesWithSelectedSelfOrbit system tau)
          (Self.selectedTriadSelfEnergyCannotReplenish system tau reality divergenceFree)))
      (Algebra.complexAddZeroLeft (totalExternalPower system tau)))

round95FullThreeLegReplenishmentEqualsExternalNetwork : Bool
round95FullThreeLegReplenishmentEqualsExternalNetwork = true

round95FullThreeLegReplenishmentEqualsExternalNetworkIsTrue :
  round95FullThreeLegReplenishmentEqualsExternalNetwork ≡ true
round95FullThreeLegReplenishmentEqualsExternalNetworkIsTrue = refl
