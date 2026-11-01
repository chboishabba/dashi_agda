module DASHI.Physics.Closure.NSTriadKNPressurePoissonSourceLiteralDivergenceRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Jinhee Jeong; Fazle Hussain.
-- Title: "On the identification of a vortex".
-- DOI: 10.1017/S0022112095000462.
--
-- ROUND85 / SAME-OBJECT PRESSURE POISSON SOURCE
--
-- The pressure potential constructed from the literal Leray correction is
--
--   pHat_k = - |k|^{-2} sum_{p+q=k} k dot w(p,q).
--
-- On a retained nonzero output mode, multiplying by |k|^2 gives exactly
--
--   |k|^2 pHat_k = - sum_{p+q=k} k dot w(p,q).
--
-- The left side is the Fourier coefficient of -Delta p.  The right side is
-- the negative divergence of the SAME unprojected advective output fibre.
-- Thus the pressure-Poisson/Q share introduced in Round85 has no remaining
-- pressure-source provenance gap: its coefficient is computed directly from
-- the literal Galerkin velocity interactions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as CRing
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayOut
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralAdvectivePressureRHSSplitRound84Exact as AP
import DASHI.Physics.Closure.NSTriadKNPressurePotentialGradientHessianSameModeRound85Exact as Potential
import DASHI.Physics.Closure.NSTriadKNPressureTransportPoissonSplitRound85Exact as Transport

orderedAdvectiveDivergenceSource :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → Physical.PhysicalTriadIncidence → C3.Complex F
orderedAdvectiveDivergenceSource {F = F} {E = E}
    system output incidence =
  C3.complexNegate
    (C3.bilinearDot3
      (C3.modeVector E output)
      (AP.rawOrderedValue system incidence))

orderedPotentialTimesNormIsDivergenceSource :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (nonzero : Z3.NonZeroMode output)
    (incidence : Physical.PhysicalTriadIncidence) →
  C3.complexMultiply
    (Potential.orderedPressurePotentialAt system output incidence)
    (C3.realEmbed F (C3.normSquared I output))
  ≡ orderedAdvectiveDivergenceSource system output incidence
orderedPotentialTimesNormIsDivergenceSource {F = F} {E = E} {I = I}
    system output nonzero incidence =
  let
    inverse = C3.realEmbed F (C3.inverseNormSquared I output)
    norm = C3.realEmbed F (C3.normSquared I output)
    divergence =
      C3.bilinearDot3
        (C3.modeVector E output)
        (AP.rawOrderedValue system incidence)
  in
  trans
    (C.solve 3
      (λ inv d n →
        ((C.⊝ (inv C.⊗ d)) C.⊗ n)
        C.⊜ (C.⊝ (d C.⊗ (inv C.⊗ n))))
      refl inverse divergence norm)
    (trans
      (cong
        (λ unit → C3.complexNegate
          (C3.complexMultiply divergence unit))
        (LerayOut.embeddedInverseSquareLaw E I output nonzero))
      (cong C3.complexNegate
        (CRing.complexMultiplyOneRight divergence)))
  where module C = CRing.Solver F

sumAdvectiveDivergenceSources :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → List Physical.PhysicalTriadIncidence → C3.Complex F
sumAdvectiveDivergenceSources {F = F} system output [] = C3.complexZero F
sumAdvectiveDivergenceSources system output (incidence ∷ rest) =
  C3.complexAdd
    (orderedAdvectiveDivergenceSource system output incidence)
    (sumAdvectiveDivergenceSources system output rest)

potentialListTimesNormIsDivergenceSum :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (nonzero : Z3.NonZeroMode output)
    (incidences : List Physical.PhysicalTriadIncidence) →
  C3.complexMultiply
    (Potential.pressurePotentialFromList system output incidences)
    (C3.realEmbed F (C3.normSquared I output))
  ≡ sumAdvectiveDivergenceSources system output incidences
potentialListTimesNormIsDivergenceSum {F = F}
    system output nonzero [] =
  Algebra.complexMultiplyZeroLeft
    (C3.realEmbed F (C3.normSquared _ output))
potentialListTimesNormIsDivergenceSum {F = F} {I = I}
    system output nonzero (incidence ∷ rest) =
  trans
    (Algebra.complexMultiplyDistributesRight
      (Potential.orderedPressurePotentialAt system output incidence)
      (Potential.pressurePotentialFromList system output rest)
      (C3.realEmbed F (C3.normSquared I output)))
    (cong₂ C3.complexAdd
      (orderedPotentialTimesNormIsDivergenceSource
        system output nonzero incidence)
      (potentialListTimesNormIsDivergenceSum
        system output nonzero rest))

literalPressurePoissonSource :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex F
literalPressurePoissonSource system output =
  sumAdvectiveDivergenceSources
    system output (Audit.concreteTriadsAt system output)

pressurePoissonSourceIsLiteralAdvectiveDivergence :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (nonzero : Z3.NonZeroMode output) →
  Transport.pressurePoissonSourceCoefficient system output
  ≡ literalPressurePoissonSource system output
pressurePoissonSourceIsLiteralAdvectiveDivergence {F = F} {I = I}
    system output nonzero =
  potentialListTimesNormIsDivergenceSum
    system output nonzero (Audit.concreteTriadsAt system output)

round85PressurePoissonSourceSameLiteralAdvectiveFibre : Bool
round85PressurePoissonSourceSameLiteralAdvectiveFibre = true

round85PressurePoissonSourceSameLiteralAdvectiveFibreIsTrue :
  round85PressurePoissonSourceSameLiteralAdvectiveFibre ≡ true
round85PressurePoissonSourceSameLiteralAdvectiveFibreIsTrue = refl
