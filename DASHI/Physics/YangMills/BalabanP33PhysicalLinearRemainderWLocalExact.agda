module DASHI.Physics.YangMills.BalabanP33PhysicalLinearRemainderWLocalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 605--636.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Give the physical constructor for W-local.  On every literal side-four
-- plaquette, the actual background-minus-flat Wilson second variation must be
-- decomposed into
--
--   correlated linear curvature part + grouped nonlinear remainder.
--
-- The selected-background estimate pays the linear part from the twelve-pair
-- cross charge with coefficient rho/36.  The grouped sixteen-atom estimate pays
-- the nonlinear remainder from the four-slot diagonal charge with coefficient
-- rho/144.  Their exact signed sum is definitionally the repository's local
-- Wilson budget, so no unnamed scalar receipt remains between these two
-- physical estimates and `PhysicalWilsonSignedLocal`.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; -_; _≤_)

import DASHI.Physics.YangMills.BalabanP33SelectedCorrelationToWLocalExact as Correlation
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as WilsonGlobal
import DASHI.Physics.YangMills.BalabanSelectedBackgroundPhysicalRadiusInstantiationExact as Instantiation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanP33SelectedBackgroundFiniteCoercivityExact as Coercivity
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PhysicalTerminalHessianCoercivityExact as Terminal
import DASHI.Physics.YangMills.BalabanP33Path4SignedRemainderCoercivityExact as P33

record PhysicalPlaquetteLinearRemainderControl
    (background : Physical.RationalSU2Background4)
    (fieldValue : Coordinates.PhysicalSU2BondField4) : Set₁ where
  field
    physicalLinearPart : Physical.Plaquette4 → ℚ
    physicalGroupedRemainder : Physical.Plaquette4 → ℚ

    physicalDecomposition : ∀ plaquette →
      Physical.plaquetteWilsonSecondVariation background fieldValue plaquette
        - Physical.plaquetteWilsonSecondVariation
            Physical.identityBackground fieldValue plaquette
      ≡ physicalLinearPart plaquette
        + physicalGroupedRemainder plaquette

    selectedCurvatureLinearLower : ∀ plaquette →
      - (WilsonGlobal.rhoOverThirtySix
          * WilsonGlobal.plaquetteCrossCharge fieldValue plaquette)
      ≤ physicalLinearPart plaquette

    groupedSixteenAtomRemainderLower : ∀ plaquette →
      - (WilsonGlobal.rhoOverOneFortyFour
          * WilsonGlobal.plaquetteDiagonalCharge fieldValue plaquette)
      ≤ physicalGroupedRemainder plaquette

open PhysicalPlaquetteLinearRemainderControl public

physicalCorrelationInputsAt :
  ∀ {background fieldValue} →
  PhysicalPlaquetteLinearRemainderControl background fieldValue →
  Physical.Plaquette4 →
  Correlation.PhysicalSelectedCorrelationInputs
physicalCorrelationInputsAt {background} {fieldValue} control plaquette =
  Correlation.physicalSelectedCorrelationInputs
    (Physical.plaquetteWilsonSecondVariation background fieldValue plaquette
      - Physical.plaquetteWilsonSecondVariation
          Physical.identityBackground fieldValue plaquette)
    (physicalLinearPart control plaquette)
    (physicalGroupedRemainder control plaquette)
    (WilsonGlobal.rhoOverThirtySix
      * WilsonGlobal.plaquetteCrossCharge fieldValue plaquette)
    (WilsonGlobal.rhoOverOneFortyFour
      * WilsonGlobal.plaquetteDiagonalCharge fieldValue plaquette)
    (physicalDecomposition control plaquette)
    (selectedCurvatureLinearLower control plaquette)
    (groupedSixteenAtomRemainderLower control plaquette)

physicalLinearRemainderControlImpliesWLocal :
  ∀ {background fieldValue} →
  PhysicalPlaquetteLinearRemainderControl background fieldValue →
  WilsonGlobal.PhysicalWilsonSignedLocal background fieldValue
physicalLinearRemainderControlImpliesWLocal control = record
  { WilsonGlobal.PhysicalWilsonSignedLocal.plaquetteLower = λ plaquette →
      Correlation.physicalInputsImplyWLocalScalar
        (physicalCorrelationInputsAt control plaquette)
  }

------------------------------------------------------------------------
-- Direct selected-background terminal composition.
------------------------------------------------------------------------

selectedVariationalCorrelationTerminalCoefficient :
  ∀ {CoarseField Lie Perturbation ConstraintIndex}
    {inputs : Instantiation.SelectedPhysicalBackgroundInstantiation
      CoarseField Lie}
    {coarse}
    {small : Variational.CoarseSmallField
      (Selected.variational (Instantiation.bridge inputs)) coarse}
    (family : Instantiation.SelectedVariationalPerturbationFamily
      {Perturbation = Perturbation}
      {ConstraintIndex = ConstraintIndex}
      inputs coarse small)
    h →
  PhysicalPlaquetteLinearRemainderControl
    (Coercivity.backgroundOf (Instantiation.model family) h)
    (Coercivity.physicalFieldOf (Instantiation.model family) h) →
  Terminal.terminalPhysicalCoefficient
      * Coordinates.physicalSU2BondNormSq
          (Coercivity.physicalFieldOf (Instantiation.model family) h)
  ≤ Jets.literalTotalSecondVariation
      (Coercivity.selectedLiteralSecondVariation
        (Instantiation.model family) h)
selectedVariationalCorrelationTerminalCoefficient family h control =
  Instantiation.selectedVariationalTerminalCoefficient
    family h
    (physicalLinearRemainderControlImpliesWLocal control)

selectedVariationalCorrelationOneThirtySecond :
  ∀ {CoarseField Lie Perturbation ConstraintIndex}
    {inputs : Instantiation.SelectedPhysicalBackgroundInstantiation
      CoarseField Lie}
    {coarse}
    {small : Variational.CoarseSmallField
      (Selected.variational (Instantiation.bridge inputs)) coarse}
    (family : Instantiation.SelectedVariationalPerturbationFamily
      {Perturbation = Perturbation}
      {ConstraintIndex = ConstraintIndex}
      inputs coarse small)
    h →
  PhysicalPlaquetteLinearRemainderControl
    (Coercivity.backgroundOf (Instantiation.model family) h)
    (Coercivity.physicalFieldOf (Instantiation.model family) h) →
  P33.p33PhysicalFloor
      * Coordinates.physicalSU2BondNormSq
          (Coercivity.physicalFieldOf (Instantiation.model family) h)
  ≤ Jets.literalTotalSecondVariation
      (Coercivity.selectedLiteralSecondVariation
        (Instantiation.model family) h)
selectedVariationalCorrelationOneThirtySecond family h control =
  Instantiation.selectedVariationalOneThirtySecond
    family h
    (physicalLinearRemainderControlImpliesWLocal control)
