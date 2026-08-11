module DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualActionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- DASHI CONTRIBUTION
--
-- The contraction estimates were proved for a literal finite kernel named
-- `flatGreenTimesPerturbationKernel`.  This module proves its vector action is
-- exactly the operator composition
--
--      R_A = G_0 E_A,
--
-- where G_0 is the already-proved Fourier inverse and E_A is the SAME
-- perturbation action appearing in K_A^reg=K_0^reg+E_A.  Thus the <1/10 and
-- <1/6 residual estimates are attached to the exact reopening factorization,
-- not merely to a kernel with matching coefficients.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as ScalarGreen
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact as Perturbation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationActionExact as PerturbationAction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeOperatorDecompositionExact as Operator
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Contraction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualPowerDecayExact as Residual

GaugeMultiplier : Set
GaugeMultiplier = FlatAdjoint.GaugeMultiplier

residualKernelIsRectangularCompose : ∀ background row column →
  Contraction.flatGreenTimesPerturbationKernel background row column
  ≡ Rect.composeRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
      Contraction.flatGreenKernelMatrix
      (Perturbation.gaugeGramPerturbationMatrix background)
      row column
residualKernelIsRectangularCompose background row column = refl

residualApplyAsRectangularCompose : ∀ background multiplier row →
  Residual.residualApply background multiplier row
  ≡ Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
      (Rect.composeRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
        Contraction.flatGreenKernelMatrix
        (Perturbation.gaugeGramPerturbationMatrix background))
      multiplier row
residualApplyAsRectangularCompose background multiplier row =
  Sums.sumRationalCong Contraction.gaugeRows _ _
    (λ column →
      cong (_* multiplier column)
        (residualKernelIsRectangularCompose background row column))

flatGreenKernelApplyAsRectangular : ∀ source row →
  Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
    Contraction.flatGreenKernelMatrix source row
  ≡ Contraction.flatGreenKernelApply source row
flatGreenKernelApplyAsRectangular source row = refl

selectedResidualActsAsFlatGreenPerturbation :
  ∀ background multiplier row →
  Residual.residualApply background multiplier row
  ≡ FlatGreen.regularizedFlatGaugeGreen
      (PerturbationAction.selectedGaugeGramPerturbationApply
        background multiplier) row
selectedResidualActsAsFlatGreenPerturbation background multiplier row =
  trans
    (residualApplyAsRectangularCompose background multiplier row)
    (trans
      (Rect.applyComposeRectangularExact
        FlatAdjoint.selectedFlatGaugeRowCarrier
        FlatAdjoint.selectedFlatGaugeRowCarrier
        Contraction.flatGreenKernelMatrix
        (Perturbation.gaugeGramPerturbationMatrix background)
        multiplier row)
      (trans
        (flatGreenKernelApplyAsRectangular
          (PerturbationAction.selectedGaugeGramPerturbationApply
            background multiplier) row)
        (caseRow row)))
  where
  caseRow : ∀ selected →
    Contraction.flatGreenKernelApply
      (PerturbationAction.selectedGaugeGramPerturbationApply
        background multiplier) selected
    ≡ FlatGreen.regularizedFlatGaugeGreen
        (PerturbationAction.selectedGaugeGramPerturbationApply
          background multiplier) selected
  caseRow (Torus.pair coordinate site) =
    Contraction.flatGreenKernelActsExactly
      (PerturbationAction.selectedGaugeGramPerturbationApply background multiplier)
      coordinate site

selectedResidualActsAsExplicitFlatGreenEA :
  ∀ background multiplier
    (coordinate : Coordinates.LieCoordinate3)
    (site : Block.PhysicalBlockL Path4.side4) →
  Residual.residualApply background multiplier (Torus.pair coordinate site)
  ≡ FlatGreen.regularizedFlatGaugeGreen
      (λ row → Operator.explicitGaugeGramPerturbation background multiplier row)
      (Torus.pair coordinate site)
selectedResidualActsAsExplicitFlatGreenEA background multiplier coordinate site =
  let
    row = Torus.pair coordinate site
    pointwise = PerturbationAction.selectedGaugeGramPerturbationActsAsExplicitEA
      background multiplier
  in
  trans
    (selectedResidualActsAsFlatGreenPerturbation background multiplier row)
    (ScalarGreen.scalarGreenRespectsPointwise
      (λ current → pointwise (Torus.pair coordinate current))
      site)

selectedResidualActionLevel : ProofLevel
selectedResidualActionLevel = machineChecked

selectedResidualExplicitEAActionLevel : ProofLevel
selectedResidualExplicitEAActionLevel = machineChecked
