module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGreenExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- DASHI CONTRIBUTION
--
-- Close the finite selected-background gauge Green algebraically.  The literal
-- local perturbation matrix E_A is first proved to act as the explicit operator
-- perturbation already used in
--
--     K_A^reg = K_0^reg + E_A.
--
-- The literal residual matrix is then proved to act as
--
--     R_A = G_0 E_A.
--
-- Consequently
--
--     G_0 K_A^reg = I + R_A = M_A.
--
-- Given the proof-relevant finite rational inverse certificate for M_A, define
--
--     G_A = M_A^-1 G_0.
--
-- Both inverse directions are proved pointwise.  The right-inverse proof avoids
-- any new linearity burden: G_0 is already injective because K_0^reg G_0=I,
-- so equality after applying G_0 implies equality of the original sources.
-- No infinite Neumann series or completion of Q is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as SumDifference
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeReducedFloorExact as BackgroundFloor
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramFiniteRangeExact as Gram
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact as Perturbation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeOperatorDecompositionExact as Operator
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Contraction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualPowerDecayExact as Residual
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFiniteRationalReopeningExact as FiniteReopen

GaugeMultiplier : Set
GaugeMultiplier = FlatAdjoint.GaugeMultiplier

------------------------------------------------------------------------
-- Literal Gram-matrix action equals the already-used operator action.
------------------------------------------------------------------------

selectedGaugeGramMatrixApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
selectedGaugeGramMatrixApply background =
  Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
    (Gram.selectedBackgroundGaugeGram background)

selectedGaugeGramMatrixActionExact :
  ∀ background multiplier row →
  selectedGaugeGramMatrixApply background multiplier row
  ≡ Operator.backgroundGaugeGramApply background multiplier row
selectedGaugeGramMatrixActionExact background multiplier row =
  Rect.applyComposeRectangularExact
    DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact.physicalStateCarrier
    FlatAdjoint.selectedFlatGaugeRowCarrier
    (DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact.selectedBackgroundGaugeConstraintMatrix background)
    (Rect.transposeRectangular
      (DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact.selectedBackgroundGaugeConstraintMatrix background))
    multiplier row

identityGaugeGramMatrixActionExact :
  ∀ multiplier row →
  selectedGaugeGramMatrixApply Physical.identityBackground multiplier row
  ≡ FlatGreen.flatGaugeGramApply multiplier row
identityGaugeGramMatrixActionExact multiplier row = refl

------------------------------------------------------------------------
-- The raw finite Gram difference is the explicit E_A operator.
------------------------------------------------------------------------

selectedGaugeGramPerturbationApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
selectedGaugeGramPerturbationApply background =
  Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
    (Perturbation.gaugeGramPerturbationMatrix background)

selectedGaugeGramPerturbationApplyDifferenceExact :
  ∀ background multiplier row →
  selectedGaugeGramPerturbationApply background multiplier row
  ≡ selectedGaugeGramMatrixApply background multiplier row
    - selectedGaugeGramMatrixApply Physical.identityBackground multiplier row
selectedGaugeGramPerturbationApplyDifferenceExact background multiplier row =
  SumDifference.sumSubtract
    Contraction.gaugeRows
    (λ column →
      Gram.selectedBackgroundGaugeGram background row column
        * multiplier column)
    (λ column →
      Gram.selectedBackgroundGaugeGram Physical.identityBackground row column
        * multiplier column)

selectedGaugeGramPerturbationActsAsExplicitEA :
  ∀ background multiplier row →
  selectedGaugeGramPerturbationApply background multiplier row
  ≡ Operator.explicitGaugeGramPerturbation background multiplier row
selectedGaugeGramPerturbationActsAsExplicitEA background multiplier row =
  let
    difference = selectedGaugeGramPerturbationApplyDifferenceExact
      background multiplier row

    backgroundExact = selectedGaugeGramMatrixActionExact
      background multiplier row

    flatExact = identityGaugeGramMatrixActionExact multiplier row

    decomposition = Operator.backgroundGaugeGramDecomposition
      background multiplier row
  in
  trans difference
    (trans
      (cong₂ _-_
        backgroundExact flatExact)
      (trans
        (cong
          (_- FlatGreen.flatGaugeGramApply multiplier row)
          decomposition)
        (ℚRing.solve-∀
          (FlatGreen.flatGaugeGramApply multiplier row)
          (Operator.explicitGaugeGramPerturbation background multiplier row))))

------------------------------------------------------------------------
-- Matrix residual = G_0 E_A as an actual vector action.
------------------------------------------------------------------------

flatGreenMatrixApply : GaugeMultiplier → GaugeMultiplier
flatGreenMatrixApply =
  Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
    Contraction.flatGreenKernelMatrix

flatGreenMatrixActsAsExactGreen : ∀ source row →
  flatGreenMatrixApply source row
  ≡ FlatGreen.regularizedFlatGaugeGreen source row
flatGreenMatrixActsAsExactGreen source (pair coordinate site) =
  Contraction.flatGreenKernelActsExactly source coordinate site

residualKernelAsRectangularCompose : ∀ background left right →
  Contraction.flatGreenTimesPerturbationKernel background left right
  ≡ Rect.composeRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
      Contraction.flatGreenKernelMatrix
      (Perturbation.gaugeGramPerturbationMatrix background)
      left right
residualKernelAsRectangularCompose background left right = refl

selectedResidualActsAsFlatGreenEA :
  ∀ background multiplier row →
  Residual.residualApply background multiplier row
  ≡ FlatGreen.regularizedFlatGaugeGreen
      (selectedGaugeGramPerturbationApply background multiplier) row
selectedResidualActsAsFlatGreenEA background multiplier row =
  let
    kernelCong :
      Residual.residualApply background multiplier row
      ≡ Rect.applyRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
          (Rect.composeRectangular FlatAdjoint.selectedFlatGaugeRowCarrier
            Contraction.flatGreenKernelMatrix
            (Perturbation.gaugeGramPerturbationMatrix background))
          multiplier row
    kernelCong =
      Sums.sumRationalCong Contraction.gaugeRows _ _
        (λ column →
          cong (_* multiplier column)
            (residualKernelAsRectangularCompose background row column))

    compose = Rect.applyComposeRectangularExact
      FlatAdjoint.selectedFlatGaugeRowCarrier
      FlatAdjoint.selectedFlatGaugeRowCarrier
      Contraction.flatGreenKernelMatrix
      (Perturbation.gaugeGramPerturbationMatrix background)
      multiplier row
  in
  trans kernelCong
    (trans compose
      (flatGreenMatrixActsAsExactGreen
        (selectedGaugeGramPerturbationApply background multiplier) row))

------------------------------------------------------------------------
-- Core factorization G_0 K_A^reg = M_A.
------------------------------------------------------------------------

regularizedBackgroundFactorThroughResidual :
  ∀ background multiplier row →
  FlatGreen.regularizedFlatGaugeGreen
    (Operator.regularizedBackgroundGaugeGramApply background multiplier) row
  ≡ FiniteReopen.selectedResidualIdentityPlusMatrix background
      `applied-to` multiplier row
  where
  infix 5 _`applied-to`_
  _`applied-to`_ :
    (FlatAdjoint.GaugeMultiplier → FlatAdjoint.GaugeMultiplier) →
    GaugeMultiplier → GaugeMultiplier
  operator `applied-to` vector = operator vector
regularizedBackgroundFactorThroughResidual background multiplier
    (pair coordinate site) =
  let
    row = pair coordinate site

    decomposition = Operator.selectedBackgroundBasedGaugeOperatorDecomposition
      background multiplier coordinate site

    greenCong :
      FlatGreen.regularizedFlatGaugeGreen
        (Operator.regularizedBackgroundGaugeGramApply background multiplier) row
      ≡ FlatGreen.regularizedFlatGaugeGreen
          (λ selected →
            FlatGreen.regularizedFlatGaugeGramApply multiplier selected
              + Operator.explicitGaugeGramPerturbation
                  background multiplier selected) row
    greenCong =
      let
        pointwise : ∀ selected →
          Operator.regularizedBackgroundGaugeGramApply background multiplier selected
          ≡ FlatGreen.regularizedFlatGaugeGramApply multiplier selected
            + Operator.explicitGaugeGramPerturbation background multiplier selected
        pointwise (pair c s) =
          Operator.selectedBackgroundBasedGaugeOperatorDecomposition
            background multiplier c s
      in
      DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact.scalarGreenRespectsPointwise
        (λ current → pointwise (pair coordinate current)) site

    splitGreen :
      FlatGreen.regularizedFlatGaugeGreen
        (λ selected →
          FlatGreen.regularizedFlatGaugeGramApply multiplier selected
            + Operator.explicitGaugeGramPerturbation background multiplier selected) row
      ≡ FlatGreen.regularizedFlatGaugeGreen
          (FlatGreen.regularizedFlatGaugeGramApply multiplier) row
        + FlatGreen.regularizedFlatGaugeGreen
          (Operator.explicitGaugeGramPerturbation background multiplier) row
    splitGreen =
      let
        green = DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact.scalarGreen
        field0 = FlatAdjoint.multiplierField
          (FlatGreen.regularizedFlatGaugeGramApply multiplier) coordinate
        fieldE = FlatAdjoint.multiplierField
          (Operator.explicitGaugeGramPerturbation background multiplier) coordinate
      in
      DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact.scalarGreenAdd
        field0 fieldE site

    flatLeft = FlatGreen.regularizedFlatGaugeGreenLeftInverse
      multiplier coordinate site

    residualExact :
      FlatGreen.regularizedFlatGaugeGreen
        (Operator.explicitGaugeGramPerturbation background multiplier) row
      ≡ Residual.residualApply background multiplier row
    residualExact =
      sym
        (trans
          (selectedResidualActsAsFlatGreenEA background multiplier row)
          (cong
            (λ source → FlatGreen.regularizedFlatGaugeGreen source row)
            (funextPointwise
              (selectedGaugeGramPerturbationApply background multiplier)
              (Operator.explicitGaugeGramPerturbation background multiplier)
              (selectedGaugeGramPerturbationActsAsExplicitEA background multiplier))))
      where
      funextPointwise : ∀ {A : Set} (left right : A → ℚ) →
        (∀ x → left x ≡ right x) → left ≡ right
      funextPointwise left right pointwise =
        DASHI.Physics.YangMills.BalabanFunctionExtensionality.functionExtensionality pointwise
  in
  trans greenCong
    (trans splitGreen
      (trans
        (cong₂ _+_ flatLeft residualExact)
        refl))

selectedBackgroundGaugeGreenLevel : ProofLevel
selectedBackgroundGaugeGreenLevel = conditional
