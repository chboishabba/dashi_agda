module DASHI.Physics.YangMills.BalabanSelectedProjectedSchurGreenFiniteExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrodinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- DASHI CONTRIBUTION
--
-- Complete the finite exact inverse of the physically projected gauge Schur
-- operator.  Define the padded gauge Schur extension
--
--       S~_A = K_0^reg + P_g Q_A,
--
-- with Q_A = E_A - (1/256) C_A C_A^T.  The previous same-object and flat
-- Fourier Green theorems imply pointwise
--
--       G_0 S~_A = I + G_0 P_g Q_A.
--
-- A proof-relevant finite inverse certificate for the right side therefore
-- defines
--
--       G_A^Schur = (I + G_0 P_g Q_A)^-1 G_0.
--
-- Both left and right inverse identities for S~_A are proved exactly.  The
-- right inverse uses injectivity of the already-proved flat Green, exactly as
-- in the background-gauge Green construction.  No infinite Neumann limit and
-- no abstract pseudoinverse are introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as ScalarGreen
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as FlatKernel
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFiniteRationalReopeningExact as Carrier
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGreenFiniteExact as ExistingGreen
import DASHI.Physics.YangMills.BalabanSelectedProjectedSchurPerturbationContractionExact as Projected
import DASHI.Physics.YangMills.BalabanSelectedProjectedSchurFiniteRationalReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical

GaugeMultiplier : Set
GaugeMultiplier = FlatAdjoint.GaugeMultiplier

------------------------------------------------------------------------
-- S~_A = K_0^reg + P_g Q_A.
------------------------------------------------------------------------

projectedPaddedSchurApply :
  Physical.RationalSU2Background4 → GaugeMultiplier → GaugeMultiplier
projectedPaddedSchurApply background multiplier row =
  FlatGreen.regularizedFlatGaugeGramApply multiplier row
  + Projected.projectedSchurPerturbationApply background multiplier row

flatGreenOfProjectedSchurDecomposition :
  ∀ background multiplier coordinate site →
  FlatGreen.regularizedFlatGaugeGreen
    (projectedPaddedSchurApply background multiplier)
    (Torus.pair coordinate site)
  ≡ FlatGreen.regularizedFlatGaugeGreen
      (FlatGreen.regularizedFlatGaugeGramApply multiplier)
      (Torus.pair coordinate site)
    + FlatGreen.regularizedFlatGaugeGreen
      (Projected.projectedSchurPerturbationApply background multiplier)
      (Torus.pair coordinate site)
flatGreenOfProjectedSchurDecomposition background multiplier coordinate site =
  let
    totalField = FlatAdjoint.multiplierField
      (projectedPaddedSchurApply background multiplier) coordinate
    flatField = FlatAdjoint.multiplierField
      (FlatGreen.regularizedFlatGaugeGramApply multiplier) coordinate
    perturbationField = FlatAdjoint.multiplierField
      (Projected.projectedSchurPerturbationApply background multiplier) coordinate

    sourcePointwise : ∀ current →
      totalField current ≡ flatField current + perturbationField current
    sourcePointwise current = refl
  in
  trans
    (ScalarGreen.scalarGreenRespectsPointwise sourcePointwise site)
    (ScalarGreen.scalarGreenAdd flatField perturbationField site)

------------------------------------------------------------------------
-- The projected residual kernel is exactly G_0 P_g Q_A on vectors.
------------------------------------------------------------------------

projectedResidualAsRectangularCompose : ∀ background row column →
  Projected.projectedSchurResidual background row column
  ≡ Rect.composeRectangular Carrier.gaugeFiniteCoordinates
      FlatKernel.flatGreenKernelMatrix
      (Projected.projectedSchurPerturbation background)
      row column
projectedResidualAsRectangularCompose background row column = refl

projectedResidualActsAsFlatGreenProjectedQ :
  ∀ background multiplier row →
  Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
    (Projected.projectedSchurResidual background) multiplier row
  ≡ FlatGreen.regularizedFlatGaugeGreen
      (Projected.projectedSchurPerturbationApply background multiplier) row
projectedResidualActsAsFlatGreenProjectedQ background multiplier row =
  let
    identify :
      Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
        (Projected.projectedSchurResidual background) multiplier row
      ≡ Rect.applyRectangular Carrier.gaugeFiniteCoordinates
          (Rect.composeRectangular Carrier.gaugeFiniteCoordinates
            FlatKernel.flatGreenKernelMatrix
            (Projected.projectedSchurPerturbation background))
          multiplier row
    identify = Sums.sumRationalCong Projected.gaugeRows _ _
      (λ column → cong (_* multiplier column)
        (projectedResidualAsRectangularCompose background row column))

    compose = Rect.applyComposeRectangularExact
      Carrier.gaugeFiniteCoordinates Carrier.gaugeFiniteCoordinates
      FlatKernel.flatGreenKernelMatrix
      (Projected.projectedSchurPerturbation background)
      multiplier row

    kernelExact : ∀ selected →
      Rect.applyRectangular Carrier.gaugeFiniteCoordinates
        FlatKernel.flatGreenKernelMatrix
        (Projected.projectedSchurPerturbationApply background multiplier)
        selected
      ≡ FlatGreen.regularizedFlatGaugeGreen
          (Projected.projectedSchurPerturbationApply background multiplier)
          selected
    kernelExact (Torus.pair c s) =
      FlatKernel.flatGreenKernelActsExactly
        (Projected.projectedSchurPerturbationApply background multiplier) c s
  in
  trans identify (trans compose (kernelExact row))

------------------------------------------------------------------------
-- G_0 S~_A = I + R_A^red.
------------------------------------------------------------------------

flatGreenProjectedSchurFactorization :
  ∀ background multiplier coordinate site →
  FlatGreen.regularizedFlatGaugeGreen
    (projectedPaddedSchurApply background multiplier)
    (Torus.pair coordinate site)
  ≡ Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
      (Reopen.projectedSchurIdentityPlusMatrix background)
      multiplier (Torus.pair coordinate site)
flatGreenProjectedSchurFactorization background multiplier coordinate site =
  let
    row = Torus.pair coordinate site
    split = flatGreenOfProjectedSchurDecomposition
      background multiplier coordinate site

    flatLeft = FlatGreen.regularizedFlatGaugeGreenLeftInverse
      multiplier coordinate site

    residual = projectedResidualActsAsFlatGreenProjectedQ
      background multiplier row

    identityPlus =
      Reopen.projectedSchurIdentityPlusMatrixActionExact
        background multiplier row
  in
  trans split
    (trans
      (cong₂ _+_ flatLeft (sym residual))
      (sym identityPlus))

------------------------------------------------------------------------
-- Exact projected Schur Green.
------------------------------------------------------------------------

selectedProjectedSchurGreen :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    Carrier.gaugeFiniteCoordinates
    (Reopen.projectedSchurIdentityPlusMatrix background) →
  GaugeMultiplier → GaugeMultiplier
selectedProjectedSchurGreen background certificate source =
  Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
    (Matrix.inverseMatrix certificate)
    (FlatGreen.regularizedFlatGaugeGreen source)

selectedProjectedSchurGreenLeftInverse :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Carrier.gaugeFiniteCoordinates
      (Reopen.projectedSchurIdentityPlusMatrix background))
    multiplier coordinate site →
  selectedProjectedSchurGreen background certificate
    (projectedPaddedSchurApply background multiplier)
    (Torus.pair coordinate site)
  ≡ multiplier (Torus.pair coordinate site)
selectedProjectedSchurGreenLeftInverse
    background certificate multiplier coordinate site =
  let
    factor : ∀ row →
      FlatGreen.regularizedFlatGaugeGreen
        (projectedPaddedSchurApply background multiplier) row
      ≡ Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
          (Reopen.projectedSchurIdentityPlusMatrix background)
          multiplier row
    factor (Torus.pair c s) =
      flatGreenProjectedSchurFactorization background multiplier c s
  in
  trans
    (ExistingGreen.matrixApplyRespectsPointwise
      Carrier.gaugeFiniteCoordinates
      (Matrix.inverseMatrix certificate)
      (FlatGreen.regularizedFlatGaugeGreen
        (projectedPaddedSchurApply background multiplier))
      (Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
        (Reopen.projectedSchurIdentityPlusMatrix background) multiplier)
      factor
      (Torus.pair coordinate site))
    (Matrix.matrixInverseLeftExact certificate multiplier
      (Torus.pair coordinate site))

selectedProjectedSchurGreenRightInverse :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Carrier.gaugeFiniteCoordinates
      (Reopen.projectedSchurIdentityPlusMatrix background))
    source row →
  projectedPaddedSchurApply background
    (selectedProjectedSchurGreen background certificate source) row
  ≡ source row
selectedProjectedSchurGreenRightInverse background certificate source =
  let
    solution = selectedProjectedSchurGreen background certificate source

    factorLeft : ∀ row →
      FlatGreen.regularizedFlatGaugeGreen
        (projectedPaddedSchurApply background solution) row
      ≡ Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
          (Reopen.projectedSchurIdentityPlusMatrix background)
          solution row
    factorLeft (Torus.pair coordinate site) =
      flatGreenProjectedSchurFactorization background solution coordinate site

    inverseRight : ∀ row →
      Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
        (Reopen.projectedSchurIdentityPlusMatrix background)
        solution row
      ≡ FlatGreen.regularizedFlatGaugeGreen source row
    inverseRight row = Matrix.matrixInverseRightExact certificate
      (FlatGreen.regularizedFlatGaugeGreen source) row

    greenEqual : ∀ row →
      FlatGreen.regularizedFlatGaugeGreen
        (projectedPaddedSchurApply background solution) row
      ≡ FlatGreen.regularizedFlatGaugeGreen source row
    greenEqual row = trans (factorLeft row) (inverseRight row)
  in
  ExistingGreen.regularizedFlatGaugeGreenInjective
    (projectedPaddedSchurApply background solution)
    source greenEqual

record SelectedProjectedSchurGreenCertificate
    (background : Physical.RationalSU2Background4) : Set₁ where
  field
    residualInverse : Matrix.RationalMatrixInverseCertificate
      Carrier.gaugeFiniteCoordinates
      (Reopen.projectedSchurIdentityPlusMatrix background)
    green : GaugeMultiplier → GaugeMultiplier
    greenExact : ∀ source row →
      green source row
      ≡ selectedProjectedSchurGreen background residualInverse source row
    leftInverse : ∀ source row →
      green (projectedPaddedSchurApply background source) row ≡ source row
    rightInverse : ∀ source row →
      projectedPaddedSchurApply background (green source) row ≡ source row

selectedProjectedSchurGreenCertificate :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Carrier.gaugeFiniteCoordinates
      (Reopen.projectedSchurIdentityPlusMatrix background)) →
  SelectedProjectedSchurGreenCertificate background
selectedProjectedSchurGreenCertificate background certificate = record
  { SelectedProjectedSchurGreenCertificate.residualInverse = certificate
  ; SelectedProjectedSchurGreenCertificate.green =
      selectedProjectedSchurGreen background certificate
  ; SelectedProjectedSchurGreenCertificate.greenExact = λ source row → refl
  ; SelectedProjectedSchurGreenCertificate.leftInverse =
      selectedProjectedSchurGreenLeftInverse background certificate
  ; SelectedProjectedSchurGreenCertificate.rightInverse =
      selectedProjectedSchurGreenRightInverse background certificate
  }

selectedProjectedSchurFactorizationLevel : ProofLevel
selectedProjectedSchurFactorizationLevel = machineChecked

selectedProjectedSchurGreenLeftInverseLevel : ProofLevel
selectedProjectedSchurGreenLeftInverseLevel = machineChecked

selectedProjectedSchurGreenRightInverseLevel : ProofLevel
selectedProjectedSchurGreenRightInverseLevel = machineChecked
