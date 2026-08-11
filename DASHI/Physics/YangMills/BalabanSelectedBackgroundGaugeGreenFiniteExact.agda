module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGreenFiniteExact where

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
-- This is the finite exact-inverse closure promised by the Round-42 residual
-- estimates.  With
--
--       K_A^reg = K_0^reg + E_A,
--       R_A     = G_0 E_A,
--       M_A     = I + R_A,
--
-- the previous modules prove the literal action identity
--
--       G_0 K_A^reg = M_A.
--
-- A finite rational inverse certificate for M_A therefore defines
--
--       G_A := M_A^-1 G_0.
--
-- Both
--
--       G_A K_A^reg = I
-- and
--       K_A^reg G_A = I
--
-- are proved pointwise.  The second direction uses injectivity of the already
-- exact flat Green: if G_0 a=G_0 b, applying the configured flat operator and
-- its proved right-inverse gives a=b.  No Neumann limit is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact as Reindex
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact as Vec
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed as Kernel
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as ScalarGreen
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact as FlatGreen
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeOperatorDecompositionExact as Operator
import DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualActionExact as ResidualAction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualReopeningExact as Reopening
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFiniteRationalReopeningExact as FiniteReopen
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical

GaugeMultiplier : Set
GaugeMultiplier = FlatAdjoint.GaugeMultiplier

------------------------------------------------------------------------
-- G_0 K_A^reg = I + R_A, pointwise and without extensionality.
------------------------------------------------------------------------

flatGreenOfBackgroundDecomposition :
  ∀ background multiplier coordinate site →
  FlatGreen.regularizedFlatGaugeGreen
    (Operator.regularizedBackgroundGaugeGramApply background multiplier)
    (Torus.pair coordinate site)
  ≡ FlatGreen.regularizedFlatGaugeGreen
      (FlatGreen.regularizedFlatGaugeGramApply multiplier)
      (Torus.pair coordinate site)
    + FlatGreen.regularizedFlatGaugeGreen
      (Operator.explicitGaugeGramPerturbation background multiplier)
      (Torus.pair coordinate site)
flatGreenOfBackgroundDecomposition background multiplier coordinate site =
  let
    backgroundField =
      FlatAdjoint.multiplierField
        (Operator.regularizedBackgroundGaugeGramApply background multiplier)
        coordinate

    flatField =
      FlatAdjoint.multiplierField
        (FlatGreen.regularizedFlatGaugeGramApply multiplier) coordinate

    perturbationField =
      FlatAdjoint.multiplierField
        (Operator.explicitGaugeGramPerturbation background multiplier) coordinate

    sourcePointwise : ∀ current →
      backgroundField current ≡ flatField current + perturbationField current
    sourcePointwise current =
      Operator.selectedBackgroundBasedGaugeOperatorDecomposition
        background multiplier coordinate current
  in
  trans
    (ScalarGreen.scalarGreenRespectsPointwise sourcePointwise site)
    (ScalarGreen.scalarGreenAdd flatField perturbationField site)

flatGreenBackgroundFactorization :
  ∀ background multiplier coordinate site →
  FlatGreen.regularizedFlatGaugeGreen
    (Operator.regularizedBackgroundGaugeGramApply background multiplier)
    (Torus.pair coordinate site)
  ≡ Reopening.unweightedIdentityPlusResidualApply background multiplier
      (Torus.pair coordinate site)
flatGreenBackgroundFactorization background multiplier coordinate site =
  let
    row = Torus.pair coordinate site
    split = flatGreenOfBackgroundDecomposition
      background multiplier coordinate site

    flatLeft = FlatGreen.regularizedFlatGaugeGreenLeftInverse
      multiplier coordinate site

    residual = ResidualAction.selectedResidualActsAsExplicitFlatGreenEA
      background multiplier coordinate site
  in
  trans split
    (cong₂ _+_ flatLeft (sym residual))

flatGreenBackgroundFactorizationAsMatrix :
  ∀ background multiplier coordinate site →
  FlatGreen.regularizedFlatGaugeGreen
    (Operator.regularizedBackgroundGaugeGramApply background multiplier)
    (Torus.pair coordinate site)
  ≡ Matrix.applyMatrix FiniteReopen.gaugeFiniteCoordinates
      (FiniteReopen.selectedResidualIdentityPlusMatrix background)
      multiplier (Torus.pair coordinate site)
flatGreenBackgroundFactorizationAsMatrix background multiplier coordinate site =
  trans
    (flatGreenBackgroundFactorization background multiplier coordinate site)
    (sym
      (FiniteReopen.selectedResidualIdentityPlusMatrixActionExact
        background multiplier (Torus.pair coordinate site)))

------------------------------------------------------------------------
-- Exact background Green.
------------------------------------------------------------------------

selectedBackgroundRegularizedGaugeGreen :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    FiniteReopen.gaugeFiniteCoordinates
    (FiniteReopen.selectedResidualIdentityPlusMatrix background) →
  GaugeMultiplier → GaugeMultiplier
selectedBackgroundRegularizedGaugeGreen background certificate source =
  Matrix.applyMatrix FiniteReopen.gaugeFiniteCoordinates
    (Matrix.inverseMatrix certificate)
    (FlatGreen.regularizedFlatGaugeGreen source)

matrixApplyRespectsPointwise :
  ∀ {Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    (matrix : Matrix.RationalMatrix Index)
    left right →
  (∀ column → left column ≡ right column) →
  ∀ row →
  Matrix.applyMatrix carrier matrix left row
  ≡ Matrix.applyMatrix carrier matrix right row
matrixApplyRespectsPointwise carrier matrix left right pointwise row =
  Sums.sumRationalCong (Matrix.coordinates carrier) _ _
    (λ column → cong (matrix row column *_) (pointwise column))

selectedBackgroundGaugeGreenLeftInverse :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      FiniteReopen.gaugeFiniteCoordinates
      (FiniteReopen.selectedResidualIdentityPlusMatrix background))
    multiplier coordinate site →
  selectedBackgroundRegularizedGaugeGreen background certificate
    (Operator.regularizedBackgroundGaugeGramApply background multiplier)
    (Torus.pair coordinate site)
  ≡ multiplier (Torus.pair coordinate site)
selectedBackgroundGaugeGreenLeftInverse
    background certificate multiplier coordinate site =
  let
    factor : ∀ row →
      FlatGreen.regularizedFlatGaugeGreen
        (Operator.regularizedBackgroundGaugeGramApply background multiplier) row
      ≡ Matrix.applyMatrix FiniteReopen.gaugeFiniteCoordinates
          (FiniteReopen.selectedResidualIdentityPlusMatrix background)
          multiplier row
    factor (Torus.pair c s) =
      flatGreenBackgroundFactorizationAsMatrix background multiplier c s
  in
  trans
    (matrixApplyRespectsPointwise
      FiniteReopen.gaugeFiniteCoordinates
      (Matrix.inverseMatrix certificate)
      (FlatGreen.regularizedFlatGaugeGreen
        (Operator.regularizedBackgroundGaugeGramApply background multiplier))
      (Matrix.applyMatrix FiniteReopen.gaugeFiniteCoordinates
        (FiniteReopen.selectedResidualIdentityPlusMatrix background) multiplier)
      factor
      (Torus.pair coordinate site))
    (Matrix.matrixInverseLeftExact certificate multiplier
      (Torus.pair coordinate site))

------------------------------------------------------------------------
-- The explicit flat Green is injective pointwise.
------------------------------------------------------------------------

configuredSiteOperatorRespectsPointwise :
  ∀ {left right} →
  (∀ site → left site ≡ right site) →
  ∀ row →
  ScalarGreen.configuredSiteOperator left row
  ≡ ScalarGreen.configuredSiteOperator right row
configuredSiteOperatorRespectsPointwise pointwise row =
  cong₂ _+_
    (Sums.sumRationalCong (Torus.allCyclicIndices Torus.four) _ _
      (λ axis → cong₂ _-_
        (cong₂ _+_ (pointwise row) (pointwise row))
        (cong₂ _+_
          (pointwise (Reindex.shiftForward4 axis row))
          (pointwise (Reindex.shiftBackward4 axis row)))))
    (trans
      (GlobalAverage.average0123EqualsGlobalMean left row)
      (trans
        (cong
          (Kernel.oneTwoFiftySix *_)
          (Vec.siteSum4Cong left right pointwise))
        (sym (GlobalAverage.average0123EqualsGlobalMean right row))))

regularizedFlatGaugeGreenInjective :
  ∀ left right →
  (∀ row →
    FlatGreen.regularizedFlatGaugeGreen left row
    ≡ FlatGreen.regularizedFlatGaugeGreen right row) →
  ∀ row → left row ≡ right row
regularizedFlatGaugeGreenInjective left right equal
    (Torus.pair coordinate site) =
  let
    leftGreen = FlatAdjoint.multiplierField
      (FlatGreen.regularizedFlatGaugeGreen left) coordinate
    rightGreen = FlatAdjoint.multiplierField
      (FlatGreen.regularizedFlatGaugeGreen right) coordinate

    greenEqual : ∀ current → leftGreen current ≡ rightGreen current
    greenEqual current = equal (Torus.pair coordinate current)

    configuredEqual = configuredSiteOperatorRespectsPointwise greenEqual site

    leftRightInverse = FlatGreen.regularizedFlatGaugeGreenRightInverse
      left coordinate site
    rightRightInverse = FlatGreen.regularizedFlatGaugeGreenRightInverse
      right coordinate site
  in
  trans
    (sym leftRightInverse)
    (trans configuredEqual rightRightInverse)

selectedBackgroundGaugeGreenRightInverse :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      FiniteReopen.gaugeFiniteCoordinates
      (FiniteReopen.selectedResidualIdentityPlusMatrix background))
    source row →
  Operator.regularizedBackgroundGaugeGramApply background
    (selectedBackgroundRegularizedGaugeGreen background certificate source) row
  ≡ source row
selectedBackgroundGaugeGreenRightInverse background certificate source =
  let
    solution = selectedBackgroundRegularizedGaugeGreen background certificate source

    factorLeft : ∀ row →
      FlatGreen.regularizedFlatGaugeGreen
        (Operator.regularizedBackgroundGaugeGramApply background solution) row
      ≡ Matrix.applyMatrix FiniteReopen.gaugeFiniteCoordinates
          (FiniteReopen.selectedResidualIdentityPlusMatrix background)
          solution row
    factorLeft (Torus.pair coordinate site) =
      flatGreenBackgroundFactorizationAsMatrix background solution coordinate site

    inverseRight : ∀ row →
      Matrix.applyMatrix FiniteReopen.gaugeFiniteCoordinates
        (FiniteReopen.selectedResidualIdentityPlusMatrix background)
        solution row
      ≡ FlatGreen.regularizedFlatGaugeGreen source row
    inverseRight row = Matrix.matrixInverseRightExact certificate
      (FlatGreen.regularizedFlatGaugeGreen source) row

    greenEqual : ∀ row →
      FlatGreen.regularizedFlatGaugeGreen
        (Operator.regularizedBackgroundGaugeGramApply background solution) row
      ≡ FlatGreen.regularizedFlatGaugeGreen source row
    greenEqual row = trans (factorLeft row) (inverseRight row)
  in
  regularizedFlatGaugeGreenInjective
    (Operator.regularizedBackgroundGaugeGramApply background solution)
    source greenEqual

record SelectedBackgroundRegularizedGaugeGreenCertificate
    (background : Physical.RationalSU2Background4) : Set₁ where
  field
    residualInverse : Matrix.RationalMatrixInverseCertificate
      FiniteReopen.gaugeFiniteCoordinates
      (FiniteReopen.selectedResidualIdentityPlusMatrix background)
    green : GaugeMultiplier → GaugeMultiplier
    greenExact : ∀ source row →
      green source row
      ≡ selectedBackgroundRegularizedGaugeGreen
          background residualInverse source row
    leftInverse : ∀ source row →
      green (Operator.regularizedBackgroundGaugeGramApply background source) row
      ≡ source row
    rightInverse : ∀ source row →
      Operator.regularizedBackgroundGaugeGramApply background (green source) row
      ≡ source row

selectedBackgroundRegularizedGaugeGreenCertificate :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      FiniteReopen.gaugeFiniteCoordinates
      (FiniteReopen.selectedResidualIdentityPlusMatrix background)) →
  SelectedBackgroundRegularizedGaugeGreenCertificate background
selectedBackgroundRegularizedGaugeGreenCertificate background certificate = record
  { SelectedBackgroundRegularizedGaugeGreenCertificate.residualInverse = certificate
  ; SelectedBackgroundRegularizedGaugeGreenCertificate.green =
      selectedBackgroundRegularizedGaugeGreen background certificate
  ; SelectedBackgroundRegularizedGaugeGreenCertificate.greenExact = λ source row → refl
  ; SelectedBackgroundRegularizedGaugeGreenCertificate.leftInverse =
      selectedBackgroundGaugeGreenLeftInverse background certificate
  ; SelectedBackgroundRegularizedGaugeGreenCertificate.rightInverse =
      selectedBackgroundGaugeGreenRightInverse background certificate
  }

selectedBackgroundGaugeGreenFactorizationLevel : ProofLevel
selectedBackgroundGaugeGreenFactorizationLevel = machineChecked

selectedBackgroundGaugeGreenLeftInverseLevel : ProofLevel
selectedBackgroundGaugeGreenLeftInverseLevel = machineChecked

selectedBackgroundGaugeGreenRightInverseLevel : ProofLevel
selectedBackgroundGaugeGreenRightInverseLevel = machineChecked
