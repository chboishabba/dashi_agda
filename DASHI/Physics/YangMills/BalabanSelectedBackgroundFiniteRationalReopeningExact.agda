module DASHI.Physics.YangMills.BalabanSelectedBackgroundFiniteRationalReopeningExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Put the already-proved selected residual on an actual complete finite
-- rational coordinate carrier.  The matrix
--
--       M_A = I + G_0 E_A
--
-- is constructed entrywise, its action is proved to be exactly the selected
-- reopening operator, and the previous strict-contraction theorem proves it
-- pointwise injective.  The same is done for the rationally weighted conjugate
-- D M_A D^-1.
--
-- The only imported step is the standard finite-dimensional theorem that an
-- injective square rational matrix is invertible.  Once its proof-relevant
-- certificate is supplied, this module proves the actual inverse actions obey
--
--       ||M_A^-1 y||_1 <= (10/9)||y||_1
--
-- and
--       ||(D M_A D^-1)^-1 y||_1 <= (6/5)||y||_1.
--
-- No infinite series and no completeness of Q are used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _*_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Strict
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRationalInjectiveInverseExact as FiniteInverse
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Contraction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalCombesThomasWeightExact as Weight
import DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualReopeningExact as Reopening
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeRow : Set
GaugeRow = Contraction.GaugeRow

GaugeVector : Set
GaugeVector = GaugeRow → ℚ

gaugeRowSelector : Basis.FiniteSelector GaugeRow
gaugeRowSelector = Rows.selectedGaugeRowFiniteSelector

gaugeFiniteCoordinates : Matrix.FiniteRationalCoordinates GaugeRow
gaugeFiniteCoordinates = record
  { Matrix.FiniteRationalCoordinates.coordinates =
      Basis.elements gaugeRowSelector
  ; Matrix.FiniteRationalCoordinates.delta =
      λ row column →
        Basis.kronecker (Basis.decide gaugeRowSelector) column row
  ; Matrix.FiniteRationalCoordinates.deltaActsAsIdentity = deltaExact
  }
  where
  deltaExact : ∀ vector row →
    Sums.sumRational (Basis.elements gaugeRowSelector)
      (λ column →
        Basis.kronecker (Basis.decide gaugeRowSelector) column row
          * vector column)
    ≡ vector row
  deltaExact vector row =
    trans
      (Sums.sumRationalCong
        (Basis.elements gaugeRowSelector) _ _
        (λ column →
          ℚP.*-comm
            (Basis.kronecker (Basis.decide gaugeRowSelector) column row)
            (vector column)))
      (Basis.selectorExact gaugeRowSelector vector row)

identityPlusKernel :
  (GaugeRow → GaugeRow → ℚ) → GaugeRow → GaugeRow → ℚ
identityPlusKernel residual row column =
  Matrix.delta gaugeFiniteCoordinates row column + residual row column

identityPlusKernelActionExact :
  ∀ residual vector row →
  Matrix.applyMatrix gaugeFiniteCoordinates
    (identityPlusKernel residual) vector row
  ≡ vector row
    + Matrix.applyMatrix gaugeFiniteCoordinates residual vector row
identityPlusKernelActionExact residual vector row =
  let
    deltaTerm = λ column →
      Matrix.delta gaugeFiniteCoordinates row column * vector column
    residualTerm = λ column → residual row column * vector column

    expand :
      Matrix.applyMatrix gaugeFiniteCoordinates
        (identityPlusKernel residual) vector row
      ≡ Sums.sumRational (Matrix.coordinates gaugeFiniteCoordinates)
          (λ column → deltaTerm column + residualTerm column)
    expand = Sums.sumRationalCong
      (Matrix.coordinates gaugeFiniteCoordinates) _ _
      (λ column → ℚRing.solve-∀
        (Matrix.delta gaugeFiniteCoordinates row column)
        (residual row column)
        (vector column))

    split = Mass.sumAddExact
      (Matrix.coordinates gaugeFiniteCoordinates)
      deltaTerm residualTerm
  in
  trans expand
    (trans split
      (cong
        (_+ Matrix.applyMatrix gaugeFiniteCoordinates residual vector row)
        (Matrix.deltaActsAsIdentity gaugeFiniteCoordinates vector row)))

selectedResidualIdentityPlusMatrix :
  Physical.RationalSU2Background4 → Matrix.RationalMatrix GaugeRow
selectedResidualIdentityPlusMatrix background =
  identityPlusKernel
    (Contraction.flatGreenTimesPerturbationKernel background)

selectedResidualIdentityPlusMatrixActionExact :
  ∀ background vector row →
  Matrix.applyMatrix gaugeFiniteCoordinates
    (selectedResidualIdentityPlusMatrix background) vector row
  ≡ Reopening.unweightedIdentityPlusResidualApply background vector row
selectedResidualIdentityPlusMatrixActionExact background vector row =
  identityPlusKernelActionExact
    (Contraction.flatGreenTimesPerturbationKernel background) vector row

selectedResidualIdentityPlusMatrixInjective :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  FiniteInverse.PointwiseInjective gaugeFiniteCoordinates
    (selectedResidualIdentityPlusMatrix background)
selectedResidualIdentityPlusMatrixInjective
    background radius left right equal row =
  Reopening.selectedBackgroundResidualIdentityPlusInjective
    background radius left right
    (λ selected →
      trans
        (sym
          (selectedResidualIdentityPlusMatrixActionExact
            background left selected))
        (trans
          (equal selected)
          (selectedResidualIdentityPlusMatrixActionExact
            background right selected)))
    row

selectedResidualIdentityPlusRationalInverse :
  FiniteInverse.FiniteRationalInjectiveInverseAuthority →
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  Matrix.RationalMatrixInverseCertificate gaugeFiniteCoordinates
    (selectedResidualIdentityPlusMatrix background)
selectedResidualIdentityPlusRationalInverse authority background radius =
  FiniteInverse.finiteSquareInjectiveImpliesRationalInverse authority
    gaugeFiniteCoordinates
    (selectedResidualIdentityPlusMatrix background)
    (selectedResidualIdentityPlusMatrixInjective background radius)

selectedResidualInverseApply :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate gaugeFiniteCoordinates
    (selectedResidualIdentityPlusMatrix background) →
  GaugeVector → GaugeVector
selectedResidualInverseApply background certificate =
  Matrix.applyMatrix gaugeFiniteCoordinates
    (Matrix.inverseMatrix certificate)

selectedResidualInverseTenNinths :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  (certificate : Matrix.RationalMatrixInverseCertificate
    gaugeFiniteCoordinates (selectedResidualIdentityPlusMatrix background)) →
  ∀ source →
  let solution = selectedResidualInverseApply background certificate source in
  L1.vectorL1 Contraction.gaugeRows solution
  ≤ Reopening.tenNinths * L1.vectorL1 Contraction.gaugeRows source
selectedResidualInverseTenNinths background radius certificate source =
  let
    solution = selectedResidualInverseApply background certificate source

    equation :
      Reopening.UnweightedReopeningEquation background solution source
    equation row =
      trans
        (sym
          (selectedResidualIdentityPlusMatrixActionExact
            background solution row))
        (Matrix.matrixInverseRightExact certificate source row)
  in
  Reopening.selectedBackgroundResidualReopeningTenNinths
    background radius solution source equation

------------------------------------------------------------------------
-- Weighted finite reopening.
------------------------------------------------------------------------

selectedWeightedIdentityPlusMatrix :
  GaugeRow → Physical.RationalSU2Background4 → Matrix.RationalMatrix GaugeRow
selectedWeightedIdentityPlusMatrix root background =
  identityPlusKernel
    (Weight.weightedSelectedBackgroundResidual root background)

selectedWeightedIdentityPlusMatrixActionExact :
  ∀ root background vector row →
  Matrix.applyMatrix gaugeFiniteCoordinates
    (selectedWeightedIdentityPlusMatrix root background) vector row
  ≡ Reopening.weightedIdentityPlusResidualApply root background vector row
selectedWeightedIdentityPlusMatrixActionExact root background vector row =
  identityPlusKernelActionExact
    (Weight.weightedSelectedBackgroundResidual root background) vector row

selectedWeightedIdentityPlusMatrixInjective :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root →
  FiniteInverse.PointwiseInjective gaugeFiniteCoordinates
    (selectedWeightedIdentityPlusMatrix root background)
selectedWeightedIdentityPlusMatrixInjective
    background radius root left right equal row =
  Reopening.selectedBackgroundWeightedResidualIdentityPlusInjective
    background radius root left right
    (λ selected →
      trans
        (sym
          (selectedWeightedIdentityPlusMatrixActionExact
            root background left selected))
        (trans
          (equal selected)
          (selectedWeightedIdentityPlusMatrixActionExact
            root background right selected)))
    row

selectedWeightedIdentityPlusRationalInverse :
  FiniteInverse.FiniteRationalInjectiveInverseAuthority →
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root →
  Matrix.RationalMatrixInverseCertificate gaugeFiniteCoordinates
    (selectedWeightedIdentityPlusMatrix root background)
selectedWeightedIdentityPlusRationalInverse authority background radius root =
  FiniteInverse.finiteSquareInjectiveImpliesRationalInverse authority
    gaugeFiniteCoordinates
    (selectedWeightedIdentityPlusMatrix root background)
    (selectedWeightedIdentityPlusMatrixInjective background radius root)

selectedWeightedResidualInverseApply :
  ∀ root background →
  Matrix.RationalMatrixInverseCertificate gaugeFiniteCoordinates
    (selectedWeightedIdentityPlusMatrix root background) →
  GaugeVector → GaugeVector
selectedWeightedResidualInverseApply root background certificate =
  Matrix.applyMatrix gaugeFiniteCoordinates
    (Matrix.inverseMatrix certificate)

selectedWeightedResidualInverseSixFifths :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root
    (certificate : Matrix.RationalMatrixInverseCertificate
      gaugeFiniteCoordinates (selectedWeightedIdentityPlusMatrix root background)) →
  ∀ source →
  let solution =
        selectedWeightedResidualInverseApply root background certificate source
  in
  L1.vectorL1 Contraction.gaugeRows solution
  ≤ Strict.sixFifths * L1.vectorL1 Contraction.gaugeRows source
selectedWeightedResidualInverseSixFifths
    background radius root certificate source =
  let
    solution =
      selectedWeightedResidualInverseApply root background certificate source

    equation :
      Reopening.WeightedReopeningEquation root background solution source
    equation row =
      trans
        (sym
          (selectedWeightedIdentityPlusMatrixActionExact
            root background solution row))
        (Matrix.matrixInverseRightExact certificate source row)
  in
  Reopening.selectedBackgroundWeightedResidualReopeningSixFifths
    background radius root solution source equation

selectedFiniteGaugeRowCarrierLevel : ProofLevel
selectedFiniteGaugeRowCarrierLevel = machineChecked

selectedResidualIdentityPlusMatrixLevel : ProofLevel
selectedResidualIdentityPlusMatrixLevel = machineChecked

selectedResidualIdentityPlusInjectivityLevel : ProofLevel
selectedResidualIdentityPlusInjectivityLevel = machineChecked

selectedResidualInverseNormLevel : ProofLevel
selectedResidualInverseNormLevel = machineChecked

selectedFiniteInjectiveToInverseAuthorityLevel : ProofLevel
selectedFiniteInjectiveToInverseAuthorityLevel = standardImported
