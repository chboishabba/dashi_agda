module DASHI.Physics.YangMills.BalabanSelectedProjectedSchurFiniteRationalReopeningExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Construct the exact finite rational inverse for the physically projected
-- Schur reopening matrix
--
--       M_A^red = I + G_0 P_g Q_A.
--
-- The preceding theorem proves both row and column mass of the residual
-- G_0 P_g Q_A are at most
--
--       126633/524288 < 1/4 < 1/2.
--
-- The column estimate yields an l1 contraction.  The q=1/2 finite reopening
-- theorem therefore makes the homogeneous equation pointwise trivial on the
-- complete 768-row gauge carrier.  Standard finite rational linear algebra
-- then supplies a proof-relevant inverse certificate.  Every solution obeys
--
--       ||(M_A^red)^-1 y||_1 <= 2 ||y||_1.
--
-- No infinite Neumann limit is used.  This module is still the Schur-factor
-- inverse; the next same-object theorem identifies its composition with G_0
-- with the padded/reduced physical Schur operator before full 12+768 KKT
-- back-substitution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRationalInjectiveInverseExact as FiniteInverse
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Strict
import DASHI.Physics.YangMills.BalabanFiniteOneHalfReopeningExact as Half
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFiniteRationalReopeningExact as Carrier
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact as Scale
import DASHI.Physics.YangMills.BalabanSelectedProjectedSchurPerturbationContractionExact as Projected
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeRow : Set
GaugeRow = Projected.GaugeRow

GaugeVector : Set
GaugeVector = GaugeRow → ℚ

gaugeRows = Projected.gaugeRows

projectedSchurIdentityPlusMatrix :
  Physical.RationalSU2Background4 → Matrix.RationalMatrix GaugeRow
projectedSchurIdentityPlusMatrix background =
  Carrier.identityPlusKernel (Projected.projectedSchurResidual background)

projectedSchurIdentityPlusMatrixActionExact : ∀ background vector row →
  Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
    (projectedSchurIdentityPlusMatrix background) vector row
  ≡ vector row
    + Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
        (Projected.projectedSchurResidual background) vector row
projectedSchurIdentityPlusMatrixActionExact background =
  Carrier.identityPlusKernelActionExact
    (Projected.projectedSchurResidual background)

projectedSchurResidualBelowOneHalf :
  Projected.projectedSchurResidualBound ≤ Half.oneHalf
projectedSchurResidualBelowOneHalf = toWitness _

projectedSchurResidualL1Bound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ vector →
  L1.vectorL1 gaugeRows
    (Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
      (Projected.projectedSchurResidual background) vector)
  ≤ Half.oneHalf * L1.vectorL1 gaugeRows vector
projectedSchurResidualL1Bound background radius vector =
  let
    qBound = L1.applyKernelL1Bound
      gaugeRows (Projected.projectedSchurResidual background) vector
      Projected.projectedSchurResidualBound
      (ℚP.nonNegative⁻¹ Projected.projectedSchurResidualBound)
      (Projected.selectedProjectedSchurResidualColumnMassBound background radius)

    vectorNorm = L1.vectorL1 gaugeRows vector
    vectorNormNonnegative = Strict.vectorL1Nonnegative gaugeRows vector

    toOneHalf :
      Projected.projectedSchurResidualBound * vectorNorm
      ≤ Half.oneHalf * vectorNorm
    toOneHalf = Scale.rightScaleMonotone
      vectorNorm
      Projected.projectedSchurResidualBound Half.oneHalf
      vectorNormNonnegative projectedSchurResidualBelowOneHalf
  in
  ℚP.≤-trans qBound toOneHalf

identityPlusDifferenceZero :
  ∀ background left right →
  (∀ row →
    Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
      (projectedSchurIdentityPlusMatrix background) left row
    ≡ Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
      (projectedSchurIdentityPlusMatrix background) right row) →
  ∀ row →
  Strict.vectorDifference left right row
    + Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
        (Projected.projectedSchurResidual background)
        (Strict.vectorDifference left right) row
  ≡ 0ℚ
identityPlusDifferenceZero background left right equal row =
  let
    matrix = projectedSchurIdentityPlusMatrix background

    differenceAction :
      Matrix.applyMatrix Carrier.gaugeFiniteCoordinates matrix
        (Strict.vectorDifference left right) row
      ≡ Matrix.applyMatrix Carrier.gaugeFiniteCoordinates matrix left row
        - Matrix.applyMatrix Carrier.gaugeFiniteCoordinates matrix right row
    differenceAction =
      Rect.applyRectangularSubtract
        Carrier.gaugeFiniteCoordinates matrix left right row

    actionZero :
      Matrix.applyMatrix Carrier.gaugeFiniteCoordinates matrix
        (Strict.vectorDifference left right) row
      ≡ 0ℚ
    actionZero = trans differenceAction
      (trans
        (cong
          (_- Matrix.applyMatrix Carrier.gaugeFiniteCoordinates matrix right row)
          (equal row))
        (ℚRing.solve-∀
          (Matrix.applyMatrix Carrier.gaugeFiniteCoordinates matrix right row)))
  in
  trans
    (sym
      (projectedSchurIdentityPlusMatrixActionExact
        background (Strict.vectorDifference left right) row))
    actionZero

projectedSchurIdentityPlusMatrixInjective :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  FiniteInverse.PointwiseInjective Carrier.gaugeFiniteCoordinates
    (projectedSchurIdentityPlusMatrix background)
projectedSchurIdentityPlusMatrixInjective background radius left right equal row =
  let
    difference = Strict.vectorDifference left right
    residualApply = λ vector →
      Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
        (Projected.projectedSchurResidual background) vector

    equation : Strict.IdentityPlusResidualEquation
      residualApply difference Strict.zeroVector
    equation selected = identityPlusDifferenceZero
      background left right equal selected

    residualContraction :
      L1.vectorL1 gaugeRows (residualApply difference)
      ≤ Half.oneHalf * L1.vectorL1 gaugeRows difference
    residualContraction = projectedSchurResidualL1Bound
      background radius difference

    differenceZero =
      Half.oneHalfHomogeneousReopeningPointwiseZero
        Carrier.gaugeRowSelector residualApply difference
        equation residualContraction row
  in
  trans
    (sym (ℚRing.solve-∀ (left row) (right row) :
      (left row - right row) + right row ≡ left row))
    (trans
      (cong (_+ right row) differenceZero)
      (ℚRing.solve-∀ (right row)))

projectedSchurIdentityPlusRationalInverse :
  FiniteInverse.FiniteRationalInjectiveInverseAuthority →
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  Matrix.RationalMatrixInverseCertificate Carrier.gaugeFiniteCoordinates
    (projectedSchurIdentityPlusMatrix background)
projectedSchurIdentityPlusRationalInverse authority background radius =
  FiniteInverse.finiteSquareInjectiveImpliesRationalInverse authority
    Carrier.gaugeFiniteCoordinates
    (projectedSchurIdentityPlusMatrix background)
    (projectedSchurIdentityPlusMatrixInjective background radius)

projectedSchurResidualInverseApply :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate Carrier.gaugeFiniteCoordinates
    (projectedSchurIdentityPlusMatrix background) →
  GaugeVector → GaugeVector
projectedSchurResidualInverseApply background certificate =
  Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
    (Matrix.inverseMatrix certificate)

projectedSchurResidualInverseFactorTwo :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  (certificate : Matrix.RationalMatrixInverseCertificate
    Carrier.gaugeFiniteCoordinates
    (projectedSchurIdentityPlusMatrix background)) →
  ∀ source →
  L1.vectorL1 gaugeRows
      (projectedSchurResidualInverseApply background certificate source)
  ≤ Half.two * L1.vectorL1 gaugeRows source
projectedSchurResidualInverseFactorTwo background radius certificate source =
  let
    solution = projectedSchurResidualInverseApply background certificate source
    residualApply = λ vector →
      Matrix.applyMatrix Carrier.gaugeFiniteCoordinates
        (Projected.projectedSchurResidual background) vector

    equation : Strict.IdentityPlusResidualEquation
      residualApply solution source
    equation row =
      trans
        (sym (projectedSchurIdentityPlusMatrixActionExact
          background solution row))
        (Matrix.matrixInverseRightExact certificate source row)

    residualContraction = projectedSchurResidualL1Bound
      background radius solution
  in
  Half.oneHalfReopeningBound
    gaugeRows residualApply solution source equation residualContraction

selectedProjectedSchurFiniteCarrierLevel : ProofLevel
selectedProjectedSchurFiniteCarrierLevel = machineChecked

selectedProjectedSchurIdentityPlusInjectivityLevel : ProofLevel
selectedProjectedSchurIdentityPlusInjectivityLevel = machineChecked

selectedProjectedSchurFiniteInverseAuthorityLevel : ProofLevel
selectedProjectedSchurFiniteInverseAuthorityLevel = standardImported

selectedProjectedSchurInverseFactorTwoLevel : ProofLevel
selectedProjectedSchurInverseFactorTwoLevel = machineChecked
