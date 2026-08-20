module DASHI.Physics.YangMills.BalabanSelectedSchurFiniteRationalReopeningExact where

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
-- Turn the exact selected Schur residual
--
--       R_A = G_0 Q_A
--
-- into an actual finite rational reopening inverse.  The preceding two-sided
-- theorem proves both row and column masses of R_A are below 1/8, hence below
-- 1/6.  The column estimate supplies the induced l1 contraction.  Therefore
-- the homogeneous equation
--
--       (I + R_A) x = 0
--
-- has x=0 on the complete 768-row finite selector.  The standard finite-field
-- theorem injective => invertible supplies a proof-relevant rational inverse.
--
-- For every source y, the resulting exact solution obeys the conservative
-- reopening estimate
--
--       ||(I+R_A)^-1 y||_1 <= (6/5) ||y||_1.
--
-- No infinite Neumann sum and no completeness of Q is used.  This module does
-- not yet identify the regularized gauge Schur operator with the physical
-- mean-zero reduced Schur operator; that same-object restriction is the next
-- weld before back-substitution into the full combined KKT Green.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _-_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRationalInjectiveInverseExact as FiniteInverse
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Strict
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact as Scale
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFiniteRationalReopeningExact as Existing
import DASHI.Physics.YangMills.BalabanSelectedSchurCrossAbsoluteMassExact as Cross
import DASHI.Physics.YangMills.BalabanSelectedSchurGaugeGreenContractionExact as Schur
import DASHI.Physics.YangMills.BalabanSelectedSchurGaugeGreenTwoSidedContractionExact as TwoSided
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeRow : Set
GaugeRow = Cross.GaugeRow

GaugeVector : Set
GaugeVector = GaugeRow → ℚ

gaugeFiniteCoordinates : Matrix.FiniteRationalCoordinates GaugeRow
gaugeFiniteCoordinates = Existing.gaugeFiniteCoordinates

gaugeRows = Matrix.coordinates gaugeFiniteCoordinates

schurResidual :
  Physical.RationalSU2Background4 → Matrix.RationalMatrix GaugeRow
schurResidual = Schur.flatGreenTimesSchurPerturbation

schurIdentityPlusMatrix :
  Physical.RationalSU2Background4 → Matrix.RationalMatrix GaugeRow
schurIdentityPlusMatrix background =
  Existing.identityPlusKernel (schurResidual background)

schurIdentityPlusMatrixActionExact : ∀ background vector row →
  Matrix.applyMatrix gaugeFiniteCoordinates
    (schurIdentityPlusMatrix background) vector row
  ≡ vector row
      + Matrix.applyMatrix gaugeFiniteCoordinates
          (schurResidual background) vector row
schurIdentityPlusMatrixActionExact background =
  Existing.identityPlusKernelActionExact (schurResidual background)

schurContractionBelowOneSixth :
  Schur.schurGreenContractionBound ≤ Strict.oneSixth
schurContractionBelowOneSixth = toWitness _

schurResidualL1Bound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ vector →
  L1.vectorL1 gaugeRows
    (Matrix.applyMatrix gaugeFiniteCoordinates
      (schurResidual background) vector)
  ≤ Strict.oneSixth * L1.vectorL1 gaugeRows vector
schurResidualL1Bound background radius vector =
  let
    qBound = L1.applyKernelL1Bound
      gaugeRows (schurResidual background) vector
      Schur.schurGreenContractionBound
      (ℚP.nonNegative⁻¹ Schur.schurGreenContractionBound)
      (TwoSided.selectedSchurResidualAbsoluteColumnMassBound background radius)

    vectorNorm = L1.vectorL1 gaugeRows vector
    vectorNormNonnegative = Strict.vectorL1Nonnegative gaugeRows vector

    toOneSixth :
      Schur.schurGreenContractionBound * vectorNorm
      ≤ Strict.oneSixth * vectorNorm
    toOneSixth = Scale.rightScaleMonotone
      vectorNorm
      Schur.schurGreenContractionBound Strict.oneSixth
      vectorNormNonnegative schurContractionBelowOneSixth
  in
  ℚP.≤-trans qBound toOneSixth

vectorDifference : GaugeVector → GaugeVector → GaugeVector
vectorDifference left right row = left row - right row

identityPlusDifferenceZero :
  ∀ background left right →
  (∀ row →
    Matrix.applyMatrix gaugeFiniteCoordinates
      (schurIdentityPlusMatrix background) left row
    ≡ Matrix.applyMatrix gaugeFiniteCoordinates
      (schurIdentityPlusMatrix background) right row) →
  ∀ row →
  vectorDifference left right row
    + Matrix.applyMatrix gaugeFiniteCoordinates
        (schurResidual background) (vectorDifference left right) row
  ≡ 0ℚ
identityPlusDifferenceZero background left right equal row =
  let
    matrix = schurIdentityPlusMatrix background
    differenceAction :
      Matrix.applyMatrix gaugeFiniteCoordinates matrix
        (vectorDifference left right) row
      ≡ Matrix.applyMatrix gaugeFiniteCoordinates matrix left row
        - Matrix.applyMatrix gaugeFiniteCoordinates matrix right row
    differenceAction =
      Rect.applyRectangularSubtract
        gaugeFiniteCoordinates matrix left right row

    actionZero :
      Matrix.applyMatrix gaugeFiniteCoordinates matrix
        (vectorDifference left right) row
      ≡ 0ℚ
    actionZero = trans differenceAction
      (trans (cong (_- Matrix.applyMatrix gaugeFiniteCoordinates matrix right row)
        (equal row))
        (ℚRing.solve-∀
          (Matrix.applyMatrix gaugeFiniteCoordinates matrix right row)))
  in
  trans
    (sym (schurIdentityPlusMatrixActionExact
      background (vectorDifference left right) row))
    actionZero

schurIdentityPlusMatrixInjective :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  FiniteInverse.PointwiseInjective gaugeFiniteCoordinates
    (schurIdentityPlusMatrix background)
schurIdentityPlusMatrixInjective background radius left right equal row =
  let
    difference = vectorDifference left right
    residualApply = λ vector →
      Matrix.applyMatrix gaugeFiniteCoordinates
        (schurResidual background) vector

    equation : Strict.IdentityPlusResidualEquation
      residualApply difference Strict.zeroVector
    equation selected = identityPlusDifferenceZero
      background left right equal selected

    residualContraction :
      L1.vectorL1 gaugeRows (residualApply difference)
      ≤ Strict.oneSixth * L1.vectorL1 gaugeRows difference
    residualContraction = schurResidualL1Bound background radius difference

    differenceZero =
      Strict.oneSixthHomogeneousReopeningPointwiseZero
        Existing.gaugeRowSelector residualApply difference
        equation residualContraction row
  in
  trans
    (sym (ℚRing.solve-∀ (left row) (right row) :
      (left row - right row) + right row ≡ left row))
    (trans
      (cong (_+ right row) differenceZero)
      (ℚRing.solve-∀ (right row)))

schurIdentityPlusRationalInverse :
  FiniteInverse.FiniteRationalInjectiveInverseAuthority →
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  Matrix.RationalMatrixInverseCertificate gaugeFiniteCoordinates
    (schurIdentityPlusMatrix background)
schurIdentityPlusRationalInverse authority background radius =
  FiniteInverse.finiteSquareInjectiveImpliesRationalInverse authority
    gaugeFiniteCoordinates
    (schurIdentityPlusMatrix background)
    (schurIdentityPlusMatrixInjective background radius)

schurResidualInverseApply :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate gaugeFiniteCoordinates
    (schurIdentityPlusMatrix background) →
  GaugeVector → GaugeVector
schurResidualInverseApply background certificate =
  Matrix.applyMatrix gaugeFiniteCoordinates (Matrix.inverseMatrix certificate)

schurResidualInverseSixFifths :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  (certificate : Matrix.RationalMatrixInverseCertificate
    gaugeFiniteCoordinates (schurIdentityPlusMatrix background)) →
  ∀ source →
  L1.vectorL1 gaugeRows
      (schurResidualInverseApply background certificate source)
  ≤ Strict.sixFifths * L1.vectorL1 gaugeRows source
schurResidualInverseSixFifths background radius certificate source =
  let
    solution = schurResidualInverseApply background certificate source
    residualApply = λ vector →
      Matrix.applyMatrix gaugeFiniteCoordinates
        (schurResidual background) vector

    equation : Strict.IdentityPlusResidualEquation
      residualApply solution source
    equation row =
      trans
        (sym (schurIdentityPlusMatrixActionExact background solution row))
        (Matrix.matrixInverseRightExact certificate source row)

    residualContraction = schurResidualL1Bound background radius solution
  in
  Strict.oneSixthReopeningBound
    gaugeRows residualApply solution source equation residualContraction

selectedSchurFiniteCarrierLevel : ProofLevel
selectedSchurFiniteCarrierLevel = machineChecked

selectedSchurIdentityPlusInjectivityLevel : ProofLevel
selectedSchurIdentityPlusInjectivityLevel = machineChecked

selectedSchurFiniteInverseAuthorityLevel : ProofLevel
selectedSchurFiniteInverseAuthorityLevel = standardImported

selectedSchurInverseSixFifthsLevel : ProofLevel
selectedSchurInverseSixFifthsLevel = machineChecked
