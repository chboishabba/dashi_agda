module DASHI.Physics.YangMills.BalabanSelectedReducedConstraintTangentProjectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers", RAIRO Analyse Numerique 8 (1974),
-- 129--151. No DOI was assigned to the cited article.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Construct the legitimate selected tangent projector after the raw-780 Gram
-- no-go.  The constraint derivative is first projected to the explicit
-- mean-zero multiplier section P.  The padded inverse from the preceding
-- module supplies a right inverse G_red of
--
--       K_red = P L_A L_A^* |im(P).
--
-- Define
--
--       N_A = L_A^* G_red P L_A,
--       Pi_A = I - N_A.
--
-- Only the right-inverse identity K_red G_red = I is needed.  Finite matrix
-- algebra then proves
--
--       P L_A Pi_A = 0,
--       Pi_A h = h  whenever P L_A h = 0,
--       Pi_A^2 = Pi_A.
--
-- Thus the computational reduced quotient now has an actual proof-bearing
-- tangent projector without ever inverting the singular raw 780-row Gram.
-- The still-separate nonlinear theorem is that this reduced linear kernel is
-- the tangent space of the selected nonlinear constraint fibre.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintFiniteKKTExact as RawKKT
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintTangentProjectorExact as FullProjector
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionOrthogonalityExact as Projection
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionCongruenceExact as ProjectionCong
import DASHI.Physics.YangMills.BalabanSelectedPaddedReducedNormalInverseExact as ReducedInverse

StateVector : Set
StateVector = KKT.StateVector

MultiplierVector : Set
MultiplierVector = ReducedInverse.RawMultiplier

minusOne : ℚ
minusOne = - (+ 1 / 1)

stateAdd : StateVector → StateVector → StateVector
stateAdd left right coordinate = left coordinate + right coordinate

stateScale : ℚ → StateVector → StateVector
stateScale coefficient vector coordinate = coefficient * vector coordinate

------------------------------------------------------------------------
-- The actual reduced linearized constraint P L_A.
------------------------------------------------------------------------

selectedReducedConstraintApply :
  Physical.RationalSU2Background4 → StateVector → MultiplierVector
selectedReducedConstraintApply background state =
  Projection.selectedReducedProjection
    (Combined.selectedBackgroundCombinedConstraintApply background state)

selectedReducedConstraintApplyIsReduced : ∀ background state row →
  Projection.selectedReducedProjection
    (selectedReducedConstraintApply background state) row
  ≡ selectedReducedConstraintApply background state row
selectedReducedConstraintApplyIsReduced background state row =
  Projection.selectedProjectionIdempotent
    (Combined.selectedBackgroundCombinedConstraintApply background state) row

rawConstraintRespectsPointwise : ∀ background left right →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ row →
  Combined.selectedBackgroundCombinedConstraintApply background left row
  ≡ Combined.selectedBackgroundCombinedConstraintApply background right row
rawConstraintRespectsPointwise background left right pointwise row =
  let matrix = Combined.selectedBackgroundLinearizedConstraintMatrix background in
  Sums.sumRationalCong (Matrix.coordinates KKT.physicalStateCarrier) _ _
    (λ coordinate → cong (matrix row coordinate *_) (pointwise coordinate))

rawConstraintAddExact : ∀ background left right row →
  Combined.selectedBackgroundCombinedConstraintApply background
      (stateAdd left right) row
  ≡ Combined.selectedBackgroundCombinedConstraintApply background left row
    + Combined.selectedBackgroundCombinedConstraintApply background right row
rawConstraintAddExact background left right row =
  Rect.applyRectangularAddExact KKT.physicalStateCarrier
    (Combined.selectedBackgroundLinearizedConstraintMatrix background)
    left right row

rawConstraintScaleExact : ∀ background coefficient vector row →
  Combined.selectedBackgroundCombinedConstraintApply background
      (stateScale coefficient vector) row
  ≡ coefficient
      * Combined.selectedBackgroundCombinedConstraintApply background vector row
rawConstraintScaleExact background coefficient vector row =
  let
    values = Matrix.coordinates KKT.physicalStateCarrier
    matrix = Combined.selectedBackgroundLinearizedConstraintMatrix background
  in
  trans
    (Sums.sumRationalCong values _ _
      (λ coordinate → ℚRing.solve-∀
        (matrix row coordinate) coefficient (vector coordinate)))
    (Sums.sumRationalScale coefficient values
      (λ coordinate → matrix row coordinate * vector coordinate))

selectedReducedConstraintAddExact : ∀ background left right row →
  selectedReducedConstraintApply background (stateAdd left right) row
  ≡ Projection.rawAdd
      (selectedReducedConstraintApply background left)
      (selectedReducedConstraintApply background right) row
selectedReducedConstraintAddExact background left right row =
  let
    rawLeft = Combined.selectedBackgroundCombinedConstraintApply background left
    rawRight = Combined.selectedBackgroundCombinedConstraintApply background right
    rawSum = Projection.rawAdd rawLeft rawRight
  in
  trans
    (ProjectionCong.selectedProjectionRespectsPointwise
      (Combined.selectedBackgroundCombinedConstraintApply
        background (stateAdd left right))
      rawSum
      (rawConstraintAddExact background left right)
      row)
    (Projection.selectedProjectionAddExact rawLeft rawRight row)

selectedReducedConstraintScaleExact : ∀ background coefficient vector row →
  selectedReducedConstraintApply background (stateScale coefficient vector) row
  ≡ Projection.rawScale coefficient
      (selectedReducedConstraintApply background vector) row
selectedReducedConstraintScaleExact background coefficient vector row =
  let raw = Combined.selectedBackgroundCombinedConstraintApply background vector in
  trans
    (ProjectionCong.selectedProjectionRespectsPointwise
      (Combined.selectedBackgroundCombinedConstraintApply
        background (stateScale coefficient vector))
      (Projection.rawScale coefficient raw)
      (rawConstraintScaleExact background coefficient vector)
      row)
    (Projection.selectedProjectionScaleExact coefficient raw row)

------------------------------------------------------------------------
-- Reduced normal correction and tangent projector.
------------------------------------------------------------------------

selectedReducedMultiplierFromState :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (ReducedInverse.selectedPaddedReducedNormalMatrix background) →
  StateVector → MultiplierVector
selectedReducedMultiplierFromState background certificate state =
  ReducedInverse.selectedReducedNormalInverseApply background certificate
    (selectedReducedConstraintApply background state)

selectedReducedNormalCorrection :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (ReducedInverse.selectedPaddedReducedNormalMatrix background) →
  StateVector → StateVector
selectedReducedNormalCorrection background certificate state =
  RawKKT.selectedCombinedConstraintTransposeApply background
    (selectedReducedMultiplierFromState background certificate state)

selectedPhysicalTangentProjectorReduced :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (ReducedInverse.selectedPaddedReducedNormalMatrix background) →
  StateVector → StateVector
selectedPhysicalTangentProjectorReduced background certificate state =
  stateAdd state
    (stateScale minusOne
      (selectedReducedNormalCorrection background certificate state))

selectedReducedNormalConstraintEqualsSource :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    state row →
  selectedReducedConstraintApply background
      (selectedReducedNormalCorrection background certificate state) row
  ≡ selectedReducedConstraintApply background state row
selectedReducedNormalConstraintEqualsSource background certificate state row =
  let
    source = selectedReducedConstraintApply background state
    multiplier = selectedReducedMultiplierFromState background certificate state
    rawGram = RawKKT.selectedCombinedConstraintGramApply background multiplier
    rawConstraint = Combined.selectedBackgroundCombinedConstraintApply background
      (selectedReducedNormalCorrection background certificate state)

    sameRaw : ∀ selected → rawGram selected ≡ rawConstraint selected
    sameRaw selected =
      RawKKT.selectedCombinedConstraintGramActionExact
        background multiplier selected

    projectedSame :
      Projection.selectedReducedProjection rawConstraint row
      ≡ Projection.selectedReducedProjection rawGram row
    projectedSame =
      ProjectionCong.selectedProjectionRespectsPointwise
        rawConstraint rawGram (λ selected → sym (sameRaw selected)) row

    rightInverse :
      ReducedInverse.selectedReducedCombinedGramApply background multiplier row
      ≡ source row
    rightInverse =
      ReducedInverse.selectedReducedCombinedGramRightInverse
        background certificate source
        (selectedReducedConstraintApplyIsReduced background state) row
  in
  trans projectedSame rightInverse

------------------------------------------------------------------------
-- Pi_A lands in ker(P L_A), fixes that kernel, and is idempotent.
------------------------------------------------------------------------

ReducedLinearizedConstraintKernel :
  ∀ {background} → StateVector → Set
ReducedLinearizedConstraintKernel {background} state =
  ∀ row → selectedReducedConstraintApply background state row ≡ 0ℚ

selectedPhysicalTangentProjectorReducedInKernel :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    state →
  ReducedLinearizedConstraintKernel {background}
    (selectedPhysicalTangentProjectorReduced background certificate state)
selectedPhysicalTangentProjectorReducedInKernel background certificate state row =
  trans
    (selectedReducedConstraintAddExact background state
      (stateScale minusOne
        (selectedReducedNormalCorrection background certificate state)) row)
    (trans
      (cong
        (selectedReducedConstraintApply background state row +_)
        (selectedReducedConstraintScaleExact background minusOne
          (selectedReducedNormalCorrection background certificate state) row))
      (trans
        (cong
          (λ correctionValue →
            selectedReducedConstraintApply background state row
              + minusOne * correctionValue)
          (selectedReducedNormalConstraintEqualsSource
            background certificate state row))
        (ℚRing.solve-∀
          (selectedReducedConstraintApply background state row))))

selectedReducedInverseOfZeroIsZero :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    row →
  ReducedInverse.selectedReducedNormalInverseApply
    background certificate (λ _ → 0ℚ) row
  ≡ 0ℚ
selectedReducedInverseOfZeroIsZero background certificate row =
  let
    inverse = Matrix.inverseMatrix certificate
    fullZero :
      Matrix.applyMatrix Rows.selectedCombinedConstraintRowCarrier
        inverse (λ _ → 0ℚ) row
      ≡ 0ℚ
    fullZero = FullProjector.matrixApplyZeroExact
      Rows.selectedCombinedConstraintRowCarrier inverse row
  in
  trans
    (ProjectionCong.selectedProjectionRespectsPointwise
      (Matrix.applyMatrix Rows.selectedCombinedConstraintRowCarrier
        inverse (λ _ → 0ℚ))
      (λ _ → 0ℚ)
      (λ selected → FullProjector.matrixApplyZeroExact
        Rows.selectedCombinedConstraintRowCarrier inverse selected)
      row)
    (selectedProjectionZero row)
  where
    selectedProjectionZero : ∀ selected →
      Projection.selectedReducedProjection (λ _ → 0ℚ) selected ≡ 0ℚ
    selectedProjectionZero selected =
      trans
        (Projection.selectedProjectionScaleExact 0ℚ (λ _ → 0ℚ) selected)
        (ℚRing.solve-∀
          (Projection.selectedReducedProjection (λ _ → 0ℚ) selected))

selectedReducedMultiplierOfKernelZero :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    state →
  ReducedLinearizedConstraintKernel {background} state →
  ∀ row → selectedReducedMultiplierFromState background certificate state row ≡ 0ℚ
selectedReducedMultiplierOfKernelZero background certificate state inKernel row =
  let
    source = selectedReducedConstraintApply background state
    sourceToZero : ∀ selected → source selected ≡ 0ℚ
    sourceToZero = inKernel

    inverseCong :
      ReducedInverse.selectedReducedNormalInverseApply background certificate source row
      ≡ ReducedInverse.selectedReducedNormalInverseApply
          background certificate (λ _ → 0ℚ) row
    inverseCong =
      ProjectionCong.selectedProjectionRespectsPointwise
        (ReducedInverse.selectedPaddedReducedNormalInverseApply
          background certificate source)
        (ReducedInverse.selectedPaddedReducedNormalInverseApply
          background certificate (λ _ → 0ℚ))
        (λ selected →
          Sums.sumRationalCong Rows.selectedCombinedConstraintRows _ _
            (λ column →
              cong
                (Matrix.inverseMatrix certificate selected column *_)
                (sourceToZero column)))
        row
  in
  trans inverseCong
    (selectedReducedInverseOfZeroIsZero background certificate row)

selectedReducedNormalCorrectionOfKernelZero :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    state →
  ReducedLinearizedConstraintKernel {background} state →
  ∀ coordinate →
  selectedReducedNormalCorrection background certificate state coordinate ≡ 0ℚ
selectedReducedNormalCorrectionOfKernelZero
    background certificate state inKernel coordinate =
  let
    multiplier = selectedReducedMultiplierFromState background certificate state
    multiplierZero = selectedReducedMultiplierOfKernelZero
      background certificate state inKernel
    transpose = Rect.transposeRectangular
      (Combined.selectedBackgroundLinearizedConstraintMatrix background)
  in
  trans
    (Sums.sumRationalCong Rows.selectedCombinedConstraintRows _ (λ _ → 0ℚ)
      (λ row → trans
        (cong (transpose coordinate row *_) (multiplierZero row))
        (ℚRing.solve-∀ (transpose coordinate row))))
    (Fubini.sumRationalZero Rows.selectedCombinedConstraintRows)

selectedPhysicalTangentProjectorReducedFixesKernel :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    state →
  ReducedLinearizedConstraintKernel {background} state →
  ∀ coordinate →
  selectedPhysicalTangentProjectorReduced background certificate state coordinate
  ≡ state coordinate
selectedPhysicalTangentProjectorReducedFixesKernel
    background certificate state inKernel coordinate =
  trans
    (cong
      (state coordinate +_)
      (cong (minusOne *_)
        (selectedReducedNormalCorrectionOfKernelZero
          background certificate state inKernel coordinate)))
    (ℚRing.solve-∀ (state coordinate))

selectedPhysicalTangentProjectorReducedIdempotent :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    state coordinate →
  selectedPhysicalTangentProjectorReduced background certificate
      (selectedPhysicalTangentProjectorReduced background certificate state)
      coordinate
  ≡ selectedPhysicalTangentProjectorReduced background certificate state coordinate
selectedPhysicalTangentProjectorReducedIdempotent
    background certificate state coordinate =
  selectedPhysicalTangentProjectorReducedFixesKernel
    background certificate
    (selectedPhysicalTangentProjectorReduced background certificate state)
    (selectedPhysicalTangentProjectorReducedInKernel
      background certificate state)
    coordinate

selectedReducedConstraintTangentProjectorLevel : ProofLevel
selectedReducedConstraintTangentProjectorLevel = machineChecked

selectedReducedConstraintTangentProjectorIdempotenceLevel : ProofLevel
selectedReducedConstraintTangentProjectorIdempotenceLevel = machineChecked

selectedReducedConstraintNonlinearTangentIdentificationLevel : ProofLevel
selectedReducedConstraintNonlinearTangentIdentificationLevel = conditional
