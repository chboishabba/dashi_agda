module DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintTangentProjectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Construct the physical tangent projector from the ACTUAL 780-row selected
-- constraint, not from the separate 768-row gauge-only Green.  Given a
-- proof-relevant two-sided inverse of
--
--       K_A = L_A L_A^*
--
-- on the complete selected multiplier carrier, define
--
--       Pi_A = I - L_A^* K_A^-1 L_A.
--
-- Finite matrix algebra proves
--
--       L_A Pi_A = 0,
--       Pi_A h = h  for L_A h = 0,
--       Pi_A^2 = Pi_A.
--
-- Thus im(Pi_A)=ker(L_A) on this literal finite carrier.  The module does not
-- confuse the gauge-only regularized inverse with this full combined Gram
-- inverse.  Constructing the latter (or a correct Schur reduction to it) is a
-- separate physical producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintFiniteKKTExact as SelectedKKT

StateVector : Set
StateVector = KKT.StateVector

MultiplierVector : Set
MultiplierVector = SelectedKKT.SelectedMultiplierVector

stateDifference : StateVector → StateVector → StateVector
stateDifference left right coordinate = left coordinate - right coordinate

zeroMultiplier : MultiplierVector
zeroMultiplier _ = 0ℚ

sumZero : ∀ {A : Set} (values : List A) →
  Sums.sumRational values (λ _ → 0ℚ) ≡ 0ℚ
sumZero [] = refl
sumZero (_ ∷ values) rewrite sumZero values = refl

combinedConstraintDifferenceExact :
  ∀ background left right row →
  Combined.selectedBackgroundCombinedConstraintApply background
      (stateDifference left right) row
  ≡ Combined.selectedBackgroundCombinedConstraintApply background left row
    - Combined.selectedBackgroundCombinedConstraintApply background right row
combinedConstraintDifferenceExact background left right row =
  let
    matrix = Combined.selectedBackgroundLinearizedConstraintMatrix background
    leftTerm = λ column → matrix row column * left column
    rightTerm = λ column → matrix row column * right column

    expanded = Sums.sumRationalCong
      (Matrix.coordinates KKT.physicalStateCarrier) _ _
      (λ column → ℚRing.solve-∀
        (matrix row column) (left column) (right column))

    split = Fubini.sumRationalAdd
      (Matrix.coordinates KKT.physicalStateCarrier)
      leftTerm (λ column → - rightTerm column)

    negate = Sums.sumRationalNegate
      (Matrix.coordinates KKT.physicalStateCarrier) rightTerm
  in
  trans expanded
    (trans split
      (trans
        (cong
          (Sums.sumRational
            (Matrix.coordinates KKT.physicalStateCarrier) leftTerm +_)
          negate)
        (ℚRing.solve-∀
          (Sums.sumRational
            (Matrix.coordinates KKT.physicalStateCarrier) leftTerm)
          (Sums.sumRational
            (Matrix.coordinates KKT.physicalStateCarrier) rightTerm))))

matrixApplyZeroExact :
  ∀ {Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    (matrix : Matrix.RationalMatrix Index) row →
  Matrix.applyMatrix carrier matrix (λ _ → 0ℚ) row ≡ 0ℚ
matrixApplyZeroExact carrier matrix row =
  trans
    (Sums.sumRationalCong (Matrix.coordinates carrier) _ (λ _ → 0ℚ)
      (λ column → ℚRing.solve-∀ (matrix row column)))
    (sumZero (Matrix.coordinates carrier))

selectedAdjointZeroExact :
  ∀ background coordinate →
  SelectedKKT.selectedCombinedConstraintTransposeApply
    background zeroMultiplier coordinate ≡ 0ℚ
selectedAdjointZeroExact background coordinate =
  let
    transpose =
      DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact.transposeRectangular
        (Combined.selectedBackgroundLinearizedConstraintMatrix background)
  in
  trans
    (Sums.sumRationalCong Rows.selectedCombinedConstraintRows _ (λ _ → 0ℚ)
      (λ row → ℚRing.solve-∀ (transpose coordinate row)))
    (sumZero Rows.selectedCombinedConstraintRows)

FullGramInverseCertificate :
  PhysicalBackground → Set₁
FullGramInverseCertificate = λ background →
  Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (Combined.selectedBackgroundConstraintGram background)
  where
  open import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact
    using (RationalSU2Background4)
  PhysicalBackground = RationalSU2Background4

selectedMultiplierFromState :
  ∀ {background} → FullGramInverseCertificate background →
  StateVector → MultiplierVector
selectedMultiplierFromState certificate state =
  Matrix.applyMatrix Rows.selectedCombinedConstraintRowCarrier
    (Matrix.inverseMatrix certificate)
    (Combined.selectedBackgroundCombinedConstraintApply _ state)

selectedNormalCorrection :
  ∀ {background} → FullGramInverseCertificate background →
  StateVector → StateVector
selectedNormalCorrection {background} certificate state =
  SelectedKKT.selectedCombinedConstraintTransposeApply background
    (selectedMultiplierFromState certificate state)

selectedPhysicalTangentProjector :
  ∀ {background} → FullGramInverseCertificate background →
  StateVector → StateVector
selectedPhysicalTangentProjector certificate state =
  stateDifference state (selectedNormalCorrection certificate state)

selectedNormalConstraintEqualsSource :
  ∀ {background}
    (certificate : FullGramInverseCertificate background)
    state row →
  Combined.selectedBackgroundCombinedConstraintApply background
      (selectedNormalCorrection certificate state) row
  ≡ Combined.selectedBackgroundCombinedConstraintApply background state row
selectedNormalConstraintEqualsSource
    {background} certificate state row =
  let
    source = Combined.selectedBackgroundCombinedConstraintApply background state
    multiplier = selectedMultiplierFromState certificate state

    toGram :
      Combined.selectedBackgroundCombinedConstraintApply background
        (selectedNormalCorrection certificate state) row
      ≡ SelectedKKT.selectedCombinedConstraintGramApply
          background multiplier row
    toGram = sym
      (SelectedKKT.selectedCombinedConstraintGramActionExact
        background multiplier row)

    inverseRight :
      SelectedKKT.selectedCombinedConstraintGramApply background multiplier row
      ≡ source row
    inverseRight = Matrix.matrixInverseRightExact certificate source row
  in
  trans toGram inverseRight

selectedPhysicalTangentProjectorInKernel :
  ∀ {background}
    (certificate : FullGramInverseCertificate background)
    state row →
  Combined.selectedBackgroundCombinedConstraintApply background
      (selectedPhysicalTangentProjector certificate state) row
  ≡ 0ℚ
selectedPhysicalTangentProjectorInKernel
    {background} certificate state row =
  trans
    (combinedConstraintDifferenceExact
      background state (selectedNormalCorrection certificate state) row)
    (trans
      (cong
        (Combined.selectedBackgroundCombinedConstraintApply background state row -_)
        (selectedNormalConstraintEqualsSource certificate state row))
      (ℚRing.solve-∀
        (Combined.selectedBackgroundCombinedConstraintApply background state row)))

LinearizedConstraintKernel :
  ∀ {background} → StateVector → Set
LinearizedConstraintKernel {background} state =
  ∀ row →
  Combined.selectedBackgroundCombinedConstraintApply background state row ≡ 0ℚ

selectedMultiplierOfKernelIsZero :
  ∀ {background}
    (certificate : FullGramInverseCertificate background)
    state →
  LinearizedConstraintKernel {background} state →
  ∀ row → selectedMultiplierFromState certificate state row ≡ 0ℚ
selectedMultiplierOfKernelIsZero
    {background} certificate state inKernel row =
  let
    source = Combined.selectedBackgroundCombinedConstraintApply background state

    sourceCong : ∀ selected → source selected ≡ zeroMultiplier selected
    sourceCong selected = inKernel selected

    inverse = Matrix.inverseMatrix certificate

    actionCong :
      Matrix.applyMatrix Rows.selectedCombinedConstraintRowCarrier inverse source row
      ≡ Matrix.applyMatrix Rows.selectedCombinedConstraintRowCarrier inverse
          zeroMultiplier row
    actionCong =
      Sums.sumRationalCong Rows.selectedCombinedConstraintRows _ _
        (λ column → cong (inverse row column *_) (sourceCong column))
  in
  trans actionCong
    (matrixApplyZeroExact
      Rows.selectedCombinedConstraintRowCarrier inverse row)

selectedNormalCorrectionOfKernelZero :
  ∀ {background}
    (certificate : FullGramInverseCertificate background)
    state →
  LinearizedConstraintKernel {background} state →
  ∀ coordinate → selectedNormalCorrection certificate state coordinate ≡ 0ℚ
selectedNormalCorrectionOfKernelZero
    {background} certificate state inKernel coordinate =
  let
    multiplier = selectedMultiplierFromState certificate state
    multiplierZero = selectedMultiplierOfKernelIsZero
      certificate state inKernel

    transpose =
      DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact.transposeRectangular
        (Combined.selectedBackgroundLinearizedConstraintMatrix background)

    replace :
      SelectedKKT.selectedCombinedConstraintTransposeApply background multiplier coordinate
      ≡ SelectedKKT.selectedCombinedConstraintTransposeApply
          background zeroMultiplier coordinate
    replace =
      Sums.sumRationalCong Rows.selectedCombinedConstraintRows _ _
        (λ row → cong (transpose coordinate row *_) (multiplierZero row))
  in
  trans replace (selectedAdjointZeroExact background coordinate)

selectedPhysicalTangentProjectorFixesKernel :
  ∀ {background}
    (certificate : FullGramInverseCertificate background)
    state →
  LinearizedConstraintKernel {background} state →
  ∀ coordinate →
  selectedPhysicalTangentProjector certificate state coordinate ≡ state coordinate
selectedPhysicalTangentProjectorFixesKernel certificate state inKernel coordinate =
  trans
    (cong
      (state coordinate -_)
      (selectedNormalCorrectionOfKernelZero
        certificate state inKernel coordinate))
    (ℚRing.solve-∀ (state coordinate))

selectedPhysicalTangentProjectorIdempotent :
  ∀ {background}
    (certificate : FullGramInverseCertificate background)
    state coordinate →
  selectedPhysicalTangentProjector certificate
      (selectedPhysicalTangentProjector certificate state) coordinate
  ≡ selectedPhysicalTangentProjector certificate state coordinate
selectedPhysicalTangentProjectorIdempotent certificate state coordinate =
  selectedPhysicalTangentProjectorFixesKernel
    certificate
    (selectedPhysicalTangentProjector certificate state)
    (selectedPhysicalTangentProjectorInKernel certificate state)
    coordinate

selectedLinearizedConstraintKernelIffProjectorFixed :
  ∀ {background}
    (certificate : FullGramInverseCertificate background)
    state →
  (LinearizedConstraintKernel {background} state)
  × (∀ coordinate →
      selectedPhysicalTangentProjector certificate state coordinate
      ≡ state coordinate)
selectedLinearizedConstraintKernelIffProjectorFixed certificate state =
  let
    projectedKernel = selectedPhysicalTangentProjectorInKernel certificate state
  in
  projectedKernel ,
    selectedPhysicalTangentProjectorFixesKernel certificate state projectedKernel
  where
    open import Data.Product.Base using (_×_; _,_)

selectedFullConstraintTangentProjectorLevel : ProofLevel
selectedFullConstraintTangentProjectorLevel = machineChecked

selectedFullConstraintProjectorIdempotenceLevel : ProofLevel
selectedFullConstraintProjectorIdempotenceLevel = machineChecked

selectedFullConstraintGramInverseProducerLevel : ProofLevel
selectedFullConstraintGramInverseProducerLevel = conditional
