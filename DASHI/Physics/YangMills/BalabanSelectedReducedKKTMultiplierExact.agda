module DASHI.Physics.YangMills.BalabanSelectedReducedKKTMultiplierExact where

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
-- Close the finite KKT algebra on the *reduced physical* multiplier carrier.
-- Let Pi_A be the tangent projector constructed from the exact reduced normal
-- right inverse and let g be a finite action gradient.  If g annihilates every
-- vector in ker(P L_A), define the multiplier by the same normal solve used by
-- Pi_A:
--
--       lambda_A = G_red P L_A g.
--
-- Then
--
--       Pi_A g = 0,
--       g = L_A^* lambda_A.
--
-- The proof is not an existential finite-dimensional dimension argument.
-- Write g = Pi_A g + L_A^*lambda_A.  The projected part is in ker(P L_A).
-- The hypothesis makes <g,Pi_A g>=0.  Adjointness, P lambda_A=lambda_A, and
-- P L_A Pi_A g=0 make the normal correction orthogonal to Pi_A g.  Therefore
-- ||Pi_A g||^2=0; the literal 3072-coordinate selector forces Pi_A g=0
-- pointwise.  The same lambda used in the projector is thus the exact KKT
-- multiplier, closing the same-object seam requested by the Round-42 roadmap.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as StateCarrier
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanFiniteSelectorL2DefinitenessExact as L2Def
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintFiniteKKTExact as RawKKT
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionOrthogonalityExact as Projection
import DASHI.Physics.YangMills.BalabanSelectedPaddedReducedNormalInverseExact as ReducedInverse
import DASHI.Physics.YangMills.BalabanSelectedReducedConstraintTangentProjectorExact as Tangent
import DASHI.Physics.YangMills.BalabanSelectedReducedNormalCorrectionBoundExact as Bound

StateVector : Set
StateVector = StateCarrier.StateVector

MultiplierVector : Set
MultiplierVector = ReducedInverse.RawMultiplier

stateDot : StateVector → StateVector → ℚ
stateDot = Rect.finiteDot StateCarrier.physicalStateCarrier

stateNormSq : StateVector → ℚ
stateNormSq = Rect.finiteNormSq StateCarrier.physicalStateCarrier

------------------------------------------------------------------------
-- A first variation annihilates the actual reduced linearized tangent kernel.
------------------------------------------------------------------------

AnnihilatesReducedLinearizedKernel :
  ∀ {background} → StateVector → Set
AnnihilatesReducedLinearizedKernel {background} gradient =
  ∀ tangent →
  Tangent.ReducedLinearizedConstraintKernel {background} tangent →
  stateDot gradient tangent ≡ 0ℚ

------------------------------------------------------------------------
-- Exact KKT multiplier: it is literally the multiplier already used by the
-- normal correction/projector, not an independently supplied witness.
------------------------------------------------------------------------

selectedLagrangeMultiplierExact :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (ReducedInverse.selectedPaddedReducedNormalMatrix background) →
  StateVector → MultiplierVector
selectedLagrangeMultiplierExact background certificate gradient =
  Tangent.selectedReducedMultiplierFromState background certificate gradient

selectedLagrangeMultiplierIsReduced :
  ∀ background certificate gradient row →
  Projection.selectedReducedProjection
    (selectedLagrangeMultiplierExact background certificate gradient) row
  ≡ selectedLagrangeMultiplierExact background certificate gradient row
selectedLagrangeMultiplierIsReduced background certificate gradient row =
  ReducedInverse.selectedReducedNormalInverseIsReduced
    background certificate
    (Tangent.selectedReducedConstraintApply background gradient) row

selectedNormalFromLagrangeMultiplier :
  ∀ background certificate gradient coordinate →
  Tangent.selectedReducedNormalCorrection background certificate gradient coordinate
  ≡ RawKKT.selectedCombinedConstraintTransposeApply background
      (selectedLagrangeMultiplierExact background certificate gradient) coordinate
selectedNormalFromLagrangeMultiplier background certificate gradient coordinate = refl

------------------------------------------------------------------------
-- Finite dot helpers.
------------------------------------------------------------------------

stateDotLeftCong : ∀ left right test →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  stateDot left test ≡ stateDot right test
stateDotLeftCong left right test pointwise =
  Sums.sumRationalCong (Matrix.coordinates StateCarrier.physicalStateCarrier) _ _
    (λ coordinate → cong (_* test coordinate) (pointwise coordinate))

stateDotAddLeftExact : ∀ left right test →
  stateDot (Tangent.stateAdd left right) test
  ≡ stateDot left test + stateDot right test
stateDotAddLeftExact left right test =
  Fubini.sumRationalAdd
    (Matrix.coordinates StateCarrier.physicalStateCarrier)
    (λ coordinate → left coordinate * test coordinate)
    (λ coordinate → right coordinate * test coordinate)

stateDotScaleLeftExact : ∀ coefficient vector test →
  stateDot (Tangent.stateScale coefficient vector) test
  ≡ coefficient * stateDot vector test
stateDotScaleLeftExact coefficient vector test =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates StateCarrier.physicalStateCarrier) _ _
      (λ coordinate → ℚRing.solve-∀
        coefficient (vector coordinate) (test coordinate)))
    (Sums.sumRationalScale coefficient
      (Matrix.coordinates StateCarrier.physicalStateCarrier)
      (λ coordinate → vector coordinate * test coordinate))

stateReconstructFromProjector :
  ∀ background certificate gradient coordinate →
  gradient coordinate
  ≡ Tangent.selectedPhysicalTangentProjectorReduced
      background certificate gradient coordinate
    + Tangent.selectedReducedNormalCorrection
        background certificate gradient coordinate
stateReconstructFromProjector background certificate gradient coordinate =
  ℚRing.solve-∀
    (gradient coordinate)
    (Tangent.selectedReducedNormalCorrection
      background certificate gradient coordinate)

------------------------------------------------------------------------
-- The normal correction is orthogonal to the projected tangent component.
------------------------------------------------------------------------

normalOrthogonalProjected :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    gradient →
  stateDot
    (Tangent.selectedReducedNormalCorrection background certificate gradient)
    (Tangent.selectedPhysicalTangentProjectorReduced
      background certificate gradient)
  ≡ 0ℚ
normalOrthogonalProjected background certificate gradient =
  let
    projected = Tangent.selectedPhysicalTangentProjectorReduced
      background certificate gradient
    multiplier = selectedLagrangeMultiplierExact
      background certificate gradient
    rawConstraint = Combined.selectedBackgroundCombinedConstraintApply
      background projected
    reducedConstraint = Tangent.selectedReducedConstraintApply
      background projected

    projectedKernel =
      Tangent.selectedPhysicalTangentProjectorReducedInKernel
        background certificate gradient

    adjointIdentity = Rect.rectangularAdjointExact
      Rows.selectedCombinedConstraintRowCarrier
      StateCarrier.physicalStateCarrier
      (Combined.selectedBackgroundLinearizedConstraintMatrix background)
      projected multiplier

    rawDotReduced :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
        rawConstraint multiplier
      ≡ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
        reducedConstraint multiplier
    rawDotReduced =
      sym
        (Bound.selectedProjectionDotReducedExact
          rawConstraint multiplier
          (selectedLagrangeMultiplierIsReduced
            background certificate gradient))

    reducedDotZero :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
        reducedConstraint multiplier ≡ 0ℚ
    reducedDotZero =
      trans
        (Sums.sumRationalCong Rows.selectedCombinedConstraintRows _ (λ _ → 0ℚ)
          (λ row → trans
            (cong (_* multiplier row) (projectedKernel row))
            (ℚRing.solve-∀ (multiplier row))))
        (Fubini.sumRationalZero Rows.selectedCombinedConstraintRows)
  in
  trans
    (Rect.finiteDotSymmetric StateCarrier.physicalStateCarrier
      (Tangent.selectedReducedNormalCorrection background certificate gradient)
      projected)
    (trans
      (sym adjointIdentity)
      (trans rawDotReduced reducedDotZero))

------------------------------------------------------------------------
-- Kernel annihilation forces the projected component to vanish pointwise.
------------------------------------------------------------------------

projectedGradientNormZero :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    gradient →
  AnnihilatesReducedLinearizedKernel {background} gradient →
  stateNormSq
    (Tangent.selectedPhysicalTangentProjectorReduced
      background certificate gradient)
  ≡ 0ℚ
projectedGradientNormZero background certificate gradient annihilates =
  let
    projected = Tangent.selectedPhysicalTangentProjectorReduced
      background certificate gradient
    normal = Tangent.selectedReducedNormalCorrection
      background certificate gradient

    projectedKernel = Tangent.selectedPhysicalTangentProjectorReducedInKernel
      background certificate gradient

    gradientDotZero : stateDot gradient projected ≡ 0ℚ
    gradientDotZero = annihilates projected projectedKernel

    normalDotZero : stateDot normal projected ≡ 0ℚ
    normalDotZero = normalOrthogonalProjected background certificate gradient

    reconstructDot :
      stateDot gradient projected
      ≡ stateDot projected projected + stateDot normal projected
    reconstructDot =
      trans
        (stateDotLeftCong gradient
          (Tangent.stateAdd projected normal) projected
          (stateReconstructFromProjector background certificate gradient))
        (stateDotAddLeftExact projected normal projected)

    dotNormExact : stateDot projected projected ≡ stateNormSq projected
    dotNormExact = refl
  in
  trans
    (sym dotNormExact)
    (trans
      (sym (ℚRing.solve-∀ (stateDot projected projected) :
        stateDot projected projected + 0ℚ ≡ stateDot projected projected))
      (trans
        (cong
          (stateDot projected projected +_)
          (sym normalDotZero))
        (trans
          (sym reconstructDot)
          gradientDotZero)))

stateNormZeroPointwise : ∀ vector →
  stateNormSq vector ≡ 0ℚ →
  ∀ coordinate → vector coordinate ≡ 0ℚ
stateNormZeroPointwise vector normZero =
  L2Def.finiteSelectorNormZeroPointwise
    Basis.physicalCoordinateFiniteSelector vector normZero

selectedProjectedEulerLagrangeExact :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    gradient →
  AnnihilatesReducedLinearizedKernel {background} gradient →
  ∀ coordinate →
  Tangent.selectedPhysicalTangentProjectorReduced
    background certificate gradient coordinate ≡ 0ℚ
selectedProjectedEulerLagrangeExact
    background certificate gradient annihilates =
  stateNormZeroPointwise
    (Tangent.selectedPhysicalTangentProjectorReduced
      background certificate gradient)
    (projectedGradientNormZero
      background certificate gradient annihilates)

selectedFirstVariationInReducedAdjointRange :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    gradient →
  AnnihilatesReducedLinearizedKernel {background} gradient →
  ∀ coordinate →
  gradient coordinate
  ≡ RawKKT.selectedCombinedConstraintTransposeApply background
      (selectedLagrangeMultiplierExact background certificate gradient) coordinate
selectedFirstVariationInReducedAdjointRange
    background certificate gradient annihilates coordinate =
  let
    projectedZero = selectedProjectedEulerLagrangeExact
      background certificate gradient annihilates coordinate
    normal = Tangent.selectedReducedNormalCorrection
      background certificate gradient
  in
  trans
    (stateReconstructFromProjector background certificate gradient coordinate)
    (trans
      (cong (_+ normal coordinate) projectedZero)
      (ℚRing.solve-∀ (normal coordinate)))

selectedReducedKKTMultiplierLevel : ProofLevel
selectedReducedKKTMultiplierLevel = machineChecked

selectedReducedProjectedEulerLagrangeLevel : ProofLevel
selectedReducedProjectedEulerLagrangeLevel = machineChecked

selectedReducedKKTPhysicalStationarityLevel : ProofLevel
selectedReducedKKTPhysicalStationarityLevel = conditional
