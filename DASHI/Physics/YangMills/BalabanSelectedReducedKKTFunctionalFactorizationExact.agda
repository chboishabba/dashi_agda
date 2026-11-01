module DASHI.Physics.YangMills.BalabanSelectedReducedKKTFunctionalFactorizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
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
-- Strengthen the already-proved same-normal-solve KKT vector identity into
-- the canonical functional factorization requested by Gate I.
--
-- The preceding module proves, for a gradient g annihilating the reduced
-- tangent kernel,
--
--   g = L_A^* lambda_A
--
-- pointwise, where lambda_A is literally the multiplier produced by the same
-- reduced normal solve used in the tangent projector.  Here we pair this
-- identity against an arbitrary ambient state v, use the exact rectangular
-- adjoint theorem, and then use reducedness of lambda_A to replace the raw
-- constraint by P L_A v.  Thus
--
--   <g,v> = <P L_A v, lambda_A>.
--
-- In functional notation this is exactly
--
--   DS_A = lambda_A o D C_A,
--
-- with no independent dual-space existence argument and no second multiplier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as StateCarrier
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionOrthogonalityExact as Projection
import DASHI.Physics.YangMills.BalabanSelectedPaddedReducedNormalInverseExact as ReducedInverse
import DASHI.Physics.YangMills.BalabanSelectedReducedConstraintTangentProjectorExact as Tangent
import DASHI.Physics.YangMills.BalabanSelectedReducedNormalCorrectionBoundExact as Bound
import DASHI.Physics.YangMills.BalabanSelectedReducedKKTMultiplierExact as KKT

StateVector : Set
StateVector = StateCarrier.StateVector

MultiplierVector : Set
MultiplierVector = ReducedInverse.RawMultiplier

canonicalReducedConstraintFunctional : MultiplierVector → MultiplierVector → ℚ
canonicalReducedConstraintFunctional multiplier reducedConstraint =
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
    reducedConstraint multiplier

selectedReducedKKTFunctionalFactorizationExact :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    gradient →
  KKT.AnnihilatesReducedLinearizedKernel {background} gradient →
  ∀ state →
  KKT.stateDot gradient state
  ≡ canonicalReducedConstraintFunctional
      (KKT.selectedLagrangeMultiplierExact background certificate gradient)
      (Tangent.selectedReducedConstraintApply background state)
selectedReducedKKTFunctionalFactorizationExact
    background certificate gradient annihilates state =
  let
    multiplier = KKT.selectedLagrangeMultiplierExact
      background certificate gradient
    adjoint =
      Combined.selectedBackgroundCombinedConstraintTransposeApply
        background multiplier
    rawConstraint =
      Combined.selectedBackgroundCombinedConstraintApply background state
    reducedConstraint =
      Tangent.selectedReducedConstraintApply background state

    gradientIsAdjoint : ∀ coordinate →
      gradient coordinate ≡ adjoint coordinate
    gradientIsAdjoint =
      KKT.selectedFirstVariationInReducedAdjointRange
        background certificate gradient annihilates

    replaceGradient :
      KKT.stateDot gradient state ≡ KKT.stateDot adjoint state
    replaceGradient =
      KKT.stateDotLeftCong gradient adjoint state gradientIsAdjoint

    swapStateDot :
      KKT.stateDot adjoint state ≡ KKT.stateDot state adjoint
    swapStateDot =
      Rect.finiteDotSymmetric StateCarrier.physicalStateCarrier adjoint state

    adjointIdentity :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
        rawConstraint multiplier
      ≡ KKT.stateDot state adjoint
    adjointIdentity =
      Rect.rectangularAdjointExact
        Rows.selectedCombinedConstraintRowCarrier
        StateCarrier.physicalStateCarrier
        (Combined.selectedBackgroundLinearizedConstraintMatrix background)
        state multiplier

    rawDotReduced :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
        rawConstraint multiplier
      ≡ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
        reducedConstraint multiplier
    rawDotReduced =
      sym
        (Bound.selectedProjectionDotReducedExact
          rawConstraint multiplier
          (KKT.selectedLagrangeMultiplierIsReduced
            background certificate gradient))
  in
  trans replaceGradient
    (trans swapStateDot
      (trans (sym adjointIdentity) rawDotReduced))

cmp109SelectedReducedKKTFunctionalFactorizationLevel : ProofLevel
cmp109SelectedReducedKKTFunctionalFactorizationLevel = machineChecked

-- The multiplier in the theorem above is definitionally the same normal-solve
-- multiplier used by the reduced tangent projector; this remains a checked
-- same-object statement, not a compatibility receipt.
cmp109SelectedReducedKKTSameNormalSolveFunctionalLevel : ProofLevel
cmp109SelectedReducedKKTSameNormalSolveFunctionalLevel = machineChecked
