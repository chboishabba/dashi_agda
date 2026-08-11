module DASHI.Physics.YangMills.BalabanSelectedPaddedReducedNormalInverseExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
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
-- Reopen the selected reduced normal equation without inventing a hand-built
-- 777-coordinate carrier.  On the literal 780-row multiplier carrier let
--
--       P = componentwise-mean-zero reduced projection,
--       C = constant gauge complement,
--       K_A = L_A L_A^*.
--
-- Define the padded square endomorphism
--
--       K~_A lambda = K_A(P lambda) + C lambda.
--
-- The already-proved orthogonal split gives <C lambda,P lambda>=0.  Therefore
-- K~_A lambda=0 implies
--
--       <K_A(P lambda),P lambda> = 0
--       = ||L_A^* P lambda||^2.
--
-- The strict selected 29/1024 reduced-adjoint floor forces P lambda=0; the
-- padded equation then forces C lambda=0, and exact reconstruction gives
-- lambda=0.  Thus K~_A is injective.  The standard finite-dimensional theorem
-- injective=>invertible over Q supplies a proof-relevant rational inverse.
--
-- For every reduced source y=P y, solve K~_A x=y and return P x.  Applying P
-- to the equation and using P C=0 proves
--
--       P K_A (P K~_A^-1 y) = y.
--
-- Hence this is an honest right inverse of the reduced normal operator, which
-- is exactly what the physical tangent normal correction needs.  No inverse of
-- the singular raw K_A is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; -_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRationalInjectiveInverseExact as FiniteInverse
import DASHI.Physics.YangMills.BalabanFiniteLinearEndomorphismMatrixExact as Endo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as StateCarrier
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintFiniteKKTExact as RawKKT
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionOrthogonalityExact as Projection
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionCongruenceExact as ProjectionCong
import DASHI.Physics.YangMills.BalabanSelectedReducedCombinedConstraintFloorExact as Floor
import DASHI.Physics.YangMills.BalabanSelectedReducedCombinedAdjointInjectiveExact as Injective

RawMultiplier : Set
RawMultiplier = Projection.RawMultiplier

zeroRawMultiplier : RawMultiplier
zeroRawMultiplier _ = 0ℚ

selectedReducedProjection : RawMultiplier → RawMultiplier
selectedReducedProjection = Projection.selectedReducedProjection

selectedConstantComplement : RawMultiplier → RawMultiplier
selectedConstantComplement = Projection.selectedConstantComplement

minusOne : ℚ
minusOne = - (+ 1 / 1)

------------------------------------------------------------------------
-- Raw Gram pointwise congruence and linearity.
------------------------------------------------------------------------

gramRespectsPointwise : ∀ background left right →
  (∀ row → left row ≡ right row) →
  ∀ row →
  RawKKT.selectedCombinedConstraintGramApply background left row
  ≡ RawKKT.selectedCombinedConstraintGramApply background right row
gramRespectsPointwise background left right pointwise row =
  let matrix = Combined.selectedBackgroundConstraintGram background in
  Sums.sumRationalCong Rows.selectedCombinedConstraintRows _ _
    (λ column → cong (matrix row column *_) (pointwise column))

gramAddExact : ∀ background left right row →
  RawKKT.selectedCombinedConstraintGramApply background
      (Projection.rawAdd left right) row
  ≡ RawKKT.selectedCombinedConstraintGramApply background left row
    + RawKKT.selectedCombinedConstraintGramApply background right row
gramAddExact background left right row =
  Rect.applyRectangularAddExact
    Rows.selectedCombinedConstraintRowCarrier
    (Combined.selectedBackgroundConstraintGram background)
    left right row

gramScaleExact : ∀ background coefficient multiplier row →
  RawKKT.selectedCombinedConstraintGramApply background
      (Projection.rawScale coefficient multiplier) row
  ≡ coefficient
      * RawKKT.selectedCombinedConstraintGramApply background multiplier row
gramScaleExact background coefficient multiplier row =
  let
    values = Rows.selectedCombinedConstraintRows
    matrix = Combined.selectedBackgroundConstraintGram background
  in
  trans
    (Sums.sumRationalCong values _ _
      (λ column → ℚRing.solve-∀
        (matrix row column) coefficient (multiplier column)))
    (Sums.sumRationalScale coefficient values
      (λ column → matrix row column * multiplier column))

gramZeroExact : ∀ background row →
  RawKKT.selectedCombinedConstraintGramApply background zeroRawMultiplier row
  ≡ 0ℚ
gramZeroExact background row =
  trans
    (Sums.sumRationalCong Rows.selectedCombinedConstraintRows _ (λ _ → 0ℚ)
      (λ column → ℚRing.solve-∀
        (Combined.selectedBackgroundConstraintGram background row column)))
    (Fubini.sumRationalZero Rows.selectedCombinedConstraintRows)

------------------------------------------------------------------------
-- The padded normal endomorphism and exact rational linearity.
------------------------------------------------------------------------

selectedPaddedReducedNormalApply :
  Physical.RationalSU2Background4 → RawMultiplier → RawMultiplier
selectedPaddedReducedNormalApply background multiplier row =
  RawKKT.selectedCombinedConstraintGramApply background
      (selectedReducedProjection multiplier) row
  + selectedConstantComplement multiplier row

selectedProjectionZero : ∀ row →
  selectedReducedProjection zeroRawMultiplier row ≡ 0ℚ
selectedProjectionZero row =
  trans
    (Projection.selectedProjectionScaleExact 0ℚ zeroRawMultiplier row)
    (ℚRing.solve-∀ (selectedReducedProjection zeroRawMultiplier row))

selectedComplementZero : ∀ row →
  selectedConstantComplement zeroRawMultiplier row ≡ 0ℚ
selectedComplementZero row =
  trans
    (Projection.selectedComplementScaleExact 0ℚ zeroRawMultiplier row)
    (ℚRing.solve-∀ (selectedConstantComplement zeroRawMultiplier row))

selectedPaddedReducedNormalZeroExact : ∀ background row →
  selectedPaddedReducedNormalApply background zeroRawMultiplier row ≡ 0ℚ
selectedPaddedReducedNormalZeroExact background row =
  trans
    (cong₂ _+_
      (trans
        (gramRespectsPointwise background
          (selectedReducedProjection zeroRawMultiplier) zeroRawMultiplier
          selectedProjectionZero row)
        (gramZeroExact background row))
      (selectedComplementZero row))
    (ℚRing.solve [])

selectedPaddedReducedNormalAddExact : ∀ background left right row →
  selectedPaddedReducedNormalApply background
      (Projection.rawAdd left right) row
  ≡ Projection.rawAdd
      (selectedPaddedReducedNormalApply background left)
      (selectedPaddedReducedNormalApply background right) row
selectedPaddedReducedNormalAddExact background left right row =
  let
    projectedAdd = Projection.rawAdd
      (selectedReducedProjection left) (selectedReducedProjection right)
  in
  trans
    (cong₂ _+_
      (trans
        (gramRespectsPointwise background
          (selectedReducedProjection (Projection.rawAdd left right))
          projectedAdd
          (Projection.selectedProjectionAddExact left right)
          row)
        (gramAddExact background
          (selectedReducedProjection left) (selectedReducedProjection right) row))
      (Projection.selectedComplementAddExact left right row))
    (ℚRing.solve-∀
      (RawKKT.selectedCombinedConstraintGramApply background
        (selectedReducedProjection left) row)
      (RawKKT.selectedCombinedConstraintGramApply background
        (selectedReducedProjection right) row)
      (selectedConstantComplement left row)
      (selectedConstantComplement right row))

selectedPaddedReducedNormalScaleExact : ∀ background coefficient multiplier row →
  selectedPaddedReducedNormalApply background
      (Projection.rawScale coefficient multiplier) row
  ≡ Projection.rawScale coefficient
      (selectedPaddedReducedNormalApply background multiplier) row
selectedPaddedReducedNormalScaleExact background coefficient multiplier row =
  trans
    (cong₂ _+_
      (trans
        (gramRespectsPointwise background
          (selectedReducedProjection
            (Projection.rawScale coefficient multiplier))
          (Projection.rawScale coefficient
            (selectedReducedProjection multiplier))
          (Projection.selectedProjectionScaleExact coefficient multiplier)
          row)
        (gramScaleExact background coefficient
          (selectedReducedProjection multiplier) row))
      (Projection.selectedComplementScaleExact coefficient multiplier row))
    (ℚRing.solve-∀ coefficient
      (RawKKT.selectedCombinedConstraintGramApply background
        (selectedReducedProjection multiplier) row)
      (selectedConstantComplement multiplier row))

selectedPaddedReducedNormalRespectsPointwise : ∀ background left right →
  (∀ row → left row ≡ right row) →
  ∀ row →
  selectedPaddedReducedNormalApply background left row
  ≡ selectedPaddedReducedNormalApply background right row
selectedPaddedReducedNormalRespectsPointwise background left right pointwise row =
  cong₂ _+_
    (gramRespectsPointwise background
      (selectedReducedProjection left) (selectedReducedProjection right)
      (ProjectionCong.selectedProjectionRespectsPointwise left right pointwise)
      row)
    (ProjectionCong.selectedComplementRespectsPointwise left right pointwise row)

selectedPaddedReducedNormalEndomorphism :
  Physical.RationalSU2Background4 →
  Endo.FiniteLinearEndomorphism Rows.selectedCombinedConstraintRowCarrier
selectedPaddedReducedNormalEndomorphism background = record
  { Endo.FiniteLinearEndomorphism.operator =
      selectedPaddedReducedNormalApply background
  ; Endo.FiniteLinearEndomorphism.zeroExact =
      selectedPaddedReducedNormalZeroExact background
  ; Endo.FiniteLinearEndomorphism.addExact =
      selectedPaddedReducedNormalAddExact background
  ; Endo.FiniteLinearEndomorphism.scaleExact =
      selectedPaddedReducedNormalScaleExact background
  ; Endo.FiniteLinearEndomorphism.pointwiseCong =
      selectedPaddedReducedNormalRespectsPointwise background
  }

selectedPaddedReducedNormalMatrix :
  Physical.RationalSU2Background4 →
  Matrix.RationalMatrix Combined.SelectedConstraintRow4
selectedPaddedReducedNormalMatrix background =
  Endo.endomorphismMatrix (selectedPaddedReducedNormalEndomorphism background)

selectedPaddedReducedNormalMatrixActsExactly : ∀ background multiplier row →
  Matrix.applyMatrix Rows.selectedCombinedConstraintRowCarrier
    (selectedPaddedReducedNormalMatrix background) multiplier row
  ≡ selectedPaddedReducedNormalApply background multiplier row
selectedPaddedReducedNormalMatrixActsExactly background =
  Endo.endomorphismMatrixActsExactly
    (selectedPaddedReducedNormalEndomorphism background)

------------------------------------------------------------------------
-- Homogeneous padded equation => P part zero by the physical 29/1024 floor.
------------------------------------------------------------------------

finiteDotAddLeftExact : ∀ left right test →
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
    (Rect.vectorAdd left right) test
  ≡ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier left test
    + Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier right test
finiteDotAddLeftExact left right test =
  Fubini.sumRationalAdd Rows.selectedCombinedConstraintRows
    (λ row → left row * test row)
    (λ row → right row * test row)

finiteDotPointwiseZero : ∀ vector test →
  (∀ row → vector row ≡ 0ℚ) →
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier vector test ≡ 0ℚ
finiteDotPointwiseZero vector test pointwise =
  trans
    (Sums.sumRationalCong Rows.selectedCombinedConstraintRows _ (λ _ → 0ℚ)
      (λ row → trans
        (cong (_* test row) (pointwise row))
        (ℚRing.solve-∀ (test row))))
    (Fubini.sumRationalZero Rows.selectedCombinedConstraintRows)

projectionAdjointNormZeroFromPaddedZero :
  ∀ background multiplier →
  (∀ row → selectedPaddedReducedNormalApply background multiplier row ≡ 0ℚ) →
  Rect.finiteNormSq StateCarrier.physicalStateCarrier
    (RawKKT.selectedCombinedConstraintTransposeApply background
      (selectedReducedProjection multiplier))
  ≡ 0ℚ
projectionAdjointNormZeroFromPaddedZero background multiplier paddedZero =
  let
    projected = selectedReducedProjection multiplier
    complement = selectedConstantComplement multiplier
    gram = RawKKT.selectedCombinedConstraintGramApply background projected

    paddedDotZero :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
        (selectedPaddedReducedNormalApply background multiplier) projected
      ≡ 0ℚ
    paddedDotZero = finiteDotPointwiseZero
      (selectedPaddedReducedNormalApply background multiplier) projected paddedZero

    splitDot :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
        (selectedPaddedReducedNormalApply background multiplier) projected
      ≡ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier gram projected
        + Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier complement projected
    splitDot = finiteDotAddLeftExact gram complement projected

    crossZero :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier complement projected
      ≡ 0ℚ
    crossZero = Projection.selectedComplementProjectionOrthogonal multiplier multiplier

    sumZero :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier gram projected
        + Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier complement projected
      ≡ 0ℚ
    sumZero = trans (sym splitDot) paddedDotZero

    removeZero :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier gram projected + 0ℚ
      ≡ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier gram projected
    removeZero = ℚRing.solve-∀
      (Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier gram projected)

    gramDotZero :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier gram projected ≡ 0ℚ
    gramDotZero =
      trans
        (sym removeZero)
        (trans
          (cong
            (Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier gram projected +_)
            (sym crossZero))
          sumZero)
  in
  trans
    (sym
      (RawKKT.selectedCombinedConstraintGramQuadraticExact background projected))
    gramDotZero

projectionReducedNormZeroFromPaddedZero :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  (∀ row → selectedPaddedReducedNormalApply background multiplier row ≡ 0ℚ) →
  Floor.reducedCombinedMultiplierNormSq
    (Split.reduceSelectedMultiplier multiplier) ≡ 0ℚ
projectionReducedNormZeroFromPaddedZero background radius multiplier paddedZero =
  let
    selected = Split.reduceSelectedMultiplier multiplier
    adjointNormZero = projectionAdjointNormZeroFromPaddedZero
      background multiplier paddedZero

    floorRaw = Floor.selectedBackgroundReducedCombinedAdjointFloor
      background radius selected

    floorToZero :
      Floor.selectedBackgroundReducedCombinedFloor
        * Floor.reducedCombinedMultiplierNormSq selected
      ≤ 0ℚ
    floorToZero =
      subst
        (λ upper →
          Floor.selectedBackgroundReducedCombinedFloor
            * Floor.reducedCombinedMultiplierNormSq selected
          ≤ upper)
        adjointNormZero floorRaw

    scaled = Norm.scaleNonnegative Injective.reciprocalReducedFloor
      Injective.reciprocalReducedFloorNonnegative floorToZero

    leftExact :
      Injective.reciprocalReducedFloor
        * (Floor.selectedBackgroundReducedCombinedFloor
            * Floor.reducedCombinedMultiplierNormSq selected)
      ≡ Floor.reducedCombinedMultiplierNormSq selected
    leftExact = ℚRing.solve-∀ (Floor.reducedCombinedMultiplierNormSq selected)

    rightExact : Injective.reciprocalReducedFloor * 0ℚ ≡ 0ℚ
    rightExact = ℚRing.solve []

    normBelowZero : Floor.reducedCombinedMultiplierNormSq selected ≤ 0ℚ
    normBelowZero =
      subst
        (λ lower → lower ≤ 0ℚ)
        leftExact
        (subst
          (λ upper →
            Injective.reciprocalReducedFloor
              * (Floor.selectedBackgroundReducedCombinedFloor
                  * Floor.reducedCombinedMultiplierNormSq selected)
            ≤ upper)
          rightExact scaled)
  in
  ℚP.≤-antisym normBelowZero
    (Injective.combinedMultiplierNormNonnegative selected)

projectionPointwiseZeroFromPaddedZero :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  (∀ row → selectedPaddedReducedNormalApply background multiplier row ≡ 0ℚ) →
  ∀ row → selectedReducedProjection multiplier row ≡ 0ℚ
projectionPointwiseZeroFromPaddedZero
    background radius multiplier paddedZero (Combined.averageConstraintRow row) =
  let
    selected = Split.reduceSelectedMultiplier multiplier
    combinedZero = projectionReducedNormZeroFromPaddedZero
      background radius multiplier paddedZero
    averageNormZero = Injective.averageNormZeroFromCombinedZero selected combinedZero
  in
  Injective.averageNormZeroPointwise selected averageNormZero row
projectionPointwiseZeroFromPaddedZero
    background radius multiplier paddedZero (Combined.gaugeConstraintRow row) =
  let
    selected = Split.reduceSelectedMultiplier multiplier
    combinedZero = projectionReducedNormZeroFromPaddedZero
      background radius multiplier paddedZero
    gaugeNormZero = Injective.gaugeNormZeroFromCombinedZero selected combinedZero
  in
  Injective.gaugeNormZeroPointwise selected gaugeNormZero row

paddedHomogeneousKernelTrivial :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  (∀ row → selectedPaddedReducedNormalApply background multiplier row ≡ 0ℚ) →
  ∀ row → multiplier row ≡ 0ℚ
paddedHomogeneousKernelTrivial background radius multiplier paddedZero row =
  let
    projectionZero = projectionPointwiseZeroFromPaddedZero
      background radius multiplier paddedZero

    gramProjectionZero :
      RawKKT.selectedCombinedConstraintGramApply background
        (selectedReducedProjection multiplier) row ≡ 0ℚ
    gramProjectionZero =
      trans
        (gramRespectsPointwise background
          (selectedReducedProjection multiplier) zeroRawMultiplier
          projectionZero row)
        (gramZeroExact background row)

    equation :
      RawKKT.selectedCombinedConstraintGramApply background
          (selectedReducedProjection multiplier) row
        + selectedConstantComplement multiplier row
      ≡ 0ℚ
    equation = paddedZero row

    insertZero :
      0ℚ + selectedConstantComplement multiplier row
      ≡ selectedConstantComplement multiplier row
    insertZero = ℚRing.solve-∀ (selectedConstantComplement multiplier row)

    complementZero : selectedConstantComplement multiplier row ≡ 0ℚ
    complementZero =
      trans
        (sym insertZero)
        (trans
          (cong (_+ selectedConstantComplement multiplier row)
            (sym gramProjectionZero))
          equation)
  in
  trans
    (Projection.selectedProjectionComplementReconstruct multiplier row)
    (trans
      (cong₂ _+_ (projectionZero row) complementZero)
      (ℚRing.solve []))

------------------------------------------------------------------------
-- Pointwise injectivity of K~ and its exact finite rational inverse.
------------------------------------------------------------------------

selectedPaddedReducedNormalInjective :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  Endo.PointwiseInjectiveEndomorphism
    (selectedPaddedReducedNormalEndomorphism background)
selectedPaddedReducedNormalInjective background radius left right equal row =
  let
    difference = Projection.rawAdd left (Projection.rawScale minusOne right)

    differenceEquation : ∀ selected →
      selectedPaddedReducedNormalApply background difference selected ≡ 0ℚ
    differenceEquation selected =
      trans
        (selectedPaddedReducedNormalAddExact background
          left (Projection.rawScale minusOne right) selected)
        (trans
          (cong
            (selectedPaddedReducedNormalApply background left selected +_)
            (selectedPaddedReducedNormalScaleExact background
              minusOne right selected))
          (trans
            (cong
              (λ leftValue →
                leftValue
                  + minusOne
                    * selectedPaddedReducedNormalApply background right selected)
              (equal selected))
            (ℚRing.solve-∀
              (selectedPaddedReducedNormalApply background right selected))))

    differenceZero = paddedHomogeneousKernelTrivial
      background radius difference differenceEquation

    reconstructLeft :
      (left row + minusOne * right row) + right row ≡ left row
    reconstructLeft = ℚRing.solve-∀ (left row) (right row)
  in
  trans
    (sym reconstructLeft)
    (trans
      (cong (_+ right row) (differenceZero row))
      (ℚRing.solve-∀ (right row)))

selectedPaddedReducedNormalMatrixInjective :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  FiniteInverse.PointwiseInjective Rows.selectedCombinedConstraintRowCarrier
    (selectedPaddedReducedNormalMatrix background)
selectedPaddedReducedNormalMatrixInjective background radius =
  Endo.endomorphismInjectiveImpliesMatrixInjective
    (selectedPaddedReducedNormalEndomorphism background)
    (selectedPaddedReducedNormalInjective background radius)

selectedPaddedReducedNormalInverseCertificate :
  FiniteInverse.FiniteRationalInjectiveInverseAuthority →
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (selectedPaddedReducedNormalMatrix background)
selectedPaddedReducedNormalInverseCertificate authority background radius =
  FiniteInverse.finiteSquareInjectiveImpliesRationalInverse authority
    Rows.selectedCombinedConstraintRowCarrier
    (selectedPaddedReducedNormalMatrix background)
    (selectedPaddedReducedNormalMatrixInjective background radius)

selectedPaddedReducedNormalInverseApply :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (selectedPaddedReducedNormalMatrix background) →
  RawMultiplier → RawMultiplier
selectedPaddedReducedNormalInverseApply background certificate =
  Matrix.applyMatrix Rows.selectedCombinedConstraintRowCarrier
    (Matrix.inverseMatrix certificate)

------------------------------------------------------------------------
-- Restriction of the padded inverse is a right inverse for the reduced normal.
------------------------------------------------------------------------

ReducedSource : RawMultiplier → Set
ReducedSource source = ∀ row → selectedReducedProjection source row ≡ source row

selectedReducedCombinedGramApply :
  Physical.RationalSU2Background4 → RawMultiplier → RawMultiplier
selectedReducedCombinedGramApply background multiplier =
  selectedReducedProjection
    (RawKKT.selectedCombinedConstraintGramApply background multiplier)

selectedReducedNormalInverseApply :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (selectedPaddedReducedNormalMatrix background) →
  RawMultiplier → RawMultiplier
selectedReducedNormalInverseApply background certificate source =
  selectedReducedProjection
    (selectedPaddedReducedNormalInverseApply background certificate source)

selectedReducedNormalInverseIsReduced :
  ∀ background certificate source row →
  selectedReducedProjection
    (selectedReducedNormalInverseApply background certificate source) row
  ≡ selectedReducedNormalInverseApply background certificate source row
selectedReducedNormalInverseIsReduced background certificate source row =
  Projection.selectedProjectionIdempotent
    (selectedPaddedReducedNormalInverseApply background certificate source) row

selectedReducedCombinedGramRightInverse :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (selectedPaddedReducedNormalMatrix background))
    source →
  ReducedSource source →
  ∀ row →
  selectedReducedCombinedGramApply background
      (selectedReducedNormalInverseApply background certificate source) row
  ≡ source row
selectedReducedCombinedGramRightInverse background certificate source sourceReduced row =
  let
    fullSolution = selectedPaddedReducedNormalInverseApply
      background certificate source
    reducedSolution = selectedReducedProjection fullSolution
    gram = RawKKT.selectedCombinedConstraintGramApply background reducedSolution
    complement = selectedConstantComplement fullSolution

    fullEquation : ∀ selected →
      selectedPaddedReducedNormalApply background fullSolution selected
      ≡ source selected
    fullEquation selected =
      trans
        (sym
          (selectedPaddedReducedNormalMatrixActsExactly
            background fullSolution selected))
        (Matrix.matrixInverseRightExact certificate source selected)

    projectEquation :
      selectedReducedProjection
        (selectedPaddedReducedNormalApply background fullSolution) row
      ≡ selectedReducedProjection source row
    projectEquation = ProjectionCong.selectedProjectionRespectsPointwise
      (selectedPaddedReducedNormalApply background fullSolution)
      source fullEquation row

    complementKilled :
      selectedReducedProjection complement row ≡ 0ℚ
    complementKilled = Projection.selectedProjectionOfComplementZero fullSolution row

    projectedPaddedSplits :
      selectedReducedProjection
        (selectedPaddedReducedNormalApply background fullSolution) row
      ≡ selectedReducedCombinedGramApply background reducedSolution row
    projectedPaddedSplits =
      trans
        (Projection.selectedProjectionAddExact gram complement row)
        (trans
          (cong₂ _+_ refl complementKilled)
          (ℚRing.solve-∀
            (selectedReducedCombinedGramApply background reducedSolution row)))
  in
  trans
    (sym projectedPaddedSplits)
    (trans projectEquation (sourceReduced row))

selectedPaddedReducedNormalEndomorphismLevel : ProofLevel
selectedPaddedReducedNormalEndomorphismLevel = machineChecked

selectedPaddedReducedNormalInjectivityLevel : ProofLevel
selectedPaddedReducedNormalInjectivityLevel = machineChecked

selectedPaddedReducedNormalInverseAuthorityLevel : ProofLevel
selectedPaddedReducedNormalInverseAuthorityLevel = standardImported

selectedReducedCombinedGramRightInverseLevel : ProofLevel
selectedReducedCombinedGramRightInverseLevel = machineChecked
