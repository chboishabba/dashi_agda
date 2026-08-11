module DASHI.Physics.YangMills.BalabanSelectedReducedNormalCorrectionBoundExact where

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
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Quantify the normal right inverse produced by the strict selected reduced
-- floor.  Let c=29/1024 and, for reduced source y, let
--
--       x = G_red y,
--       n = L_A^* x.
--
-- The exact reduced normal equation gives P K_A x=y.  Since x is reduced and
-- P is orthogonal,
--
--       <y,x> = <K_A x,x> = ||L_A^*x||^2.
--
-- The already-proved floor gives c||x||^2 <= <y,x>.  Combining it with the
-- exact scaled Young inequality
--
--       2c<y,x> <= c^2||x||^2 + ||y||^2
--
-- yields c^2||x||^2 <= ||y||^2 and then
--
--       ||n||^2 <= c^-1 ||y||^2 = (1024/29)||y||^2.
--
-- This is the square-root-free quantitative normal-correction estimate needed
-- to instantiate the repository's existing quantitative implicit-function /
-- Newton machinery.  No new completeness or spectral assumption is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as StateCarrier
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageRowCarrierExact as AverageRows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintFiniteKKTExact as RawKKT
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionOrthogonalityExact as Projection
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionCongruenceExact as ProjectionCong
import DASHI.Physics.YangMills.BalabanSelectedReducedCombinedConstraintFloorExact as Floor
import DASHI.Physics.YangMills.BalabanSelectedPaddedReducedNormalInverseExact as ReducedInverse
import DASHI.Physics.YangMills.BalabanFiniteScaledYoungDotExact as Young

RawMultiplier : Set
RawMultiplier = ReducedInverse.RawMultiplier

selectedFloor : ℚ
selectedFloor = Floor.selectedBackgroundReducedCombinedFloor

selectedFloorReciprocal : ℚ
selectedFloorReciprocal = + 1024 / 29

selectedHalfFloorReciprocal : ℚ
selectedHalfFloorReciprocal = + 512 / 29

selectedFloorNonnegative : 0ℚ ≤ selectedFloor
selectedFloorNonnegative = toWitness {a? = 0ℚ ≤? selectedFloor} _

selectedHalfFloorReciprocalNonnegative : 0ℚ ≤ selectedHalfFloorReciprocal
selectedHalfFloorReciprocalNonnegative =
  toWitness {a? = 0ℚ ≤? selectedHalfFloorReciprocal} _

------------------------------------------------------------------------
-- Dot congruence and the orthogonal-projection identity <Pz,x>=<z,x> for
-- every reduced x.
------------------------------------------------------------------------

finiteDotLeftCong : ∀ left right test →
  (∀ row → left row ≡ right row) →
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier left test
  ≡ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier right test
finiteDotLeftCong left right test pointwise =
  Sums.sumRationalCong Rows.selectedCombinedConstraintRows _ _
    (λ row → cong (_* test row) (pointwise row))

finiteDotRightCong : ∀ test left right →
  (∀ row → left row ≡ right row) →
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier test left
  ≡ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier test right
finiteDotRightCong test left right pointwise =
  Sums.sumRationalCong Rows.selectedCombinedConstraintRows _ _
    (λ row → cong (test row *_) (pointwise row))

finiteDotAddLeftExact : ∀ left right test →
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
    (Rect.vectorAdd left right) test
  ≡ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier left test
    + Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier right test
finiteDotAddLeftExact left right test =
  Fubini.sumRationalAdd Rows.selectedCombinedConstraintRows
    (λ row → left row * test row)
    (λ row → right row * test row)

selectedProjectionDotReducedExact : ∀ source reduced →
  ReducedInverse.ReducedSource reduced →
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
    (Projection.selectedReducedProjection source) reduced
  ≡ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier source reduced
selectedProjectionDotReducedExact source reduced reducedExact =
  let
    complementDotProjection :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
        (Projection.selectedConstantComplement source)
        (Projection.selectedReducedProjection reduced)
      ≡ 0ℚ
    complementDotProjection =
      Projection.selectedComplementProjectionOrthogonal source reduced

    complementDotReduced :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
        (Projection.selectedConstantComplement source) reduced
      ≡ 0ℚ
    complementDotReduced =
      trans
        (sym
          (finiteDotRightCong
            (Projection.selectedConstantComplement source)
            (Projection.selectedReducedProjection reduced) reduced
            reducedExact))
        complementDotProjection

    reconstructDot :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier source reduced
      ≡ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
          (Rect.vectorAdd
            (Projection.selectedReducedProjection source)
            (Projection.selectedConstantComplement source)) reduced
    reconstructDot = finiteDotLeftCong source
      (Rect.vectorAdd
        (Projection.selectedReducedProjection source)
        (Projection.selectedConstantComplement source))
      reduced (Projection.selectedProjectionComplementReconstruct source)

    split = finiteDotAddLeftExact
      (Projection.selectedReducedProjection source)
      (Projection.selectedConstantComplement source) reduced
  in
  sym
    (trans reconstructDot
      (trans split
        (trans
          (cong
            (Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
              (Projection.selectedReducedProjection source) reduced +_)
            complementDotReduced)
          (ℚRing.solve-∀
            (Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
              (Projection.selectedReducedProjection source) reduced)))))

------------------------------------------------------------------------
-- Raw norm of a P-fixed multiplier equals the reduced split norm.
------------------------------------------------------------------------

rawMultiplierNormSq : RawMultiplier → ℚ
rawMultiplierNormSq = Rect.finiteNormSq Rows.selectedCombinedConstraintRowCarrier

rawReducedNormExact : ∀ multiplier →
  rawMultiplierNormSq (Projection.selectedReducedProjection multiplier)
  ≡ Floor.reducedCombinedMultiplierNormSq
      (Split.reduceSelectedMultiplier multiplier)
rawReducedNormExact multiplier =
  let
    projected = Projection.selectedReducedProjection multiplier
    selected = Split.reduceSelectedMultiplier multiplier

    splitRows = Fubini.sumRationalAppend
      (Data.List.Base.map Combined.averageConstraintRow
        (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector))
      (Data.List.Base.map Combined.gaugeConstraintRow
        (Basis.elements Rows.selectedGaugeRowFiniteSelector))
      (λ row → projected row * projected row)

    averageMap = Fubini.sumRationalMap Combined.averageConstraintRow
      (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
      (λ row → projected row * projected row)

    gaugeMap = Fubini.sumRationalMap Combined.gaugeConstraintRow
      (Basis.elements Rows.selectedGaugeRowFiniteSelector)
      (λ row → projected row * projected row)
  in
  trans splitRows
    (trans
      (cong
        (λ averagePart → averagePart
          + Sums.sumRational
              (Basis.elements Rows.selectedGaugeRowFiniteSelector)
              (λ row → projected (Combined.gaugeConstraintRow row)
                * projected (Combined.gaugeConstraintRow row)))
        averageMap)
      (trans
        (cong
          (λ averagePart → averagePart
            + Sums.sumRational
                (Basis.elements Rows.selectedGaugeRowFiniteSelector)
                (λ row → projected (Combined.gaugeConstraintRow row)
                  * projected (Combined.gaugeConstraintRow row)))
          refl)
        (trans
          (cong
            (Floor.averageMultiplierNormSq selected +_)
            gaugeMap)
          refl)))

rawNormOfReducedSourceExact : ∀ source →
  ReducedInverse.ReducedSource source →
  rawMultiplierNormSq source
  ≡ Floor.reducedCombinedMultiplierNormSq
      (Split.reduceSelectedMultiplier source)
rawNormOfReducedSourceExact source sourceReduced =
  trans
    (sym
      (Rect.finiteNormSqCong Rows.selectedCombinedConstraintRowCarrier
        (Projection.selectedReducedProjection source) source sourceReduced))
    (rawReducedNormExact source)

------------------------------------------------------------------------
-- Pairing identity for x=G_red y.
------------------------------------------------------------------------

selectedReducedSolutionPairingExact :
  ∀ background
    (certificate : Matrix.RationalMatrixInverseCertificate
      Rows.selectedCombinedConstraintRowCarrier
      (ReducedInverse.selectedPaddedReducedNormalMatrix background))
    source → ReducedInverse.ReducedSource source →
  let x = ReducedInverse.selectedReducedNormalInverseApply
      background certificate source in
  Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier source x
  ≡ Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (RawKKT.selectedCombinedConstraintTransposeApply background x)
selectedReducedSolutionPairingExact background certificate source sourceReduced =
  let
    x = ReducedInverse.selectedReducedNormalInverseApply
      background certificate source
    xReduced = ReducedInverse.selectedReducedNormalInverseIsReduced
      background certificate source
    gram = RawKKT.selectedCombinedConstraintGramApply background x

    rightInverse = ReducedInverse.selectedReducedCombinedGramRightInverse
      background certificate source sourceReduced

    sourceDot :
      Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier source x
      ≡ Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier
          (Projection.selectedReducedProjection gram) x
    sourceDot = finiteDotLeftCong source
      (Projection.selectedReducedProjection gram) x
      (λ row → sym (rightInverse row))

    removeProjection = selectedProjectionDotReducedExact gram x xReduced

    gramQuadratic = RawKKT.selectedCombinedConstraintGramQuadraticExact
      background x
  in
  trans sourceDot (trans removeProjection gramQuadratic)

------------------------------------------------------------------------
-- The selected floor applies directly to the reduced solution x.
------------------------------------------------------------------------

selectedReducedSolutionFloor :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  (certificate : Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (ReducedInverse.selectedPaddedReducedNormalMatrix background)) →
  source → ReducedInverse.ReducedSource source →
  let x = ReducedInverse.selectedReducedNormalInverseApply
      background certificate source in
  selectedFloor * rawMultiplierNormSq x
  ≤ Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (RawKKT.selectedCombinedConstraintTransposeApply background x)
selectedReducedSolutionFloor background radius certificate source sourceReduced =
  let
    x = ReducedInverse.selectedReducedNormalInverseApply
      background certificate source
    xReduced = ReducedInverse.selectedReducedNormalInverseIsReduced
      background certificate source
    selected = Split.reduceSelectedMultiplier x

    floor = Floor.selectedBackgroundReducedCombinedAdjointFloor
      background radius selected

    inputNormExact :
      rawMultiplierNormSq x ≡ Floor.reducedCombinedMultiplierNormSq selected
    inputNormExact = rawNormOfReducedSourceExact x xReduced

    outputPointwise : ∀ coordinate →
      Floor.selectedReducedCombinedAdjoint background selected coordinate
      ≡ RawKKT.selectedCombinedConstraintTransposeApply background x coordinate
    outputPointwise coordinate =
      RawKKT.transposeApplyRespectsPointwise background
        (Split.reopenReducedMultiplier selected) x
        (λ row →
          trans
            (Split.reopenReduceProjectionIdempotent x row)
            (xReduced row))
        coordinate

    outputNormExact = Rect.finiteNormSqCong StateCarrier.physicalStateCarrier
      (Floor.selectedReducedCombinedAdjoint background selected)
      (RawKKT.selectedCombinedConstraintTransposeApply background x)
      outputPointwise
  in
  subst
    (λ lower → lower ≤
      Rect.finiteNormSq StateCarrier.physicalStateCarrier
        (RawKKT.selectedCombinedConstraintTransposeApply background x))
    (cong (selectedFloor *_) (sym inputNormExact))
    (subst
      (λ upper → selectedFloor
        * Floor.reducedCombinedMultiplierNormSq selected ≤ upper)
      outputNormExact floor)

------------------------------------------------------------------------
-- Explicit 1024/29 bound.
------------------------------------------------------------------------

selectedReducedSolutionNormBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  (certificate : Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (ReducedInverse.selectedPaddedReducedNormalMatrix background)) →
  source → ReducedInverse.ReducedSource source →
  let x = ReducedInverse.selectedReducedNormalInverseApply
      background certificate source in
  (selectedFloor * selectedFloor) * rawMultiplierNormSq x
  ≤ rawMultiplierNormSq source
selectedReducedSolutionNormBound
    background radius certificate source sourceReduced =
  let
    x = ReducedInverse.selectedReducedNormalInverseApply
      background certificate source
    xNorm = rawMultiplierNormSq x
    yNorm = rawMultiplierNormSq source
    pairing = Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier source x
    outputNorm = Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (RawKKT.selectedCombinedConstraintTransposeApply background x)

    pairingExact = selectedReducedSolutionPairingExact
      background certificate source sourceReduced

    floorToPairing : selectedFloor * xNorm ≤ pairing
    floorToPairing = subst
      (λ upper → selectedFloor * xNorm ≤ upper)
      (sym pairingExact)
      (selectedReducedSolutionFloor
        background radius certificate source sourceReduced)

    young = Young.finiteTwiceScaledDotUpper
      Rows.selectedCombinedConstraintRowCarrier selectedFloor source x
  in
  Young.coercivePairingImpliesScaledNorm
    selectedFloor xNorm yNorm pairing
    selectedFloorNonnegative floorToPairing young

selectedReducedNormalCorrectionBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  (certificate : Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (ReducedInverse.selectedPaddedReducedNormalMatrix background)) →
  source → ReducedInverse.ReducedSource source →
  let x = ReducedInverse.selectedReducedNormalInverseApply
      background certificate source in
  Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (RawKKT.selectedCombinedConstraintTransposeApply background x)
  ≤ selectedFloorReciprocal * rawMultiplierNormSq source
selectedReducedNormalCorrectionBound
    background radius certificate source sourceReduced =
  let
    x = ReducedInverse.selectedReducedNormalInverseApply
      background certificate source
    xNorm = rawMultiplierNormSq x
    yNorm = rawMultiplierNormSq source
    pairing = Rect.finiteDot Rows.selectedCombinedConstraintRowCarrier source x
    outputNorm = Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (RawKKT.selectedCombinedConstraintTransposeApply background x)

    pairingExact = selectedReducedSolutionPairingExact
      background certificate source sourceReduced

    xBound = selectedReducedSolutionNormBound
      background radius certificate source sourceReduced

    young = Young.finiteTwiceScaledDotUpper
      Rows.selectedCombinedConstraintRowCarrier selectedFloor source x

    replaceX :
      (selectedFloor * selectedFloor) * xNorm + yNorm
      ≤ yNorm + yNorm
    replaceX =
      ℚP.+-mono-≤ xBound ℚP.≤-refl

    twiceFloorPairingBelow :
      (+ 2 / 1) * selectedFloor * pairing ≤ yNorm + yNorm
    twiceFloorPairingBelow = ℚP.≤-trans young replaceX

    scaled = Norm.scaleNonnegative selectedHalfFloorReciprocal
      selectedHalfFloorReciprocalNonnegative twiceFloorPairingBelow

    leftExact :
      selectedHalfFloorReciprocal
        * ((+ 2 / 1) * selectedFloor * pairing)
      ≡ pairing
    leftExact = ℚRing.solve-∀ pairing

    rightExact :
      selectedHalfFloorReciprocal * (yNorm + yNorm)
      ≡ selectedFloorReciprocal * yNorm
    rightExact = ℚRing.solve-∀ yNorm

    pairingBound : pairing ≤ selectedFloorReciprocal * yNorm
    pairingBound =
      subst
        (λ lower → lower ≤ selectedFloorReciprocal * yNorm)
        leftExact
        (subst
          (λ upper →
            selectedHalfFloorReciprocal
              * ((+ 2 / 1) * selectedFloor * pairing)
            ≤ upper)
          rightExact scaled)
  in
  subst
    (λ left → left ≤ selectedFloorReciprocal * yNorm)
    pairingExact pairingBound

selectedReducedNormalCorrectionBoundLevel : ProofLevel
selectedReducedNormalCorrectionBoundLevel = machineChecked
