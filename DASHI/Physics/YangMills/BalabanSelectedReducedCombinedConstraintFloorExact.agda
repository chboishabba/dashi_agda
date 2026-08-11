module DASHI.Physics.YangMills.BalabanSelectedReducedCombinedConstraintFloorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers", RAIRO Analyse Numerique 8 (1974),
-- 129--151. No DOI was assigned to the cited article.
--
-- DASHI CONTRIBUTION
--
-- Put the split reduced combined multiplier presentation on the *actual*
-- selected constraint transpose and prove a strict background floor without
-- inverting the singular raw 780-row Gram.
--
-- The proof uses three facts already available on the literal side-four
-- carrier:
--
--   (i)  the twelve block-average rows have normal operator exactly 256 I;
--   (ii) the flat gauge adjoint has floor 1/16 on componentwise mean-zero
--        multipliers;
--   (iii) the selected-background gauge-adjoint defect has squared norm at
--        most (3/1024)||gamma||^2.
--
-- A new exact summation argument proves the average adjoint is orthogonal to
-- the flat gauge adjoint: a constant bond field pairs to zero with a periodic
-- gradient because the finite sum of every forward difference vanishes.
-- Hence the flat *combined* reduced adjoint already has floor 1/16.  Treating
-- the background change as the single gauge-adjoint defect and applying the
-- square-root-free finite perturbation theorem gives
--
--      (29/1024)(||alpha||^2 + ||gamma||^2)
--        <= ||L_A^* s(alpha,gamma)||^2.
--
-- The theorem is on L_A^* composed with the explicit reopening section s.
-- It therefore proves positivity on the computational quotient presentation
-- while making no false claim that the flat constant sector is the nonlinear
-- stabilizer at every background.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; -_; _/_)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (pair; map)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as StateCarrier
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageSectionExact as AverageSection
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageRowCarrierExact as AverageRows
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeReducedFloorExact as GaugeReduced
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as Perturb
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as RawRows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintFiniteKKTExact as RawKKT
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split

ReducedMultiplier : Set
ReducedMultiplier = Split.SelectedReducedCombinedMultiplier

averageRows : List Average.SelectedBlockAverageRow4
averageRows = Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector

------------------------------------------------------------------------
-- Reduced multiplier norm and the three pieces of the selected adjoint.
------------------------------------------------------------------------

averageMultiplierNormSq : ReducedMultiplier → ℚ
averageMultiplierNormSq selected =
  Rect.finiteNormSq AverageRows.selectedBlockAverageRowCarrier
    (Split.averageMultiplier selected)

gaugeMultiplierNormSq : ReducedMultiplier → ℚ
gaugeMultiplierNormSq selected =
  FlatFloor.gaugeMultiplierNormSq (Split.gaugeMultiplier selected)

reducedCombinedMultiplierNormSq : ReducedMultiplier → ℚ
reducedCombinedMultiplierNormSq selected =
  averageMultiplierNormSq selected + gaugeMultiplierNormSq selected

averageAdjoint : ReducedMultiplier → StateCarrier.StateVector
averageAdjoint selected =
  AverageRows.selectedBlockAverageTransposeApply
    (Split.averageMultiplier selected)

flatGaugeAdjoint : ReducedMultiplier → StateCarrier.StateVector
flatGaugeAdjoint selected =
  FlatAdjoint.actualFlatGaugeAdjoint (Split.gaugeMultiplier selected)

backgroundGaugeAdjoint :
  Physical.RationalSU2Background4 → ReducedMultiplier → StateCarrier.StateVector
backgroundGaugeAdjoint background selected =
  GaugeReduced.backgroundGaugeAdjoint background (Split.gaugeMultiplier selected)

gaugeAdjointDefect :
  Physical.RationalSU2Background4 → ReducedMultiplier → StateCarrier.StateVector
gaugeAdjointDefect background selected =
  Defect.gaugeAdjointDefectApply background (Split.gaugeMultiplier selected)

flatReducedCombinedAdjoint : ReducedMultiplier → StateCarrier.StateVector
flatReducedCombinedAdjoint selected =
  Rect.vectorAdd (averageAdjoint selected) (flatGaugeAdjoint selected)

assembledBackgroundCombinedAdjoint :
  Physical.RationalSU2Background4 → ReducedMultiplier → StateCarrier.StateVector
assembledBackgroundCombinedAdjoint background selected =
  Rect.vectorAdd (averageAdjoint selected) (backgroundGaugeAdjoint background selected)

selectedReducedCombinedAdjoint :
  Physical.RationalSU2Background4 → ReducedMultiplier → StateCarrier.StateVector
selectedReducedCombinedAdjoint background selected =
  RawKKT.selectedCombinedConstraintTransposeApply background
    (Split.reopenReducedMultiplier selected)

------------------------------------------------------------------------
-- Same-object theorem: the reduced adjoint is literally L_A^* after reopening.
------------------------------------------------------------------------

averageTaggedTransposePart :
  Physical.RationalSU2Background4 → ReducedMultiplier →
  StateCarrier.State → ℚ
averageTaggedTransposePart background selected stateCoordinate =
  Sums.sumRational
    (map Combined.averageConstraintRow averageRows)
    (λ row →
      Rect.transposeRectangular
        (Combined.selectedBackgroundLinearizedConstraintMatrix background)
        stateCoordinate row
      * Split.reopenReducedMultiplier selected row)

gaugeTaggedTransposePart :
  Physical.RationalSU2Background4 → ReducedMultiplier →
  StateCarrier.State → ℚ
gaugeTaggedTransposePart background selected stateCoordinate =
  Sums.sumRational
    (map Combined.gaugeConstraintRow
      (Basis.elements RawRows.selectedGaugeRowFiniteSelector))
    (λ row →
      Rect.transposeRectangular
        (Combined.selectedBackgroundLinearizedConstraintMatrix background)
        stateCoordinate row
      * Split.reopenReducedMultiplier selected row)

averageTaggedTransposePartExact :
  ∀ background selected stateCoordinate →
  averageTaggedTransposePart background selected stateCoordinate
  ≡ averageAdjoint selected stateCoordinate
averageTaggedTransposePartExact background selected stateCoordinate =
  trans
    (Fubini.sumRationalMap
      Combined.averageConstraintRow averageRows
      (λ row →
        Rect.transposeRectangular
          (Combined.selectedBackgroundLinearizedConstraintMatrix background)
          stateCoordinate row
        * Split.reopenReducedMultiplier selected row))
    refl

gaugeTaggedTransposePartExact :
  ∀ background selected stateCoordinate →
  gaugeTaggedTransposePart background selected stateCoordinate
  ≡ backgroundGaugeAdjoint background selected stateCoordinate
gaugeTaggedTransposePartExact background selected stateCoordinate =
  trans
    (Fubini.sumRationalMap
      Combined.gaugeConstraintRow
      (Basis.elements RawRows.selectedGaugeRowFiniteSelector)
      (λ row →
        Rect.transposeRectangular
          (Combined.selectedBackgroundLinearizedConstraintMatrix background)
          stateCoordinate row
        * Split.reopenReducedMultiplier selected row))
    refl

selectedReducedCombinedAdjointSameObject :
  ∀ background selected stateCoordinate →
  selectedReducedCombinedAdjoint background selected stateCoordinate
  ≡ assembledBackgroundCombinedAdjoint background selected stateCoordinate
selectedReducedCombinedAdjointSameObject background selected stateCoordinate =
  trans
    (Fubini.sumRationalAppend
      (map Combined.averageConstraintRow averageRows)
      (map Combined.gaugeConstraintRow
        (Basis.elements RawRows.selectedGaugeRowFiniteSelector))
      (λ row →
        Rect.transposeRectangular
          (Combined.selectedBackgroundLinearizedConstraintMatrix background)
          stateCoordinate row
        * Split.reopenReducedMultiplier selected row))
    (cong₂ _+_
      (averageTaggedTransposePartExact background selected stateCoordinate)
      (gaugeTaggedTransposePartExact background selected stateCoordinate))

------------------------------------------------------------------------
-- Periodic gradient has exactly zero block average.
------------------------------------------------------------------------

sumSitesForwardDifferenceZero : ∀ axis field →
  Periodic.sumSites (Periodic.forwardDifference axis field) ≡ 0ℚ
sumSitesForwardDifferenceZero axis field =
  trans
    (Periodic.sumSitesSubtract
      (λ site → field (Periodic.shiftForward axis site)) field)
    (trans
      (cong (_- Periodic.sumSites field)
        (Periodic.sumSitesForwardInvariant field axis))
      (ℚRing.solve-∀ (Periodic.sumSites field)))

sumSitesNegativeForwardDifferenceZero : ∀ axis field →
  Periodic.sumSites
    (λ site → - Periodic.forwardDifference axis field site)
  ≡ 0ℚ
sumSitesNegativeForwardDifferenceZero axis field =
  trans
    (Periodic.sumSitesNeg (Periodic.forwardDifference axis field))
    (trans
      (cong -_ (sumSitesForwardDifferenceZero axis field))
      (ℚRing.solve []))

physicalSiteSumNegativeForwardDifferenceZero : ∀ axis field →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site → - Periodic.forwardDifference axis field site)
  ≡ 0ℚ
physicalSiteSumNegativeForwardDifferenceZero axis field =
  trans
    (sym
      (Bridge.sumSitesMatchesGlobalSiteSum
        (λ site → - Periodic.forwardDifference axis field site)))
    (sumSitesNegativeForwardDifferenceZero axis field)

flatGaugeAdjointBlockAverageZero : ∀ selected row →
  Average.selectedBackgroundBlockAverageConstraintApply
    (flatGaugeAdjoint selected) row
  ≡ 0ℚ
flatGaugeAdjointBlockAverageZero selected (pair coordinate axis) =
  trans
    (Average.selectedBackgroundBlockAverageConstraintMatrixApplyExact
      (flatGaugeAdjoint selected) (pair coordinate axis))
    (trans
      (Sums.sumRationalCong
        (Block.physicalBlockSites Path4.side4)
        (λ site →
          flatGaugeAdjoint selected (pair coordinate (pair axis site)))
        (λ site →
          - Periodic.forwardDifference axis
              (FlatAdjoint.multiplierField
                (Split.gaugeMultiplier selected) coordinate) site)
        (λ site →
          FlatAdjoint.actualFlatGaugeAdjointPointwiseExact
            (Split.gaugeMultiplier selected)
            (pair coordinate (pair axis site))))
      (physicalSiteSumNegativeForwardDifferenceZero axis
        (FlatAdjoint.multiplierField
          (Split.gaugeMultiplier selected) coordinate)))

------------------------------------------------------------------------
-- Exact average/gauge orthogonality at the flat reference.
------------------------------------------------------------------------

selectedAverageFlatGaugeAdjointOrthogonal : ∀ selected →
  Rect.finiteDot StateCarrier.physicalStateCarrier
    (averageAdjoint selected) (flatGaugeAdjoint selected)
  ≡ 0ℚ
selectedAverageFlatGaugeAdjointOrthogonal selected =
  let
    alpha = Split.averageMultiplier selected
    gauge = flatGaugeAdjoint selected

    adjointIdentity =
      Rect.rectangularAdjointExact
        AverageRows.selectedBlockAverageRowCarrier
        StateCarrier.physicalStateCarrier
        Average.selectedBackgroundBlockAverageConstraintMatrix
        gauge alpha

    rowDotZero :
      Rect.finiteDot AverageRows.selectedBlockAverageRowCarrier
        (Average.selectedBackgroundBlockAverageConstraintApply gauge) alpha
      ≡ 0ℚ
    rowDotZero =
      trans
        (Sums.sumRationalCong averageRows _ (λ _ → 0ℚ)
          (λ row →
            trans
              (cong (_* alpha row)
                (flatGaugeAdjointBlockAverageZero selected row))
              (ℚRing.solve-∀ (alpha row))))
        (Fubini.sumRationalZero averageRows)
  in
  trans
    (Rect.finiteDotSymmetric StateCarrier.physicalStateCarrier
      (averageAdjoint selected) gauge)
    (trans (sym adjointIdentity) rowDotZero)

------------------------------------------------------------------------
-- Exact 256 I norm for the average adjoint.
------------------------------------------------------------------------

averageAdjointNormExact : ∀ selected →
  Rect.finiteNormSq StateCarrier.physicalStateCarrier (averageAdjoint selected)
  ≡ AverageSection.siteCount * averageMultiplierNormSq selected
averageAdjointNormExact selected =
  let
    alpha = Split.averageMultiplier selected
    adjoint = averageAdjoint selected

    adjointIdentity =
      Rect.rectangularAdjointExact
        AverageRows.selectedBlockAverageRowCarrier
        StateCarrier.physicalStateCarrier
        Average.selectedBackgroundBlockAverageConstraintMatrix
        adjoint alpha

    rowExact :
      Rect.finiteDot AverageRows.selectedBlockAverageRowCarrier
        (Average.selectedBackgroundBlockAverageConstraintApply adjoint) alpha
      ≡ AverageSection.siteCount * averageMultiplierNormSq selected
    rowExact =
      trans
        (Sums.sumRationalCong averageRows _ _
          (λ row →
            trans
              (cong (_* alpha row)
                (AverageRows.selectedBlockAverageLiteralGramExact alpha row))
              (ℚRing.solve-∀ AverageSection.siteCount (alpha row))))
        (Sums.sumRationalScale AverageSection.siteCount averageRows
          (λ row → alpha row * alpha row))
  in
  trans (sym adjointIdentity) rowExact

oneSixteenthBelowSiteCount :
  LDL.oneSixteenth ≤ AverageSection.siteCount
oneSixteenthBelowSiteCount =
  toWitness {a? = LDL.oneSixteenth ≤? AverageSection.siteCount} _

averageMultiplierNormNonnegative : ∀ selected →
  0ℚ ≤ averageMultiplierNormSq selected
averageMultiplierNormNonnegative selected =
  Rect.finiteNormSqNonnegative AverageRows.selectedBlockAverageRowCarrier
    (Split.averageMultiplier selected)

gaugeMultiplierNormNonnegative : ∀ selected →
  0ℚ ≤ gaugeMultiplierNormSq selected
gaugeMultiplierNormNonnegative selected =
  subst
    (λ value → 0ℚ ≤ value)
    (GaugeReduced.gaugeMultiplierRowNormSqExact (Split.gaugeMultiplier selected))
    (Rect.finiteNormSqNonnegative FlatAdjoint.selectedFlatGaugeRowCarrier
      (Split.gaugeMultiplier selected))

averageAdjointOneSixteenthFloor : ∀ selected →
  LDL.oneSixteenth * averageMultiplierNormSq selected
  ≤ Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (averageAdjoint selected)
averageAdjointOneSixteenthFloor selected =
  let
    norm = averageMultiplierNormSq selected
    scaled = Norm.scaleNonnegative norm
      (averageMultiplierNormNonnegative selected)
      oneSixteenthBelowSiteCount

    lowerExact : norm * LDL.oneSixteenth
      ≡ LDL.oneSixteenth * norm
    lowerExact = ℚP.*-comm norm LDL.oneSixteenth

    upperExact : norm * AverageSection.siteCount
      ≡ Rect.finiteNormSq StateCarrier.physicalStateCarrier
          (averageAdjoint selected)
    upperExact =
      trans
        (ℚP.*-comm norm AverageSection.siteCount)
        (sym (averageAdjointNormExact selected))
  in
  subst
    (λ lower → lower ≤ Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (averageAdjoint selected))
    lowerExact
    (subst
      (λ upper → norm * LDL.oneSixteenth ≤ upper)
      upperExact scaled)

------------------------------------------------------------------------
-- Norm of an orthogonal sum and the strict flat combined floor.
------------------------------------------------------------------------

finiteNormSqAddExpansion :
  ∀ {Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index)
    left right →
  Rect.finiteNormSq carrier (Rect.vectorAdd left right)
  ≡ Rect.finiteNormSq carrier left + Rect.finiteNormSq carrier right
    + (+ 2 / 1) * Rect.finiteDot carrier left right
finiteNormSqAddExpansion carrier left right =
  let
    values = Matrix.coordinates carrier
  in
  trans
    (Sums.sumRationalCong values _ _
      (λ index → ℚRing.solve-∀ (left index) (right index)))
    (trans
      (Fubini.sumRationalAdd values
        (λ index → left index * left index)
        (λ index → right index * right index
          + (+ 2 / 1) * (left index * right index)))
      (trans
        (cong
          (Rect.finiteNormSq carrier left +_)
          (Fubini.sumRationalAdd values
            (λ index → right index * right index)
            (λ index → (+ 2 / 1) * (left index * right index))))
        (trans
          (cong
            (λ cross →
              Rect.finiteNormSq carrier left
              + (Rect.finiteNormSq carrier right + cross))
            (Sums.sumRationalScale (+ 2 / 1) values
              (λ index → left index * right index)))
          (ℚRing.solve-∀
            (Rect.finiteNormSq carrier left)
            (Rect.finiteNormSq carrier right)
            (Rect.finiteDot carrier left right)))))

flatReducedCombinedAdjointNormExact : ∀ selected →
  Rect.finiteNormSq StateCarrier.physicalStateCarrier
    (flatReducedCombinedAdjoint selected)
  ≡ Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (averageAdjoint selected)
    + Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (flatGaugeAdjoint selected)
flatReducedCombinedAdjointNormExact selected =
  trans
    (finiteNormSqAddExpansion StateCarrier.physicalStateCarrier
      (averageAdjoint selected) (flatGaugeAdjoint selected))
    (trans
      (cong
        (λ cross →
          Rect.finiteNormSq StateCarrier.physicalStateCarrier
            (averageAdjoint selected)
          + Rect.finiteNormSq StateCarrier.physicalStateCarrier
            (flatGaugeAdjoint selected)
          + (+ 2 / 1) * cross)
        (selectedAverageFlatGaugeAdjointOrthogonal selected))
      (ℚRing.solve-∀
        (Rect.finiteNormSq StateCarrier.physicalStateCarrier
          (averageAdjoint selected))
        (Rect.finiteNormSq StateCarrier.physicalStateCarrier
          (flatGaugeAdjoint selected))))

selectedFlatReducedCombinedFloor : ∀ selected →
  LDL.oneSixteenth * reducedCombinedMultiplierNormSq selected
  ≤ Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (flatReducedCombinedAdjoint selected)
selectedFlatReducedCombinedFloor selected =
  let
    averageLower = averageAdjointOneSixteenthFloor selected
    gaugeLower =
      FlatAdjoint.actualFlatGaugeGramReducedFloor
        (Split.gaugeMultiplier selected) (Split.gaugeReduced selected)

    summed = ℚP.+-mono-≤ averageLower gaugeLower

    lowerExact :
      LDL.oneSixteenth * reducedCombinedMultiplierNormSq selected
      ≡ LDL.oneSixteenth * averageMultiplierNormSq selected
        + LDL.oneSixteenth * gaugeMultiplierNormSq selected
    lowerExact = ℚRing.solve-∀ LDL.oneSixteenth
      (averageMultiplierNormSq selected) (gaugeMultiplierNormSq selected)
  in
  subst
    (λ lower → lower ≤ Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (flatReducedCombinedAdjoint selected))
    lowerExact
    (subst
      (λ upper →
        LDL.oneSixteenth * averageMultiplierNormSq selected
          + LDL.oneSixteenth * gaugeMultiplierNormSq selected
        ≤ upper)
      (sym (flatReducedCombinedAdjointNormExact selected))
      summed)

------------------------------------------------------------------------
-- The only background perturbation is the already bounded gauge defect.
------------------------------------------------------------------------

backgroundCombinedSplits : ∀ background selected stateCoordinate →
  selectedReducedCombinedAdjoint background selected stateCoordinate
  ≡ flatReducedCombinedAdjoint selected stateCoordinate
    + gaugeAdjointDefect background selected stateCoordinate
backgroundCombinedSplits background selected stateCoordinate =
  trans
    (selectedReducedCombinedAdjointSameObject
      background selected stateCoordinate)
    (trans
      (cong
        (averageAdjoint selected stateCoordinate +_)
        (GaugeReduced.backgroundGaugeAdjointSplits
          background (Split.gaugeMultiplier selected) stateCoordinate))
      (ℚRing.solve-∀
        (averageAdjoint selected stateCoordinate)
        (flatGaugeAdjoint selected stateCoordinate)
        (gaugeAdjointDefect background selected stateCoordinate)))

gaugeNormBelowCombinedNorm : ∀ selected →
  gaugeMultiplierNormSq selected ≤ reducedCombinedMultiplierNormSq selected
gaugeNormBelowCombinedNorm selected =
  subst
    (λ upper → gaugeMultiplierNormSq selected ≤ upper)
    (ℚP.+-comm
      (gaugeMultiplierNormSq selected) (averageMultiplierNormSq selected))
    (ℚP.+-monoʳ-≤
      (gaugeMultiplierNormSq selected)
      (averageMultiplierNormNonnegative selected))

selectedDefectCoefficientNonnegative :
  0ℚ ≤ Defect.selectedAdjointDefectCoefficient
selectedDefectCoefficientNonnegative =
  toWitness {a? = 0ℚ ≤? Defect.selectedAdjointDefectCoefficient} _

selectedCombinedGaugeDefectUpper :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ selected →
  Rect.finiteNormSq StateCarrier.physicalStateCarrier
    (gaugeAdjointDefect background selected)
  ≤ Defect.selectedAdjointDefectCoefficient
      * reducedCombinedMultiplierNormSq selected
selectedCombinedGaugeDefectUpper background radius selected =
  let
    gauge = Split.gaugeMultiplier selected
    raw = Defect.gaugeAdjointDefectSelectedRadiusBound background radius gauge

    toGaugeNorm =
      subst
        (λ upper →
          Defect.gaugeAdjointDefectNormSq background gauge
          ≤ Defect.selectedAdjointDefectCoefficient * upper)
        (GaugeReduced.gaugeMultiplierRowNormSqExact gauge) raw

    extend = Norm.scaleNonnegative Defect.selectedAdjointDefectCoefficient
      selectedDefectCoefficientNonnegative
      (gaugeNormBelowCombinedNorm selected)
  in
  ℚP.≤-trans toGaugeNorm extend

selectedBackgroundReducedCombinedPerturbationData :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  Perturb.ReducedFloorPerturbationData StateCarrier.physicalStateCarrier
selectedBackgroundReducedCombinedPerturbationData background radius = record
  { Perturb.ReducedFloorPerturbationData.Multiplier = ReducedMultiplier
  ; Perturb.ReducedFloorPerturbationData.multiplierNormSq =
      reducedCombinedMultiplierNormSq
  ; Perturb.ReducedFloorPerturbationData.reference =
      flatReducedCombinedAdjoint
  ; Perturb.ReducedFloorPerturbationData.defect =
      gaugeAdjointDefect background
  ; Perturb.ReducedFloorPerturbationData.full =
      selectedReducedCombinedAdjoint background
  ; Perturb.ReducedFloorPerturbationData.referenceFloor =
      LDL.oneSixteenth
  ; Perturb.ReducedFloorPerturbationData.defectCoefficient =
      Defect.selectedAdjointDefectCoefficient
  ; Perturb.ReducedFloorPerturbationData.fullSplits =
      backgroundCombinedSplits background
  ; Perturb.ReducedFloorPerturbationData.referenceCoercive =
      selectedFlatReducedCombinedFloor
  ; Perturb.ReducedFloorPerturbationData.defectUpper =
      selectedCombinedGaugeDefectUpper background radius
  }

selectedBackgroundReducedCombinedFloor : ℚ
selectedBackgroundReducedCombinedFloor = + 29 / 1024

selectedBackgroundReducedCombinedFloorExact :
  Perturb.oneHalf * LDL.oneSixteenth
    - Defect.selectedAdjointDefectCoefficient
  ≡ selectedBackgroundReducedCombinedFloor
selectedBackgroundReducedCombinedFloorExact = ℚRing.solve []

selectedBackgroundReducedCombinedAdjointFloor :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ selected →
  selectedBackgroundReducedCombinedFloor
      * reducedCombinedMultiplierNormSq selected
  ≤ Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (selectedReducedCombinedAdjoint background selected)
selectedBackgroundReducedCombinedAdjointFloor background radius selected =
  subst
    (λ coefficient →
      coefficient * reducedCombinedMultiplierNormSq selected
      ≤ Rect.finiteNormSq StateCarrier.physicalStateCarrier
          (selectedReducedCombinedAdjoint background selected))
    selectedBackgroundReducedCombinedFloorExact
    (Perturb.perturbedReducedFloor
      (selectedBackgroundReducedCombinedPerturbationData background radius)
      selected)

selectedReducedCombinedSameObjectLevel : ProofLevel
selectedReducedCombinedSameObjectLevel = machineChecked

selectedAverageFlatGaugeOrthogonalityLevel : ProofLevel
selectedAverageFlatGaugeOrthogonalityLevel = machineChecked

selectedFlatReducedCombinedFloorLevel : ProofLevel
selectedFlatReducedCombinedFloorLevel = machineChecked

selectedBackgroundReducedCombinedFloorLevel : ProofLevel
selectedBackgroundReducedCombinedFloorLevel = machineChecked
