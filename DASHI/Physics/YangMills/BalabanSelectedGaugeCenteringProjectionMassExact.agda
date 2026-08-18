module DASHI.Physics.YangMills.BalabanSelectedGaugeCenteringProjectionMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Balaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Realize the componentwise mean-zero gauge projection as a literal 768x768
-- rational matrix on the selected gauge-row carrier.  For each Lie coordinate
-- it is
--
--       P = I - (1/256) 11^T.
--
-- Its matrix action is proved pointwise equal to the existing
-- `centeredMultiplier`.  A deliberately coarse absolute-mass estimate gives
--
--       rowMass(P) <= 2,
--       columnMass(P) <= 2.
--
-- The sharp value 255/128 is unnecessary for the selected Schur contraction;
-- the factor 2 still leaves substantial strict headroom.  Keeping the proof
-- coarse avoids a case split on diagonal versus off-diagonal sites while
-- retaining exact rational control.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as Difference
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPath4GlobalAverageExact as GlobalAverage
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageSectionExact as AverageSection
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteColumnMassExact as ColumnMass

GaugeRow : Set
GaugeRow = Rows.GaugeRow

GaugeMultiplier : Set
GaugeMultiplier = Rows.GaugeMultiplier

gaugeRows = Basis.elements Rows.selectedGaugeRowFiniteSelector

oneOverSites : ℚ
oneOverSites = AverageSection.oneOverSiteCount

oneOverSitesMatchesGlobalMean :
  oneOverSites ≡ GlobalAverage.oneTwoFiftySix
oneOverSitesMatchesGlobalMean = ℚRing.solve []

gaugeIdentityKernel : GaugeRow → GaugeRow → ℚ
gaugeIdentityKernel row column =
  Basis.kronecker (Basis.decide Rows.selectedGaugeRowFiniteSelector) column row

constantGaugeProjectionKernel : GaugeRow → GaugeRow → ℚ
constantGaugeProjectionKernel
    (pair outputCoordinate outputSite)
    (pair inputCoordinate inputSite) =
  oneOverSites
    * Basis.kronecker
        (Basis.decide Basis.lieCoordinateFiniteSelector)
        inputCoordinate outputCoordinate

gaugeCenteringProjectionMatrix : GaugeRow → GaugeRow → ℚ
gaugeCenteringProjectionMatrix row column =
  gaugeIdentityKernel row column - constantGaugeProjectionKernel row column

------------------------------------------------------------------------
-- Exact action = existing centeredMultiplier.
------------------------------------------------------------------------

identityKernelActionExact : ∀ vector row →
  Sums.sumRational gaugeRows
    (λ column → gaugeIdentityKernel row column * vector column)
  ≡ vector row
identityKernelActionExact vector row =
  trans
    (Sums.sumRationalCong gaugeRows _ _
      (λ column → ℚP.*-comm
        (gaugeIdentityKernel row column) (vector column)))
    (Basis.selectorExact Rows.selectedGaugeRowFiniteSelector vector row)

constantKernelCoordinateActionExact :
  ∀ vector outputCoordinate outputSite inputCoordinate →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ inputSite →
      constantGaugeProjectionKernel
        (pair outputCoordinate outputSite)
        (pair inputCoordinate inputSite)
      * vector (pair inputCoordinate inputSite))
  ≡ oneOverSites
      * Basis.kronecker
          (Basis.decide Basis.lieCoordinateFiniteSelector)
          inputCoordinate outputCoordinate
      * Sums.sumRational (Block.physicalBlockSites Path4.side4)
          (λ inputSite → vector (pair inputCoordinate inputSite))
constantKernelCoordinateActionExact vector outputCoordinate outputSite inputCoordinate =
  let
    coefficient = oneOverSites
      * Basis.kronecker
          (Basis.decide Basis.lieCoordinateFiniteSelector)
          inputCoordinate outputCoordinate
  in
  trans
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4) _ _
      (λ inputSite → ℚRing.solve-∀
        oneOverSites
        (Basis.kronecker
          (Basis.decide Basis.lieCoordinateFiniteSelector)
          inputCoordinate outputCoordinate)
        (vector (pair inputCoordinate inputSite))))
    (Sums.sumRationalScale coefficient
      (Block.physicalBlockSites Path4.side4)
      (λ inputSite → vector (pair inputCoordinate inputSite)))

constantProjectionMatrixActionExact :
  ∀ vector outputCoordinate outputSite →
  Sums.sumRational gaugeRows
    (λ column →
      constantGaugeProjectionKernel
        (pair outputCoordinate outputSite) column * vector column)
  ≡ Mean.constantProjection vector (pair outputCoordinate outputSite)
constantProjectionMatrixActionExact vector outputCoordinate outputSite =
  let
    siteSum : Coordinates.LieCoordinate3 → ℚ
    siteSum inputCoordinate =
      Sums.sumRational (Block.physicalBlockSites Path4.side4)
        (λ inputSite → vector (pair inputCoordinate inputSite))

    split = Fubini.sumCartesian
      Coordinates.lieCoordinates3
      (Block.physicalBlockSites Path4.side4)
      (λ column →
        constantGaugeProjectionKernel
          (pair outputCoordinate outputSite) column * vector column)

    inner = Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
      (λ inputCoordinate →
        constantKernelCoordinateActionExact
          vector outputCoordinate outputSite inputCoordinate)

    reorder = Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
      (λ inputCoordinate → ℚRing.solve-∀
        oneOverSites
        (Basis.kronecker
          (Basis.decide Basis.lieCoordinateFiniteSelector)
          inputCoordinate outputCoordinate)
        (siteSum inputCoordinate))

    factor = Sums.sumRationalScale oneOverSites
      Coordinates.lieCoordinates3
      (λ inputCoordinate →
        Basis.kronecker
          (Basis.decide Basis.lieCoordinateFiniteSelector)
          inputCoordinate outputCoordinate * siteSum inputCoordinate)

    select = Basis.selectorExact Basis.lieCoordinateFiniteSelector
      siteSum outputCoordinate

    globalMatch :
      siteSum outputCoordinate
      ≡ Periodic.sumSites
          (FlatAdjoint.multiplierField vector outputCoordinate)
    globalMatch = sym
      (Bridge.sumSitesMatchesGlobalSiteSum
        (FlatAdjoint.multiplierField vector outputCoordinate))

    coefficientMatch :
      oneOverSites
        * Periodic.sumSites
            (FlatAdjoint.multiplierField vector outputCoordinate)
      ≡ Mean.constantProjection vector (pair outputCoordinate outputSite)
    coefficientMatch =
      trans
        (cong
          (_* Periodic.sumSites
                (FlatAdjoint.multiplierField vector outputCoordinate))
          oneOverSitesMatchesGlobalMean)
        refl
  in
  trans split
    (trans inner
      (trans reorder
        (trans factor
          (trans
            (cong (oneOverSites *_) select)
            (trans
              (cong (oneOverSites *_) globalMatch)
              coefficientMatch)))))

gaugeCenteringProjectionActionExact : ∀ vector row →
  Sums.sumRational gaugeRows
    (λ column → gaugeCenteringProjectionMatrix row column * vector column)
  ≡ Mean.centeredMultiplier vector row
gaugeCenteringProjectionActionExact vector
    (pair outputCoordinate outputSite) =
  let
    identityTerm = λ column →
      gaugeIdentityKernel (pair outputCoordinate outputSite) column
        * vector column
    constantTerm = λ column →
      constantGaugeProjectionKernel (pair outputCoordinate outputSite) column
        * vector column

    distribute = Sums.sumRationalCong gaugeRows _ _
      (λ column → ℚRing.solve-∀
        (gaugeIdentityKernel (pair outputCoordinate outputSite) column)
        (constantGaugeProjectionKernel
          (pair outputCoordinate outputSite) column)
        (vector column))

    split = Difference.sumSubtract gaugeRows identityTerm constantTerm
  in
  trans distribute
    (trans split
      (cong₂ _-_
        (identityKernelActionExact vector (pair outputCoordinate outputSite))
        (constantProjectionMatrixActionExact
          vector outputCoordinate outputSite)))

------------------------------------------------------------------------
-- Coarse exact absolute-mass bound <= 2.
------------------------------------------------------------------------

kroneckerAbsoluteExact :
  ∀ {A : Set} (selector : Basis.FiniteSelector A) left right →
  ∣ Basis.kronecker (Basis.decide selector) left right ∣
  ≡ Basis.kronecker (Basis.decide selector) left right
kroneckerAbsoluteExact selector left right
  with Basis.decide selector left right
... | yes _ = refl
... | no _ = refl

identityKernelRowMassExact : ∀ row →
  Mass.squareRowMass gaugeRows gaugeIdentityKernel row ≡ 1ℚ
identityKernelRowMassExact row =
  trans
    (Sums.sumRationalCong gaugeRows _ _
      (λ column → kroneckerAbsoluteExact
        Rows.selectedGaugeRowFiniteSelector column row))
    (trans
      (Sums.sumRationalCong gaugeRows _ _
        (λ column →
          sym (ℚP.*-identityˡ
            (Basis.kronecker
              (Basis.decide Rows.selectedGaugeRowFiniteSelector)
              column row))))
      (Basis.selectorExact Rows.selectedGaugeRowFiniteSelector
        (λ _ → 1ℚ) row))

constantKernelCoordinateMassExact :
  ∀ outputCoordinate outputSite inputCoordinate →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ inputSite →
      ∣ constantGaugeProjectionKernel
          (pair outputCoordinate outputSite)
          (pair inputCoordinate inputSite) ∣)
  ≡ Basis.kronecker
      (Basis.decide Basis.lieCoordinateFiniteSelector)
      inputCoordinate outputCoordinate
constantKernelCoordinateMassExact outputCoordinate outputSite inputCoordinate =
  let
    lie = Basis.kronecker
      (Basis.decide Basis.lieCoordinateFiniteSelector)
      inputCoordinate outputCoordinate

    entryAbs :
      ∣ oneOverSites * lie ∣ ≡ oneOverSites * lie
    entryAbs with Basis.decide Basis.lieCoordinateFiniteSelector
        inputCoordinate outputCoordinate
    ... | yes _ = ℚP.0≤p⇒∣p∣≡p (ℚP.nonNegative⁻¹ oneOverSites)
    ... | no _ = refl
  in
  trans
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4) _ _
      (λ _ → entryAbs))
    (trans
      (AverageSection.sideFourSumConstantExact (oneOverSites * lie))
      (ℚRing.solve-∀ lie))

constantKernelRowMassExact : ∀ row →
  Mass.squareRowMass gaugeRows constantGaugeProjectionKernel row ≡ 1ℚ
constantKernelRowMassExact (pair outputCoordinate outputSite) =
  trans
    (Fubini.sumCartesian Coordinates.lieCoordinates3
      (Block.physicalBlockSites Path4.side4)
      (λ column →
        ∣ constantGaugeProjectionKernel
            (pair outputCoordinate outputSite) column ∣))
    (trans
      (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
        (constantKernelCoordinateMassExact outputCoordinate outputSite))
      (trans
        (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
          (λ inputCoordinate →
            sym (ℚP.*-identityˡ
              (Basis.kronecker
                (Basis.decide Basis.lieCoordinateFiniteSelector)
                inputCoordinate outputCoordinate))))
        (Basis.selectorExact Basis.lieCoordinateFiniteSelector
          (λ _ → 1ℚ) outputCoordinate)))

centeringProjectionRowMassBound : ℚ
centeringProjectionRowMassBound = + 2 / 1

gaugeCenteringProjectionAbsoluteRowMassBound : ∀ row →
  Mass.squareRowMass gaugeRows gaugeCenteringProjectionMatrix row
  ≤ centeringProjectionRowMassBound
gaugeCenteringProjectionAbsoluteRowMassBound row =
  let
    triangle = Schur.sumPointwiseBelow gaugeRows _ _
      (λ column → ℚP.∣p-q∣≤∣p∣+∣q∣
        (gaugeIdentityKernel row column)
        (constantGaugeProjectionKernel row column))

    split = Mass.sumAddExact gaugeRows
      (λ column → ∣ gaugeIdentityKernel row column ∣)
      (λ column → ∣ constantGaugeProjectionKernel row column ∣)

    exact :
      Sums.sumRational gaugeRows
        (λ column →
          ∣ gaugeIdentityKernel row column ∣
            + ∣ constantGaugeProjectionKernel row column ∣)
      ≡ centeringProjectionRowMassBound
    exact = trans split
      (trans
        (cong₂ _+_
          (identityKernelRowMassExact row)
          (constantKernelRowMassExact row))
        (ℚRing.solve []))
  in
  subst
    (λ upper →
      Mass.squareRowMass gaugeRows gaugeCenteringProjectionMatrix row ≤ upper)
    exact triangle

genericKroneckerSymmetric :
  ∀ {A : Set} (selector : Basis.FiniteSelector A) left right →
  Basis.kronecker (Basis.decide selector) left right
  ≡ Basis.kronecker (Basis.decide selector) right left
genericKroneckerSymmetric selector left right
  with Basis.decide selector left right
... | yes refl
    with Basis.decide selector right right
...   | yes _ = refl
...   | no different = ⊥-elim (different refl)
... | no different
    with Basis.decide selector right left
...   | yes equality = ⊥-elim (different (sym equality))
...   | no _ = refl

gaugeCenteringProjectionSymmetric : ∀ left right →
  gaugeCenteringProjectionMatrix left right
  ≡ gaugeCenteringProjectionMatrix right left
gaugeCenteringProjectionSymmetric
    (pair leftCoordinate leftSite)
    (pair rightCoordinate rightSite) =
  cong₂ _-_
    (genericKroneckerSymmetric
      Rows.selectedGaugeRowFiniteSelector
      (pair rightCoordinate rightSite)
      (pair leftCoordinate leftSite))
    (cong (oneOverSites *_)
      (genericKroneckerSymmetric
        Basis.lieCoordinateFiniteSelector
        rightCoordinate leftCoordinate))

gaugeCenteringProjectionColumnMassAsRowMass : ∀ column →
  ColumnMass.squareColumnMass gaugeRows gaugeCenteringProjectionMatrix column
  ≡ Mass.squareRowMass gaugeRows gaugeCenteringProjectionMatrix column
gaugeCenteringProjectionColumnMassAsRowMass column =
  Sums.sumRationalCong gaugeRows _ _
    (λ row → cong ∣_∣ (gaugeCenteringProjectionSymmetric row column))

gaugeCenteringProjectionAbsoluteColumnMassBound : ∀ column →
  ColumnMass.squareColumnMass gaugeRows gaugeCenteringProjectionMatrix column
  ≤ centeringProjectionRowMassBound
gaugeCenteringProjectionAbsoluteColumnMassBound column =
  subst
    (λ lower → lower ≤ centeringProjectionRowMassBound)
    (sym (gaugeCenteringProjectionColumnMassAsRowMass column))
    (gaugeCenteringProjectionAbsoluteRowMassBound column)

selectedGaugeCenteringProjectionActionLevel : ProofLevel
selectedGaugeCenteringProjectionActionLevel = machineChecked

selectedGaugeCenteringProjectionMassLevel : ProofLevel
selectedGaugeCenteringProjectionMassLevel = machineChecked
