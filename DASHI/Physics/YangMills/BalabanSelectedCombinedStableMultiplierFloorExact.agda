module DASHI.Physics.YangMills.BalabanSelectedCombinedStableMultiplierFloorExact where

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
-- DASHI CONTRIBUTION
--
-- Close a concrete, background-stable coercive subspace of the literal
-- 780-row selected constraint operator.  The twelve block-average multipliers
-- are unrestricted.  The 768 gauge multipliers are restricted only by the
-- three componentwise mean-zero conditions which are known to be coercive at
-- the identity background.
--
-- At the identity background the average adjoint is a constant lift and the
-- gauge adjoint is a negative periodic gradient.  Their cross pairing vanishes
-- exactly because the finite sum of a periodic forward difference is zero.
-- Thus the reference adjoint has the direct-sum lower bound
--
--      (1/16)(||alpha||^2 + ||lambda||^2)
--        <= ||L_1^*(alpha,lambda)||^2.
--
-- The average rows are background-independent and the selected gauge-adjoint
-- defect obeys the independently proved finite Frobenius estimate
--
--      ||(L_A^*-L_1^*)(0,lambda)||^2
--        <= (3/1024)||lambda||^2.
--
-- The exact rational perturbation theorem therefore gives
--
--      (29/1024)(||alpha||^2 + ||lambda||^2)
--        <= ||L_A^*(alpha,lambda)||^2.
--
-- The final theorem identifies the left side with the transpose of the actual
-- tagged 780 x 3072 matrix, not a separately supplied product operator.  This
-- is deliberately called a *stable multiplier floor*, not rank stability:
-- the companion holonomy counterexample shows that the flat constant gauge
-- zero modes do not automatically remain the background kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageSectionExact as AverageSection
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageRowCarrierExact as AverageRows
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as CombinedRows
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as GaugeDefect
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeReducedFloorExact as GaugeFloor
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as Perturb
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedBackgroundPhysicalRadiusInstantiationExact as SelectedRadius
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational

AverageMultiplier : Set
AverageMultiplier = Average.SelectedBlockAverageRow4 → ℚ

GaugeMultiplier : Set
GaugeMultiplier = GaugeDefect.GaugeMultiplier

averageMultiplierNormSq : AverageMultiplier → ℚ
averageMultiplierNormSq average =
  AverageSection.selectedBlockAverageRowDot average average

gaugeMultiplierNormSq : GaugeMultiplier → ℚ
gaugeMultiplierNormSq = FlatFloor.gaugeMultiplierNormSq

averageMultiplierNormSqNonnegative : ∀ average →
  0ℚ ≤ averageMultiplierNormSq average
averageMultiplierNormSqNonnegative average =
  Schur.sumNonnegative
    Average.selectedBlockAverageRows4
    (λ row → average row * average row)
    (λ row → FiniteL2.squareNonnegative (average row))

gaugeMultiplierNormSqNonnegative : ∀ gauge →
  0ℚ ≤ gaugeMultiplierNormSq gauge
gaugeMultiplierNormSqNonnegative gauge =
  let
    rowNorm = GaugeDefect.gaugeMultiplierRowNormSq gauge
    rowNonnegative =
      Schur.sumNonnegative GaugeDefect.gaugeRows
        (λ row → gauge row * gauge row)
        (λ row → FiniteL2.squareNonnegative (gauge row))
  in
  subst
    (λ norm → 0ℚ ≤ norm)
    (GaugeFloor.gaugeMultiplierRowNormSqExact gauge)
    rowNonnegative

------------------------------------------------------------------------
-- Average adjoint: exact norm 256 ||alpha||^2.
------------------------------------------------------------------------

averageAdjointNormExact : ∀ average →
  KKT.stateNormSq (AverageSection.selectedBlockAverageAdjointLift average)
  ≡ AverageSection.siteCount * averageMultiplierNormSq average
averageAdjointNormExact average =
  let
    adjoint = AverageSection.selectedBlockAverageAdjointLift average

    pairing :
      AverageSection.selectedBlockAverageRowDot
        (AverageSection.selectedBlockAverageNormalApply average) average
      ≡ Coordinates.physicalCoordinateDot adjoint adjoint
    pairing = AverageSection.selectedBlockAverageAdjointExact adjoint average

    normalPointwise :
      AverageSection.selectedBlockAverageRowDot
        (AverageSection.selectedBlockAverageNormalApply average) average
      ≡ AverageSection.siteCount * averageMultiplierNormSq average
    normalPointwise =
      trans
        (Sums.sumRationalCong Average.selectedBlockAverageRows4 _ _
          (λ row →
            trans
              (cong (_* average row)
                (AverageSection.selectedBlockAverageNormalExact average row))
              (ℚRing.solve-∀ AverageSection.siteCount (average row))))
        (Sums.sumRationalScale AverageSection.siteCount
          Average.selectedBlockAverageRows4
          (λ row → average row * average row))
  in
  trans (sym pairing) normalPointwise

averageAdjointOneSixteenthFloor : ∀ average →
  LDL.oneSixteenth * averageMultiplierNormSq average
  ≤ KKT.stateNormSq (AverageSection.selectedBlockAverageAdjointLift average)
averageAdjointOneSixteenthFloor average =
  let
    coefficientBelow : LDL.oneSixteenth ≤ AverageSection.siteCount
    coefficientBelow = toWitness _

    scaled :
      averageMultiplierNormSq average * LDL.oneSixteenth
      ≤ averageMultiplierNormSq average * AverageSection.siteCount
    scaled =
      Norm.scaleNonnegative
        (averageMultiplierNormSq average)
        (averageMultiplierNormSqNonnegative average)
        coefficientBelow

    reordered :
      LDL.oneSixteenth * averageMultiplierNormSq average
      ≤ AverageSection.siteCount * averageMultiplierNormSq average
    reordered =
      subst
        (λ left → left ≤ AverageSection.siteCount * averageMultiplierNormSq average)
        (ℚRing.solve-∀ LDL.oneSixteenth (averageMultiplierNormSq average))
        (subst
          (λ right → averageMultiplierNormSq average * LDL.oneSixteenth ≤ right)
          (ℚRing.solve-∀ AverageSection.siteCount (averageMultiplierNormSq average))
          scaled)
  in
  subst
    (λ upper →
      LDL.oneSixteenth * averageMultiplierNormSq average ≤ upper)
    (sym (averageAdjointNormExact average))
    reordered

------------------------------------------------------------------------
-- Constant average lift is exactly orthogonal to the flat gauge gradient.
------------------------------------------------------------------------

periodicForwardDifferenceSumZero : ∀ axis field →
  Periodic.sumSites (Periodic.forwardDifference axis field) ≡ 0ℚ
periodicForwardDifferenceSumZero axis field =
  trans
    (Periodic.sumSitesSubtract
      (λ site → field (Periodic.shiftForward axis site)) field)
    (trans
      (cong₂ _-_
        (Periodic.sumSitesForwardInvariant field axis) refl)
      (ℚRing.solve-∀ (Periodic.sumSites field)))

periodicNegativeForwardDifferenceSumZero : ∀ axis field →
  Periodic.sumSites
    (λ site → - Periodic.forwardDifference axis field site)
  ≡ 0ℚ
periodicNegativeForwardDifferenceSumZero axis field =
  trans
    (Periodic.sumSitesNeg (Periodic.forwardDifference axis field))
    (trans
      (cong -_ (periodicForwardDifferenceSumZero axis field))
      (ℚRing.solve []))

flatGaugeAverageConstraintZero : ∀ gauge row →
  Average.selectedBackgroundBlockAverageConstraintApply
    (FlatAdjoint.actualFlatGaugeAdjoint gauge) row
  ≡ 0ℚ
flatGaugeAverageConstraintZero gauge
    (DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.pair coordinate axis) =
  let
    field = FlatAdjoint.multiplierField gauge coordinate

    asGradient :
      Average.selectedBackgroundBlockAverageConstraintApply
        (FlatAdjoint.actualFlatGaugeAdjoint gauge)
        (DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.pair coordinate axis)
      ≡ Sums.sumRational (Block.physicalBlockSites
          DASHI.Physics.YangMills.BalabanPath4AxisAverageExact.side4)
          (λ site → - Periodic.forwardDifference axis field site)
    asGradient =
      trans
        (Average.selectedBackgroundBlockAverageConstraintMatrixApplyExact
          (FlatAdjoint.actualFlatGaugeAdjoint gauge)
          (DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.pair coordinate axis))
        (Sums.sumRationalCong
          (Block.physicalBlockSites
            DASHI.Physics.YangMills.BalabanPath4AxisAverageExact.side4)
          (λ site →
            FlatAdjoint.actualFlatGaugeAdjoint gauge
              (DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.pair coordinate
                (DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.pair axis site)))
          (λ site → - Periodic.forwardDifference axis field site)
          (λ site →
            FlatAdjoint.actualFlatGaugeAdjointPointwiseExact gauge
              (DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.pair coordinate
                (DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.pair axis site))))
  in
  trans asGradient
    (trans
      (sym
        (Bridge.sumSitesMatchesGlobalSiteSum
          (λ site → - Periodic.forwardDifference axis field site)))
      (periodicNegativeForwardDifferenceSumZero axis field))

flatGaugeAverageRowPairingZero : ∀ gauge average →
  AverageSection.selectedBlockAverageRowDot
    (Average.selectedBackgroundBlockAverageConstraintApply
      (FlatAdjoint.actualFlatGaugeAdjoint gauge)) average
  ≡ 0ℚ
flatGaugeAverageRowPairingZero gauge average =
  trans
    (Sums.sumRationalCong Average.selectedBlockAverageRows4 _ (λ _ → 0ℚ)
      (λ row →
        trans
          (cong (_* average row) (flatGaugeAverageConstraintZero gauge row))
          (ℚRing.solve-∀ (average row))))
    (Fubini.sumRationalZero Average.selectedBlockAverageRows4)

averageFlatGaugeOrthogonal : ∀ average gauge →
  KKT.stateDot
    (AverageSection.selectedBlockAverageAdjointLift average)
    (FlatAdjoint.actualFlatGaugeAdjoint gauge)
  ≡ 0ℚ
averageFlatGaugeOrthogonal average gauge =
  trans
    (Rect.finiteDotSymmetric KKT.physicalStateCarrier
      (AverageSection.selectedBlockAverageAdjointLift average)
      (FlatAdjoint.actualFlatGaugeAdjoint gauge))
    (trans
      (sym
        (AverageSection.selectedBlockAverageAdjointExact
          (FlatAdjoint.actualFlatGaugeAdjoint gauge) average))
      (flatGaugeAverageRowPairingZero gauge average))

------------------------------------------------------------------------
-- Orthogonal finite sum and reference floor.
------------------------------------------------------------------------

stateAdd : KKT.StateVector → KKT.StateVector → KKT.StateVector
stateAdd left right coordinate = left coordinate + right coordinate

stateNormAddOrthogonal : ∀ left right →
  KKT.stateDot left right ≡ 0ℚ →
  KKT.stateNormSq (stateAdd left right)
  ≡ KKT.stateNormSq left + KKT.stateNormSq right
stateNormAddOrthogonal left right orthogonal =
  let
    coordinates =
      DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact.coordinates
        KKT.physicalStateCarrier

    expanded :
      KKT.stateNormSq (stateAdd left right)
      ≡ Sums.sumRational coordinates
          (λ coordinate →
            left coordinate * left coordinate
            + right coordinate * right coordinate
            + (+ 2 / 1) * (left coordinate * right coordinate))
    expanded =
      Sums.sumRationalCong coordinates _ _
        (λ coordinate → ℚRing.solve-∀ (left coordinate) (right coordinate))

    folded =
      trans
        (Fubini.sumRationalAdd coordinates
          (λ coordinate → left coordinate * left coordinate)
          (λ coordinate →
            right coordinate * right coordinate
            + (+ 2 / 1) * (left coordinate * right coordinate)))
        (cong
          (KKT.stateNormSq left +_)
          (trans
            (Fubini.sumRationalAdd coordinates
              (λ coordinate → right coordinate * right coordinate)
              (λ coordinate → (+ 2 / 1) * (left coordinate * right coordinate)))
            (cong
              (KKT.stateNormSq right +_)
              (trans
                (Sums.sumRationalScale (+ 2 / 1) coordinates
                  (λ coordinate → left coordinate * right coordinate))
                (trans (cong ((+ 2 / 1) *_ ) orthogonal)
                  (ℚRing.solve []))))))
  in
  trans expanded folded

record StableCombinedMultiplier : Set where
  constructor stableCombinedMultiplier
  field
    average : AverageMultiplier
    gauge : GaugeMultiplier
    gaugeReduced : FlatFloor.FlatGaugeReducedMultiplier gauge
open StableCombinedMultiplier public

stableCombinedMultiplierNormSq : StableCombinedMultiplier → ℚ
stableCombinedMultiplierNormSq selected =
  averageMultiplierNormSq (average selected)
  + gaugeMultiplierNormSq (gauge selected)

referenceCombinedAdjoint : StableCombinedMultiplier → KKT.StateVector
referenceCombinedAdjoint selected =
  stateAdd
    (AverageSection.selectedBlockAverageAdjointLift (average selected))
    (FlatAdjoint.actualFlatGaugeAdjoint (gauge selected))

referenceCombinedNormExact : ∀ selected →
  KKT.stateNormSq (referenceCombinedAdjoint selected)
  ≡ KKT.stateNormSq
      (AverageSection.selectedBlockAverageAdjointLift (average selected))
    + KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint (gauge selected))
referenceCombinedNormExact selected =
  stateNormAddOrthogonal
    (AverageSection.selectedBlockAverageAdjointLift (average selected))
    (FlatAdjoint.actualFlatGaugeAdjoint (gauge selected))
    (averageFlatGaugeOrthogonal (average selected) (gauge selected))

referenceCombinedOneSixteenthFloor : ∀ selected →
  LDL.oneSixteenth * stableCombinedMultiplierNormSq selected
  ≤ KKT.stateNormSq (referenceCombinedAdjoint selected)
referenceCombinedOneSixteenthFloor selected =
  let
    componentwise :
      LDL.oneSixteenth * averageMultiplierNormSq (average selected)
      + LDL.oneSixteenth * gaugeMultiplierNormSq (gauge selected)
      ≤ KKT.stateNormSq
          (AverageSection.selectedBlockAverageAdjointLift (average selected))
        + KKT.stateNormSq
          (FlatAdjoint.actualFlatGaugeAdjoint (gauge selected))
    componentwise = ℚP.+-mono-≤
      (averageAdjointOneSixteenthFloor (average selected))
      (FlatAdjoint.actualFlatGaugeGramReducedFloor
        (gauge selected) (gaugeReduced selected))

    leftExact :
      LDL.oneSixteenth * stableCombinedMultiplierNormSq selected
      ≡ LDL.oneSixteenth * averageMultiplierNormSq (average selected)
        + LDL.oneSixteenth * gaugeMultiplierNormSq (gauge selected)
    leftExact = ℚRing.solve-∀
      LDL.oneSixteenth
      (averageMultiplierNormSq (average selected))
      (gaugeMultiplierNormSq (gauge selected))
  in
  subst
    (λ lower → lower ≤ KKT.stateNormSq (referenceCombinedAdjoint selected))
    leftExact
    (subst
      (λ upper →
        LDL.oneSixteenth * averageMultiplierNormSq (average selected)
        + LDL.oneSixteenth * gaugeMultiplierNormSq (gauge selected)
        ≤ upper)
      (sym (referenceCombinedNormExact selected))
      componentwise)

------------------------------------------------------------------------
-- Literal 780-row transpose equals the physical component sum.
------------------------------------------------------------------------

combinedMultiplierVector :
  StableCombinedMultiplier → Combined.SelectedConstraintRow4 → ℚ
combinedMultiplierVector selected (Combined.averageConstraintRow row) =
  average selected row
combinedMultiplierVector selected (Combined.gaugeConstraintRow row) =
  gauge selected row

literalCombinedAdjoint :
  Physical.RationalSU2Background4 →
  StableCombinedMultiplier → KKT.StateVector
literalCombinedAdjoint background selected =
  Rect.applyRectangular CombinedRows.selectedCombinedConstraintRowCarrier
    (Rect.transposeRectangular
      (Combined.selectedBackgroundLinearizedConstraintMatrix background))
    (combinedMultiplierVector selected)

componentCombinedAdjoint :
  Physical.RationalSU2Background4 →
  StableCombinedMultiplier → KKT.StateVector
componentCombinedAdjoint background selected coordinate =
  AverageSection.selectedBlockAverageAdjointLift (average selected) coordinate
  + GaugeFloor.backgroundGaugeAdjoint background (gauge selected) coordinate

literalCombinedAdjointComponentExact :
  ∀ background selected coordinate →
  literalCombinedAdjoint background selected coordinate
  ≡ componentCombinedAdjoint background selected coordinate
literalCombinedAdjointComponentExact background selected coordinate =
  let
    averageRows =
      DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.map
        Combined.averageConstraintRow
        (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
    gaugeRows =
      DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.map
        Combined.gaugeConstraintRow
        (Basis.elements CombinedRows.selectedGaugeRowFiniteSelector)

    split =
      Fubini.sumRationalAppend averageRows gaugeRows
        (λ row →
          Combined.selectedBackgroundLinearizedConstraintMatrix
            background row coordinate
          * combinedMultiplierVector selected row)

    averagePart :
      Sums.sumRational averageRows
        (λ row →
          Combined.selectedBackgroundLinearizedConstraintMatrix
            background row coordinate
          * combinedMultiplierVector selected row)
      ≡ AverageSection.selectedBlockAverageAdjointLift
          (average selected) coordinate
    averagePart =
      trans
        (Fubini.sumRationalMap Combined.averageConstraintRow
          (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
          (λ row →
            Combined.selectedBackgroundLinearizedConstraintMatrix
              background row coordinate
            * combinedMultiplierVector selected row))
        (AverageRows.selectedBlockAverageTransposeApplyExact
          (average selected) coordinate)

    gaugePart :
      Sums.sumRational gaugeRows
        (λ row →
          Combined.selectedBackgroundLinearizedConstraintMatrix
            background row coordinate
          * combinedMultiplierVector selected row)
      ≡ GaugeFloor.backgroundGaugeAdjoint background (gauge selected) coordinate
    gaugePart =
      Fubini.sumRationalMap Combined.gaugeConstraintRow
        (Basis.elements CombinedRows.selectedGaugeRowFiniteSelector)
        (λ row →
          Combined.selectedBackgroundLinearizedConstraintMatrix
            background row coordinate
          * combinedMultiplierVector selected row)
  in
  trans split (cong₂ _+_ averagePart gaugePart)

------------------------------------------------------------------------
-- Selected-background perturbation and explicit 29/1024 floor.
------------------------------------------------------------------------

selectedCombinedDefect :
  Physical.RationalSU2Background4 →
  StableCombinedMultiplier → KKT.StateVector
selectedCombinedDefect background selected =
  GaugeDefect.gaugeAdjointDefectApply background (gauge selected)

componentCombinedAdjointSplits : ∀ background selected coordinate →
  componentCombinedAdjoint background selected coordinate
  ≡ referenceCombinedAdjoint selected coordinate
    + selectedCombinedDefect background selected coordinate
componentCombinedAdjointSplits background selected coordinate =
  trans
    (cong
      (AverageSection.selectedBlockAverageAdjointLift (average selected) coordinate +_)
      (GaugeFloor.backgroundGaugeAdjointSplits
        background (gauge selected) coordinate))
    (ℚRing.solve-∀
      (AverageSection.selectedBlockAverageAdjointLift (average selected) coordinate)
      (FlatAdjoint.actualFlatGaugeAdjoint (gauge selected) coordinate)
      (GaugeDefect.gaugeAdjointDefectApply
        background (gauge selected) coordinate))

combinedNormContainsGaugeNorm : ∀ selected →
  gaugeMultiplierNormSq (gauge selected)
  ≤ stableCombinedMultiplierNormSq selected
combinedNormContainsGaugeNorm selected =
  subst
    (λ lower → lower ≤
      averageMultiplierNormSq (average selected)
      + gaugeMultiplierNormSq (gauge selected))
    (ℚP.+-identityˡ (gaugeMultiplierNormSq (gauge selected)))
    (ℚP.+-monoʳ-≤
      (gaugeMultiplierNormSq (gauge selected))
      (averageMultiplierNormSqNonnegative (average selected)))

selectedCombinedDefectUpper :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ selected →
  KKT.stateNormSq (selectedCombinedDefect background selected)
  ≤ GaugeDefect.selectedAdjointDefectCoefficient
      * stableCombinedMultiplierNormSq selected
selectedCombinedDefectUpper background radius selected =
  let
    raw = GaugeDefect.gaugeAdjointDefectSelectedRadiusBound
      background radius (gauge selected)

    rowToGauge :
      KKT.stateNormSq (selectedCombinedDefect background selected)
      ≤ GaugeDefect.selectedAdjointDefectCoefficient
          * gaugeMultiplierNormSq (gauge selected)
    rowToGauge =
      subst
        (λ rowNorm →
          KKT.stateNormSq (selectedCombinedDefect background selected)
          ≤ GaugeDefect.selectedAdjointDefectCoefficient * rowNorm)
        (GaugeFloor.gaugeMultiplierRowNormSqExact (gauge selected))
        raw

    scaled =
      Norm.scaleNonnegative
        GaugeDefect.selectedAdjointDefectCoefficient
        (ℚP.nonNegative⁻¹ GaugeDefect.selectedAdjointDefectCoefficient)
        (combinedNormContainsGaugeNorm selected)
  in
  ℚP.≤-trans rowToGauge scaled

combinedPerturbationData :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  Perturb.ReducedFloorPerturbationData KKT.physicalStateCarrier
combinedPerturbationData background radius = record
  { Perturb.ReducedFloorPerturbationData.Multiplier = StableCombinedMultiplier
  ; Perturb.ReducedFloorPerturbationData.multiplierNormSq =
      stableCombinedMultiplierNormSq
  ; Perturb.ReducedFloorPerturbationData.reference = referenceCombinedAdjoint
  ; Perturb.ReducedFloorPerturbationData.defect = selectedCombinedDefect background
  ; Perturb.ReducedFloorPerturbationData.full = componentCombinedAdjoint background
  ; Perturb.ReducedFloorPerturbationData.referenceFloor = LDL.oneSixteenth
  ; Perturb.ReducedFloorPerturbationData.defectCoefficient =
      GaugeDefect.selectedAdjointDefectCoefficient
  ; Perturb.ReducedFloorPerturbationData.fullSplits =
      componentCombinedAdjointSplits background
  ; Perturb.ReducedFloorPerturbationData.referenceCoercive =
      referenceCombinedOneSixteenthFloor
  ; Perturb.ReducedFloorPerturbationData.defectUpper =
      selectedCombinedDefectUpper background radius
  }

selectedCombinedStableFloor : ℚ
selectedCombinedStableFloor = + 29 / 1024

selectedCombinedStableFloorExact :
  Perturb.oneHalf * LDL.oneSixteenth
  - GaugeDefect.selectedAdjointDefectCoefficient
  ≡ selectedCombinedStableFloor
selectedCombinedStableFloorExact = ℚRing.solve []

selectedBackgroundCombinedStableMultiplierFloor :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ selected →
  selectedCombinedStableFloor * stableCombinedMultiplierNormSq selected
  ≤ KKT.stateNormSq (literalCombinedAdjoint background selected)
selectedBackgroundCombinedStableMultiplierFloor background radius selected =
  let
    componentFloor =
      Perturb.perturbedReducedFloor
        (combinedPerturbationData background radius) selected

    componentFloorNormalized :
      selectedCombinedStableFloor * stableCombinedMultiplierNormSq selected
      ≤ KKT.stateNormSq (componentCombinedAdjoint background selected)
    componentFloorNormalized =
      subst
        (λ coefficient →
          coefficient * stableCombinedMultiplierNormSq selected
          ≤ KKT.stateNormSq (componentCombinedAdjoint background selected))
        selectedCombinedStableFloorExact
        componentFloor

    normExact :
      KKT.stateNormSq (literalCombinedAdjoint background selected)
      ≡ KKT.stateNormSq (componentCombinedAdjoint background selected)
    normExact =
      Sums.sumRationalCong
        (DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact.coordinates
          KKT.physicalStateCarrier) _ _
        (λ coordinate →
          cong₂ _*_
            (literalCombinedAdjointComponentExact background selected coordinate)
            (literalCombinedAdjointComponentExact background selected coordinate))
  in
  subst
    (λ upper →
      selectedCombinedStableFloor * stableCombinedMultiplierNormSq selected
      ≤ upper)
    (sym normExact)
    componentFloorNormalized

selectedVariationalCombinedStableMultiplierFloor :
  ∀ {CoarseField Lie}
    (inputs : SelectedRadius.SelectedPhysicalBackgroundInstantiation
      CoarseField Lie)
    coarse
    (small : Variational.CoarseSmallField
      (Selected.variational (SelectedRadius.bridge inputs)) coarse)
    selected →
  selectedCombinedStableFloor * stableCombinedMultiplierNormSq selected
  ≤ KKT.stateNormSq
      (literalCombinedAdjoint
        (Selected.selectedBackground (SelectedRadius.bridge inputs) coarse small)
        selected)
selectedVariationalCombinedStableMultiplierFloor inputs coarse small selected =
  selectedBackgroundCombinedStableMultiplierFloor
    (Selected.selectedBackground (SelectedRadius.bridge inputs) coarse small)
    (SelectedRadius.selectedBackgroundRelaxedInverseLinkRadius inputs coarse small)
    selected

selectedCombinedStableMultiplierFloorLevel : ProofLevel
selectedCombinedStableMultiplierFloorLevel = machineChecked

selectedVariationalCombinedStableMultiplierFloorLevel : ProofLevel
selectedVariationalCombinedStableMultiplierFloorLevel = machineChecked
