module DASHI.Promotion.MaxwellExteriorCalculusAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.ClassicalFieldObligations as Classical

------------------------------------------------------------------------
-- A finite symbolic exterior-calculus adapter for the Maxwell lane.
--
-- This module advances the Maxwell lane only on the homogeneous side:
-- it gives a concrete finite symbolic carrier for A, F = d A, and
-- d F = 0 for the canonical potential.  The metric/Hodge/current and
-- empirical source equation are still authority-bound, so no Maxwell
-- field-equation promotion follows.

data FormDegree : Set where
  degree0 : FormDegree
  degree1 : FormDegree
  degree2 : FormDegree
  degree3 : FormDegree
  degree4 : FormDegree

data ZeroForm : Set where
  zeroScalarForm : ZeroForm
  canonicalGaugeParameter : ZeroForm
  canonicalChargeScalar : ZeroForm

data OneForm : Set where
  zeroOneForm : OneForm
  canonicalPotentialOneForm : OneForm
  exactGaugeOneForm : OneForm
  gaugeShiftedPotentialOneForm : OneForm

data TwoForm : Set where
  zeroTwoForm : TwoForm
  canonicalCurvatureTwoForm : TwoForm
  hodgeDualCurvatureTwoForm : TwoForm
  uncalibratedFluxTwoForm : TwoForm

data ThreeForm : Set where
  zeroThreeForm : ThreeForm
  sourceCurrentThreeForm : ThreeForm
  unverifiedDStarFThreeForm : ThreeForm
  continuityDefectThreeForm : ThreeForm

data FourForm : Set where
  zeroFourForm : FourForm
  continuityFourForm : FourForm
  actionDensityFourForm : FourForm

data SymbolicEquationStatus : Set where
  constructedByExteriorDerivative : SymbolicEquationStatus
  authorityBoundMetricHodge : SymbolicEquationStatus
  authorityBoundSourceCurrent : SymbolicEquationStatus
  authorityBoundEmpiricalObservable : SymbolicEquationStatus
  promotionClosed : SymbolicEquationStatus

d0 : ZeroForm → OneForm
d0 zeroScalarForm = zeroOneForm
d0 canonicalGaugeParameter = exactGaugeOneForm
d0 canonicalChargeScalar = zeroOneForm

d1 : OneForm → TwoForm
d1 zeroOneForm = zeroTwoForm
d1 canonicalPotentialOneForm = canonicalCurvatureTwoForm
d1 exactGaugeOneForm = zeroTwoForm
d1 gaugeShiftedPotentialOneForm = canonicalCurvatureTwoForm

d2 : TwoForm → ThreeForm
d2 zeroTwoForm = zeroThreeForm
d2 canonicalCurvatureTwoForm = zeroThreeForm
d2 hodgeDualCurvatureTwoForm = unverifiedDStarFThreeForm
d2 uncalibratedFluxTwoForm = continuityDefectThreeForm

d3 : ThreeForm → FourForm
d3 zeroThreeForm = zeroFourForm
d3 sourceCurrentThreeForm = continuityFourForm
d3 unverifiedDStarFThreeForm = continuityFourForm
d3 continuityDefectThreeForm = actionDensityFourForm

d4 : FourForm → FourForm
d4 zeroFourForm = zeroFourForm
d4 continuityFourForm = zeroFourForm
d4 actionDensityFourForm = zeroFourForm

hodge2Symbolic : TwoForm → TwoForm
hodge2Symbolic zeroTwoForm = zeroTwoForm
hodge2Symbolic canonicalCurvatureTwoForm = hodgeDualCurvatureTwoForm
hodge2Symbolic hodgeDualCurvatureTwoForm = canonicalCurvatureTwoForm
hodge2Symbolic uncalibratedFluxTwoForm = uncalibratedFluxTwoForm

gaugeShift : OneForm → ZeroForm → OneForm
gaugeShift zeroOneForm zeroScalarForm = zeroOneForm
gaugeShift zeroOneForm canonicalGaugeParameter = exactGaugeOneForm
gaugeShift zeroOneForm canonicalChargeScalar = zeroOneForm
gaugeShift canonicalPotentialOneForm zeroScalarForm =
  canonicalPotentialOneForm
gaugeShift canonicalPotentialOneForm canonicalGaugeParameter =
  gaugeShiftedPotentialOneForm
gaugeShift canonicalPotentialOneForm canonicalChargeScalar =
  canonicalPotentialOneForm
gaugeShift exactGaugeOneForm zeroScalarForm = exactGaugeOneForm
gaugeShift exactGaugeOneForm canonicalGaugeParameter = exactGaugeOneForm
gaugeShift exactGaugeOneForm canonicalChargeScalar = exactGaugeOneForm
gaugeShift gaugeShiftedPotentialOneForm zeroScalarForm =
  gaugeShiftedPotentialOneForm
gaugeShift gaugeShiftedPotentialOneForm canonicalGaugeParameter =
  gaugeShiftedPotentialOneForm
gaugeShift gaugeShiftedPotentialOneForm canonicalChargeScalar =
  gaugeShiftedPotentialOneForm

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

canonicalDegrees : List FormDegree
canonicalDegrees =
  degree0
  ∷ degree1
  ∷ degree2
  ∷ degree3
  ∷ degree4
  ∷ []

canonicalZeroForms : List ZeroForm
canonicalZeroForms =
  zeroScalarForm
  ∷ canonicalGaugeParameter
  ∷ canonicalChargeScalar
  ∷ []

canonicalOneForms : List OneForm
canonicalOneForms =
  zeroOneForm
  ∷ canonicalPotentialOneForm
  ∷ exactGaugeOneForm
  ∷ gaugeShiftedPotentialOneForm
  ∷ []

canonicalTwoForms : List TwoForm
canonicalTwoForms =
  zeroTwoForm
  ∷ canonicalCurvatureTwoForm
  ∷ hodgeDualCurvatureTwoForm
  ∷ uncalibratedFluxTwoForm
  ∷ []

canonicalThreeForms : List ThreeForm
canonicalThreeForms =
  zeroThreeForm
  ∷ sourceCurrentThreeForm
  ∷ unverifiedDStarFThreeForm
  ∷ continuityDefectThreeForm
  ∷ []

canonicalFourForms : List FourForm
canonicalFourForms =
  zeroFourForm
  ∷ continuityFourForm
  ∷ actionDensityFourForm
  ∷ []

record MaxwellSymbolicFormInventory : Set where
  field
    degrees : List FormDegree
    zeroForms : List ZeroForm
    oneForms : List OneForm
    twoForms : List TwoForm
    threeForms : List ThreeForm
    fourForms : List FourForm
    degreeCount : Nat
    degreeCountIs5 : degreeCount ≡ listLength degrees
    zeroFormCount : Nat
    zeroFormCountIs3 : zeroFormCount ≡ listLength zeroForms
    oneFormCount : Nat
    oneFormCountIs4 : oneFormCount ≡ listLength oneForms
    twoFormCount : Nat
    twoFormCountIs4 : twoFormCount ≡ listLength twoForms
    threeFormCount : Nat
    threeFormCountIs4 : threeFormCount ≡ listLength threeForms
    fourFormCount : Nat
    fourFormCountIs3 : fourFormCount ≡ listLength fourForms

open MaxwellSymbolicFormInventory public

canonicalMaxwellSymbolicFormInventory :
  MaxwellSymbolicFormInventory
canonicalMaxwellSymbolicFormInventory = record
  { degrees = canonicalDegrees
  ; zeroForms = canonicalZeroForms
  ; oneForms = canonicalOneForms
  ; twoForms = canonicalTwoForms
  ; threeForms = canonicalThreeForms
  ; fourForms = canonicalFourForms
  ; degreeCount = 5
  ; degreeCountIs5 = refl
  ; zeroFormCount = 3
  ; zeroFormCountIs3 = refl
  ; oneFormCount = 4
  ; oneFormCountIs4 = refl
  ; twoFormCount = 4
  ; twoFormCountIs4 = refl
  ; threeFormCount = 4
  ; threeFormCountIs4 = refl
  ; fourFormCount = 3
  ; fourFormCountIs3 = refl
  }

record CanonicalCurvatureConstruction : Set where
  field
    potential : OneForm
    curvature : TwoForm
    curvatureDefinition : String
    curvatureIsExteriorDerivative : curvature ≡ d1 potential
    gaugeParameter : ZeroForm
    shiftedPotential : OneForm
    shiftedPotentialIsGaugeShift :
      shiftedPotential ≡ gaugeShift potential gaugeParameter
    gaugeShiftKeepsCurvature :
      d1 shiftedPotential ≡ d1 potential
    homogeneousEquationTarget : String
    bianchiStatus : SymbolicEquationStatus
    bianchiThreeForm : ThreeForm
    bianchiByConstruction : d2 curvature ≡ zeroThreeForm
    exteriorSquareOnPotentialIsZero :
      d2 (d1 potential) ≡ zeroThreeForm

open CanonicalCurvatureConstruction public

canonicalCurvatureConstruction :
  CanonicalCurvatureConstruction
canonicalCurvatureConstruction = record
  { potential = canonicalPotentialOneForm
  ; curvature = canonicalCurvatureTwoForm
  ; curvatureDefinition = "F = d A"
  ; curvatureIsExteriorDerivative = refl
  ; gaugeParameter = canonicalGaugeParameter
  ; shiftedPotential = gaugeShiftedPotentialOneForm
  ; shiftedPotentialIsGaugeShift = refl
  ; gaugeShiftKeepsCurvature = refl
  ; homogeneousEquationTarget = "d F = 0"
  ; bianchiStatus = constructedByExteriorDerivative
  ; bianchiThreeForm = zeroThreeForm
  ; bianchiByConstruction = refl
  ; exteriorSquareOnPotentialIsZero = refl
  }

record HodgeSourceAuthorityBoundary : Set₁ where
  field
    symbolicHodgeTarget : TwoForm
    symbolicDStarF : ThreeForm
    hodgeBoundaryStatus : SymbolicEquationStatus
    sourceBoundaryStatus : SymbolicEquationStatus
    empiricalBoundaryStatus : SymbolicEquationStatus
    metricCarrierRequired : String
    orientationCarrierRequired : String
    hodgeStarAuthorityRequired : String
    sourceCurrentCarrier : ThreeForm
    sourceCurrentAuthorityRequired : String
    chargeCalibrationAuthorityRequired : String
    hodgeEquationPromoted : Bool
    hodgeEquationPromotedIsFalse : hodgeEquationPromoted ≡ false
    sourceEquationPromoted : Bool
    sourceEquationPromotedIsFalse : sourceEquationPromoted ≡ false
    empiricalObservablePromoted : Bool
    empiricalObservablePromotedIsFalse :
      empiricalObservablePromoted ≡ false

open HodgeSourceAuthorityBoundary public

canonicalHodgeSourceAuthorityBoundary :
  HodgeSourceAuthorityBoundary
canonicalHodgeSourceAuthorityBoundary = record
  { symbolicHodgeTarget =
      hodge2Symbolic canonicalCurvatureTwoForm
  ; symbolicDStarF =
      d2 (hodge2Symbolic canonicalCurvatureTwoForm)
  ; hodgeBoundaryStatus = authorityBoundMetricHodge
  ; sourceBoundaryStatus = authorityBoundSourceCurrent
  ; empiricalBoundaryStatus = authorityBoundEmpiricalObservable
  ; metricCarrierRequired =
      Classical.MaxwellHodgeObligation.metricCarrierRequired
        Classical.canonicalMaxwellHodgeObligation
  ; orientationCarrierRequired =
      Classical.MaxwellHodgeObligation.orientationVolumeCarrierRequired
        Classical.canonicalMaxwellHodgeObligation
  ; hodgeStarAuthorityRequired =
      Classical.MaxwellHodgeObligation.hodgeStarOnTwoFormsRequired
        Classical.canonicalMaxwellHodgeObligation
  ; sourceCurrentCarrier = sourceCurrentThreeForm
  ; sourceCurrentAuthorityRequired =
      Classical.MaxwellSourceCurrentObligation.sourceExtractionReceiptRequired
        Classical.canonicalMaxwellSourceCurrentObligation
  ; chargeCalibrationAuthorityRequired =
      Classical.MaxwellSourceCurrentObligation.chargeCalibrationReceiptRequired
        Classical.canonicalMaxwellSourceCurrentObligation
  ; hodgeEquationPromoted = false
  ; hodgeEquationPromotedIsFalse = refl
  ; sourceEquationPromoted = false
  ; sourceEquationPromotedIsFalse = refl
  ; empiricalObservablePromoted = false
  ; empiricalObservablePromotedIsFalse = refl
  }

record MaxwellExteriorCalculusAdapter : Set₁ where
  field
    sourceRegistry :
      Registry.ConstantsRegistry
    sourcePhysicsReceipt :
      Registry.PhysicsAdapterKnownInputsReferenceReceipt
    sourceClassicalIndex :
      Classical.ClassicalFieldPromotionObligationIndex
    sourceMaxwellObligation :
      Classical.MaxwellFieldEquationPromotionObligation
    connectedCurvatureObligation :
      Classical.MaxwellCurvatureObligation
    connectedHodgeObligation :
      Classical.MaxwellHodgeObligation
    connectedSourceCurrentObligation :
      Classical.MaxwellSourceCurrentObligation
    formInventory :
      MaxwellSymbolicFormInventory
    curvatureConstruction :
      CanonicalCurvatureConstruction
    hodgeSourceAuthorityBoundary :
      HodgeSourceAuthorityBoundary
    connectedPotentialCarrier :
      Classical.MaxwellCurvatureObligation.potentialCarrier
        connectedCurvatureObligation
      ≡ Classical.electromagneticPotentialOneForm
    connectedCurvatureCarrier :
      Classical.MaxwellCurvatureObligation.curvatureCarrier
        connectedCurvatureObligation
      ≡ Classical.electromagneticCurvatureTwoForm
    connectedHodgeCarrierSupplied :
      Classical.MaxwellHodgeObligation.hodgeCarrierSupplied
        connectedHodgeObligation
      ≡ true
    connectedSourceCurrentCarrier :
      Classical.MaxwellSourceCurrentObligation.currentCarrier
        connectedSourceCurrentObligation
      ≡ Classical.electricChargeCurrentThreeForm
    connectedHomogeneousTarget :
      Classical.MaxwellFieldEquationPromotionObligation.homogeneousEquationTarget
        sourceMaxwellObligation
      ≡ "d F = 0"
    connectedInhomogeneousTarget :
      Classical.MaxwellFieldEquationPromotionObligation.inhomogeneousEquationTarget
        sourceMaxwellObligation
      ≡ "d * F = J"
    constructedEquationCount :
      Nat
    constructedEquationCountIs1 :
      constructedEquationCount ≡ 1
    authorityBoundEquationCount :
      Nat
    authorityBoundEquationCountIs3 :
      authorityBoundEquationCount ≡ 3
    connectedObligationFieldCount :
      Nat
    connectedObligationFieldCountIs4 :
      connectedObligationFieldCount ≡ 4
    modelLawPromoted :
      Bool
    modelLawPromotedIsFalse :
      modelLawPromoted ≡ false
    sourceEquationPromoted :
      Bool
    sourceEquationPromotedIsFalse :
      sourceEquationPromoted ≡ false
    maxwellFieldEquationPromoted :
      Bool
    maxwellFieldEquationPromotedIsFalse :
      maxwellFieldEquationPromoted ≡ false

open MaxwellExteriorCalculusAdapter public

canonicalMaxwellExteriorCalculusAdapter :
  MaxwellExteriorCalculusAdapter
canonicalMaxwellExteriorCalculusAdapter = record
  { sourceRegistry =
      Registry.repoWideConstantsRegistry
  ; sourcePhysicsReceipt =
      Registry.canonicalPhysicsAdapterKnownInputsReferenceReceipt
  ; sourceClassicalIndex =
      Classical.canonicalClassicalFieldPromotionObligationIndex
  ; sourceMaxwellObligation =
      Classical.canonicalMaxwellFieldEquationPromotionObligation
  ; connectedCurvatureObligation =
      Classical.canonicalMaxwellCurvatureObligation
  ; connectedHodgeObligation =
      Classical.canonicalMaxwellHodgeObligation
  ; connectedSourceCurrentObligation =
      Classical.canonicalMaxwellSourceCurrentObligation
  ; formInventory =
      canonicalMaxwellSymbolicFormInventory
  ; curvatureConstruction =
      canonicalCurvatureConstruction
  ; hodgeSourceAuthorityBoundary =
      canonicalHodgeSourceAuthorityBoundary
  ; connectedPotentialCarrier =
      refl
  ; connectedCurvatureCarrier =
      refl
  ; connectedHodgeCarrierSupplied =
      refl
  ; connectedSourceCurrentCarrier =
      refl
  ; connectedHomogeneousTarget =
      refl
  ; connectedInhomogeneousTarget =
      refl
  ; constructedEquationCount =
      1
  ; constructedEquationCountIs1 =
      refl
  ; authorityBoundEquationCount =
      3
  ; authorityBoundEquationCountIs3 =
      refl
  ; connectedObligationFieldCount =
      4
  ; connectedObligationFieldCountIs4 =
      refl
  ; modelLawPromoted =
      false
  ; modelLawPromotedIsFalse =
      refl
  ; sourceEquationPromoted =
      false
  ; sourceEquationPromotedIsFalse =
      refl
  ; maxwellFieldEquationPromoted =
      false
  ; maxwellFieldEquationPromotedIsFalse =
      refl
  }

canonicalDegreeCountIs5 :
  MaxwellSymbolicFormInventory.degreeCount
    canonicalMaxwellSymbolicFormInventory
  ≡ 5
canonicalDegreeCountIs5 = refl

canonicalZeroFormCountIs3 :
  MaxwellSymbolicFormInventory.zeroFormCount
    canonicalMaxwellSymbolicFormInventory
  ≡ 3
canonicalZeroFormCountIs3 = refl

canonicalOneFormCountIs4 :
  MaxwellSymbolicFormInventory.oneFormCount
    canonicalMaxwellSymbolicFormInventory
  ≡ 4
canonicalOneFormCountIs4 = refl

canonicalTwoFormCountIs4 :
  MaxwellSymbolicFormInventory.twoFormCount
    canonicalMaxwellSymbolicFormInventory
  ≡ 4
canonicalTwoFormCountIs4 = refl

canonicalThreeFormCountIs4 :
  MaxwellSymbolicFormInventory.threeFormCount
    canonicalMaxwellSymbolicFormInventory
  ≡ 4
canonicalThreeFormCountIs4 = refl

canonicalFourFormCountIs3 :
  MaxwellSymbolicFormInventory.fourFormCount
    canonicalMaxwellSymbolicFormInventory
  ≡ 3
canonicalFourFormCountIs3 = refl

canonicalCurvatureIsDA :
  CanonicalCurvatureConstruction.curvature
    canonicalCurvatureConstruction
  ≡
  d1
    (CanonicalCurvatureConstruction.potential
      canonicalCurvatureConstruction)
canonicalCurvatureIsDA = refl

canonicalBianchiByConstruction :
  d2
    (CanonicalCurvatureConstruction.curvature
      canonicalCurvatureConstruction)
  ≡ zeroThreeForm
canonicalBianchiByConstruction = refl

canonicalExteriorSquareOnPotentialIsZero :
  d2
    (d1
      (CanonicalCurvatureConstruction.potential
        canonicalCurvatureConstruction))
  ≡ zeroThreeForm
canonicalExteriorSquareOnPotentialIsZero = refl

canonicalGaugeShiftKeepsCurvature :
  d1
    (CanonicalCurvatureConstruction.shiftedPotential
      canonicalCurvatureConstruction)
  ≡
  d1
    (CanonicalCurvatureConstruction.potential
      canonicalCurvatureConstruction)
canonicalGaugeShiftKeepsCurvature = refl

canonicalSymbolicHodgeTargetIsDualCurvature :
  HodgeSourceAuthorityBoundary.symbolicHodgeTarget
    canonicalHodgeSourceAuthorityBoundary
  ≡ hodgeDualCurvatureTwoForm
canonicalSymbolicHodgeTargetIsDualCurvature = refl

canonicalSymbolicDStarFIsUnverified :
  HodgeSourceAuthorityBoundary.symbolicDStarF
    canonicalHodgeSourceAuthorityBoundary
  ≡ unverifiedDStarFThreeForm
canonicalSymbolicDStarFIsUnverified = refl

canonicalConstructedEquationCountIs1 :
  MaxwellExteriorCalculusAdapter.constructedEquationCount
    canonicalMaxwellExteriorCalculusAdapter
  ≡ 1
canonicalConstructedEquationCountIs1 = refl

canonicalAuthorityBoundEquationCountIs3 :
  MaxwellExteriorCalculusAdapter.authorityBoundEquationCount
    canonicalMaxwellExteriorCalculusAdapter
  ≡ 3
canonicalAuthorityBoundEquationCountIs3 = refl

canonicalConnectedObligationFieldCountIs4 :
  MaxwellExteriorCalculusAdapter.connectedObligationFieldCount
    canonicalMaxwellExteriorCalculusAdapter
  ≡ 4
canonicalConnectedObligationFieldCountIs4 = refl

canonicalAdapterConnectedPotentialCarrier :
  Classical.MaxwellCurvatureObligation.potentialCarrier
    (MaxwellExteriorCalculusAdapter.connectedCurvatureObligation
      canonicalMaxwellExteriorCalculusAdapter)
  ≡ Classical.electromagneticPotentialOneForm
canonicalAdapterConnectedPotentialCarrier = refl

canonicalAdapterConnectedCurvatureCarrier :
  Classical.MaxwellCurvatureObligation.curvatureCarrier
    (MaxwellExteriorCalculusAdapter.connectedCurvatureObligation
      canonicalMaxwellExteriorCalculusAdapter)
  ≡ Classical.electromagneticCurvatureTwoForm
canonicalAdapterConnectedCurvatureCarrier = refl

canonicalAdapterConnectedHomogeneousTarget :
  Classical.MaxwellFieldEquationPromotionObligation.homogeneousEquationTarget
    (MaxwellExteriorCalculusAdapter.sourceMaxwellObligation
      canonicalMaxwellExteriorCalculusAdapter)
  ≡ "d F = 0"
canonicalAdapterConnectedHomogeneousTarget = refl

canonicalAdapterConnectedInhomogeneousTarget :
  Classical.MaxwellFieldEquationPromotionObligation.inhomogeneousEquationTarget
    (MaxwellExteriorCalculusAdapter.sourceMaxwellObligation
      canonicalMaxwellExteriorCalculusAdapter)
  ≡ "d * F = J"
canonicalAdapterConnectedInhomogeneousTarget = refl

canonicalAdapterModelLawPromotedIsFalse :
  MaxwellExteriorCalculusAdapter.modelLawPromoted
    canonicalMaxwellExteriorCalculusAdapter
  ≡ false
canonicalAdapterModelLawPromotedIsFalse = refl

canonicalAdapterSourceEquationPromotedIsFalse :
  MaxwellExteriorCalculusAdapter.sourceEquationPromoted
    canonicalMaxwellExteriorCalculusAdapter
  ≡ false
canonicalAdapterSourceEquationPromotedIsFalse = refl

canonicalAdapterMaxwellFieldEquationPromotedIsFalse :
  MaxwellExteriorCalculusAdapter.maxwellFieldEquationPromoted
    canonicalMaxwellExteriorCalculusAdapter
  ≡ false
canonicalAdapterMaxwellFieldEquationPromotedIsFalse = refl

canonicalClassicalIndexStillKeepsMaxwellFalse :
  Classical.ClassicalFieldPromotionObligationIndex.maxwellFieldEquationsPromoted
    Classical.canonicalClassicalFieldPromotionObligationIndex
  ≡ false
canonicalClassicalIndexStillKeepsMaxwellFalse = refl

canonicalRegistryPhysicsReceiptStillKeepsMaxwellFalse :
  Registry.PhysicsAdapterKnownInputsReferenceReceipt.maxwellFieldEquationPromoted
    Registry.canonicalPhysicsAdapterKnownInputsReferenceReceipt
  ≡ false
canonicalRegistryPhysicsReceiptStillKeepsMaxwellFalse = refl
