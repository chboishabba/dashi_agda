module DASHI.Physics.ExoticGravity.LiTorrMagnitudeTriangleBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LI/TORR MAGNITUDE TRIANGLE
--
-- This owner does not promote the Li/Torr enhancement.  It decomposes the
-- quantitative comparison into three same-apparatus branches:
--   (1) source-paper prediction,
--   (2) correction/rebuttal path,
--   (3) ordinary weak-field GR baseline.
------------------------------------------------------------------------

data TriangleBranch : Set where
  liTorrPrediction : TriangleBranch
  kowittCorrection : TriangleBranch
  harrisCorrection : TriangleBranch
  standardGRBaseline : TriangleBranch
  measuredResidual : TriangleBranch

record MagnitudeCoordinate : Set where
  constructor magnitude-coordinate
  field
    branch : TriangleBranch
    quantityName units geometryLabel : String
    valueExpression sourceReference : String

open MagnitudeCoordinate public

------------------------------------------------------------------------
-- Same-apparatus requirement.
------------------------------------------------------------------------

record SameApparatusWeld : Set where
  constructor same-apparatus-weld
  field
    sameMaterial : Bool
    sameGeometry : Bool
    sameDriveObservable : Bool
    sameProbeLocation : Bool
    sameUnits : Bool
    allRequiredForDirectMagnitudeComparison : Bool
    allRequiredForDirectMagnitudeComparisonIsTrue :
      allRequiredForDirectMagnitudeComparison ≡ true

canonicalSameApparatusWeld : SameApparatusWeld
canonicalSameApparatusWeld =
  same-apparatus-weld true true true true true true refl

------------------------------------------------------------------------
-- Distinct correction coordinates.
-- Kowitt attacks the permeability/microscopic constitutive weld.
-- Harris attacks unrealistic microscopic/geometric assumptions in the
-- gravitoelectric magnitude estimate.  They are not definitionally identical.
------------------------------------------------------------------------

data CorrectionCoordinate : Set where
  bulkPermeabilityInterpretation : CorrectionCoordinate
  microscopicSuperconductorDynamics : CorrectionCoordinate
  microscopicDistanceOrGeometryAssumption : CorrectionCoordinate
  externalFieldMagnitudeScaling : CorrectionCoordinate

record CorrectionReceipt : Set where
  constructor correction-receipt
  field
    correction : CorrectionCoordinate
    critic year sourceReference claimScope : String

kowittPermeabilityReceipt : CorrectionReceipt
kowittPermeabilityReceipt = correction-receipt
  bulkPermeabilityInterpretation
  "Mark Kowitt"
  "1994"
  "Physical Review B 49, 704-708"
  "Li/Torr gravitomagnetic magnitude is grossly overestimated because bulk superconducting permeability is misinterpreted"

kowittMicroscopicReceipt : CorrectionReceipt
kowittMicroscopicReceipt = correction-receipt
  microscopicSuperconductorDynamics
  "Mark Kowitt"
  "1994"
  "Physical Review B 49, 704-708"
  "microscopic dynamics invoked to support the enhancement are criticized as flawed"

harrisGeometryReceipt : CorrectionReceipt
harrisGeometryReceipt = correction-receipt
  microscopicDistanceOrGeometryAssumption
  "Edward G. Harris"
  "1999"
  "Foundations of Physics Letters 12, 201-208"
  "recalculation of Torr/Li gravitoelectric coupling finds unrealistic assumptions and a many-orders-of-magnitude overestimate"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record MagnitudeTriangleBoundary : Set where
  constructor magnitude-triangle-boundary
  field
    historicalEquationImpliesCorrectMagnitude : Bool
    historicalEquationImpliesCorrectMagnitudeIsFalse :
      historicalEquationImpliesCorrectMagnitude ≡ false

    kowittAndHarrisAreSameCorrection : Bool
    kowittAndHarrisAreSameCorrectionIsFalse :
      kowittAndHarrisAreSameCorrection ≡ false

    correctedTinyEffectImpliesZeroEffectExactly : Bool
    correctedTinyEffectImpliesZeroEffectExactlyIsFalse :
      correctedTinyEffectImpliesZeroEffectExactly ≡ false

    ordinaryGRBaselineMustShareGeometry : Bool
    ordinaryGRBaselineMustShareGeometryIsTrue :
      ordinaryGRBaselineMustShareGeometry ≡ true

canonicalMagnitudeTriangleBoundary : MagnitudeTriangleBoundary
canonicalMagnitudeTriangleBoundary =
  magnitude-triangle-boundary false refl false refl false refl true refl

------------------------------------------------------------------------
-- BIDI first-open-coordinate router.
------------------------------------------------------------------------

data MagnitudeLeaf : Set where
  sourcePredictionLeaf : MagnitudeLeaf
  constitutiveCorrectionLeaf : MagnitudeLeaf
  microscopicGeometryLeaf : MagnitudeLeaf
  standardGRLeaf : MagnitudeLeaf
  experimentalResidualLeaf : MagnitudeLeaf
  closedMagnitudeTriangle : MagnitudeLeaf

record MagnitudeClosureState : Set where
  constructor magnitude-closure-state
  field
    sourcePredictionOwned : Bool
    constitutiveCorrectionOwned : Bool
    microscopicGeometryOwned : Bool
    standardGROwned : Bool
    experimentalResidualOwned : Bool

firstOpenMagnitudeLeaf : MagnitudeClosureState → MagnitudeLeaf
firstOpenMagnitudeLeaf (magnitude-closure-state false c g s e) = sourcePredictionLeaf
firstOpenMagnitudeLeaf (magnitude-closure-state true false g s e) = constitutiveCorrectionLeaf
firstOpenMagnitudeLeaf (magnitude-closure-state true true false s e) = microscopicGeometryLeaf
firstOpenMagnitudeLeaf (magnitude-closure-state true true true false e) = standardGRLeaf
firstOpenMagnitudeLeaf (magnitude-closure-state true true true true false) = experimentalResidualLeaf
firstOpenMagnitudeLeaf (magnitude-closure-state true true true true true) = closedMagnitudeTriangle

currentLiteratureFrontier : MagnitudeClosureState
currentLiteratureFrontier = magnitude-closure-state true true true false false

currentFirstOpenMagnitudeLeaf : MagnitudeLeaf
currentFirstOpenMagnitudeLeaf = firstOpenMagnitudeLeaf currentLiteratureFrontier
