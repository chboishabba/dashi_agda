module DASHI.Physics.Closure.G2DiscreteCurvatureCarrier where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftFiniteGaugeSymmetry as SFGS
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
import DASHI.Physics.ShiftSpatialLaplacian as SSL

------------------------------------------------------------------------
-- G2 discrete curvature carrier shape.
--
-- This module does not construct curvature for the current shift gauge field.
-- It names the smallest carrier shape needed before the Maxwell field-strength
-- bridge can be closed.

record DiscreteCurvatureCarrier (ConnectionCarrier : Set) : Set₁ where
  field
    CurvatureCarrier :
      Set

    curvatureFromConnection :
      ConnectionCarrier →
      CurvatureCarrier

    FieldStrengthCarrier :
      Set

    curvatureToFieldStrength :
      CurvatureCarrier →
      FieldStrengthCarrier

    carrierBoundary :
      List String

curvatureToFieldStrengthFromShiftGaugeConnection :
  (carrier : DiscreteCurvatureCarrier SFGC.GaugeField) →
  SFGC.GaugeField →
  DiscreteCurvatureCarrier.FieldStrengthCarrier carrier
curvatureToFieldStrengthFromShiftGaugeConnection carrier connection =
  DiscreteCurvatureCarrier.curvatureToFieldStrength carrier
    (DiscreteCurvatureCarrier.curvatureFromConnection carrier connection)

------------------------------------------------------------------------
-- Prime-lattice 2-cell layer needed before the carrier can be inhabited.

record PrimeLattice2CellLayer (ConnectionCarrier : Set) : Set₁ where
  field
    PrimeLattice0Cell :
      Set

    PrimeLattice1Cell :
      Set

    PrimeLattice2Cell :
      Set

    Plaquette :
      Set

    plaquette2Cell :
      Plaquette →
      PrimeLattice2Cell

    plaquetteBoundary1Cells :
      Plaquette →
      List PrimeLattice1Cell

    Discrete0Form :
      Set

    Discrete1Form :
      Set

    Discrete2Form :
      Set

    connectionTo1Form :
      ConnectionCarrier →
      Discrete1Form

    discreteExteriorDerivative0 :
      Discrete0Form →
      Discrete1Form

    discreteExteriorDerivative1 :
      Discrete1Form →
      Discrete2Form

    zeroDiscrete2Form :
      Discrete2Form

    exteriorDerivativeSquaredZero :
      (form : Discrete0Form) →
      discreteExteriorDerivative1
        (discreteExteriorDerivative0 form)
      ≡
      zeroDiscrete2Form

    FieldStrengthCarrier :
      Set

    fieldStrengthFrom2Form :
      Discrete2Form →
      FieldStrengthCarrier

    layerBoundary :
      List String

discreteCurvatureCarrierFromPrimeLattice2CellLayer :
  {ConnectionCarrier : Set} →
  PrimeLattice2CellLayer ConnectionCarrier →
  DiscreteCurvatureCarrier ConnectionCarrier
discreteCurvatureCarrierFromPrimeLattice2CellLayer layer =
  record
    { CurvatureCarrier =
        PrimeLattice2CellLayer.Discrete2Form layer
    ; curvatureFromConnection =
        λ connection →
          PrimeLattice2CellLayer.discreteExteriorDerivative1 layer
            (PrimeLattice2CellLayer.connectionTo1Form layer connection)
    ; FieldStrengthCarrier =
        PrimeLattice2CellLayer.FieldStrengthCarrier layer
    ; curvatureToFieldStrength =
        PrimeLattice2CellLayer.fieldStrengthFrom2Form layer
    ; carrierBoundary =
        PrimeLattice2CellLayer.layerBoundary layer
    }

data G2PrimeLattice2CellLayerStatus : Set where
  primeLattice2CellLayerObligationOnlyNoPromotion :
    G2PrimeLattice2CellLayerStatus

data G2PrimeLattice2CellMissingBaseType : Set where
  missingPrimeLattice0Cell :
    G2PrimeLattice2CellMissingBaseType

  missingPrimeLattice1Cell :
    G2PrimeLattice2CellMissingBaseType

  missingPrimeLattice2Cell :
    G2PrimeLattice2CellMissingBaseType

  missingPrimeLatticePlaquette :
    G2PrimeLattice2CellMissingBaseType

  missingPlaquetteBoundary1Cells :
    G2PrimeLattice2CellMissingBaseType

  missingDiscrete0Form :
    G2PrimeLattice2CellMissingBaseType

  missingDiscrete1Form :
    G2PrimeLattice2CellMissingBaseType

  missingDiscrete2Form :
    G2PrimeLattice2CellMissingBaseType

  missingShiftGaugeConnectionTo1Form :
    G2PrimeLattice2CellMissingBaseType

  missingDiscreteExteriorDerivative0 :
    G2PrimeLattice2CellMissingBaseType

  missingDiscreteExteriorDerivative1 :
    G2PrimeLattice2CellMissingBaseType

  missingZeroDiscrete2Form :
    G2PrimeLattice2CellMissingBaseType

  missingExteriorDerivativeSquaredZero :
    G2PrimeLattice2CellMissingBaseType

  missingFieldStrengthFrom2Form :
    G2PrimeLattice2CellMissingBaseType

data G2PrimeLatticeCochainLawStatus : Set where
  cochainLawObligationOnlyNoPromotion :
    G2PrimeLatticeCochainLawStatus

data G2PrimeLatticeCochainMissingLaw : Set where
  missingVec15UpdateCommutes :
    G2PrimeLatticeCochainMissingLaw

  missingSignedEndpointIncidenceSummation :
    G2PrimeLatticeCochainMissingLaw

  missingOrientedPrimeLattice1CellEndpoints :
    G2PrimeLatticeCochainMissingLaw

  missingOrientedEdgeEndpoint :
    G2PrimeLatticeCochainMissingLaw

  missingOrientedSignedPlaquetteBoundary :
    G2PrimeLatticeCochainMissingLaw

  missingCorrectedSignedSquareBoundary :
    G2PrimeLatticeCochainMissingLaw

  missingBoundaryOfBoundaryZero :
    G2PrimeLatticeCochainMissingLaw

  missingFiniteIncidenceSummation :
    G2PrimeLatticeCochainMissingLaw

  missingD0EndpointCompatibility :
    G2PrimeLatticeCochainMissingLaw

  missingD1PlaquetteBoundaryCompatibility :
    G2PrimeLatticeCochainMissingLaw

  missingPhase4AdditionAssociativity :
    G2PrimeLatticeCochainMissingLaw

  missingPhase4AdditionCommutativity :
    G2PrimeLatticeCochainMissingLaw

  missingPhase4RightIdentity :
    G2PrimeLatticeCochainMissingLaw

  missingPhase4InverseCancellation :
    G2PrimeLatticeCochainMissingLaw

  missingPhase4AbelianGroupLawPackage :
    G2PrimeLatticeCochainMissingLaw

  missingPhase4CochainNormalizationSolver :
    G2PrimeLatticeCochainMissingLaw

data BoundarySign : Set where
  positiveBoundary :
    BoundarySign

  negativeBoundary :
    BoundarySign

record SignedBoundaryEdge (Edge : Set) : Set where
  constructor signedBoundaryEdge
  field
    sign :
      BoundarySign

    edge :
      Edge

flipBoundarySign :
  BoundarySign →
  BoundarySign
flipBoundarySign positiveBoundary =
  negativeBoundary
flipBoundarySign negativeBoundary =
  positiveBoundary

flipBoundarySign-involutive :
  (sign : BoundarySign) →
  flipBoundarySign (flipBoundarySign sign) ≡ sign
flipBoundarySign-involutive positiveBoundary =
  refl
flipBoundarySign-involutive negativeBoundary =
  refl

reverseSignedBoundaryEdge :
  {Edge : Set} →
  SignedBoundaryEdge Edge →
  SignedBoundaryEdge Edge
reverseSignedBoundaryEdge (signedBoundaryEdge sign edge) =
  signedBoundaryEdge (flipBoundarySign sign) edge

reverseSignedBoundaryEdge-involutive :
  {Edge : Set} →
  (edge : SignedBoundaryEdge Edge) →
  reverseSignedBoundaryEdge (reverseSignedBoundaryEdge edge) ≡ edge
reverseSignedBoundaryEdge-involutive (signedBoundaryEdge positiveBoundary edge) =
  refl
reverseSignedBoundaryEdge-involutive (signedBoundaryEdge negativeBoundary edge) =
  refl

record AbelianCoefficientLawSurface (Coefficient : Set) : Set₁ where
  field
    zeroCoeff :
      Coefficient

    addCoeff :
      Coefficient →
      Coefficient →
      Coefficient

    invCoeff :
      Coefficient →
      Coefficient

    addAssoc :
      (a b c : Coefficient) →
      addCoeff (addCoeff a b) c
        ≡
      addCoeff a (addCoeff b c)

    addComm :
      (a b : Coefficient) →
      addCoeff a b
        ≡
      addCoeff b a

    addIdentityʳ :
      (a : Coefficient) →
      addCoeff a zeroCoeff
        ≡
      a

    addInverseʳ :
      (a : Coefficient) →
      addCoeff a (invCoeff a)
        ≡
      zeroCoeff

phase4-addAssoc :
  (a b c : SPTI4.Phase4) →
  SFGS.phaseAdd4 (SFGS.phaseAdd4 a b) c
    ≡
  SFGS.phaseAdd4 a (SFGS.phaseAdd4 b c)
phase4-addAssoc SPTI4.φ0 SPTI4.φ0 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ0 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ0 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ0 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ1 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ1 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ1 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ1 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ2 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ2 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ2 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ2 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ3 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ3 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ3 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ0 SPTI4.φ3 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ0 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ0 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ0 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ0 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ1 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ1 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ1 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ1 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ2 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ2 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ2 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ2 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ3 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ3 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ3 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ1 SPTI4.φ3 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ0 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ0 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ0 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ0 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ1 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ1 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ1 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ1 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ2 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ2 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ2 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ2 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ3 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ3 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ3 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ2 SPTI4.φ3 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ0 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ0 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ0 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ0 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ1 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ1 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ1 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ1 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ2 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ2 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ2 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ2 SPTI4.φ3 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ3 SPTI4.φ0 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ3 SPTI4.φ1 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ3 SPTI4.φ2 = refl
phase4-addAssoc SPTI4.φ3 SPTI4.φ3 SPTI4.φ3 = refl

phase4-addComm :
  (a b : SPTI4.Phase4) →
  SFGS.phaseAdd4 a b ≡ SFGS.phaseAdd4 b a
phase4-addComm SPTI4.φ0 SPTI4.φ0 = refl
phase4-addComm SPTI4.φ0 SPTI4.φ1 = refl
phase4-addComm SPTI4.φ0 SPTI4.φ2 = refl
phase4-addComm SPTI4.φ0 SPTI4.φ3 = refl
phase4-addComm SPTI4.φ1 SPTI4.φ0 = refl
phase4-addComm SPTI4.φ1 SPTI4.φ1 = refl
phase4-addComm SPTI4.φ1 SPTI4.φ2 = refl
phase4-addComm SPTI4.φ1 SPTI4.φ3 = refl
phase4-addComm SPTI4.φ2 SPTI4.φ0 = refl
phase4-addComm SPTI4.φ2 SPTI4.φ1 = refl
phase4-addComm SPTI4.φ2 SPTI4.φ2 = refl
phase4-addComm SPTI4.φ2 SPTI4.φ3 = refl
phase4-addComm SPTI4.φ3 SPTI4.φ0 = refl
phase4-addComm SPTI4.φ3 SPTI4.φ1 = refl
phase4-addComm SPTI4.φ3 SPTI4.φ2 = refl
phase4-addComm SPTI4.φ3 SPTI4.φ3 = refl

phase4-addIdentityʳ :
  (a : SPTI4.Phase4) →
  SFGS.phaseAdd4 a SPTI4.φ0 ≡ a
phase4-addIdentityʳ SPTI4.φ0 = refl
phase4-addIdentityʳ SPTI4.φ1 = refl
phase4-addIdentityʳ SPTI4.φ2 = refl
phase4-addIdentityʳ SPTI4.φ3 = refl

phase4-addInverseʳ :
  (a : SPTI4.Phase4) →
  SFGS.phaseAdd4 a (SFGS.phaseInv4 a) ≡ SPTI4.φ0
phase4-addInverseʳ SPTI4.φ0 = refl
phase4-addInverseʳ SPTI4.φ1 = refl
phase4-addInverseʳ SPTI4.φ2 = refl
phase4-addInverseʳ SPTI4.φ3 = refl

phase4AbelianCoefficientLawSurface :
  AbelianCoefficientLawSurface SPTI4.Phase4
phase4AbelianCoefficientLawSurface =
  record
    { zeroCoeff = SPTI4.φ0
    ; addCoeff = SFGS.phaseAdd4
    ; invCoeff = SFGS.phaseInv4
    ; addAssoc = phase4-addAssoc
    ; addComm = phase4-addComm
    ; addIdentityʳ = phase4-addIdentityʳ
    ; addInverseʳ = phase4-addInverseʳ
    }

signedCoefficient :
  {Coefficient : Set} →
  AbelianCoefficientLawSurface Coefficient →
  BoundarySign →
  Coefficient →
  Coefficient
signedCoefficient laws positiveBoundary coefficient =
  coefficient
signedCoefficient laws negativeBoundary coefficient =
  AbelianCoefficientLawSurface.invCoeff laws coefficient

signedCoefficient-positive :
  {Coefficient : Set} →
  (laws : AbelianCoefficientLawSurface Coefficient) →
  (coefficient : Coefficient) →
  signedCoefficient laws positiveBoundary coefficient ≡ coefficient
signedCoefficient-positive laws coefficient =
  refl

signedCoefficient-negative :
  {Coefficient : Set} →
  (laws : AbelianCoefficientLawSurface Coefficient) →
  (coefficient : Coefficient) →
  signedCoefficient laws negativeBoundary coefficient
    ≡
  AbelianCoefficientLawSurface.invCoeff laws coefficient
signedCoefficient-negative laws coefficient =
  refl

signedBoundarySum :
  {Cell Coefficient : Set} →
  AbelianCoefficientLawSurface Coefficient →
  (Cell → Coefficient) →
  List (SignedBoundaryEdge Cell) →
  Coefficient
signedBoundarySum laws evaluate [] =
  AbelianCoefficientLawSurface.zeroCoeff laws
signedBoundarySum laws evaluate (signedBoundaryEdge sign cell ∷ boundary) =
  AbelianCoefficientLawSurface.addCoeff laws
    (signedCoefficient laws sign (evaluate cell))
    (signedBoundarySum laws evaluate boundary)

signedBoundarySum-empty :
  {Cell Coefficient : Set} →
  (laws : AbelianCoefficientLawSurface Coefficient) →
  (evaluate : Cell → Coefficient) →
  signedBoundarySum laws evaluate [] ≡
  AbelianCoefficientLawSurface.zeroCoeff laws
signedBoundarySum-empty laws evaluate =
  refl

signedBoundarySum-positive-singleton :
  {Cell Coefficient : Set} →
  (laws : AbelianCoefficientLawSurface Coefficient) →
  (evaluate : Cell → Coefficient) →
  (cell : Cell) →
  signedBoundarySum laws evaluate
    (signedBoundaryEdge positiveBoundary cell ∷ [])
    ≡
  AbelianCoefficientLawSurface.addCoeff laws
    (evaluate cell)
    (AbelianCoefficientLawSurface.zeroCoeff laws)
signedBoundarySum-positive-singleton laws evaluate cell =
  refl

signedBoundarySum-negative-singleton :
  {Cell Coefficient : Set} →
  (laws : AbelianCoefficientLawSurface Coefficient) →
  (evaluate : Cell → Coefficient) →
  (cell : Cell) →
  signedBoundarySum laws evaluate
    (signedBoundaryEdge negativeBoundary cell ∷ [])
    ≡
  AbelianCoefficientLawSurface.addCoeff laws
    (AbelianCoefficientLawSurface.invCoeff laws (evaluate cell))
    (AbelianCoefficientLawSurface.zeroCoeff laws)
signedBoundarySum-negative-singleton laws evaluate cell =
  refl

correctedSquareBoundary :
  {Edge : Set} →
  Edge →
  Edge →
  Edge →
  Edge →
  List (SignedBoundaryEdge Edge)
correctedSquareBoundary bottom right top left =
  signedBoundaryEdge positiveBoundary bottom
  ∷ signedBoundaryEdge positiveBoundary right
  ∷ signedBoundaryEdge negativeBoundary top
  ∷ signedBoundaryEdge negativeBoundary left
  ∷ []

correctedSquareBoundary-shape :
  {Edge : Set} →
  (bottom right top left : Edge) →
  correctedSquareBoundary bottom right top left
    ≡
  signedBoundaryEdge positiveBoundary bottom
  ∷ signedBoundaryEdge positiveBoundary right
  ∷ signedBoundaryEdge negativeBoundary top
  ∷ signedBoundaryEdge negativeBoundary left
  ∷ []
correctedSquareBoundary-shape bottom right top left =
  refl

correctedSquareBoundarySignedSum-shape :
  {Edge Coefficient : Set} →
  (laws : AbelianCoefficientLawSurface Coefficient) →
  (evaluate : Edge → Coefficient) →
  (bottom right top left : Edge) →
  signedBoundarySum laws evaluate
    (correctedSquareBoundary bottom right top left)
    ≡
  AbelianCoefficientLawSurface.addCoeff laws
    (evaluate bottom)
    (AbelianCoefficientLawSurface.addCoeff laws
      (evaluate right)
      (AbelianCoefficientLawSurface.addCoeff laws
        (AbelianCoefficientLawSurface.invCoeff laws (evaluate top))
        (AbelianCoefficientLawSurface.addCoeff laws
          (AbelianCoefficientLawSurface.invCoeff laws (evaluate left))
          (AbelianCoefficientLawSurface.zeroCoeff laws))))
correctedSquareBoundarySignedSum-shape laws evaluate bottom right top left =
  refl

correctedOrientedEdgeBoundary :
  {Vertex : Set} →
  Vertex →
  Vertex →
  List (SignedBoundaryEdge Vertex)
correctedOrientedEdgeBoundary source target =
  signedBoundaryEdge negativeBoundary source
  ∷ signedBoundaryEdge positiveBoundary target
  ∷ []

correctedOrientedEdgeBoundary-shape :
  {Vertex : Set} →
  (source target : Vertex) →
  correctedOrientedEdgeBoundary source target
    ≡
  signedBoundaryEdge negativeBoundary source
  ∷ signedBoundaryEdge positiveBoundary target
  ∷ []
correctedOrientedEdgeBoundary-shape source target =
  refl

record SignedBoundaryIncidenceSummationSurface
  (Vertex Edge Face Coefficient : Set) : Set₁ where
  field
    coefficientLaws :
      AbelianCoefficientLawSurface Coefficient

    edgeSource :
      Edge →
      Vertex

    edgeTarget :
      Edge →
      Vertex

    faceBoundary :
      Face →
      List (SignedBoundaryEdge Edge)

    edgeBoundary :
      Edge →
      List (SignedBoundaryEdge Vertex)

    edgeBoundary-corrected :
      (edge : Edge) →
      edgeBoundary edge
        ≡
      correctedOrientedEdgeBoundary (edgeSource edge) (edgeTarget edge)

    Vertex0Cochain :
      Set

    vertexEvaluate :
      Vertex0Cochain →
      Vertex →
      Coefficient

    boundary0Sum :
      Vertex0Cochain →
      Edge →
      Coefficient

    boundary0Sum-correct :
      (cochain : Vertex0Cochain) →
      (edge : Edge) →
      boundary0Sum cochain edge
        ≡
      signedBoundarySum coefficientLaws
        (vertexEvaluate cochain)
        (edgeBoundary edge)

    boundaryOfBoundaryVertexSum :
      Vertex0Cochain →
      Face →
      Coefficient

    boundaryOfBoundaryZero :
      (cochain : Vertex0Cochain) →
      (face : Face) →
      boundaryOfBoundaryVertexSum cochain face
        ≡
      AbelianCoefficientLawSurface.zeroCoeff coefficientLaws

record CorrectedSquareBoundaryCochainSurface
  (Vertex Edge Square Coefficient : Set) : Set₁ where
  field
    coefficientLaws :
      AbelianCoefficientLawSurface Coefficient

    edgeSource :
      Edge →
      Vertex

    edgeTarget :
      Edge →
      Vertex

    squareSW :
      Square →
      Vertex

    squareSE :
      Square →
      Vertex

    squareNE :
      Square →
      Vertex

    squareNW :
      Square →
      Vertex

    squareBottom :
      Square →
      Edge

    squareRight :
      Square →
      Edge

    squareTop :
      Square →
      Edge

    squareLeft :
      Square →
      Edge

    squareBottomEndpoints :
      (s : Square) →
      edgeSource (squareBottom s) ≡ squareSW s

    squareBottomTarget :
      (s : Square) →
      edgeTarget (squareBottom s) ≡ squareSE s

    squareRightEndpoints :
      (s : Square) →
      edgeSource (squareRight s) ≡ squareSE s

    squareRightTarget :
      (s : Square) →
      edgeTarget (squareRight s) ≡ squareNE s

    squareTopEndpoints :
      (s : Square) →
      edgeSource (squareTop s) ≡ squareNW s

    squareTopTarget :
      (s : Square) →
      edgeTarget (squareTop s) ≡ squareNE s

    squareLeftEndpoints :
      (s : Square) →
      edgeSource (squareLeft s) ≡ squareSW s

    squareLeftTarget :
      (s : Square) →
      edgeTarget (squareLeft s) ≡ squareNW s

    signedSquareBoundary :
      Square →
      List (SignedBoundaryEdge Edge)

    signedSquareBoundary-corrected :
      (s : Square) →
      signedSquareBoundary s
        ≡
      signedBoundaryEdge positiveBoundary (squareBottom s)
        ∷ signedBoundaryEdge positiveBoundary (squareRight s)
        ∷ signedBoundaryEdge negativeBoundary (squareTop s)
        ∷ signedBoundaryEdge negativeBoundary (squareLeft s)
        ∷ []

    Discrete0Form :
      Set

    Discrete1Form :
      Set

    Discrete2Form :
      Set

    evaluate0 :
      Discrete0Form →
      Vertex →
      Coefficient

    evaluate1 :
      Discrete1Form →
      Edge →
      Coefficient

    evaluate2 :
      Discrete2Form →
      Square →
      Coefficient

    δ₀ :
      Discrete0Form →
      Discrete1Form

    δ₁ :
      Discrete1Form →
      Discrete2Form

    δ₀-endpoint-law :
      (f : Discrete0Form) →
      (e : Edge) →
      evaluate1 (δ₀ f) e
        ≡
      AbelianCoefficientLawSurface.addCoeff coefficientLaws
        (evaluate0 f (edgeTarget e))
        (AbelianCoefficientLawSurface.invCoeff coefficientLaws
          (evaluate0 f (edgeSource e)))

    δ₁-corrected-square-boundary-law :
      (a : Discrete1Form) →
      (s : Square) →
      evaluate2 (δ₁ a) s
        ≡
      AbelianCoefficientLawSurface.addCoeff coefficientLaws
        (AbelianCoefficientLawSurface.addCoeff coefficientLaws
          (AbelianCoefficientLawSurface.addCoeff coefficientLaws
            (evaluate1 a (squareBottom s))
            (evaluate1 a (squareRight s)))
          (AbelianCoefficientLawSurface.invCoeff coefficientLaws
            (evaluate1 a (squareTop s))))
        (AbelianCoefficientLawSurface.invCoeff coefficientLaws
          (evaluate1 a (squareLeft s)))

    corrected-square-δ₁∘δ₀≡0 :
      (f : Discrete0Form) →
      (s : Square) →
      evaluate2 (δ₁ (δ₀ f)) s
        ≡
      AbelianCoefficientLawSurface.zeroCoeff coefficientLaws

correctedSquareBoundaryFromSurface :
  {Vertex Edge Square Coefficient : Set} →
  (surface : CorrectedSquareBoundaryCochainSurface
    Vertex Edge Square Coefficient) →
  (s : Square) →
  CorrectedSquareBoundaryCochainSurface.signedSquareBoundary surface s
    ≡
  correctedSquareBoundary
    (CorrectedSquareBoundaryCochainSurface.squareBottom surface s)
    (CorrectedSquareBoundaryCochainSurface.squareRight surface s)
    (CorrectedSquareBoundaryCochainSurface.squareTop surface s)
    (CorrectedSquareBoundaryCochainSurface.squareLeft surface s)
correctedSquareBoundaryFromSurface surface s =
  CorrectedSquareBoundaryCochainSurface.signedSquareBoundary-corrected
    surface
    s

correctedSquareBoundarySurfaceSignedSum-shape :
  {Vertex Edge Square Coefficient : Set} →
  (surface : CorrectedSquareBoundaryCochainSurface
    Vertex Edge Square Coefficient) →
  (evaluate : Edge → Coefficient) →
  (s : Square) →
  signedBoundarySum
    (CorrectedSquareBoundaryCochainSurface.coefficientLaws surface)
    evaluate
    (CorrectedSquareBoundaryCochainSurface.signedSquareBoundary surface s)
    ≡
  AbelianCoefficientLawSurface.addCoeff
    (CorrectedSquareBoundaryCochainSurface.coefficientLaws surface)
    (evaluate
      (CorrectedSquareBoundaryCochainSurface.squareBottom surface s))
    (AbelianCoefficientLawSurface.addCoeff
      (CorrectedSquareBoundaryCochainSurface.coefficientLaws surface)
      (evaluate
        (CorrectedSquareBoundaryCochainSurface.squareRight surface s))
      (AbelianCoefficientLawSurface.addCoeff
        (CorrectedSquareBoundaryCochainSurface.coefficientLaws surface)
        (AbelianCoefficientLawSurface.invCoeff
          (CorrectedSquareBoundaryCochainSurface.coefficientLaws surface)
          (evaluate
            (CorrectedSquareBoundaryCochainSurface.squareTop surface s)))
        (AbelianCoefficientLawSurface.addCoeff
          (CorrectedSquareBoundaryCochainSurface.coefficientLaws surface)
          (AbelianCoefficientLawSurface.invCoeff
            (CorrectedSquareBoundaryCochainSurface.coefficientLaws surface)
            (evaluate
              (CorrectedSquareBoundaryCochainSurface.squareLeft surface s)))
          (AbelianCoefficientLawSurface.zeroCoeff
            (CorrectedSquareBoundaryCochainSurface.coefficientLaws
              surface)))))
correctedSquareBoundarySurfaceSignedSum-shape surface evaluate s
  rewrite CorrectedSquareBoundaryCochainSurface.signedSquareBoundary-corrected
    surface
    s =
  refl

record G2PrimeLatticeCochainLawObligation : Set₁ where
  field
    status :
      G2PrimeLatticeCochainLawStatus

    candidateLayerName :
      String

    inspectedCoefficientCarrierName :
      String

    inspectedZeroName :
      String

    inspectedAdditionName :
      String

    inspectedInverseName :
      String

    inspectedVec15UpdateName :
      String

    inspectedVec15UpdateCommutesName :
      String

    candidateD0Shape :
      String

    candidateD1Shape :
      String

    correctedSquareBoundaryShape :
      String

    correctedSquareBoundarySurfaceName :
      String

    missingBaseLaws :
      List G2PrimeLatticeCochainMissingLaw

    requiredSolverOrBaseLawNames :
      List String

    rejectedShortcut :
      String

    noPromotionBoundary :
      List String

canonicalSFGCCochainLawObligation :
  G2PrimeLatticeCochainLawObligation
canonicalSFGCCochainLawObligation =
  record
    { status =
        cochainLawObligationOnlyNoPromotion
    ; candidateLayerName =
        "PrimeLattice2CellLayer SFGC.GaugeField"
    ; inspectedCoefficientCarrierName =
        "Phase4"
    ; inspectedZeroName =
        "φ0"
    ; inspectedAdditionName =
        "SFGS.phaseAdd4"
    ; inspectedInverseName =
        "SFGS.phaseInv4"
    ; inspectedVec15UpdateName =
        "Ontology.GodelLattice.updateVec15"
    ; inspectedVec15UpdateCommutesName =
        "Ontology.GodelLattice.updateVec15-commutes"
    ; candidateD0Shape =
        "d0 f edge = f target(edge) - f source(edge)"
    ; candidateD1Shape =
        "d1 a plaquette = signed sum of a over oriented plaquette boundary"
    ; correctedSquareBoundaryShape =
        "δ1 a square = a(bottom) + a(right) - a(top) - a(left), with top/left negated because their canonical edge orientations oppose the square traversal"
    ; correctedSquareBoundarySurfaceName =
        "CorrectedSquareBoundaryCochainSurface.corrected-square-δ₁∘δ₀≡0"
    ; missingBaseLaws =
        missingSignedEndpointIncidenceSummation
        ∷ missingOrientedPrimeLattice1CellEndpoints
        ∷ missingOrientedEdgeEndpoint
        ∷ missingOrientedSignedPlaquetteBoundary
        ∷ missingCorrectedSignedSquareBoundary
        ∷ missingBoundaryOfBoundaryZero
        ∷ missingFiniteIncidenceSummation
        ∷ missingD0EndpointCompatibility
        ∷ missingD1PlaquetteBoundaryCompatibility
        ∷ missingPhase4CochainNormalizationSolver
        ∷ []
    ; requiredSolverOrBaseLawNames =
        "Vec15.updateCommutes : discharged for updateVec15 as updateVec15-commutes; still no prime-lattice cochain geometry follows from it"
        ∷ "SignedBoundaryIncidenceSummationSurface Vertex Edge Face Phase4"
        ∷ "edgeSource : PrimeLattice1Cell -> PrimeLattice0Cell"
        ∷ "edgeTarget : PrimeLattice1Cell -> PrimeLattice0Cell"
        ∷ "edgeBoundary : PrimeLattice1Cell -> [-source, +target]"
        ∷ "oriented edge endpoint law for square bottom/right/top/left"
        ∷ "signedPlaquetteBoundary : Plaquette -> List SignedPrimeLattice1Cell"
        ∷ "signedSquareBoundary : Square -> +bottom, +right, -top, -left"
        ∷ "boundaryOfBoundaryZero : signed endpoint sum of signedPlaquetteBoundary p cancels"
        ∷ "finiteIncidenceSum : finite signed sums over incident cells normalize"
        ∷ "Phase4 abelian coefficient laws are now packaged locally as phase4AbelianCoefficientLawSurface"
        ∷ "phase4-cochain-normalizer : solver for finite Phase4 signed cochain sums"
        ∷ []
    ; rejectedShortcut =
        "constant-zero d1 would make d1 (d0 f) definitional, but would not encode plaquette curvature"
    ; noPromotionBoundary =
        "Existing Phase4 support now gives a local abelian coefficient package, but not a cochain-sum normalizer"
        ∷ "This module defines generic signedBoundarySum and a typed SignedBoundaryIncidenceSummationSurface, but it does not instantiate them for SFGC.GaugeField"
        ∷ "Existing shift gauge support gives a three-point link assignment, not oriented prime-lattice cells"
        ∷ "Only degenerate right-edge return boundaries are available: +edge,-edge and a four-term 1D two-step return; no nondegenerate signed plaquette boundary or boundary-of-boundary-zero law is available"
        ∷ "Therefore no concrete d0/d1/exteriorDerivativeSquaredZero proof is constructed here"
        ∷ []
    }

record G2PrimeLattice2CellLayerObligation
  (ConnectionCarrier : Set) : Set₁ where
  field
    status :
      G2PrimeLattice2CellLayerStatus

    requiredLayerName :
      String

    requiredCarrierBuilderName :
      String

    requiredBaseTypeNames :
      List String

    missingBaseTypes :
      List G2PrimeLattice2CellMissingBaseType

    cochainLawObligation :
      G2PrimeLatticeCochainLawObligation

    inspectedConnectionCarrier :
      Set

    inspectedConnectionCarrierName :
      String

    blockedConstructorName :
      String

    noPromotionBoundary :
      List String

canonicalSFGCPrimeLattice2CellLayerObligation :
  G2PrimeLattice2CellLayerObligation SFGC.GaugeField
canonicalSFGCPrimeLattice2CellLayerObligation =
  record
    { status =
        primeLattice2CellLayerObligationOnlyNoPromotion
    ; requiredLayerName =
        "PrimeLattice2CellLayer SFGC.GaugeField"
    ; requiredCarrierBuilderName =
        "discreteCurvatureCarrierFromPrimeLattice2CellLayer"
    ; requiredBaseTypeNames =
        "PrimeLattice0Cell"
        ∷ "PrimeLattice1Cell"
        ∷ "PrimeLattice2Cell"
        ∷ "Plaquette"
        ∷ "plaquette2Cell"
        ∷ "plaquetteBoundary1Cells"
        ∷ "Discrete0Form"
        ∷ "Discrete1Form"
        ∷ "Discrete2Form"
        ∷ "connectionTo1Form"
        ∷ "discreteExteriorDerivative0"
        ∷ "discreteExteriorDerivative1"
        ∷ "zeroDiscrete2Form"
        ∷ "exteriorDerivativeSquaredZero"
        ∷ "FieldStrengthCarrier"
        ∷ "fieldStrengthFrom2Form"
        ∷ []
    ; missingBaseTypes =
        missingPrimeLattice0Cell
        ∷ missingPrimeLattice1Cell
        ∷ missingPrimeLattice2Cell
        ∷ missingPrimeLatticePlaquette
        ∷ missingPlaquetteBoundary1Cells
        ∷ missingDiscrete0Form
        ∷ missingDiscrete1Form
        ∷ missingDiscrete2Form
        ∷ missingShiftGaugeConnectionTo1Form
        ∷ missingDiscreteExteriorDerivative0
        ∷ missingDiscreteExteriorDerivative1
        ∷ missingZeroDiscrete2Form
        ∷ missingExteriorDerivativeSquaredZero
        ∷ missingFieldStrengthFrom2Form
        ∷ []
    ; cochainLawObligation =
        canonicalSFGCCochainLawObligation
    ; inspectedConnectionCarrier =
        SFGC.GaugeField
    ; inspectedConnectionCarrierName =
        "SFGC.GaugeField"
    ; blockedConstructorName =
        "DiscreteCurvatureCarrier SFGC.GaugeField"
    ; noPromotionBoundary =
        "The current shift gauge field is a three-point Phase4 link assignment; a local right-edge 1-form bridge exists, but no full 2-cell layer exists"
        ∷ "PrimeLattice0Cell/1Cell can be read locally as ShiftPressurePoint/right-edge anchors, but no PrimeLattice2Cell base type is defined in the inspected G2 curvature lane"
        ∷ "No plaquette carrier or plaquette boundary operator into prime-lattice 1-cells is defined"
        ∷ "Right-edge endpoint maps, a degenerate return plaquette normalizer, and a four-term 1D two-step return normalizer are available, but no nondegenerate signed plaquette boundary or boundary-of-boundary-zero incidence law is defined"
        ∷ "A Phase4 abelian coefficient law package and return-boundary normalizer are available, but no general finite cochain-sum normalizer is defined"
        ∷ "A local right-edge return δ0/δ1 zero law is available, but no nondegenerate discrete exterior derivative pair or d^2=0 law is available for the lane"
        ∷ "A local connectionToPrimeLattice1Form exists for right edges, but no selected PrimeLattice2CellLayer consumes it"
        ∷ "Therefore no DiscreteCurvatureCarrier SFGC.GaugeField is constructed here"
        ∷ []
    }

------------------------------------------------------------------------
-- Upstream data required before the current SFGC.GaugeField can honestly
-- become a curvature carrier.

record ShiftGaugeCurvatureData : Set₁ where
  field
    ConnectionCarrier :
      Set

    VacuumConnection :
      ConnectionCarrier

    PlaquetteOrTwoCellCarrier :
      Set

    CurvatureCarrier :
      Set

    flatCurvature :
      CurvatureCarrier

    curvatureFromConnection :
      ConnectionCarrier →
      CurvatureCarrier

    FieldStrengthCarrier :
      Set

    curvatureToFieldStrength :
      CurvatureCarrier →
      FieldStrengthCarrier

    vacuumFlatnessLaw :
      curvatureFromConnection VacuumConnection ≡ flatCurvature

    bianchiLaw :
      CurvatureCarrier →
      Set

    bianchiFromCurvature :
      (curvature : CurvatureCarrier) →
      bianchiLaw curvature

    fieldStrengthBoundary :
      List String

data G2ShiftGaugeCurvatureMissingField : Set where
  missingPrimeLattice2CellLayer :
    G2ShiftGaugeCurvatureMissingField

  missingPlaquetteOrTwoCellCarrier :
    G2ShiftGaugeCurvatureMissingField

  missingDiscreteExteriorDerivative :
    G2ShiftGaugeCurvatureMissingField

  missingExteriorDerivativeSquaredZero :
    G2ShiftGaugeCurvatureMissingField

  missingCurvatureCarrierForSFGCGaugeField :
    G2ShiftGaugeCurvatureMissingField

  missingCurvatureFromSFGCGaugeConnection :
    G2ShiftGaugeCurvatureMissingField

  missingCurvatureToMaxwellFieldStrength :
    G2ShiftGaugeCurvatureMissingField

  missingVacuumFlatnessLaw :
    G2ShiftGaugeCurvatureMissingField

  missingBianchiLaw :
    G2ShiftGaugeCurvatureMissingField

data G2ShiftGaugeCurvatureObstructionStatus : Set where
  blockedBeforeDiscreteCellsNoPromotion :
    G2ShiftGaugeCurvatureObstructionStatus

data G2SFGCGaugeFieldCurvatureAPIGap : Set where
  missingConnectionCarrierForSFGCGaugeField :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingShiftGaugeFieldGaugeConnection :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingGaugeFieldAtProjection :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingPhase4ToU1ComponentSelection :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingConnectionToPrimeLattice1Form :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingGaugeFieldImaginaryComponent :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingGaugeFieldHeckeEigenvalue :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingVacuumImaginaryZeroLaw :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingIndependentTransverseEdgeAPI :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingTransverseEdgeEndpointLaws :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingPlaquetteBumpCommutationAPI :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingPlaquetteBumpCommutationLaws :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingPlaquetteCurvatureLoop :
    G2SFGCGaugeFieldCurvatureAPIGap

SFGCPointLink1Form : Set
SFGCPointLink1Form =
  SPTI.ShiftPressurePoint → SPTI4.Phase4

connectionToPointLink1Form :
  SFGC.GaugeField →
  SFGCPointLink1Form
connectionToPointLink1Form A =
  A

connectionToPointLink1Form-samples :
  (A : SFGC.GaugeField) →
  (s : SPTI.ShiftPressurePoint) →
  connectionToPointLink1Form A s ≡ A s
connectionToPointLink1Form-samples A s =
  refl

vacuumPointLink1FormZero :
  (s : SPTI.ShiftPressurePoint) →
  connectionToPointLink1Form SFGC.vacuumGaugeField s ≡ SPTI4.φ0
vacuumPointLink1FormZero s =
  refl

record SFGCPointLink1FormBridge : Set₁ where
  field
    ConnectionCarrier :
      Set

    Discrete1Form :
      Set

    coefficientLaws :
      AbelianCoefficientLawSurface SPTI4.Phase4

    connectionTo1Form :
      SFGC.GaugeField →
      Discrete1Form

    evaluate1 :
      Discrete1Form →
      SPTI.ShiftPressurePoint →
      SPTI4.Phase4

    connectionTo1Form-samples :
      (A : SFGC.GaugeField) →
      (s : SPTI.ShiftPressurePoint) →
      evaluate1 (connectionTo1Form A) s ≡ A s

    vacuumZeroLaw :
      (s : SPTI.ShiftPressurePoint) →
      evaluate1 (connectionTo1Form SFGC.vacuumGaugeField) s
        ≡
      SPTI4.φ0

    bridgeBoundary :
      List String

canonicalSFGCPointLink1FormBridge :
  SFGCPointLink1FormBridge
canonicalSFGCPointLink1FormBridge =
  record
    { ConnectionCarrier =
        SFGC.GaugeField
    ; Discrete1Form =
        SFGCPointLink1Form
    ; coefficientLaws =
        phase4AbelianCoefficientLawSurface
    ; connectionTo1Form =
        connectionToPointLink1Form
    ; evaluate1 =
        λ form s → form s
    ; connectionTo1Form-samples =
        connectionToPointLink1Form-samples
    ; vacuumZeroLaw =
        vacuumPointLink1FormZero
    ; bridgeBoundary =
        "This is a Phase4-native point-link 1-form bridge over the existing three-point ShiftPressurePoint carrier"
        ∷ "connectionTo1Form is the identity bridge from SFGC.GaugeField to ShiftPressurePoint -> Phase4"
        ∷ "The vacuum-zero law is pointwise definitional because SFGC.vacuumGaugeField is constantly φ0"
        ∷ "This bridge does not select a real/imaginary U(1) component and does not claim a continuous U(1) connection"
        ∷ "This bridge does not provide PrimeLattice0Cell/1Cell/2Cell, plaquettes, δ₁, d²=0, curvature, Bianchi, or Maxwell field strength"
        ∷ []
    }

------------------------------------------------------------------------
-- Honest Phase4 right-edge 1-form surface.
--
-- The existing SFGC field assigns one Phase4 transport value to each shift
-- point.  ShiftSpatialLaplacian already exposes the corresponding
-- right-neighbor orientation, so this is the narrowest real move from the
-- point-link bridge toward a prime-lattice 1-form.  It still stops before any
-- 2-cell or curvature claim.

SFGCShiftRightEdge : Set
SFGCShiftRightEdge =
  SPTI.ShiftPressurePoint

sfgcShiftRightEdgeSource :
  SFGCShiftRightEdge →
  SPTI.ShiftPressurePoint
sfgcShiftRightEdgeSource edge =
  edge

sfgcShiftRightEdgeTarget :
  SFGCShiftRightEdge →
  SPTI.ShiftPressurePoint
sfgcShiftRightEdgeTarget edge =
  SSL.rightNeighbor edge

SFGCShiftRightEdge1Form : Set
SFGCShiftRightEdge1Form =
  SFGCShiftRightEdge → SPTI4.Phase4

connectionToShiftRightEdge1Form :
  SFGC.GaugeField →
  SFGCShiftRightEdge1Form
connectionToShiftRightEdge1Form A edge =
  A edge

connectionToShiftRightEdge1Form-samples :
  (A : SFGC.GaugeField) →
  (edge : SFGCShiftRightEdge) →
  connectionToShiftRightEdge1Form A edge ≡ A edge
connectionToShiftRightEdge1Form-samples A edge =
  refl

shiftRightEdgePointLinkAgreement :
  (A : SFGC.GaugeField) →
  (edge : SFGCShiftRightEdge) →
  connectionToShiftRightEdge1Form A edge
    ≡
  connectionToPointLink1Form A
    (sfgcShiftRightEdgeSource edge)
shiftRightEdgePointLinkAgreement A edge =
  refl

vacuumShiftRightEdge1FormZero :
  (edge : SFGCShiftRightEdge) →
  connectionToShiftRightEdge1Form SFGC.vacuumGaugeField edge
    ≡
  SPTI4.φ0
vacuumShiftRightEdge1FormZero edge =
  refl

record SFGCShiftRightEdgePlaquette : Set where
  constructor rightEdgeReturnPlaquette
  field
    plaquetteAnchor :
      SFGCShiftRightEdge

SFGCShiftRightEdgePrimeLattice2Cell : Set
SFGCShiftRightEdgePrimeLattice2Cell =
  SFGCShiftRightEdgePlaquette

sfgcShiftRightEdgePlaquette2Cell :
  SFGCShiftRightEdgePlaquette →
  SFGCShiftRightEdgePrimeLattice2Cell
sfgcShiftRightEdgePlaquette2Cell plaquette =
  plaquette

sfgcShiftRightEdgeSignedPlaquetteBoundary :
  SFGCShiftRightEdgePlaquette →
  List (SignedBoundaryEdge SFGCShiftRightEdge)
sfgcShiftRightEdgeSignedPlaquetteBoundary plaquette =
  signedBoundaryEdge positiveBoundary
    (SFGCShiftRightEdgePlaquette.plaquetteAnchor plaquette)
  ∷ signedBoundaryEdge negativeBoundary
    (SFGCShiftRightEdgePlaquette.plaquetteAnchor plaquette)
  ∷ []

sfgcShiftRightEdgeSignedPlaquetteBoundary-shape :
  (plaquette : SFGCShiftRightEdgePlaquette) →
  sfgcShiftRightEdgeSignedPlaquetteBoundary plaquette
    ≡
  signedBoundaryEdge positiveBoundary
    (SFGCShiftRightEdgePlaquette.plaquetteAnchor plaquette)
  ∷ signedBoundaryEdge negativeBoundary
    (SFGCShiftRightEdgePlaquette.plaquetteAnchor plaquette)
  ∷ []
sfgcShiftRightEdgeSignedPlaquetteBoundary-shape plaquette =
  refl

SFGCShiftRightEdge0Form : Set
SFGCShiftRightEdge0Form =
  SPTI.ShiftPressurePoint → SPTI4.Phase4

SFGCShiftRightEdge2Form : Set
SFGCShiftRightEdge2Form =
  SFGCShiftRightEdgePlaquette → SPTI4.Phase4

sfgcShiftRightEdgeδ₀ :
  SFGCShiftRightEdge0Form →
  SFGCShiftRightEdge1Form
sfgcShiftRightEdgeδ₀ f edge =
  SFGS.phaseAdd4
    (f (sfgcShiftRightEdgeTarget edge))
    (SFGS.phaseInv4 (f (sfgcShiftRightEdgeSource edge)))

sfgcShiftRightEdgeδ₁ :
  SFGCShiftRightEdge1Form →
  SFGCShiftRightEdge2Form
sfgcShiftRightEdgeδ₁ a plaquette =
  signedBoundarySum
    phase4AbelianCoefficientLawSurface
    a
    (sfgcShiftRightEdgeSignedPlaquetteBoundary plaquette)

sfgcShiftRightEdgeδ₁-signedBoundaryNormalizer :
  (a : SFGCShiftRightEdge1Form) →
  (plaquette : SFGCShiftRightEdgePlaquette) →
  sfgcShiftRightEdgeδ₁ a plaquette
    ≡
  signedBoundarySum
    phase4AbelianCoefficientLawSurface
    a
    (sfgcShiftRightEdgeSignedPlaquetteBoundary plaquette)
sfgcShiftRightEdgeδ₁-signedBoundaryNormalizer a plaquette =
  refl

sfgcShiftRightEdgeδ₁-returnPlaquetteZero :
  (a : SFGCShiftRightEdge1Form) →
  (plaquette : SFGCShiftRightEdgePlaquette) →
  sfgcShiftRightEdgeδ₁ a plaquette ≡ SPTI4.φ0
sfgcShiftRightEdgeδ₁-returnPlaquetteZero a plaquette
  rewrite phase4-addIdentityʳ
    (SFGS.phaseInv4
      (a (SFGCShiftRightEdgePlaquette.plaquetteAnchor plaquette)))
  | phase4-addInverseʳ
    (a (SFGCShiftRightEdgePlaquette.plaquetteAnchor plaquette)) =
  refl

sfgcShiftRightEdgeδ₁δ₀-returnPlaquetteZero :
  (f : SFGCShiftRightEdge0Form) →
  (plaquette : SFGCShiftRightEdgePlaquette) →
  sfgcShiftRightEdgeδ₁ (sfgcShiftRightEdgeδ₀ f) plaquette
    ≡
  SPTI4.φ0
sfgcShiftRightEdgeδ₁δ₀-returnPlaquetteZero f plaquette =
  sfgcShiftRightEdgeδ₁-returnPlaquetteZero
    (sfgcShiftRightEdgeδ₀ f)
    plaquette

------------------------------------------------------------------------
-- Four-term right-edge signed-boundary surface.
--
-- This extends the conservative +edge,-edge return plaquette without
-- promoting it to a full 2D plaquette geometry.  The current SFGC/Phase4 APIs
-- expose only right-neighbor edges on the three-point shift carrier, so the
-- only closed four-term boundary available here is a 1D two-step return:
-- +start, +next, -next, -start.

data SFGCShiftRightEdgeTwoStepReturnPlaquette : Set where
  startNextRightEdgeReturnSquare :
    SFGCShiftRightEdgeTwoStepReturnPlaquette

sfgcShiftRightEdgeTwoStepBottom :
  SFGCShiftRightEdgeTwoStepReturnPlaquette →
  SFGCShiftRightEdge
sfgcShiftRightEdgeTwoStepBottom startNextRightEdgeReturnSquare =
  SPTI.shiftStartPoint

sfgcShiftRightEdgeTwoStepRight :
  SFGCShiftRightEdgeTwoStepReturnPlaquette →
  SFGCShiftRightEdge
sfgcShiftRightEdgeTwoStepRight startNextRightEdgeReturnSquare =
  SPTI.shiftNextPoint

sfgcShiftRightEdgeTwoStepTop :
  SFGCShiftRightEdgeTwoStepReturnPlaquette →
  SFGCShiftRightEdge
sfgcShiftRightEdgeTwoStepTop startNextRightEdgeReturnSquare =
  SPTI.shiftNextPoint

sfgcShiftRightEdgeTwoStepLeft :
  SFGCShiftRightEdgeTwoStepReturnPlaquette →
  SFGCShiftRightEdge
sfgcShiftRightEdgeTwoStepLeft startNextRightEdgeReturnSquare =
  SPTI.shiftStartPoint

sfgcShiftRightEdgeTwoStepSignedBoundary :
  SFGCShiftRightEdgeTwoStepReturnPlaquette →
  List (SignedBoundaryEdge SFGCShiftRightEdge)
sfgcShiftRightEdgeTwoStepSignedBoundary plaquette =
  correctedSquareBoundary
    (sfgcShiftRightEdgeTwoStepBottom plaquette)
    (sfgcShiftRightEdgeTwoStepRight plaquette)
    (sfgcShiftRightEdgeTwoStepTop plaquette)
    (sfgcShiftRightEdgeTwoStepLeft plaquette)

sfgcShiftRightEdgeTwoStepSignedBoundary-shape :
  (plaquette : SFGCShiftRightEdgeTwoStepReturnPlaquette) →
  sfgcShiftRightEdgeTwoStepSignedBoundary plaquette
    ≡
  signedBoundaryEdge positiveBoundary SPTI.shiftStartPoint
  ∷ signedBoundaryEdge positiveBoundary SPTI.shiftNextPoint
  ∷ signedBoundaryEdge negativeBoundary SPTI.shiftNextPoint
  ∷ signedBoundaryEdge negativeBoundary SPTI.shiftStartPoint
  ∷ []
sfgcShiftRightEdgeTwoStepSignedBoundary-shape
  startNextRightEdgeReturnSquare =
  refl

SFGCShiftRightEdgeTwoStep2Form : Set
SFGCShiftRightEdgeTwoStep2Form =
  SFGCShiftRightEdgeTwoStepReturnPlaquette → SPTI4.Phase4

sfgcShiftRightEdgeTwoStepδ₁ :
  SFGCShiftRightEdge1Form →
  SFGCShiftRightEdgeTwoStep2Form
sfgcShiftRightEdgeTwoStepδ₁ a plaquette =
  signedBoundarySum
    phase4AbelianCoefficientLawSurface
    a
    (sfgcShiftRightEdgeTwoStepSignedBoundary plaquette)

sfgcShiftRightEdgeTwoStepδ₁-signedBoundaryNormalizer :
  (a : SFGCShiftRightEdge1Form) →
  (plaquette : SFGCShiftRightEdgeTwoStepReturnPlaquette) →
  sfgcShiftRightEdgeTwoStepδ₁ a plaquette
    ≡
  signedBoundarySum
    phase4AbelianCoefficientLawSurface
    a
    (sfgcShiftRightEdgeTwoStepSignedBoundary plaquette)
sfgcShiftRightEdgeTwoStepδ₁-signedBoundaryNormalizer a plaquette =
  refl

sfgcShiftRightEdgeTwoStepδ₁Zero :
  (a : SFGCShiftRightEdge1Form) →
  (plaquette : SFGCShiftRightEdgeTwoStepReturnPlaquette) →
  sfgcShiftRightEdgeTwoStepδ₁ a plaquette ≡ SPTI4.φ0
sfgcShiftRightEdgeTwoStepδ₁Zero a startNextRightEdgeReturnSquare
  with a SPTI.shiftStartPoint | a SPTI.shiftNextPoint
... | SPTI4.φ0 | SPTI4.φ0 = refl
... | SPTI4.φ0 | SPTI4.φ1 = refl
... | SPTI4.φ0 | SPTI4.φ2 = refl
... | SPTI4.φ0 | SPTI4.φ3 = refl
... | SPTI4.φ1 | SPTI4.φ0 = refl
... | SPTI4.φ1 | SPTI4.φ1 = refl
... | SPTI4.φ1 | SPTI4.φ2 = refl
... | SPTI4.φ1 | SPTI4.φ3 = refl
... | SPTI4.φ2 | SPTI4.φ0 = refl
... | SPTI4.φ2 | SPTI4.φ1 = refl
... | SPTI4.φ2 | SPTI4.φ2 = refl
... | SPTI4.φ2 | SPTI4.φ3 = refl
... | SPTI4.φ3 | SPTI4.φ0 = refl
... | SPTI4.φ3 | SPTI4.φ1 = refl
... | SPTI4.φ3 | SPTI4.φ2 = refl
... | SPTI4.φ3 | SPTI4.φ3 = refl

sfgcShiftRightEdgeTwoStepδ₁δ₀Zero :
  (f : SFGCShiftRightEdge0Form) →
  (plaquette : SFGCShiftRightEdgeTwoStepReturnPlaquette) →
  sfgcShiftRightEdgeTwoStepδ₁ (sfgcShiftRightEdgeδ₀ f) plaquette
    ≡
  SPTI4.φ0
sfgcShiftRightEdgeTwoStepδ₁δ₀Zero f plaquette =
  sfgcShiftRightEdgeTwoStepδ₁Zero
    (sfgcShiftRightEdgeδ₀ f)
    plaquette

data SFGCPrimeLattice1FormNextRequiredLaw : Set where
  missingRightEdgePlaquette2CellCarrier :
    SFGCPrimeLattice1FormNextRequiredLaw

  missingRightEdgeSignedPlaquetteBoundary :
    SFGCPrimeLattice1FormNextRequiredLaw

  missingRightEdgeδ₁SignedBoundaryNormalizer :
    SFGCPrimeLattice1FormNextRequiredLaw

  missingRightEdgeδ₁δ₀ZeroLaw :
    SFGCPrimeLattice1FormNextRequiredLaw

  missingNondegenerateRightEdgePlaquetteGeometry :
    SFGCPrimeLattice1FormNextRequiredLaw

record SFGCShiftRightEdgePrimeLattice1FormBridge : Set₁ where
  field
    pointLinkBridge :
      SFGCPointLink1FormBridge

    coefficientLaws :
      AbelianCoefficientLawSurface SPTI4.Phase4

    edgeSource :
      SFGCShiftRightEdge →
      SPTI.ShiftPressurePoint

    edgeTarget :
      SFGCShiftRightEdge →
      SPTI.ShiftPressurePoint

    primeLattice0CellName :
      String

    primeLattice1CellName :
      String

    evaluatePrimeLattice1 :
      SFGCShiftRightEdge1Form →
      SFGCShiftRightEdge →
      SPTI4.Phase4

    connectionToPrimeLattice1Form :
      SFGC.GaugeField →
      SFGCShiftRightEdge1Form

    connectionToPrimeLattice1Form-samples :
      (A : SFGC.GaugeField) →
      (edge : SFGCShiftRightEdge) →
      evaluatePrimeLattice1 (connectionToPrimeLattice1Form A) edge
        ≡
      A edge

    rightEdgeSourceLaw :
      (edge : SFGCShiftRightEdge) →
      edgeSource edge ≡ edge

    rightEdgeTargetLaw :
      (edge : SFGCShiftRightEdge) →
      edgeTarget edge ≡ SSL.rightNeighbor edge

    rightEdgePointLinkAgreement :
      (A : SFGC.GaugeField) →
      (edge : SFGCShiftRightEdge) →
      evaluatePrimeLattice1 (connectionToPrimeLattice1Form A) edge
        ≡
      SFGCPointLink1FormBridge.evaluate1 pointLinkBridge
        (SFGCPointLink1FormBridge.connectionTo1Form pointLinkBridge A)
        (edgeSource edge)

    vacuumRightEdgeZero :
      (edge : SFGCShiftRightEdge) →
      evaluatePrimeLattice1
        (connectionToPrimeLattice1Form SFGC.vacuumGaugeField)
        edge
        ≡
      SPTI4.φ0

    firstMissingForCurvature :
      SFGCPrimeLattice1FormNextRequiredLaw

    nextRequiredLawName :
      String

    nextRequiredLawShape :
      String

    bridgeBoundary :
      List String

record SFGCShiftRightEdgeTwoStepPlaquetteSurface : Set₁ where
  field
    oneFormBridge :
      SFGCShiftRightEdgePrimeLattice1FormBridge

    Plaquette :
      Set

    signedPlaquetteBoundary :
      Plaquette →
      List (SignedBoundaryEdge SFGCShiftRightEdge)

    Discrete0Form :
      Set

    Discrete1Form :
      Set

    Discrete2Form :
      Set

    evaluate1 :
      Discrete1Form →
      SFGCShiftRightEdge →
      SPTI4.Phase4

    evaluate2 :
      Discrete2Form →
      Plaquette →
      SPTI4.Phase4

    δ₀ :
      Discrete0Form →
      Discrete1Form

    δ₁ :
      Discrete1Form →
      Discrete2Form

    δ₁-signedBoundaryNormalizer :
      (a : Discrete1Form) →
      (plaquette : Plaquette) →
      evaluate2 (δ₁ a) plaquette
        ≡
      signedBoundarySum
        phase4AbelianCoefficientLawSurface
        (evaluate1 a)
        (signedPlaquetteBoundary plaquette)

    twoStepPlaquetteδ₁Zero :
      (a : Discrete1Form) →
      (plaquette : Plaquette) →
      evaluate2 (δ₁ a) plaquette ≡ SPTI4.φ0

    twoStepPlaquetteδ₁δ₀Zero :
      (f : Discrete0Form) →
      (plaquette : Plaquette) →
      evaluate2 (δ₁ (δ₀ f)) plaquette ≡ SPTI4.φ0

    remainingMissingForFullCurvature :
      SFGCPrimeLattice1FormNextRequiredLaw

    surfaceBoundary :
      List String

canonicalSFGCShiftRightEdgePrimeLattice1FormBridge :
  SFGCShiftRightEdgePrimeLattice1FormBridge
canonicalSFGCShiftRightEdgePrimeLattice1FormBridge =
  record
    { pointLinkBridge =
        canonicalSFGCPointLink1FormBridge
    ; coefficientLaws =
        phase4AbelianCoefficientLawSurface
    ; edgeSource =
        sfgcShiftRightEdgeSource
    ; edgeTarget =
        sfgcShiftRightEdgeTarget
    ; primeLattice0CellName =
        "ShiftPressurePoint"
    ; primeLattice1CellName =
        "SFGCShiftRightEdge"
    ; evaluatePrimeLattice1 =
        λ form edge → form edge
    ; connectionToPrimeLattice1Form =
        connectionToShiftRightEdge1Form
    ; connectionToPrimeLattice1Form-samples =
        connectionToShiftRightEdge1Form-samples
    ; rightEdgeSourceLaw =
        λ edge → refl
    ; rightEdgeTargetLaw =
        λ edge → refl
    ; rightEdgePointLinkAgreement =
        shiftRightEdgePointLinkAgreement
    ; vacuumRightEdgeZero =
        vacuumShiftRightEdge1FormZero
    ; firstMissingForCurvature =
        missingNondegenerateRightEdgePlaquetteGeometry
    ; nextRequiredLawName =
        "nondegenerateRightEdgePlaquetteGeometry"
    ; nextRequiredLawShape =
        "provide a nondegenerate PrimeLattice2Cell/Plaquette geometry with independent boundary edges beyond the local +edge,-edge return plaquette"
    ; bridgeBoundary =
        "This bridge upgrades the SFGC point-link field to a typed right-neighbor oriented 1-form over ShiftPressurePoint"
        ∷ "PrimeLattice0Cell is ShiftPressurePoint and PrimeLattice1Cell is the right-edge anchor ShiftPressurePoint -> SSL.rightNeighbor"
        ∷ "connectionToPrimeLattice1Form samples exactly the existing SFGC.GaugeField value on the edge anchor"
        ∷ "The bridge reuses the local Phase4 abelian coefficient law surface"
        ∷ "Separate degenerate right-edge return and four-term 1D two-step return plaquette normalizer surfaces exist, but no nondegenerate curvature, Bianchi law, or field strength is constructed"
        ∷ []
    }

canonicalSFGCShiftRightEdgeTwoStepPlaquetteSurface :
  SFGCShiftRightEdgeTwoStepPlaquetteSurface
canonicalSFGCShiftRightEdgeTwoStepPlaquetteSurface =
  record
    { oneFormBridge =
        canonicalSFGCShiftRightEdgePrimeLattice1FormBridge
    ; Plaquette =
        SFGCShiftRightEdgeTwoStepReturnPlaquette
    ; signedPlaquetteBoundary =
        sfgcShiftRightEdgeTwoStepSignedBoundary
    ; Discrete0Form =
        SFGCShiftRightEdge0Form
    ; Discrete1Form =
        SFGCShiftRightEdge1Form
    ; Discrete2Form =
        SFGCShiftRightEdgeTwoStep2Form
    ; evaluate1 =
        λ form edge → form edge
    ; evaluate2 =
        λ form plaquette → form plaquette
    ; δ₀ =
        sfgcShiftRightEdgeδ₀
    ; δ₁ =
        sfgcShiftRightEdgeTwoStepδ₁
    ; δ₁-signedBoundaryNormalizer =
        sfgcShiftRightEdgeTwoStepδ₁-signedBoundaryNormalizer
    ; twoStepPlaquetteδ₁Zero =
        sfgcShiftRightEdgeTwoStepδ₁Zero
    ; twoStepPlaquetteδ₁δ₀Zero =
        sfgcShiftRightEdgeTwoStepδ₁δ₀Zero
    ; remainingMissingForFullCurvature =
        missingNondegenerateRightEdgePlaquetteGeometry
    ; surfaceBoundary =
        "This is a four-term right-edge signed-boundary surface over the existing SFGCShiftRightEdge API"
        ∷ "The boundary is +shiftStartPoint, +shiftNextPoint, -shiftNextPoint, -shiftStartPoint"
        ∷ "δ₁ is exactly the Phase4 signedBoundarySum over that corrected-square-shaped boundary"
        ∷ "The boundary normalizes to φ0 for every right-edge 1-form, so δ₁∘δ₀ also normalizes to φ0"
        ∷ "This is still a 1D two-step return surface: right and top share shiftNextPoint, bottom and left share shiftStartPoint"
        ∷ "No transverse edge API, independent plaquette vertices, nondegenerate endpoint law, Bianchi law, Maxwell field strength, or DiscreteCurvatureCarrier SFGC.GaugeField is constructed"
        ∷ []
    }

record SFGCShiftRightEdgePlaquetteNormalizerSurface : Set₁ where
  field
    oneFormBridge :
      SFGCShiftRightEdgePrimeLattice1FormBridge

    PrimeLattice2Cell :
      Set

    Plaquette :
      Set

    plaquette2Cell :
      Plaquette →
      PrimeLattice2Cell

    signedPlaquetteBoundary :
      Plaquette →
      List (SignedBoundaryEdge SFGCShiftRightEdge)

    Discrete0Form :
      Set

    Discrete1Form :
      Set

    Discrete2Form :
      Set

    evaluate1 :
      Discrete1Form →
      SFGCShiftRightEdge →
      SPTI4.Phase4

    evaluate2 :
      Discrete2Form →
      Plaquette →
      SPTI4.Phase4

    δ₀ :
      Discrete0Form →
      Discrete1Form

    δ₁ :
      Discrete1Form →
      Discrete2Form

    δ₁-signedBoundaryNormalizer :
      (a : Discrete1Form) →
      (plaquette : Plaquette) →
      evaluate2 (δ₁ a) plaquette
        ≡
      signedBoundarySum
        phase4AbelianCoefficientLawSurface
        (evaluate1 a)
        (signedPlaquetteBoundary plaquette)

    returnPlaquetteδ₁Zero :
      (a : Discrete1Form) →
      (plaquette : Plaquette) →
      evaluate2 (δ₁ a) plaquette ≡ SPTI4.φ0

    returnPlaquetteδ₁δ₀Zero :
      (f : Discrete0Form) →
      (plaquette : Plaquette) →
      evaluate2 (δ₁ (δ₀ f)) plaquette ≡ SPTI4.φ0

    remainingMissingForFullCurvature :
      SFGCPrimeLattice1FormNextRequiredLaw

    surfaceBoundary :
      List String

canonicalSFGCShiftRightEdgePlaquetteNormalizerSurface :
  SFGCShiftRightEdgePlaquetteNormalizerSurface
canonicalSFGCShiftRightEdgePlaquetteNormalizerSurface =
  record
    { oneFormBridge =
        canonicalSFGCShiftRightEdgePrimeLattice1FormBridge
    ; PrimeLattice2Cell =
        SFGCShiftRightEdgePrimeLattice2Cell
    ; Plaquette =
        SFGCShiftRightEdgePlaquette
    ; plaquette2Cell =
        sfgcShiftRightEdgePlaquette2Cell
    ; signedPlaquetteBoundary =
        sfgcShiftRightEdgeSignedPlaquetteBoundary
    ; Discrete0Form =
        SFGCShiftRightEdge0Form
    ; Discrete1Form =
        SFGCShiftRightEdge1Form
    ; Discrete2Form =
        SFGCShiftRightEdge2Form
    ; evaluate1 =
        λ form edge → form edge
    ; evaluate2 =
        λ form plaquette → form plaquette
    ; δ₀ =
        sfgcShiftRightEdgeδ₀
    ; δ₁ =
        sfgcShiftRightEdgeδ₁
    ; δ₁-signedBoundaryNormalizer =
        sfgcShiftRightEdgeδ₁-signedBoundaryNormalizer
    ; returnPlaquetteδ₁Zero =
        sfgcShiftRightEdgeδ₁-returnPlaquetteZero
    ; returnPlaquetteδ₁δ₀Zero =
        sfgcShiftRightEdgeδ₁δ₀-returnPlaquetteZero
    ; remainingMissingForFullCurvature =
        missingNondegenerateRightEdgePlaquetteGeometry
    ; surfaceBoundary =
        "This is a conservative right-edge return plaquette surface: every plaquette has boundary +edge then -edge"
        ∷ "δ₁ is exactly the Phase4 signedBoundarySum over signedPlaquetteBoundary"
        ∷ "The return boundary normalizes to φ0 for every right-edge 1-form, so δ₁∘δ₀ is also φ0 on this degenerate surface"
        ∷ "This surface does not provide a nondegenerate 2D square plaquette, independent transverse edges, Bianchi law, Maxwell field strength, or DiscreteCurvatureCarrier SFGC.GaugeField"
        ∷ []
    }

data SFGCNondegeneratePlaquetteMissingAPI : Set where
  sfgcMissingShiftGaugeFieldGaugeConnectionAPI :
    SFGCNondegeneratePlaquetteMissingAPI

  sfgcMissingDirectionIndexedGaugeFieldAPI :
    SFGCNondegeneratePlaquetteMissingAPI

  sfgcMissingIndependentTransverseEdgeAPI :
    SFGCNondegeneratePlaquetteMissingAPI

  sfgcMissingTransverseEdgeEndpointLaws :
    SFGCNondegeneratePlaquetteMissingAPI

  sfgcMissingNondegeneratePlaquetteVertexAPI :
    SFGCNondegeneratePlaquetteMissingAPI

  sfgcMissingNondegenerateSignedPlaquetteBoundary :
    SFGCNondegeneratePlaquetteMissingAPI

  sfgcMissingPlaquetteBumpCommutationAPI :
    SFGCNondegeneratePlaquetteMissingAPI

  sfgcMissingPlaquetteBumpCommutationLaws :
    SFGCNondegeneratePlaquetteMissingAPI

  sfgcMissingPlaquetteBoundaryOfBoundaryZero :
    SFGCNondegeneratePlaquetteMissingAPI

record SFGCNondegeneratePlaquetteCarrierRequest : Set₁ where
  field
    inspectedConnectionAPIName :
      String

    inspectedConnectionAPIShape :
      String

    inspectedRightEdgeAPIName :
      String

    inspectedRightEdgeAPIShape :
      String

    availableRightEdgeBridge :
      SFGCShiftRightEdgePrimeLattice1FormBridge

    availableReturnPlaquetteSurface :
      SFGCShiftRightEdgePlaquetteNormalizerSurface

    availableTwoStepReturnSurface :
      SFGCShiftRightEdgeTwoStepPlaquetteSurface

    missingAPIs :
      List SFGCNondegeneratePlaquetteMissingAPI

    requiredShiftGaugeFieldGaugeConnectionName :
      String

    requiredShiftGaugeFieldGaugeConnectionShape :
      String

    requiredTransverseEdgeName :
      String

    requiredTransverseEdgeShape :
      String

    requiredTransverseEndpointLawName :
      String

    requiredTransverseEndpointLawShape :
      String

    requiredPlaquetteBumpCommutationAPIName :
      String

    requiredPlaquetteBumpCommutationAPIShape :
      String

    requiredPlaquetteBumpCommutationLawName :
      String

    requiredPlaquetteBumpCommutationLawShape :
      String

    blockedPromotionName :
      String

    noPromotionBoundary :
      List String

canonicalSFGCNondegeneratePlaquetteCarrierRequest :
  SFGCNondegeneratePlaquetteCarrierRequest
canonicalSFGCNondegeneratePlaquetteCarrierRequest =
  record
    { inspectedConnectionAPIName =
        "ShiftGaugeFieldGaugeConnection"
    ; inspectedConnectionAPIShape =
        "No ShiftGaugeFieldGaugeConnection API was found in the inspected SFGC lane; the available package is ShiftFiniteGaugeCoupling with StaticGaugeField = SFGC.GaugeField"
    ; inspectedRightEdgeAPIName =
        "SFGCShiftRightEdge"
    ; inspectedRightEdgeAPIShape =
        "SFGCShiftRightEdge is only the right-neighbor anchor ShiftPressurePoint -> SSL.rightNeighbor; it has no independent direction coordinate"
    ; availableRightEdgeBridge =
        canonicalSFGCShiftRightEdgePrimeLattice1FormBridge
    ; availableReturnPlaquetteSurface =
        canonicalSFGCShiftRightEdgePlaquetteNormalizerSurface
    ; availableTwoStepReturnSurface =
        canonicalSFGCShiftRightEdgeTwoStepPlaquetteSurface
    ; missingAPIs =
        sfgcMissingShiftGaugeFieldGaugeConnectionAPI
        ∷ sfgcMissingDirectionIndexedGaugeFieldAPI
        ∷ sfgcMissingIndependentTransverseEdgeAPI
        ∷ sfgcMissingTransverseEdgeEndpointLaws
        ∷ sfgcMissingNondegeneratePlaquetteVertexAPI
        ∷ sfgcMissingNondegenerateSignedPlaquetteBoundary
        ∷ sfgcMissingPlaquetteBumpCommutationAPI
        ∷ sfgcMissingPlaquetteBumpCommutationLaws
        ∷ sfgcMissingPlaquetteBoundaryOfBoundaryZero
        ∷ []
    ; requiredShiftGaugeFieldGaugeConnectionName =
        "ShiftGaugeFieldGaugeConnection"
    ; requiredShiftGaugeFieldGaugeConnectionShape =
        "record with a connection carrier, direction-indexed edge/link sampler, right and transverse edge projections, gauge action, and vacuum connection over the same point carrier"
    ; requiredTransverseEdgeName =
        "SFGCShiftTransverseEdge"
    ; requiredTransverseEdgeShape =
        "independent transverse oriented edge type with source/target maps not definitionally equal to SFGCShiftRightEdge on the same anchor"
    ; requiredTransverseEndpointLawName =
        "sfgcShiftTransverseEdgeEndpointLaws"
    ; requiredTransverseEndpointLawShape =
        "laws naming square vertices SW SE NE NW and proving bottom/right/top/left endpoints form a nondegenerate corrected square"
    ; requiredPlaquetteBumpCommutationAPIName =
        "sfgcPlaquettePrimeBumpCommutes"
    ; requiredPlaquetteBumpCommutationAPIShape =
        "API exposing two independent plaquette-building moves or prime-address bumps whose actions on the selected connection/edge carrier can be compared in both orders"
    ; requiredPlaquetteBumpCommutationLawName =
        "sfgcPlaquettePrimeBumpCommutationLaws"
    ; requiredPlaquetteBumpCommutationLawShape =
        "bottom-then-transverse and transverse-then-bottom construction laws proving equal NE vertex/transport data and supporting boundaryOfBoundaryZero for the signed plaquette"
    ; blockedPromotionName =
        "DiscreteCurvatureCarrier SFGC.GaugeField"
    ; noPromotionBoundary =
        "This request is the nondegenerate SFGC plaquette API surface; it is not a carrier inhabitant"
        ∷ "The inspected SFGC API has one right-neighbor link value per ShiftPressurePoint and no direction-indexed transverse edge sampler"
        ∷ "The available return plaquette surfaces are degenerate: they cancel repeated right-edge anchors and therefore cannot witness independent plaquette curvature"
        ∷ "A real plaquette needs independent bottom/right/top/left edges, endpoint laws for four vertices, and a bump-commutation law tying the two directions to the same NE corner"
        ∷ "No postulate, identity carrier, constant-zero δ₁, or return-boundary normalizer is promoted to DiscreteCurvatureCarrier SFGC.GaugeField here"
        ∷ []
    }

record SFGCGaugeFieldConnectionProjectionRequest : Set₁ where
  field
    inspectedConnectionCarrier :
      Set

    inspectedPointCarrier :
      Set

    inspectedPhaseCarrier :
      Set

    inspectedVacuumConnection :
      inspectedConnectionCarrier

    availablePointLink1FormBridge :
      SFGCPointLink1FormBridge

    availableRightEdgePrimeLattice1FormBridge :
      SFGCShiftRightEdgePrimeLattice1FormBridge

    nondegeneratePlaquetteCarrierRequest :
      SFGCNondegeneratePlaquetteCarrierRequest

    existingSamplerShape :
      String

    absentNamedSampler :
      String

    absentPhaseProjection :
      String

    requiredConnectionProjectionName :
      String

    requiredConnectionProjectionShape :
      String

    requiredVacuumRealLawName :
      String

    requiredVacuumRealLawShape :
      String

    availablePhase4VacuumZeroLawName :
      String

    availablePhase4VacuumZeroLawShape :
      String

    firstMissingAPI :
      G2SFGCGaugeFieldCurvatureAPIGap

    blockedCarrierName :
      String

    noPromotionBoundary :
      List String

canonicalSFGCGaugeFieldConnectionProjectionRequest :
  SFGCGaugeFieldConnectionProjectionRequest
canonicalSFGCGaugeFieldConnectionProjectionRequest =
  record
    { inspectedConnectionCarrier =
        SFGC.GaugeField
    ; inspectedPointCarrier =
        SPTI.ShiftPressurePoint
    ; inspectedPhaseCarrier =
        SPTI4.Phase4
    ; inspectedVacuumConnection =
        SFGC.vacuumGaugeField
    ; availablePointLink1FormBridge =
        canonicalSFGCPointLink1FormBridge
    ; availableRightEdgePrimeLattice1FormBridge =
        canonicalSFGCShiftRightEdgePrimeLattice1FormBridge
    ; nondegeneratePlaquetteCarrierRequest =
        canonicalSFGCNondegeneratePlaquetteCarrierRequest
    ; existingSamplerShape =
        "SFGC.GaugeField is definitionally ShiftPressurePoint -> Phase4; the local right-edge 1-form samples A edge along edge -> SSL.rightNeighbor edge"
    ; absentNamedSampler =
        "No named gaugeFieldAt : SFGC.GaugeField -> ShiftPressurePoint -> Phase4 API is exported"
    ; absentPhaseProjection =
        "No imaginaryComponent/realComponent projection is exported for Phase4 link values"
    ; requiredConnectionProjectionName =
        "nondegenerateRightEdgePlaquetteGeometry"
    ; requiredConnectionProjectionShape =
        "A nondegenerate PrimeLattice2Cell/Plaquette geometry over SFGCShiftRightEdge; the local return plaquette only supplies +edge,-edge and normalizes to φ0"
    ; requiredVacuumRealLawName =
        "vacuumGaugeConnectionReal"
    ; requiredVacuumRealLawShape =
        "vacuumGaugeConnectionReal : every coefficient of connectionTo1Form SFGC.vacuumGaugeField has zero imaginary component, or the Phase4-native equivalent used by the selected Discrete1Form"
    ; availablePhase4VacuumZeroLawName =
        "vacuumPointLink1FormZero"
    ; availablePhase4VacuumZeroLawShape =
        "vacuumPointLink1FormZero : (s : ShiftPressurePoint) -> connectionToPointLink1Form SFGC.vacuumGaugeField s == φ0"
    ; firstMissingAPI =
        missingShiftGaugeFieldGaugeConnection
    ; blockedCarrierName =
        "DiscreteCurvatureCarrier SFGC.GaugeField"
    ; noPromotionBoundary =
        "This is a provider-facing request, not a curvature-carrier inhabitant"
        ∷ "A Phase4-native point-link bridge and a typed right-edge 1-form bridge now exist"
        ∷ "A nondegenerate SFGC plaquette request now names the missing ShiftGaugeFieldGaugeConnection, transverse edge, and bump-commutation APIs exactly"
        ∷ "Degenerate right-edge return normalizers exist, but they only prove +edge,-edge and 1D two-step return boundaries normalize to φ0"
        ∷ "Without a nondegenerate PrimeLattice2Cell/Plaquette geometry, there is no curvatureFromConnection over SFGC.GaugeField"
        ∷ "Without a selected Phase4-to-U(1) component, imaginaryComponent is not a meaningful request for the current finite API"
        ∷ "Therefore no DiscreteCurvatureCarrier SFGC.GaugeField is constructed here"
        ∷ []
    }

record G2SFGCGaugeFieldCurvatureAPIObstruction : Set₁ where
  field
    inspectedGaugeFieldCarrier :
      Set

    inspectedVacuumGaugeField :
      inspectedGaugeFieldCarrier

    inspectedGaugeFieldShape :
      String

    firstMissing :
      G2SFGCGaugeFieldCurvatureAPIGap

    missingAPIGaps :
      List G2SFGCGaugeFieldCurvatureAPIGap

    connectionProjectionRequest :
      SFGCGaugeFieldConnectionProjectionRequest

    honestBridgeBoundary :
      List String

canonicalSFGCGaugeFieldCurvatureAPIObstruction :
  G2SFGCGaugeFieldCurvatureAPIObstruction
canonicalSFGCGaugeFieldCurvatureAPIObstruction =
  record
    { inspectedGaugeFieldCarrier =
        SFGC.GaugeField
    ; inspectedVacuumGaugeField =
        SFGC.vacuumGaugeField
    ; inspectedGaugeFieldShape =
        "SFGC.GaugeField = ShiftPressurePoint -> Phase4; it is a static finite link assignment, not a connection record"
    ; firstMissing =
        missingShiftGaugeFieldGaugeConnection
    ; missingAPIGaps =
        missingConnectionCarrierForSFGCGaugeField
        ∷ missingShiftGaugeFieldGaugeConnection
        ∷ missingPhase4ToU1ComponentSelection
        ∷ missingGaugeFieldImaginaryComponent
        ∷ missingGaugeFieldHeckeEigenvalue
        ∷ missingVacuumImaginaryZeroLaw
        ∷ missingIndependentTransverseEdgeAPI
        ∷ missingTransverseEdgeEndpointLaws
        ∷ missingPlaquetteBumpCommutationAPI
        ∷ missingPlaquetteBumpCommutationLaws
        ∷ missingPlaquetteCurvatureLoop
        ∷ []
    ; connectionProjectionRequest =
        canonicalSFGCGaugeFieldConnectionProjectionRequest
    ; honestBridgeBoundary =
        "A Phase4-native point-link connectionTo1Form bridge is available as canonicalSFGCPointLink1FormBridge"
        ∷ "A typed right-neighbor oriented 1-form bridge is available as canonicalSFGCShiftRightEdgePrimeLattice1FormBridge"
        ∷ "A conservative right-edge return plaquette normalizer is available as canonicalSFGCShiftRightEdgePlaquetteNormalizerSurface"
        ∷ "A four-term 1D two-step return surface is available as canonicalSFGCShiftRightEdgeTwoStepPlaquetteSurface"
        ∷ "No SFGC field exposes an imaginaryComponent projection because no Phase4-to-U(1) component selection is present"
        ∷ "No SFGC field exposes a scalar Hecke eigenvalue"
        ∷ "Available vacuum law: vacuumPointLink1FormZero for the Phase4-native point-link bridge"
        ∷ "Available right-edge vacuum law: vacuumShiftRightEdge1FormZero"
        ∷ "Nondegenerate plaquette request: canonicalSFGCNondegeneratePlaquetteCarrierRequest"
        ∷ "Still required: nondegenerate PrimeLattice2Cell/Plaquette geometry for the right-edge 1-form"
        ∷ "Still required: ShiftGaugeFieldGaugeConnection with distinct right/transverse direction data"
        ∷ "Still required: transverse edge endpoint laws and plaquette bump-commutation laws"
        ∷ "Still required if a continuum U(1) reading is intended: Phase4 component/projection law identifying what imaginaryComponent means"
        ∷ "No plaquette loop operator exists over the three-point shift carrier"
        ∷ "Therefore this module records the API obstruction instead of constructing a fake DiscreteCurvatureCarrier SFGC.GaugeField"
        ∷ []
    }

record G2ShiftGaugeCurvatureUpstreamObstruction : Set₁ where
  field
    status :
      G2ShiftGaugeCurvatureObstructionStatus

    inspectedConnectionCarrier :
      Set

    inspectedVacuumConnection :
      inspectedConnectionCarrier

    requiredTypedInterface :
      String

    firstMissing :
      G2ShiftGaugeCurvatureMissingField

    missingFields :
      List G2ShiftGaugeCurvatureMissingField

    inspectedDefinitions :
      List String

    absentUpstreamData :
      List String

    curvatureAPIObstruction :
      G2SFGCGaugeFieldCurvatureAPIObstruction

    noFakeCarrierBoundary :
      List String

canonicalSFGCGaugeCurvatureUpstreamObstruction :
  G2ShiftGaugeCurvatureUpstreamObstruction
canonicalSFGCGaugeCurvatureUpstreamObstruction =
  record
    { status =
        blockedBeforeDiscreteCellsNoPromotion
    ; inspectedConnectionCarrier =
        SFGC.GaugeField
    ; inspectedVacuumConnection =
        SFGC.vacuumGaugeField
    ; requiredTypedInterface =
        "PrimeLattice2CellLayer SFGC.GaugeField before ShiftGaugeCurvatureData with ConnectionCarrier = SFGC.GaugeField"
    ; firstMissing =
        missingPrimeLattice2CellLayer
    ; missingFields =
        missingPrimeLattice2CellLayer
        ∷ missingPlaquetteOrTwoCellCarrier
        ∷ missingDiscreteExteriorDerivative
        ∷ missingExteriorDerivativeSquaredZero
        ∷ missingCurvatureCarrierForSFGCGaugeField
        ∷ missingCurvatureFromSFGCGaugeConnection
        ∷ missingCurvatureToMaxwellFieldStrength
        ∷ missingVacuumFlatnessLaw
        ∷ missingBianchiLaw
        ∷ []
    ; inspectedDefinitions =
        "SFGC.GaugeField = ShiftPressurePoint -> Phase4"
        ∷ "SFGC.vacuumGaugeField is the constant φ0 static link assignment"
        ∷ "SFGC.transformGauge transports static links under finite C4 gauge transforms"
        ∷ "SGCC.updateGauge is current-sourced but uses a neutral currentPhase reducer"
        ∷ []
    ; absentUpstreamData =
        "no PrimeLattice2CellLayer SFGC.GaugeField"
        ∷ "right-edge PrimeLattice0Cell/1Cell candidates exist locally, but no PrimeLattice2Cell base carrier exists"
        ∷ "degenerate right-edge return Plaquette carriers exist, including +edge,-edge and four-term 1D two-step return surfaces, but no nondegenerate Plaquette carrier with boundary in independent prime-lattice 1-cells exists"
        ∷ "right-edge source/target maps and degenerate signed return boundaries exist locally, but no nondegenerate signed plaquette boundary exists"
        ∷ "no boundaryOfBoundaryZero incidence law"
        ∷ "Phase4 abelian coefficient laws and a return-boundary normalizer exist locally, but no general finite cochain-sum normalizer exists"
        ∷ "no nondegenerate discreteExteriorDerivative0/discreteExteriorDerivative1 pair or exteriorDerivativeSquaredZero law"
        ∷ "a right-edge connectionToPrimeLattice1Form exists locally, but no PrimeLattice2CellLayer selects a δ₁ over it"
        ∷ "no CurvatureCarrier whose elements are derived from closed link loops or an exterior derivative"
        ∷ "no curvatureFromConnection : SFGC.GaugeField -> CurvatureCarrier"
        ∷ "no curvatureToFieldStrength map into a Maxwell field-strength carrier"
        ∷ "no vacuumFlatnessLaw proving curvatureFromConnection SFGC.vacuumGaugeField is flat"
        ∷ "no Bianchi law or exterior-nilpotency witness for the resulting curvature"
        ∷ []
    ; curvatureAPIObstruction =
        canonicalSFGCGaugeFieldCurvatureAPIObstruction
    ; noFakeCarrierBoundary =
        "A degenerate identity carrier would satisfy the bare DiscreteCurvatureCarrier shape but would not supply plaquettes, curvature, vacuum flatness, or Bianchi data"
        ∷ "This obstruction therefore does not construct DiscreteCurvatureCarrier SFGC.GaugeField"
        ∷ "Promotion requires an actual ShiftGaugeCurvatureData instance or equivalent upstream geometry"
        ∷ []
    }

g2ShiftGaugeCurvatureFirstMissingIsPrimeLattice2CellLayer :
  G2ShiftGaugeCurvatureUpstreamObstruction.firstMissing
    canonicalSFGCGaugeCurvatureUpstreamObstruction
  ≡
  missingPrimeLattice2CellLayer
g2ShiftGaugeCurvatureFirstMissingIsPrimeLattice2CellLayer = refl

------------------------------------------------------------------------
-- Vacuum Hecke eigenvalue reality lane.
--
-- The current Hecke modules expose operator families, compatibility scans, and
-- coarse EigenProfile counters. They do not expose a scalar Hecke eigenvalue
-- over a typed vacuum state, nor a complex/imaginary-part structure.  The
-- following bridge shape records exactly what would be needed before a
-- `vacuumHeckeEigenvaluesReal` candidate could feed a vacuum-flatness route.

record VacuumHeckeEigenvalueRealityBridge : Set₁ where
  field
    VacuumState :
      Set

    Mode :
      Set

    HeckeEigenvalue :
      Set

    ImaginaryPart :
      Set

    zeroImaginaryPart :
      ImaginaryPart

    RealEigenvalue :
      HeckeEigenvalue →
      Set

    activeMode :
      VacuumState →
      Mode

    heckeEigenvalue :
      VacuumState →
      Mode →
      HeckeEigenvalue

    imaginaryPart :
      HeckeEigenvalue →
      ImaginaryPart

    realEigenvalueBridge :
      (vacuum : VacuumState) →
      imaginaryPart (heckeEigenvalue vacuum (activeMode vacuum))
        ≡
      zeroImaginaryPart →
      RealEigenvalue (heckeEigenvalue vacuum (activeMode vacuum))

    bridgeBoundary :
      List String

vacuumHeckeEigenvaluesRealFromBridge :
  (bridge : VacuumHeckeEigenvalueRealityBridge) →
  (vacuum : VacuumHeckeEigenvalueRealityBridge.VacuumState bridge) →
  VacuumHeckeEigenvalueRealityBridge.imaginaryPart bridge
    (VacuumHeckeEigenvalueRealityBridge.heckeEigenvalue bridge vacuum
      (VacuumHeckeEigenvalueRealityBridge.activeMode bridge vacuum))
    ≡
  VacuumHeckeEigenvalueRealityBridge.zeroImaginaryPart bridge →
  VacuumHeckeEigenvalueRealityBridge.RealEigenvalue bridge
    (VacuumHeckeEigenvalueRealityBridge.heckeEigenvalue bridge vacuum
      (VacuumHeckeEigenvalueRealityBridge.activeMode bridge vacuum))
vacuumHeckeEigenvaluesRealFromBridge bridge vacuum zero-imaginary =
  VacuumHeckeEigenvalueRealityBridge.realEigenvalueBridge bridge
    vacuum
    zero-imaginary

data G2VacuumHeckeEigenvalueRealityStatus : Set where
  vacuumHeckeEigenvaluesRealBlockedNoPromotion :
    G2VacuumHeckeEigenvalueRealityStatus

data G2VacuumHeckeEigenvalueMissingField : Set where
  missingVacuumState :
    G2VacuumHeckeEigenvalueMissingField

  missingActiveMode :
    G2VacuumHeckeEigenvalueMissingField

  missingHeckeEigenvalue :
    G2VacuumHeckeEigenvalueMissingField

  missingImaginaryPart :
    G2VacuumHeckeEigenvalueMissingField

  missingZeroImaginaryPart :
    G2VacuumHeckeEigenvalueMissingField

  missingRealEigenvaluePredicate :
    G2VacuumHeckeEigenvalueMissingField

  missingRealEigenvalueBridge :
    G2VacuumHeckeEigenvalueMissingField

record G2VacuumHeckeEigenvalueRealityObligation : Set₁ where
  field
    status :
      G2VacuumHeckeEigenvalueRealityStatus

    blockedCandidateName :
      String

    inspectedVacuumGaugeCarrier :
      Set

    inspectedVacuumGaugeName :
      String

    inspectedVacuumGaugeValue :
      inspectedVacuumGaugeCarrier

    inspectedHeckeFamilyName :
      String

    inspectedEigenProfileName :
      String

    requiredBridgeShapeName :
      String

    missingFields :
      List G2VacuumHeckeEigenvalueMissingField

    missingFieldNames :
      List String

    candidateVacuumFlatnessUse :
      String

    noPromotionBoundary :
      List String

canonicalVacuumHeckeEigenvalueRealityObligation :
  G2VacuumHeckeEigenvalueRealityObligation
canonicalVacuumHeckeEigenvalueRealityObligation =
  record
    { status =
        vacuumHeckeEigenvaluesRealBlockedNoPromotion
    ; blockedCandidateName =
        "vacuumHeckeEigenvaluesReal"
    ; inspectedVacuumGaugeCarrier =
        SFGC.GaugeField
    ; inspectedVacuumGaugeName =
        "SFGC.vacuumGaugeField"
    ; inspectedVacuumGaugeValue =
        SFGC.vacuumGaugeField
    ; inspectedHeckeFamilyName =
        "HS.HeckeFamilyOn"
    ; inspectedEigenProfileName =
        "PHEM.EigenProfile"
    ; requiredBridgeShapeName =
        "VacuumHeckeEigenvalueRealityBridge"
    ; missingFields =
        missingVacuumState
        ∷ missingActiveMode
        ∷ missingHeckeEigenvalue
        ∷ missingImaginaryPart
        ∷ missingZeroImaginaryPart
        ∷ missingRealEigenvaluePredicate
        ∷ missingRealEigenvalueBridge
        ∷ []
    ; missingFieldNames =
        "VacuumState"
        ∷ "activeMode"
        ∷ "heckeEigenvalue"
        ∷ "imaginaryPart"
        ∷ "zeroImaginaryPart"
        ∷ "RealEigenvalue"
        ∷ "realEigenvalueBridge"
        ∷ []
    ; candidateVacuumFlatnessUse =
        "After a real eigenvalue bridge and a curvature carrier exist, this can be considered as input evidence for a vacuumFlatnessLaw; it is not such a law now"
    ; noPromotionBoundary =
        "SFGC.vacuumGaugeField is a static Phase4 gauge link assignment, not a VacuumState carrying active Hecke modes"
        ∷ "HS.HeckeFamilyOn exposes T and compat over a carrier, but not a scalar heckeEigenvalue field"
        ∷ "PHEM.EigenProfile exposes Nat counters earth/spoke/hub, not complex eigenvalues"
        ∷ "No imaginaryPart projection, zeroImaginaryPart value, RealEigenvalue predicate, or realEigenvalueBridge is present"
        ∷ "Therefore vacuumHeckeEigenvaluesReal is not constructed from current definitions"
        ∷ []
    }

data G2DiscreteCurvatureCarrierStatus : Set where
  carrierShapeOnlyNoPromotion :
    G2DiscreteCurvatureCarrierStatus

record G2ShiftGaugeDiscreteCurvatureCarrierObligation : Set₁ where
  field
    status :
      G2DiscreteCurvatureCarrierStatus

    connectionCarrier :
      Set

    requiredCarrierName :
      String

    requiredBridgeLemmaName :
      String

    requiredConstructorPath :
      String

    inspectedSupport :
      List String

    primeLattice2CellLayerRequirement :
      G2PrimeLattice2CellLayerObligation connectionCarrier

    typedUpstreamObstruction :
      G2ShiftGaugeCurvatureUpstreamObstruction

    missingSupport :
      List String

    noPromotionBoundary :
      List String

canonicalSFGCGaugeDiscreteCurvatureCarrierObligation :
  G2ShiftGaugeDiscreteCurvatureCarrierObligation
canonicalSFGCGaugeDiscreteCurvatureCarrierObligation =
  record
    { status =
        carrierShapeOnlyNoPromotion
    ; connectionCarrier =
        SFGC.GaugeField
    ; requiredCarrierName =
        "DiscreteCurvatureCarrier for SFGC.GaugeField"
    ; requiredBridgeLemmaName =
        "curvatureToFieldStrengthFromShiftGaugeConnection"
    ; requiredConstructorPath =
        "provide DiscreteCurvatureCarrier SFGC.GaugeField, then apply curvatureToFieldStrengthFromShiftGaugeConnection"
    ; inspectedSupport =
        "SFGC.GaugeField is a static ShiftPressurePoint -> Phase4 link assignment"
        ∷ "SFGC.gaugePotential samples the static link phase at a carrier point"
        ∷ "SFGC.transformGauge gives finite C4 link transport under a GaugeTransform"
        ∷ []
    ; primeLattice2CellLayerRequirement =
        canonicalSFGCPrimeLattice2CellLayerObligation
    ; typedUpstreamObstruction =
        canonicalSFGCGaugeCurvatureUpstreamObstruction
    ; missingSupport =
        "first missing field: PrimeLattice2CellLayer SFGC.GaugeField"
        ∷ "right-edge PrimeLattice0Cell/1Cell candidates are present locally, but no PrimeLattice2Cell base carrier is present"
        ∷ "degenerate right-edge return Plaquette carriers are present, including +edge,-edge and four-term 1D two-step return surfaces, but no nondegenerate plaquetteBoundary1Cells operator is present"
        ∷ "right-edge source/target maps and degenerate signed return boundaries are present locally, but no nondegenerate signed plaquette boundary is present"
        ∷ "no boundaryOfBoundaryZero incidence law is present"
        ∷ "Phase4 abelian coefficient laws and a return-boundary normalizer exist locally, but no general finite cochain-sum normalizer is present"
        ∷ "local right-edge 0/1/2-form carriers are present only for the degenerate return plaquette, not for a full prime-lattice cochain complex"
        ∷ "no nondegenerate discreteExteriorDerivative0/discreteExteriorDerivative1 pair or d^2=0 witness is present"
        ∷ "a right-edge connectionToPrimeLattice1Form embeds SFGC.GaugeField into an oriented-edge 1-form, but no 2-cell layer consumes it"
        ∷ "no closed CurvatureCarrier constructor is present for the current three-point shift gauge surface"
        ∷ "no vacuumFlatnessLaw for SFGC.vacuumGaugeField is available"
        ∷ "no Bianchi law or exterior-nilpotency witness is available"
        ∷ "no Maxwell field-strength carrier is present until DiscreteCurvatureCarrier SFGC.GaugeField is supplied"
        ∷ []
    ; noPromotionBoundary =
        "This record names the typed curvature-carrier obligation only"
        ∷ "It does not construct DiscreteCurvatureCarrier SFGC.GaugeField"
        ∷ "It does not inhabit MaxwellGaugeFieldEquationTheorem"
        ∷ []
    }
