module DASHI.Physics.Closure.G2DiscreteCurvatureCarrier where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC

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
        ∷ missingPhase4AdditionAssociativity
        ∷ missingPhase4AdditionCommutativity
        ∷ missingPhase4RightIdentity
        ∷ missingPhase4InverseCancellation
        ∷ missingPhase4AbelianGroupLawPackage
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
        ∷ "AbelianCoefficientLawSurface Phase4 with zero/add/inverse/assoc/comm/identity/inverse laws"
        ∷ "phaseAdd4-assoc : phaseAdd4 (phaseAdd4 a b) c == phaseAdd4 a (phaseAdd4 b c)"
        ∷ "phaseAdd4-comm : phaseAdd4 a b == phaseAdd4 b a"
        ∷ "phaseAdd4-identityʳ : phaseAdd4 a φ0 == a"
        ∷ "phaseAdd4-inverse-cancel : phaseAdd4 a (phaseInv4 a) == φ0 and phaseAdd4 (phaseInv4 a) a == φ0"
        ∷ "phase4-cochain-normalizer : solver for finite Phase4 signed cochain sums"
        ∷ []
    ; rejectedShortcut =
        "constant-zero d1 would make d1 (d0 f) definitional, but would not encode plaquette curvature"
    ; noPromotionBoundary =
        "Existing Phase4 support gives operations, not the named abelian-group proof package or normalizer"
        ∷ "This module now defines generic signedBoundarySum and a typed SignedBoundaryIncidenceSummationSurface, but it does not instantiate them for SFGC.GaugeField"
        ∷ "Existing shift gauge support gives a three-point link assignment, not oriented prime-lattice cells"
        ∷ "No signed plaquette boundary or boundary-of-boundary-zero law is available"
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
        "The current shift gauge field is a three-point Phase4 link assignment, not a prime-lattice 1-form"
        ∷ "No PrimeLattice0Cell, PrimeLattice1Cell, or PrimeLattice2Cell base type is defined in the inspected G2 curvature lane"
        ∷ "No plaquette carrier or plaquette boundary operator into prime-lattice 1-cells is defined"
        ∷ "No oriented edge endpoint maps, signed plaquette boundary, or boundary-of-boundary-zero incidence law is defined"
        ∷ "No Phase4 abelian-group law package or finite cochain-sum normalizer is defined"
        ∷ "No discrete exterior derivative d0/d1 or d^2=0 law is available for the lane"
        ∷ "No connectionTo1Form map embeds SFGC.GaugeField into a prime-lattice 1-form"
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

  missingConnectionToPrimeLattice1Form :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingGaugeFieldImaginaryComponent :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingGaugeFieldHeckeEigenvalue :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingVacuumImaginaryZeroLaw :
    G2SFGCGaugeFieldCurvatureAPIGap

  missingPlaquetteCurvatureLoop :
    G2SFGCGaugeFieldCurvatureAPIGap

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
        missingConnectionCarrierForSFGCGaugeField
    ; missingAPIGaps =
        missingConnectionCarrierForSFGCGaugeField
        ∷ missingConnectionToPrimeLattice1Form
        ∷ missingGaugeFieldImaginaryComponent
        ∷ missingGaugeFieldHeckeEigenvalue
        ∷ missingVacuumImaginaryZeroLaw
        ∷ missingPlaquetteCurvatureLoop
        ∷ []
    ; honestBridgeBoundary =
        "No SFGC field exposes an imaginaryComponent projection"
        ∷ "No SFGC field exposes a scalar Hecke eigenvalue"
        ∷ "No map exists from SFGC.GaugeField to a prime-lattice 1-form"
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
        ∷ "no PrimeLattice0Cell, PrimeLattice1Cell, or PrimeLattice2Cell base carrier"
        ∷ "no Plaquette carrier with boundary in prime-lattice 1-cells"
        ∷ "no oriented edge source/target maps or signed plaquette boundary"
        ∷ "no boundaryOfBoundaryZero incidence law"
        ∷ "no Phase4 abelian-group proof package or finite cochain-sum normalizer"
        ∷ "no discreteExteriorDerivative0/discreteExteriorDerivative1 pair or exteriorDerivativeSquaredZero law"
        ∷ "no connectionTo1Form : SFGC.GaugeField -> Discrete1Form"
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
        ∷ "no PrimeLattice0Cell, PrimeLattice1Cell, or PrimeLattice2Cell base carrier is present"
        ∷ "no Plaquette carrier or plaquetteBoundary1Cells operator is present"
        ∷ "no oriented edge source/target maps or signed plaquette boundary is present"
        ∷ "no boundaryOfBoundaryZero incidence law is present"
        ∷ "no Phase4 abelian-group proof package or finite cochain-sum normalizer is present"
        ∷ "no discrete 0/1/2-form carriers are present for a prime-lattice cochain complex"
        ∷ "no discreteExteriorDerivative0/discreteExteriorDerivative1 pair or d^2=0 witness is present"
        ∷ "no connectionTo1Form embeds SFGC.GaugeField into a prime-lattice 1-form"
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
