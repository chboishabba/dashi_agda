module DASHI.Physics.QFT.OPEConformalBootstrapReceiptSurface where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface as AQFTColim

------------------------------------------------------------------------
-- OPE / conformal-bootstrap target surface.
--
-- This module records the non-promoting target that would connect the
-- depth-filtered local-algebra colimit to conformal data:
--
--   * OPE coefficient targets from the depth-filtered colimit algebra,
--   * scaling dimensions and a dilatation-operator target,
--   * conformal-bootstrap crossing-equation targets,
--   * and a mass-gap boundary as a non-conformal spectral output property.
--
-- It does not construct an OPE algebra, CFT, conformal bootstrap solution,
-- interacting QFT, mass gap, Standard Model, GRQFT, or TOE promotion receipt.

data OPEConformalBootstrapStatus : Set where
  opeBootstrapTargetOnlyNoPromotion :
    OPEConformalBootstrapStatus

data OPEConformalBootstrapOpenObligation : Set where
  missingDepthFilteredColimitToOperatorBasis :
    OPEConformalBootstrapOpenObligation

  missingOPECoefficientExtractionLaw :
    OPEConformalBootstrapOpenObligation

  missingScalingDimensionAssignment :
    OPEConformalBootstrapOpenObligation

  missingDilatationOperatorConstruction :
    OPEConformalBootstrapOpenObligation

  missingDilatationEigenstateLaw :
    OPEConformalBootstrapOpenObligation

  missingFourPointFunctionCarrier :
    OPEConformalBootstrapOpenObligation

  missingCrossRatioDomain :
    OPEConformalBootstrapOpenObligation

  missingCrossingEquationSystem :
    OPEConformalBootstrapOpenObligation

  missingConformalRegimeJustification :
    OPEConformalBootstrapOpenObligation

  missingMassGapAsNonConformalSpectralOutput :
    OPEConformalBootstrapOpenObligation

canonicalOPEConformalBootstrapOpenObligations :
  List OPEConformalBootstrapOpenObligation
canonicalOPEConformalBootstrapOpenObligations =
  missingDepthFilteredColimitToOperatorBasis
  ∷ missingOPECoefficientExtractionLaw
  ∷ missingScalingDimensionAssignment
  ∷ missingDilatationOperatorConstruction
  ∷ missingDilatationEigenstateLaw
  ∷ missingFourPointFunctionCarrier
  ∷ missingCrossRatioDomain
  ∷ missingCrossingEquationSystem
  ∷ missingConformalRegimeJustification
  ∷ missingMassGapAsNonConformalSpectralOutput
  ∷ []

data OPEConformalBootstrapPromotionAuthorityToken : Set where

postulate
  Operator :
    Set

  OPECoefficient :
    Set

  ScalingDimension :
    Set

  DilatationOperator :
    Set

  FourPointFunction :
    Set

  CrossRatio :
    Set

  CrossingEquation :
    Set

  SpectralMassGap :
    Set

  opeCoefficientTargetFromColimit :
    Operator →
    Operator →
    Operator →
    OPECoefficient

  scalingDimensionTarget :
    Operator →
    ScalingDimension

  dilatationOperatorTarget :
    DilatationOperator

  dilatationEigenstateTarget :
    Operator →
    Set

  conformalBootstrapCrossingTarget :
    FourPointFunction →
    CrossRatio →
    CrossingEquation

  massGapNonConformalSpectralOutputTarget :
    SpectralMassGap

record OPEConformalBootstrapReceiptSurface : Setω where
  field
    status :
      OPEConformalBootstrapStatus

    depthFilteredLocalAlgebraSurface :
      AQFTColim.DepthFilteredLocalAlgebraSurface

    depthFilteredColimitSource :
      String

    depthFilteredColimitSource-v :
      depthFilteredColimitSource
      ≡
      "AQFTCarrierAlgebraQuotientSurface.DepthFilteredLocalAlgebraSurface.A_colim"

    operatorCarrier :
      Set

    opeCoefficientCarrier :
      Set

    scalingDimensionCarrier :
      Set

    dilatationOperatorCarrier :
      Set

    fourPointFunctionCarrier :
      Set

    crossRatioCarrier :
      Set

    crossingEquationCarrier :
      Set

    spectralMassGapCarrier :
      Set

    opeCoefficientTarget :
      operatorCarrier →
      operatorCarrier →
      operatorCarrier →
      opeCoefficientCarrier

    scalingDimensionOf :
      operatorCarrier →
      scalingDimensionCarrier

    dilatationOperator :
      dilatationOperatorCarrier

    dilatationEigenstateLawTarget :
      operatorCarrier →
      Set

    crossingEquationTarget :
      fourPointFunctionCarrier →
      crossRatioCarrier →
      crossingEquationCarrier

    massGapSpectralOutputTarget :
      spectralMassGapCarrier

    massGapBoundary :
      String

    massGapBoundary-v :
      massGapBoundary
      ≡
      "mass-gap-is-non-conformal-spectral-output-property-not-an-OPE-bootstrap-input"

    openObligations :
      List OPEConformalBootstrapOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalOPEConformalBootstrapOpenObligations

    conformalBootstrapPromoted :
      Bool

    conformalBootstrapPromotedIsFalse :
      conformalBootstrapPromoted ≡ false

    noPromotionWithoutAuthority :
      OPEConformalBootstrapPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open OPEConformalBootstrapReceiptSurface public

canonicalOPEConformalBootstrapReceiptSurface :
  OPEConformalBootstrapReceiptSurface
canonicalOPEConformalBootstrapReceiptSurface =
  record
    { status =
        opeBootstrapTargetOnlyNoPromotion
    ; depthFilteredLocalAlgebraSurface =
        AQFTColim.canonicalDepthFilteredLocalAlgebraSurface
    ; depthFilteredColimitSource =
        "AQFTCarrierAlgebraQuotientSurface.DepthFilteredLocalAlgebraSurface.A_colim"
    ; depthFilteredColimitSource-v =
        refl
    ; operatorCarrier =
        Operator
    ; opeCoefficientCarrier =
        OPECoefficient
    ; scalingDimensionCarrier =
        ScalingDimension
    ; dilatationOperatorCarrier =
        DilatationOperator
    ; fourPointFunctionCarrier =
        FourPointFunction
    ; crossRatioCarrier =
        CrossRatio
    ; crossingEquationCarrier =
        CrossingEquation
    ; spectralMassGapCarrier =
        SpectralMassGap
    ; opeCoefficientTarget =
        opeCoefficientTargetFromColimit
    ; scalingDimensionOf =
        scalingDimensionTarget
    ; dilatationOperator =
        dilatationOperatorTarget
    ; dilatationEigenstateLawTarget =
        dilatationEigenstateTarget
    ; crossingEquationTarget =
        conformalBootstrapCrossingTarget
    ; massGapSpectralOutputTarget =
        massGapNonConformalSpectralOutputTarget
    ; massGapBoundary =
        "mass-gap-is-non-conformal-spectral-output-property-not-an-OPE-bootstrap-input"
    ; massGapBoundary-v =
        refl
    ; openObligations =
        canonicalOPEConformalBootstrapOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; conformalBootstrapPromoted =
        false
    ; conformalBootstrapPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "OPE coefficients are targets extracted from the depth-filtered colimit local algebra, not constructed here"
        ∷ "Scaling dimensions and a dilatation operator are target carriers; no conformal spectrum is proved"
        ∷ "Conformal-bootstrap crossing equations are target equations, not an inhabited bootstrap solution"
        ∷ "The conformal regime itself remains an explicit obligation before OPE/bootstrap claims can be interpreted"
        ∷ "Mass gap is tracked separately as a non-conformal spectral output property of the composed interacting theory"
        ∷ "This surface does not promote CFT, interacting QFT, mass gap, Standard Model, GRQFT, or TOE closure"
        ∷ []
    }
