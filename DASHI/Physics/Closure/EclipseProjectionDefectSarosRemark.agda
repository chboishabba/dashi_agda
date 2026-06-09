module DASHI.Physics.Closure.EclipseProjectionDefectSarosRemark where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Eclipse projection-defect / Saros stability remark.
--
-- This receipt records a bounded illustration only.  A single eclipse can
-- be described at the observer's sky as an archimedean/projective angular
-- overlap of the solar and lunar disks.  That overlap is not, by itself, a
-- product-formula proof or a physical promotion.
--
-- Regular eclipse recurrence and Saros stability require orbital periods,
-- resonances, nodal/perigee structure, and KAM/Diophantine-style stability
-- conditions.  They are not established by the single projected angular
-- overlap.  The correction recorded here is that Sun and Moon may share a
-- projected angular coordinate while their defects -- mass, density, orbit,
-- and dynamical carrier data -- remain different.

data EclipseProjectionDefectSarosRemarkStatus : Set where
  projectionDefectIllustration_sarosStabilityRemark_notEvidence :
    EclipseProjectionDefectSarosRemarkStatus

data EclipseSurface : Set where
  singleEclipseAngularOverlap :
    EclipseSurface

  regularEclipseSarosStability :
    EclipseSurface

data SingleEclipseGeometry : Set where
  archimedeanProjectiveAngularOverlap :
    SingleEclipseGeometry

data SarosStabilityStructure : Set where
  orbitalPeriods :
    SarosStabilityStructure

  orbitalResonance :
    SarosStabilityStructure

  nodalAndPerigeeStructure :
    SarosStabilityStructure

  kamDiophantineStyleStability :
    SarosStabilityStructure

data ProjectedBody : Set where
  Sun :
    ProjectedBody

  Moon :
    ProjectedBody

data DefectCoordinate : Set where
  projectedAngularCoordinate :
    DefectCoordinate

  massDefect :
    DefectCoordinate

  densityDefect :
    DefectCoordinate

  orbitalDefect :
    DefectCoordinate

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

canonicalSarosStabilityStructure :
  List SarosStabilityStructure
canonicalSarosStabilityStructure =
  orbitalPeriods
  ∷ orbitalResonance
  ∷ nodalAndPerigeeStructure
  ∷ kamDiophantineStyleStability
  ∷ []

canonicalDistinctDefects :
  List DefectCoordinate
canonicalDistinctDefects =
  massDefect
  ∷ densityDefect
  ∷ orbitalDefect
  ∷ []

singleEclipseStatement :
  String
singleEclipseStatement =
  "A single eclipse angular overlap is an archimedean/projective sky-coordinate illustration."

sarosStabilityStatement :
  String
sarosStabilityStatement =
  "Regular eclipse and Saros stability require orbital periods, resonances, nodal/perigee structure, and KAM/Diophantine-style stability."

productFormulaBoundaryStatement :
  String
productFormulaBoundaryStatement =
  "No product formula is proved for a single eclipse angular overlap."

projectedCoordinateCorrectionStatement :
  String
projectedCoordinateCorrectionStatement =
  "Sun and Moon may share a projected angular coordinate while their mass, density, and orbital defects differ."

promotionBoundaryStatement :
  String
promotionBoundaryStatement =
  "Projection-defect illustration only: no physical proof, physical evidence, product-formula proof, or promotion is asserted."

record EclipseProjectionDefectSarosRemark : Set where
  field
    status :
      EclipseProjectionDefectSarosRemarkStatus

    statusIsProjectionDefectIllustrationSarosStabilityRemarkNotEvidence :
      status
      ≡ projectionDefectIllustration_sarosStabilityRemark_notEvidence

    singleEclipseSurface :
      EclipseSurface

    singleEclipseSurfaceIsAngularOverlap :
      singleEclipseSurface ≡ singleEclipseAngularOverlap

    singleEclipseGeometry :
      SingleEclipseGeometry

    singleEclipseGeometryIsArchimedeanProjective :
      singleEclipseGeometry ≡ archimedeanProjectiveAngularOverlap

    singleEclipseSummary :
      String

    singleEclipseSummaryIsCanonical :
      singleEclipseSummary ≡ singleEclipseStatement

    sarosSurface :
      EclipseSurface

    sarosSurfaceIsRegularEclipseSarosStability :
      sarosSurface ≡ regularEclipseSarosStability

    sarosStabilityRequires :
      List SarosStabilityStructure

    sarosStabilityRequiresCanonical :
      sarosStabilityRequires ≡ canonicalSarosStabilityStructure

    sarosStabilitySummary :
      String

    sarosStabilitySummaryIsCanonical :
      sarosStabilitySummary ≡ sarosStabilityStatement

    singleOverlapProvesSarosStability :
      Bool

    singleOverlapProvesSarosStabilityIsFalse :
      singleOverlapProvesSarosStability ≡ false

    productFormulaProvedForSingleEclipse :
      Bool

    productFormulaProvedForSingleEclipseIsFalse :
      productFormulaProvedForSingleEclipse ≡ false

    productFormulaBoundary :
      String

    productFormulaBoundaryIsCanonical :
      productFormulaBoundary ≡ productFormulaBoundaryStatement

    firstProjectedBody :
      ProjectedBody

    firstProjectedBodyIsSun :
      firstProjectedBody ≡ Sun

    secondProjectedBody :
      ProjectedBody

    secondProjectedBodyIsMoon :
      secondProjectedBody ≡ Moon

    sharedProjectedCoordinate :
      DefectCoordinate

    sharedProjectedCoordinateIsAngular :
      sharedProjectedCoordinate ≡ projectedAngularCoordinate

    sharedProjectedCoordinateAllowed :
      Bool

    sharedProjectedCoordinateAllowedIsTrue :
      sharedProjectedCoordinateAllowed ≡ true

    distinctDefects :
      List DefectCoordinate

    distinctDefectsAreCanonical :
      distinctDefects ≡ canonicalDistinctDefects

    sharedProjectionImpliesSameDefects :
      Bool

    sharedProjectionImpliesSameDefectsIsFalse :
      sharedProjectionImpliesSameDefects ≡ false

    projectedCoordinateCorrection :
      String

    projectedCoordinateCorrectionIsCanonical :
      projectedCoordinateCorrection
      ≡ projectedCoordinateCorrectionStatement

    physicalProofProvided :
      Bool

    physicalProofProvidedIsFalse :
      physicalProofProvided ≡ false

    physicalEvidencePromoted :
      Bool

    physicalEvidencePromotedIsFalse :
      physicalEvidencePromoted ≡ false

    promotionFlags :
      List PromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    promotionBoundary :
      String

    promotionBoundaryIsCanonical :
      promotionBoundary ≡ promotionBoundaryStatement

open EclipseProjectionDefectSarosRemark public

canonicalEclipseProjectionDefectSarosRemark :
  EclipseProjectionDefectSarosRemark
canonicalEclipseProjectionDefectSarosRemark =
  record
    { status =
        projectionDefectIllustration_sarosStabilityRemark_notEvidence
    ; statusIsProjectionDefectIllustrationSarosStabilityRemarkNotEvidence =
        refl
    ; singleEclipseSurface =
        singleEclipseAngularOverlap
    ; singleEclipseSurfaceIsAngularOverlap =
        refl
    ; singleEclipseGeometry =
        archimedeanProjectiveAngularOverlap
    ; singleEclipseGeometryIsArchimedeanProjective =
        refl
    ; singleEclipseSummary =
        singleEclipseStatement
    ; singleEclipseSummaryIsCanonical =
        refl
    ; sarosSurface =
        regularEclipseSarosStability
    ; sarosSurfaceIsRegularEclipseSarosStability =
        refl
    ; sarosStabilityRequires =
        canonicalSarosStabilityStructure
    ; sarosStabilityRequiresCanonical =
        refl
    ; sarosStabilitySummary =
        sarosStabilityStatement
    ; sarosStabilitySummaryIsCanonical =
        refl
    ; singleOverlapProvesSarosStability =
        false
    ; singleOverlapProvesSarosStabilityIsFalse =
        refl
    ; productFormulaProvedForSingleEclipse =
        false
    ; productFormulaProvedForSingleEclipseIsFalse =
        refl
    ; productFormulaBoundary =
        productFormulaBoundaryStatement
    ; productFormulaBoundaryIsCanonical =
        refl
    ; firstProjectedBody =
        Sun
    ; firstProjectedBodyIsSun =
        refl
    ; secondProjectedBody =
        Moon
    ; secondProjectedBodyIsMoon =
        refl
    ; sharedProjectedCoordinate =
        projectedAngularCoordinate
    ; sharedProjectedCoordinateIsAngular =
        refl
    ; sharedProjectedCoordinateAllowed =
        true
    ; sharedProjectedCoordinateAllowedIsTrue =
        refl
    ; distinctDefects =
        canonicalDistinctDefects
    ; distinctDefectsAreCanonical =
        refl
    ; sharedProjectionImpliesSameDefects =
        false
    ; sharedProjectionImpliesSameDefectsIsFalse =
        refl
    ; projectedCoordinateCorrection =
        projectedCoordinateCorrectionStatement
    ; projectedCoordinateCorrectionIsCanonical =
        refl
    ; physicalProofProvided =
        false
    ; physicalProofProvidedIsFalse =
        refl
    ; physicalEvidencePromoted =
        false
    ; physicalEvidencePromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; promotionBoundary =
        promotionBoundaryStatement
    ; promotionBoundaryIsCanonical =
        refl
    }

canonicalStatus :
  EclipseProjectionDefectSarosRemarkStatus
canonicalStatus =
  status canonicalEclipseProjectionDefectSarosRemark
