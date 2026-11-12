module DASHI.Physics.Motors.DonSmithOriginalPDFDiagramBidiExact where

-- Source-specific discrimination of four non-interchangeable original
-- PDF diagram families and of the later editor's reconstruction.
-- Uploaded source: Brendan J. Darrer (ed.), The high-power devices of
-- Don Smith (2022), excerpts of Patrick J. Kelly's guide (hearsay caveat).
-- Does NOT assert Smith's excess-power claims are physically observed.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as Circuit
import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Maxwell

data Contradiction : Set where

data DiagramFamily : Set where
  smithPatentPlates : DiagramFamily
  smithTabletopFigureSix : DiagramFamily
  smithSuitcaseFigureTen : DiagramFamily
  smithSuitcaseFigureEleven : DiagramFamily
  editorLaterFigureForty : DiagramFamily
  editorPracticalChapterFour : DiagramFamily

-- Printed PDF page numbers, not a claim of original manuscript pagination.
data SourcePage : Set where
  page10to16 page17to18 page28 page29 page65 page67to101 : SourcePage

sourcePage : DiagramFamily → SourcePage
sourcePage smithPatentPlates = page10to16
sourcePage smithTabletopFigureSix = page17to18
sourcePage smithSuitcaseFigureTen = page28
sourcePage smithSuitcaseFigureEleven = page29
sourcePage editorLaterFigureForty = page65
sourcePage editorPracticalChapterFour = page67to101

-- Source attribution stays separate from a diagram title or appearance.
data SourceAuthority : Set where
  smithPatentTextAsRewordedByEditor : SourceAuthority
  smithPhotoClaimAsCompiled : SourceAuthority
  smithSuitcaseDiagramAsCompiled : SourceAuthority
  editorLaterCircuit : SourceAuthority
  editorUnverifiedPracticalProposal : SourceAuthority

sourceAuthority : DiagramFamily → SourceAuthority
sourceAuthority smithPatentPlates = smithPatentTextAsRewordedByEditor
sourceAuthority smithTabletopFigureSix = smithPhotoClaimAsCompiled
sourceAuthority smithSuitcaseFigureTen = smithSuitcaseDiagramAsCompiled
sourceAuthority smithSuitcaseFigureEleven = smithSuitcaseDiagramAsCompiled
sourceAuthority editorLaterFigureForty = editorLaterCircuit
sourceAuthority editorPracticalChapterFour = editorUnverifiedPracticalProposal

-- These identities must not collapse to a single physically established
-- 'Don Smith commercial device' by name-only attribution.
tabletopNotLaterCircuit :
  smithTabletopFigureSix ≡ editorLaterFigureForty → Contradiction
tabletopNotLaterCircuit ()

suitcaseDiagramsDistinct :
  smithSuitcaseFigureTen ≡ smithSuitcaseFigureEleven → Contradiction
suitcaseDiagramsDistinct ()

smithPatentNotFilsingerSource :
  smithPatentPlates ≡ editorPracticalChapterFour → Contradiction
smithPatentNotFilsingerSource ()

-- Forward: admissible prediction classes for a selected circuit.
data PredictedMeasurement : Set where
  drivenPlateVoltage : PredictedMeasurement
  supplyAndLoadPower : PredictedMeasurement
  resonantModeResponse : PredictedMeasurement
  switchingAndRectification : PredictedMeasurement

prediction : DiagramFamily → PredictedMeasurement
prediction smithPatentPlates = drivenPlateVoltage
prediction smithTabletopFigureSix = supplyAndLoadPower
prediction smithSuitcaseFigureTen = resonantModeResponse
prediction smithSuitcaseFigureEleven = resonantModeResponse
prediction editorLaterFigureForty = switchingAndRectification
prediction editorPracticalChapterFour = switchingAndRectification

-- Reverse: what admits an actual original same-object circuit match.
record DiagramElectricalAdmission (d : DiagramFamily) : Set₁ where
  field
    SourceImageAuthority : Set
    PinLevelContinuity : Set
    IndependentPowerCalibration : Set
    sourceReadback : SourceImageAuthority
    sameDiagramPinReadback : PinLevelContinuity
    sameDevicePowerReadback : IndependentPowerCalibration

-- Reuse the golden Maxwell and Circuit36927 types; the document does
-- not supply eigenmode solutions, calibrated Earth power or proof of
-- the inhomogeneous Maxwell equation.
record ExistingPhysicsOwners : Set where
  field
    sourcePin : Circuit.Pin
    symbolicFieldStrength : Maxwell.TwoForm

-- No DiagramElectricalAdmission is fabricated for the physical hardware.
