module DASHI.Physics.QFT.SMGaugeBosonsFromCSBoundaryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Standard Model gauge-boson candidates from CS/WZW boundaries.
--
-- This receipt records candidate bookkeeping only.  The boundary reading is
-- that Chern-Simons bulk data can expose WZW / affine current modes.  The
-- weak sector has three SU(2)-adjoint W candidates, the colour sector has
-- eight SU(3)-adjoint gluon candidates, and the neutral electroweak
-- Z/photon split is left open because Weinberg-angle / Higgs-sector mixing
-- has not been constructed here.
--
-- No exact physical gauge-boson spectrum, exact Standard Model, G_DHR ~= G_SM,
-- or terminal promotion is made.

data GaugeBosonFamily : Set where
  weakSU2Adjoint :
    GaugeBosonFamily

  colourSU3Adjoint :
    GaugeBosonFamily

  neutralElectroweakMixed :
    GaugeBosonFamily

data GaugeBosonCandidate : Set where
  WPlusCandidate :
    GaugeBosonCandidate

  WMinusCandidate :
    GaugeBosonCandidate

  WNeutralCandidate :
    GaugeBosonCandidate

  gluon1Candidate :
    GaugeBosonCandidate

  gluon2Candidate :
    GaugeBosonCandidate

  gluon3Candidate :
    GaugeBosonCandidate

  gluon4Candidate :
    GaugeBosonCandidate

  gluon5Candidate :
    GaugeBosonCandidate

  gluon6Candidate :
    GaugeBosonCandidate

  gluon7Candidate :
    GaugeBosonCandidate

  gluon8Candidate :
    GaugeBosonCandidate

  ZCandidate :
    GaugeBosonCandidate

  photonCandidate :
    GaugeBosonCandidate

canonicalWModes :
  List GaugeBosonCandidate
canonicalWModes =
  WPlusCandidate
  ∷ WMinusCandidate
  ∷ WNeutralCandidate
  ∷ []

canonicalGluonModes :
  List GaugeBosonCandidate
canonicalGluonModes =
  gluon1Candidate
  ∷ gluon2Candidate
  ∷ gluon3Candidate
  ∷ gluon4Candidate
  ∷ gluon5Candidate
  ∷ gluon6Candidate
  ∷ gluon7Candidate
  ∷ gluon8Candidate
  ∷ []

canonicalNeutralMixedModes :
  List GaugeBosonCandidate
canonicalNeutralMixedModes =
  ZCandidate
  ∷ photonCandidate
  ∷ []

data CSWZWBoundaryStatus : Set where
  currentAlgebraBoundaryCandidate :
    CSWZWBoundaryStatus

data NeutralMixingStatus : Set where
  zPhotonMixingOpen :
    NeutralMixingStatus

cswzwBoundaryLabel : String
cswzwBoundaryLabel =
  "CS/WZW boundary current-algebra gauge-boson candidate"

weakModesLabel : String
weakModesLabel =
  "three SU(2)_L adjoint W-mode candidates: W+, W-, W0"

gluonModesLabel : String
gluonModesLabel =
  "eight SU(3)_c adjoint gluon candidates"

neutralMixingOpenLabel : String
neutralMixingOpenLabel =
  "Z/photon mixing remains open until electroweak symmetry breaking and mixing angle data are constructed"

record SMGaugeBosonsFromCSBoundaryReceipt : Setω where
  field
    status :
      CSWZWBoundaryStatus

    statusIsBoundaryCandidate :
      status ≡ currentAlgebraBoundaryCandidate

    boundaryReading :
      String

    boundaryReadingIsCanonical :
      boundaryReading ≡ cswzwBoundaryLabel

    csBoundaryCandidate :
      Bool

    csBoundaryCandidateIsTrue :
      csBoundaryCandidate ≡ true

    wzwCurrentAlgebraCandidate :
      Bool

    wzwCurrentAlgebraCandidateIsTrue :
      wzwCurrentAlgebraCandidate ≡ true

    weakFamily :
      GaugeBosonFamily

    weakFamilyIsSU2Adjoint :
      weakFamily ≡ weakSU2Adjoint

    wModes :
      List GaugeBosonCandidate

    wModesAreCanonical :
      wModes ≡ canonicalWModes

    wModeCount :
      Nat

    wModeCountIsThree :
      wModeCount ≡ 3

    wModesCandidate :
      Bool

    wModesCandidateIsTrue :
      wModesCandidate ≡ true

    weakModesStatement :
      String

    weakModesStatementIsCanonical :
      weakModesStatement ≡ weakModesLabel

    colourFamily :
      GaugeBosonFamily

    colourFamilyIsSU3Adjoint :
      colourFamily ≡ colourSU3Adjoint

    gluonModes :
      List GaugeBosonCandidate

    gluonModesAreCanonical :
      gluonModes ≡ canonicalGluonModes

    gluonModeCount :
      Nat

    gluonModeCountIsEight :
      gluonModeCount ≡ 8

    gluonModesCandidate :
      Bool

    gluonModesCandidateIsTrue :
      gluonModesCandidate ≡ true

    gluonModesStatement :
      String

    gluonModesStatementIsCanonical :
      gluonModesStatement ≡ gluonModesLabel

    neutralFamily :
      GaugeBosonFamily

    neutralFamilyIsMixed :
      neutralFamily ≡ neutralElectroweakMixed

    neutralModes :
      List GaugeBosonCandidate

    neutralModesAreCanonical :
      neutralModes ≡ canonicalNeutralMixedModes

    neutralMixingStatus :
      NeutralMixingStatus

    neutralMixingStatusIsOpen :
      neutralMixingStatus ≡ zPhotonMixingOpen

    zPhotonMixingOpenFlag :
      Bool

    zPhotonMixingOpenFlagIsTrue :
      zPhotonMixingOpenFlag ≡ true

    neutralMixingBoundary :
      String

    neutralMixingBoundaryIsCanonical :
      neutralMixingBoundary ≡ neutralMixingOpenLabel

    exactPhysicalGaugeBosonSpectrum :
      Bool

    exactPhysicalGaugeBosonSpectrumIsFalse :
      exactPhysicalGaugeBosonSpectrum ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    exactGDHREqualsGSMPromoted :
      Bool

    exactGDHREqualsGSMPromotedIsFalse :
      exactGDHREqualsGSMPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    receiptBoundary :
      List String

open SMGaugeBosonsFromCSBoundaryReceipt public

canonicalSMGaugeBosonsFromCSBoundaryReceipt :
  SMGaugeBosonsFromCSBoundaryReceipt
canonicalSMGaugeBosonsFromCSBoundaryReceipt =
  record
    { status =
        currentAlgebraBoundaryCandidate
    ; statusIsBoundaryCandidate =
        refl
    ; boundaryReading =
        cswzwBoundaryLabel
    ; boundaryReadingIsCanonical =
        refl
    ; csBoundaryCandidate =
        true
    ; csBoundaryCandidateIsTrue =
        refl
    ; wzwCurrentAlgebraCandidate =
        true
    ; wzwCurrentAlgebraCandidateIsTrue =
        refl
    ; weakFamily =
        weakSU2Adjoint
    ; weakFamilyIsSU2Adjoint =
        refl
    ; wModes =
        canonicalWModes
    ; wModesAreCanonical =
        refl
    ; wModeCount =
        3
    ; wModeCountIsThree =
        refl
    ; wModesCandidate =
        true
    ; wModesCandidateIsTrue =
        refl
    ; weakModesStatement =
        weakModesLabel
    ; weakModesStatementIsCanonical =
        refl
    ; colourFamily =
        colourSU3Adjoint
    ; colourFamilyIsSU3Adjoint =
        refl
    ; gluonModes =
        canonicalGluonModes
    ; gluonModesAreCanonical =
        refl
    ; gluonModeCount =
        8
    ; gluonModeCountIsEight =
        refl
    ; gluonModesCandidate =
        true
    ; gluonModesCandidateIsTrue =
        refl
    ; gluonModesStatement =
        gluonModesLabel
    ; gluonModesStatementIsCanonical =
        refl
    ; neutralFamily =
        neutralElectroweakMixed
    ; neutralFamilyIsMixed =
        refl
    ; neutralModes =
        canonicalNeutralMixedModes
    ; neutralModesAreCanonical =
        refl
    ; neutralMixingStatus =
        zPhotonMixingOpen
    ; neutralMixingStatusIsOpen =
        refl
    ; zPhotonMixingOpenFlag =
        true
    ; zPhotonMixingOpenFlagIsTrue =
        refl
    ; neutralMixingBoundary =
        neutralMixingOpenLabel
    ; neutralMixingBoundaryIsCanonical =
        refl
    ; exactPhysicalGaugeBosonSpectrum =
        false
    ; exactPhysicalGaugeBosonSpectrumIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; exactGDHREqualsGSMPromoted =
        false
    ; exactGDHREqualsGSMPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; receiptBoundary =
        "CS/WZW boundary current modes are recorded as gauge-boson candidates"
        ∷ "The weak sector records exactly three W-mode candidates"
        ∷ "The colour sector records exactly eight gluon candidates"
        ∷ "The neutral Z/photon split remains open pending EWSB and mixing data"
        ∷ "No exact physical gauge-boson spectrum, Standard Model, G_DHR ~= G_SM, or terminal promotion is asserted"
        ∷ []
    }

smGaugeBosonsWModesCountIsThree :
  wModeCount canonicalSMGaugeBosonsFromCSBoundaryReceipt
  ≡
  3
smGaugeBosonsWModesCountIsThree =
  refl

smGaugeBosonsGluonCountIsEight :
  gluonModeCount canonicalSMGaugeBosonsFromCSBoundaryReceipt
  ≡
  8
smGaugeBosonsGluonCountIsEight =
  refl

smGaugeBosonsZPhotonMixingOpen :
  zPhotonMixingOpenFlag canonicalSMGaugeBosonsFromCSBoundaryReceipt
  ≡
  true
smGaugeBosonsZPhotonMixingOpen =
  refl

smGaugeBosonsExactSpectrumFalse :
  exactPhysicalGaugeBosonSpectrum canonicalSMGaugeBosonsFromCSBoundaryReceipt
  ≡
  false
smGaugeBosonsExactSpectrumFalse =
  refl
