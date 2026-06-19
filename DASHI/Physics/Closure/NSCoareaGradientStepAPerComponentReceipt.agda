module DASHI.Physics.Closure.NSCoareaGradientStepAPerComponentReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only geometry receipt for the corrected coarea gradient bound
-- and the StepA_PerComponent closure route.
--
-- This surface records the corrected exponent as r^1, not r^(7/2), and it
-- records the StepA_PerComponent route as assembling corrected coarea,
-- local concentration, and pigeon concentration into the component-local L3
-- closure with diameter/layer-thickness hypotheses.  It is
-- geometry/standard-lemma bookkeeping only; no Clay promotion or theorem
-- promotion is claimed.

data NSCoareaGradientStepAPerComponentStatus : Set where
  candidateOnlyFailClosed :
    NSCoareaGradientStepAPerComponentStatus

data NSCoareaGradientStepAPerComponentRow : Set where
  correctedCoareaExponentRecorded :
    NSCoareaGradientStepAPerComponentRow
  stepAPerComponentClosureRecorded :
    NSCoareaGradientStepAPerComponentRow
  geometryStandardLemmaOnly :
    NSCoareaGradientStepAPerComponentRow
  noClayPromotion :
    NSCoareaGradientStepAPerComponentRow

canonicalNSCoareaGradientStepAPerComponentRows :
  List NSCoareaGradientStepAPerComponentRow
canonicalNSCoareaGradientStepAPerComponentRows =
  correctedCoareaExponentRecorded
  ∷ stepAPerComponentClosureRecorded
  ∷ geometryStandardLemmaOnly
  ∷ noClayPromotion
  ∷ []

data NSCoareaGradientStepAPerComponentSurfaceStage : Set where
  correctedExponentR1Recorded :
    NSCoareaGradientStepAPerComponentSurfaceStage
  stepAPerComponentAssemblyRecorded :
    NSCoareaGradientStepAPerComponentSurfaceStage
  failClosedSurfaceRecorded :
    NSCoareaGradientStepAPerComponentSurfaceStage

canonicalNSCoareaGradientStepAPerComponentSurfaceStages :
  List NSCoareaGradientStepAPerComponentSurfaceStage
canonicalNSCoareaGradientStepAPerComponentSurfaceStages =
  correctedExponentR1Recorded
  ∷ stepAPerComponentAssemblyRecorded
  ∷ failClosedSurfaceRecorded
  ∷ []

linkedReceiptLabels : List String
linkedReceiptLabels =
  "CorrectedCoareaGradientBoundReceipt"
  ∷ "LocalConcentrationPigeonConcentrationReceipt"
  ∷ "NSKatoHessianConfinementReceipt"
  ∷ []

exactObjectLabels : List String
exactObjectLabels =
  "f=lambda2+"
  ∷ "B(x0,r)"
  ∷ "K"
  ∷ "C_geo"
  ∷ "r"
  ∷ "C_iso"
  ∷ "component C_n"
  ∷ "d₀"
  ∷ "τ₀"
  ∷ "local L3 near component C_n"
  ∷ "diam(C_n) >= d0"
  ∷ "layer_thickness >= tau0"
  ∷ "ball radius r"
  ∷ "K_n -> infinity"
  ∷ "sup_{partial C_n}|grad lambda2| -> infinity"
  ∷ []

record NSCoareaGradientStepAPerComponentAssembly : Set where
  constructor mkNSCoareaGradientStepAPerComponentAssembly
  field
    correctedCoareaGradientBoundReceipt :
      String
    correctedCoareaGradientBoundReceiptIsCanonical :
      correctedCoareaGradientBoundReceipt ≡
      "CorrectedCoareaGradientBoundReceipt"

    localConcentrationPigeonConcentrationReceipt :
      String
    localConcentrationPigeonConcentrationReceiptIsCanonical :
      localConcentrationPigeonConcentrationReceipt ≡
      "LocalConcentrationPigeonConcentrationReceipt"

    nskatoHessianConfinementReceipt :
      String
    nskatoHessianConfinementReceiptIsCanonical :
      nskatoHessianConfinementReceipt ≡
      "NSKatoHessianConfinementReceipt"

    localL3NearComponent :
      String
    localL3NearComponentIsCanonical :
      localL3NearComponent ≡ "local L3 near component C_n"

    componentName :
      String
    componentNameIsCanonical :
      componentName ≡ "component C_n"

    diameterLowerBound :
      String
    diameterLowerBoundIsCanonical :
      diameterLowerBound ≡ "diam(C_n) >= d0"

    layerThicknessLowerBound :
      String
    layerThicknessLowerBoundIsCanonical :
      layerThicknessLowerBound ≡ "layer_thickness >= tau0"

    ballRadius :
      String
    ballRadiusIsCanonical :
      ballRadius ≡ "ball radius r"

    kSequence :
      String
    kSequenceIsCanonical :
      kSequence ≡ "K_n -> infinity"

    conclusion :
      String
    conclusionIsCanonical :
      conclusion ≡ "sup_{partial C_n}|grad lambda2| -> infinity"

    assemblyText :
      String
    assemblyTextIsCanonical :
      assemblyText
        ≡ "LocalConcentration + pigeon_concentration + corrected coareaGradientBound assemble StepA_PerComponent with local L3 near component C_n, diam(C_n) >= d0, layer_thickness >= tau0, ball radius r, and K_n -> infinity."

canonicalNSCoareaGradientStepAPerComponentAssembly :
  NSCoareaGradientStepAPerComponentAssembly
canonicalNSCoareaGradientStepAPerComponentAssembly =
  mkNSCoareaGradientStepAPerComponentAssembly
    "CorrectedCoareaGradientBoundReceipt"
    refl
    "LocalConcentrationPigeonConcentrationReceipt"
    refl
    "NSKatoHessianConfinementReceipt"
    refl
    "local L3 near component C_n"
    refl
    "component C_n"
    refl
    "diam(C_n) >= d0"
    refl
    "layer_thickness >= tau0"
    refl
    "ball radius r"
    refl
    "K_n -> infinity"
    refl
    "sup_{partial C_n}|grad lambda2| -> infinity"
    refl
    "LocalConcentration + pigeon_concentration + corrected coareaGradientBound assemble StepA_PerComponent with local L3 near component C_n, diam(C_n) >= d0, layer_thickness >= tau0, ball radius r, and K_n -> infinity."
    refl

coareaExponentText : String
coareaExponentText =
  "coareaGradientBound exponent is r^1, not r^(7/2)"

stepAPerComponentText : String
stepAPerComponentText =
  "StepA_PerComponent assembles LocalConcentration + pigeon_concentration + corrected coareaGradientBound to close from local L3 near component C_n with diam(C_n) >= d0, layer_thickness >= tau0, ball radius r, K_n -> infinity, and sup_{partial C_n}|grad lambda2| -> infinity"

conclusionText : String
conclusionText =
  "sup_{partial C_n}|grad lambda2| -> infinity"

geometryNoteText : String
geometryNoteText =
  "Geometry/standard lemma only; not Clay promotion."

boundaryText : String
boundaryText =
  "Candidate-only geometry receipt: the corrected coarea gradient bound is fixed at r^1, the StepA_PerComponent route is recorded as an explicit assembly of LocalConcentration, pigeon_concentration, and corrected coareaGradientBound, and all promotion flags stay false."

record NSCoareaGradientStepAPerComponentFormalSurface : Set where
  constructor mkNSCoareaGradientStepAPerComponentFormalSurface
  field
    correctedCoareaExponentSurface :
      String
    correctedCoareaExponentSurfaceIsCanonical :
      correctedCoareaExponentSurface ≡ coareaExponentText

    stepAPerComponentAssemblySurface :
      String
    stepAPerComponentAssemblySurfaceIsCanonical :
      stepAPerComponentAssemblySurface ≡ stepAPerComponentText

    closeableSurface :
      String
    closeableSurfaceIsCanonical :
      closeableSurface
        ≡ "candidate-only closeable StepA_PerComponent surface"

    assemblyWitness :
      NSCoareaGradientStepAPerComponentAssembly
    assemblyWitnessIsCanonical :
      assemblyWitness ≡ canonicalNSCoareaGradientStepAPerComponentAssembly

    surfaceStages :
      List NSCoareaGradientStepAPerComponentSurfaceStage
    surfaceStagesIsCanonical :
      surfaceStages ≡ canonicalNSCoareaGradientStepAPerComponentSurfaceStages

canonicalNSCoareaGradientStepAPerComponentFormalSurface :
  NSCoareaGradientStepAPerComponentFormalSurface
canonicalNSCoareaGradientStepAPerComponentFormalSurface =
  mkNSCoareaGradientStepAPerComponentFormalSurface
    coareaExponentText
    refl
    stepAPerComponentText
    refl
    "candidate-only closeable StepA_PerComponent surface"
    refl
    canonicalNSCoareaGradientStepAPerComponentAssembly
    refl
    canonicalNSCoareaGradientStepAPerComponentSurfaceStages
    refl

record NSCoareaGradientStepAPerComponentORCSLPGF : Set where
  constructor mkNSCoareaGradientStepAPerComponentORCSLPGF
  field
    O :
      String
    OIsCanonical :
      O ≡
      "Worker 2 owns the corrected coarea gradient bound receipt surface only."

    R :
      String
    RIsCanonical :
      R ≡
      "Record the corrected coarea exponent as r^1 and close StepA_PerComponent by assembling LocalConcentration + pigeon_concentration + corrected coareaGradientBound around local L3 near component C_n."

    C :
      String
    CIsCanonical :
      C ≡
      "Create only NSCoareaGradientStepAPerComponentReceipt.agda."

    S :
      String
    SIsCanonical :
      S ≡
      "Related surfaces are CorrectedCoareaGradientBoundReceipt, LocalConcentrationPigeonConcentrationReceipt, and NSKatoHessianConfinementReceipt; no other files are touched."

    L :
      String
    LIsCanonical :
      L ≡
      "CorrectedCoareaGradientBoundReceipt -> LocalConcentrationPigeonConcentrationReceipt -> StepA_PerComponent -> sup_{partial C_n}|grad lambda2| -> infinity"

    P :
      String
    PIsCanonical :
      P ≡
      "f=lambda2+, B(x0,r), K, C_geo, r, C_iso, component C_n, d0, tau0, local L3 near component C_n, diam(C_n) >= d0, layer_thickness >= tau0, ball radius r, K_n -> infinity, conclusion sup_{partial C_n}|grad lambda2| -> infinity"

    G :
      String
    GIsCanonical :
      G ≡
      "Candidate-only; no theorem promotion; main runs Agda."

    F :
      String
    FIsCanonical :
      F ≡
      "Avoid depending on unavailable math libraries; this is a receipt surface, not a full formal coarea proof, and it stays candidate-only."

    routeAssembly :
      NSCoareaGradientStepAPerComponentAssembly
    routeAssemblyIsCanonical :
      routeAssembly ≡ canonicalNSCoareaGradientStepAPerComponentAssembly

canonicalNSCoareaGradientStepAPerComponentORCSLPGF :
  NSCoareaGradientStepAPerComponentORCSLPGF
canonicalNSCoareaGradientStepAPerComponentORCSLPGF =
  mkNSCoareaGradientStepAPerComponentORCSLPGF
    "Worker 2 owns the corrected coarea gradient bound receipt surface only."
    refl
    "Record the corrected coarea exponent as r^1 and close StepA_PerComponent by assembling LocalConcentration + pigeon_concentration + corrected coareaGradientBound around local L3 near component C_n."
    refl
    "Create only NSCoareaGradientStepAPerComponentReceipt.agda."
    refl
    "Related surfaces are CorrectedCoareaGradientBoundReceipt, LocalConcentrationPigeonConcentrationReceipt, and NSKatoHessianConfinementReceipt; no other files are touched."
    refl
    "CorrectedCoareaGradientBoundReceipt -> LocalConcentrationPigeonConcentrationReceipt -> StepA_PerComponent -> sup_{partial C_n}|grad lambda2| -> infinity"
    refl
    "f=lambda2+, B(x0,r), K, C_geo, r, C_iso, component C_n, d0, tau0, local L3 near component C_n, diam(C_n) >= d0, layer_thickness >= tau0, ball radius r, K_n -> infinity, conclusion sup_{partial C_n}|grad lambda2| -> infinity"
    refl
    "Candidate-only; no theorem promotion; main runs Agda."
    refl
    "Avoid depending on unavailable math libraries; this is a receipt surface, not a full formal coarea proof, and it stays candidate-only."
    refl
    canonicalNSCoareaGradientStepAPerComponentAssembly
    refl

record NSCoareaGradientStepAPerComponentReceipt : Set where
  constructor mkNSCoareaGradientStepAPerComponentReceipt
  field
    status :
      NSCoareaGradientStepAPerComponentStatus
    statusIsCanonical :
      status ≡ candidateOnlyFailClosed

    linkedReceipts :
      List String
    linkedReceiptsIsCanonical :
      linkedReceipts ≡ linkedReceiptLabels

    linkedReceiptCount :
      Nat
    linkedReceiptCountIsThree :
      linkedReceiptCount ≡ 3

    exactObjectLabelsField :
      List String
    exactObjectLabelsFieldIsCanonical :
      exactObjectLabelsField ≡ exactObjectLabels

    canonicalRows :
      List NSCoareaGradientStepAPerComponentRow
    canonicalRowsIsCanonical :
      canonicalRows ≡ canonicalNSCoareaGradientStepAPerComponentRows

    coareaExponent :
      String
    coareaExponentIsCanonical :
      coareaExponent ≡ coareaExponentText

    stepAPerComponentClosure :
      String
    stepAPerComponentClosureIsCanonical :
      stepAPerComponentClosure ≡ stepAPerComponentText

    conclusion :
      String
    conclusionIsCanonical :
      conclusion ≡ conclusionText

    geometryNote :
      String
    geometryNoteIsCanonical :
      geometryNote ≡ geometryNoteText

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ boundaryText

    formalSurface :
      NSCoareaGradientStepAPerComponentFormalSurface
    formalSurfaceIsCanonical :
      formalSurface ≡ canonicalNSCoareaGradientStepAPerComponentFormalSurface

    routeAssembly :
      NSCoareaGradientStepAPerComponentAssembly
    routeAssemblyIsCanonical :
      routeAssembly ≡ canonicalNSCoareaGradientStepAPerComponentAssembly

    orcslpgf :
      NSCoareaGradientStepAPerComponentORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSCoareaGradientStepAPerComponentORCSLPGF

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalPromoted :
      Bool
    terminalPromotedIsFalse :
      terminalPromoted ≡ false

canonicalNSCoareaGradientStepAPerComponentReceipt :
  NSCoareaGradientStepAPerComponentReceipt
canonicalNSCoareaGradientStepAPerComponentReceipt =
  mkNSCoareaGradientStepAPerComponentReceipt
    candidateOnlyFailClosed
    refl
    linkedReceiptLabels
    refl
    3
    refl
    exactObjectLabels
    refl
    canonicalNSCoareaGradientStepAPerComponentRows
    refl
    coareaExponentText
    refl
    stepAPerComponentText
    refl
    conclusionText
    refl
    geometryNoteText
    refl
    boundaryText
    refl
    canonicalNSCoareaGradientStepAPerComponentFormalSurface
    refl
    canonicalNSCoareaGradientStepAPerComponentAssembly
    refl
    canonicalNSCoareaGradientStepAPerComponentORCSLPGF
    refl
    false
    refl
    false
    refl
    false
    refl

open NSCoareaGradientStepAPerComponentReceipt public
open NSCoareaGradientStepAPerComponentFormalSurface public
open NSCoareaGradientStepAPerComponentAssembly public
open NSCoareaGradientStepAPerComponentORCSLPGF public
