module DASHI.Physics.Closure.NSFourierOutputPushforwardBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSLeiRenTianFourierOutputCouplingBoundary
  as FourierCoupling
import DASHI.Physics.Closure.NSLeiRenTianGreatCircleCriterionBoundary
  as LRT
import DASHI.Physics.Closure.NSLeiRenTianOutputSupportTransferBoundary
  as OutputSupport
import DASHI.Physics.Closure.NSTriadicAngularDefectSheafLeakageBoundary
  as Sheaf

------------------------------------------------------------------------
-- NS A4 Fourier-output pushforward boundary.
--
-- Analytic target:
--
--   Phi(theta1,theta2) = normalize(theta1 + theta2)
--
-- pushes localized non-antipodal input angular mass to the Fourier triadic
-- output-direction measure used by the A4 LRT physical-to-Fourier coupling.
--
-- This is a child proof-contract surface only.  It records the map, the
-- antipodal exclusion/null-set obligation, the pushforward angular measure,
-- the coplanar half-angle sanity check, the off-antipodal Lipschitz bound,
-- and the residual blockers.  It does not prove the Sard/Fubini step, does
-- not prove quantitative measure equivalence, does not prove the A4 output
-- support transfer, and does not promote Navier-Stokes Clay.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support anchors.

fourierCouplingBoundaryReference : String
fourierCouplingBoundaryReference =
  "DASHI.Physics.Closure.NSLeiRenTianFourierOutputCouplingBoundary"

outputSupportTransferBoundaryReference : String
outputSupportTransferBoundaryReference =
  "DASHI.Physics.Closure.NSLeiRenTianOutputSupportTransferBoundary"

triadicSheafOutputProjectionReference : String
triadicSheafOutputProjectionReference =
  "DASHI.Physics.Closure.NSTriadicAngularDefectSheafLeakageBoundary.OutputProjection"

leiRenTianGreatCircleBoundaryReference : String
leiRenTianGreatCircleBoundaryReference =
  "DASHI.Physics.Closure.NSLeiRenTianGreatCircleCriterionBoundary"

fourierCouplingBoundaryImported : Bool
fourierCouplingBoundaryImported =
  true

outputSupportTransferBoundaryImported : Bool
outputSupportTransferBoundaryImported =
  true

triadicSheafBoundaryImported : Bool
triadicSheafBoundaryImported =
  true

leiRenTianBoundaryImported : Bool
leiRenTianBoundaryImported =
  true

record ImportedFourierOutputPushforwardSupport : Set where
  field
    couplingMapCarrier :
      FourierCoupling.FourierOutputDirectionMapCarrier
    couplingMapCarrierIsCanonical :
      couplingMapCarrier
        ≡ FourierCoupling.canonicalFourierOutputDirectionMapCarrier
    outputSupportRichness :
      OutputSupport.FourierTriadicOutputDirectionRichness
    outputSupportRichnessIsCanonical :
      outputSupportRichness
        ≡ OutputSupport.canonicalFourierTriadicOutputDirectionRichness
    sheafOutputProjection :
      Sheaf.OutputProjection
    sheafOutputProjectionIsCanonical :
      sheafOutputProjection ≡ Sheaf.canonicalOutputProjection
    lrtGreatCircleProperty :
      LRT.GreatCircleHittingProperty
    lrtGreatCirclePropertyIsCanonical :
      lrtGreatCircleProperty ≡ LRT.canonicalGreatCircleHittingProperty
    couplingImportedTrue :
      fourierCouplingBoundaryImported ≡ true
    outputSupportImportedTrue :
      outputSupportTransferBoundaryImported ≡ true
    sheafImportedTrue :
      triadicSheafBoundaryImported ≡ true
    lrtImportedTrue :
      leiRenTianBoundaryImported ≡ true

canonicalImportedFourierOutputPushforwardSupport :
  ImportedFourierOutputPushforwardSupport
canonicalImportedFourierOutputPushforwardSupport =
  record
    { couplingMapCarrier =
        FourierCoupling.canonicalFourierOutputDirectionMapCarrier
    ; couplingMapCarrierIsCanonical =
        refl
    ; outputSupportRichness =
        OutputSupport.canonicalFourierTriadicOutputDirectionRichness
    ; outputSupportRichnessIsCanonical =
        refl
    ; sheafOutputProjection =
        Sheaf.canonicalOutputProjection
    ; sheafOutputProjectionIsCanonical =
        refl
    ; lrtGreatCircleProperty =
        LRT.canonicalGreatCircleHittingProperty
    ; lrtGreatCirclePropertyIsCanonical =
        refl
    ; couplingImportedTrue =
        refl
    ; outputSupportImportedTrue =
        refl
    ; sheafImportedTrue =
        refl
    ; lrtImportedTrue =
        refl
    }

------------------------------------------------------------------------
-- Phi map and angular-measure carriers.

data InputAngularPairCarrier : Set where
  nonAntipodalInputDirectionPair :
    LRT.SphereDirectionCarrier →
    LRT.SphereDirectionCarrier →
    InputAngularPairCarrier

data AntipodalExclusionCarrier : Set where
  antipodalDiagonalExcludedAsNullSet :
    InputAngularPairCarrier →
    AntipodalExclusionCarrier

data FourierOutputPhiMap : Set where
  Phi-theta1-theta2-normalizeSum :
    InputAngularPairCarrier →
    AntipodalExclusionCarrier →
    FourierOutputPhiMap

data PushforwardAngularMeasureCarrier : Set where
  PhiPushforwardOfInputAngularProductMeasure :
    FourierOutputPhiMap →
    Sheaf.OutputProjection →
    PushforwardAngularMeasureCarrier

data CoplanarHalfAngleSanityCheck : Set where
  coplanarHalfAngleDerivativeHasConstantOneHalfNorm :
    FourierOutputPhiMap →
    CoplanarHalfAngleSanityCheck

data OffAntipodalLipschitzControl : Set where
  PhiLocallyLipschitzAwayFromAntipodalDiagonal :
    FourierOutputPhiMap →
    AntipodalExclusionCarrier →
    OffAntipodalLipschitzControl

data SardFubiniNullSetObligation : Set where
  antipodalTubeMassIsQuadraticInTubeWidth :
    AntipodalExclusionCarrier →
    SardFubiniNullSetObligation

data OutputProjectionCompatibility : Set where
  PhiOutputAgreesWithTriadicSheafPiOut :
    PushforwardAngularMeasureCarrier →
    FourierCoupling.FourierOutputDirectionMapCarrier →
    Sheaf.OutputProjection →
    OutputProjectionCompatibility

data FourierOutputPushforwardTarget : Set where
  PhiPushforwardSupportsA4FourierOutputRichness :
    PushforwardAngularMeasureCarrier →
    CoplanarHalfAngleSanityCheck →
    OffAntipodalLipschitzControl →
    SardFubiniNullSetObligation →
    OutputProjectionCompatibility →
    OutputSupport.FourierTriadicOutputDirectionRichness →
    FourierOutputPushforwardTarget

canonicalInputAngularPairCarrier :
  InputAngularPairCarrier
canonicalInputAngularPairCarrier =
  nonAntipodalInputDirectionPair
    LRT.canonicalSphereDirectionCarrier
    LRT.canonicalSphereDirectionCarrier

canonicalAntipodalExclusionCarrier :
  AntipodalExclusionCarrier
canonicalAntipodalExclusionCarrier =
  antipodalDiagonalExcludedAsNullSet
    canonicalInputAngularPairCarrier

canonicalFourierOutputPhiMap :
  FourierOutputPhiMap
canonicalFourierOutputPhiMap =
  Phi-theta1-theta2-normalizeSum
    canonicalInputAngularPairCarrier
    canonicalAntipodalExclusionCarrier

canonicalPushforwardAngularMeasureCarrier :
  PushforwardAngularMeasureCarrier
canonicalPushforwardAngularMeasureCarrier =
  PhiPushforwardOfInputAngularProductMeasure
    canonicalFourierOutputPhiMap
    Sheaf.canonicalOutputProjection

canonicalCoplanarHalfAngleSanityCheck :
  CoplanarHalfAngleSanityCheck
canonicalCoplanarHalfAngleSanityCheck =
  coplanarHalfAngleDerivativeHasConstantOneHalfNorm
    canonicalFourierOutputPhiMap

canonicalOffAntipodalLipschitzControl :
  OffAntipodalLipschitzControl
canonicalOffAntipodalLipschitzControl =
  PhiLocallyLipschitzAwayFromAntipodalDiagonal
    canonicalFourierOutputPhiMap
    canonicalAntipodalExclusionCarrier

canonicalSardFubiniNullSetObligation :
  SardFubiniNullSetObligation
canonicalSardFubiniNullSetObligation =
  antipodalTubeMassIsQuadraticInTubeWidth
    canonicalAntipodalExclusionCarrier

canonicalOutputProjectionCompatibility :
  OutputProjectionCompatibility
canonicalOutputProjectionCompatibility =
  PhiOutputAgreesWithTriadicSheafPiOut
    canonicalPushforwardAngularMeasureCarrier
    FourierCoupling.canonicalFourierOutputDirectionMapCarrier
    Sheaf.canonicalOutputProjection

canonicalFourierOutputPushforwardTarget :
  FourierOutputPushforwardTarget
canonicalFourierOutputPushforwardTarget =
  PhiPushforwardSupportsA4FourierOutputRichness
    canonicalPushforwardAngularMeasureCarrier
    canonicalCoplanarHalfAngleSanityCheck
    canonicalOffAntipodalLipschitzControl
    canonicalSardFubiniNullSetObligation
    canonicalOutputProjectionCompatibility
    OutputSupport.canonicalFourierTriadicOutputDirectionRichness

------------------------------------------------------------------------
-- Sub-obligations, sanity checks, and blockers.

data FourierOutputPushforwardObligation : Set where
  definePhiNormalizeSumOnNonAntipodalPairs :
    FourierOutputPushforwardObligation
  excludeAntipodalDiagonalAsProductMeasureNullSet :
    FourierOutputPushforwardObligation
  definePhiPushforwardAngularMeasure :
    FourierOutputPushforwardObligation
  verifyCoplanarHalfAngleDerivativeSanityCheck :
    FourierOutputPushforwardObligation
  proveLocalLipschitzBoundAwayFromAntipodalDiagonal :
    FourierOutputPushforwardObligation
  proveSardFubiniAntipodalTubeDiscard :
    FourierOutputPushforwardObligation
  comparePhiPushforwardWithSheafOutputProjection :
    FourierOutputPushforwardObligation
  feedOutputPushforwardIntoA4Coupling :
    FourierOutputPushforwardObligation

canonicalFourierOutputPushforwardObligations :
  List FourierOutputPushforwardObligation
canonicalFourierOutputPushforwardObligations =
  definePhiNormalizeSumOnNonAntipodalPairs
  ∷ excludeAntipodalDiagonalAsProductMeasureNullSet
  ∷ definePhiPushforwardAngularMeasure
  ∷ verifyCoplanarHalfAngleDerivativeSanityCheck
  ∷ proveLocalLipschitzBoundAwayFromAntipodalDiagonal
  ∷ proveSardFubiniAntipodalTubeDiscard
  ∷ comparePhiPushforwardWithSheafOutputProjection
  ∷ feedOutputPushforwardIntoA4Coupling
  ∷ []

fourierOutputPushforwardObligationCount : Nat
fourierOutputPushforwardObligationCount =
  listLength canonicalFourierOutputPushforwardObligations

fourierOutputPushforwardObligationCountIs8 :
  fourierOutputPushforwardObligationCount ≡ 8
fourierOutputPushforwardObligationCountIs8 =
  refl

data PhiMapSanityRow : Set where
  PhiFormulaRecordedAsNormalizeThetaOnePlusThetaTwo :
    PhiMapSanityRow
  antipodalPairThetaOnePlusThetaTwoZero :
    PhiMapSanityRow
  coplanarHalfAngleFormulaRecorded :
    PhiMapSanityRow
  coplanarDerivativeNormOneHalfRecorded :
    PhiMapSanityRow
  productUniformSanityExpectedUniformOutput :
    PhiMapSanityRow
  sanityCheckIsDiagnosticNotProof :
    PhiMapSanityRow

canonicalPhiMapSanityRows :
  List PhiMapSanityRow
canonicalPhiMapSanityRows =
  PhiFormulaRecordedAsNormalizeThetaOnePlusThetaTwo
  ∷ antipodalPairThetaOnePlusThetaTwoZero
  ∷ coplanarHalfAngleFormulaRecorded
  ∷ coplanarDerivativeNormOneHalfRecorded
  ∷ productUniformSanityExpectedUniformOutput
  ∷ sanityCheckIsDiagnosticNotProof
  ∷ []

phiMapSanityRowCount : Nat
phiMapSanityRowCount =
  listLength canonicalPhiMapSanityRows

phiMapSanityRowCountIs6 :
  phiMapSanityRowCount ≡ 6
phiMapSanityRowCountIs6 =
  refl

data FourierOutputPushforwardBlocker : Set where
  missingSardFubiniProofForAntipodalTube :
    FourierOutputPushforwardBlocker
  missingQuantitativeJacobianLowerBound :
    FourierOutputPushforwardBlocker
  missingPhysicalToFrequencyFrameCoupling :
    FourierOutputPushforwardBlocker
  missingOutputSupportLiftIntoAbelMeasure :
    FourierOutputPushforwardBlocker
  missingA4Completion :
    FourierOutputPushforwardBlocker
  missingClayPromotion :
    FourierOutputPushforwardBlocker

canonicalFourierOutputPushforwardBlockers :
  List FourierOutputPushforwardBlocker
canonicalFourierOutputPushforwardBlockers =
  missingSardFubiniProofForAntipodalTube
  ∷ missingQuantitativeJacobianLowerBound
  ∷ missingPhysicalToFrequencyFrameCoupling
  ∷ missingOutputSupportLiftIntoAbelMeasure
  ∷ missingA4Completion
  ∷ missingClayPromotion
  ∷ []

fourierOutputPushforwardBlockerCount : Nat
fourierOutputPushforwardBlockerCount =
  listLength canonicalFourierOutputPushforwardBlockers

fourierOutputPushforwardBlockerCountIs6 :
  fourierOutputPushforwardBlockerCount ≡ 6
fourierOutputPushforwardBlockerCountIs6 =
  refl

data FourierOutputPushforwardStatusRow : Set where
  childBoundaryRecordedStatus :
    FourierOutputPushforwardStatusRow
  PhiMapCarrierRecordedStatus :
    FourierOutputPushforwardStatusRow
  antipodalExclusionRecordedStatus :
    FourierOutputPushforwardStatusRow
  pushforwardMeasureCarrierRecordedStatus :
    FourierOutputPushforwardStatusRow
  coplanarHalfAngleSanityRecordedStatus :
    FourierOutputPushforwardStatusRow
  offAntipodalLipschitzTargetRecordedStatus :
    FourierOutputPushforwardStatusRow
  residualBlockersRemainStatus :
    FourierOutputPushforwardStatusRow
  allTheoremAndPromotionFlagsFalseStatus :
    FourierOutputPushforwardStatusRow

canonicalFourierOutputPushforwardStatusRows :
  List FourierOutputPushforwardStatusRow
canonicalFourierOutputPushforwardStatusRows =
  childBoundaryRecordedStatus
  ∷ PhiMapCarrierRecordedStatus
  ∷ antipodalExclusionRecordedStatus
  ∷ pushforwardMeasureCarrierRecordedStatus
  ∷ coplanarHalfAngleSanityRecordedStatus
  ∷ offAntipodalLipschitzTargetRecordedStatus
  ∷ residualBlockersRemainStatus
  ∷ allTheoremAndPromotionFlagsFalseStatus
  ∷ []

fourierOutputPushforwardStatusRowCount : Nat
fourierOutputPushforwardStatusRowCount =
  listLength canonicalFourierOutputPushforwardStatusRows

fourierOutputPushforwardStatusRowCountIs8 :
  fourierOutputPushforwardStatusRowCount ≡ 8
fourierOutputPushforwardStatusRowCountIs8 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data FourierOutputPushforwardPromotion : Set where

fourierOutputPushforwardPromotionImpossibleHere :
  FourierOutputPushforwardPromotion →
  ⊥
fourierOutputPushforwardPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed flags.

NSFourierOutputPushforwardBoundaryRecorded : Bool
NSFourierOutputPushforwardBoundaryRecorded =
  true

PhiNormalizeSumMapRecorded : Bool
PhiNormalizeSumMapRecorded =
  true

antipodalExclusionNullSetRecorded : Bool
antipodalExclusionNullSetRecorded =
  true

pushforwardAngularMeasureRecorded : Bool
pushforwardAngularMeasureRecorded =
  true

coplanarHalfAngleSanityCheckRecorded : Bool
coplanarHalfAngleSanityCheckRecorded =
  true

offAntipodalLipschitzBoundTargetRecorded : Bool
offAntipodalLipschitzBoundTargetRecorded =
  true

SardFubiniAntipodalNullSetProved : Bool
SardFubiniAntipodalNullSetProved =
  false

PhiPushforwardMeasureEquivalenceProved : Bool
PhiPushforwardMeasureEquivalenceProved =
  false

FourierOutputPushforwardTheoremProved : Bool
FourierOutputPushforwardTheoremProved =
  false

A4LRTFourierOutputCouplingProved : Bool
A4LRTFourierOutputCouplingProved =
  false

fullLocalDefectMonotonicity : Bool
fullLocalDefectMonotonicity =
  false

mechanismExhaustionForFullClayNS : Bool
mechanismExhaustionForFullClayNS =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordsBoundary :
  NSFourierOutputPushforwardBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsPhiNormalizeSumMap :
  PhiNormalizeSumMapRecorded ≡ true
recordsPhiNormalizeSumMap =
  refl

recordsAntipodalExclusionNullSet :
  antipodalExclusionNullSetRecorded ≡ true
recordsAntipodalExclusionNullSet =
  refl

recordsPushforwardAngularMeasure :
  pushforwardAngularMeasureRecorded ≡ true
recordsPushforwardAngularMeasure =
  refl

recordsCoplanarHalfAngleSanityCheck :
  coplanarHalfAngleSanityCheckRecorded ≡ true
recordsCoplanarHalfAngleSanityCheck =
  refl

recordsOffAntipodalLipschitzBoundTarget :
  offAntipodalLipschitzBoundTargetRecorded ≡ true
recordsOffAntipodalLipschitzBoundTarget =
  refl

keepsSardFubiniAntipodalNullSetFalse :
  SardFubiniAntipodalNullSetProved ≡ false
keepsSardFubiniAntipodalNullSetFalse =
  refl

keepsPhiPushforwardMeasureEquivalenceFalse :
  PhiPushforwardMeasureEquivalenceProved ≡ false
keepsPhiPushforwardMeasureEquivalenceFalse =
  refl

keepsFourierOutputPushforwardTheoremFalse :
  FourierOutputPushforwardTheoremProved ≡ false
keepsFourierOutputPushforwardTheoremFalse =
  refl

keepsA4LRTFourierOutputCouplingFalse :
  A4LRTFourierOutputCouplingProved ≡ false
keepsA4LRTFourierOutputCouplingFalse =
  refl

keepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

organizationString : String
organizationString =
  "O: Worker 3 owns the A4 Fourier-output pushforward child boundary for Phi(theta1,theta2)=normalize(theta1+theta2)."

requirementString : String
requirementString =
  "R: Record the Phi map, antipodal exclusion/null set, pushforward angular measure, coplanar half-angle sanity check, Lipschitz off-antipodal target, and residual blockers."

codeArtifactString : String
codeArtifactString =
  "C: NSFourierOutputPushforwardBoundary exports typed carriers, canonical obligations, fail-closed flags, and a receipt consumed by the larger A4 coupling lane."

stateString : String
stateString =
  "S: The child boundary is checked, but Sard/Fubini, quantitative Jacobian, physical-to-frequency coupling, output support lift, and A4 completion remain open."

latticeString : String
latticeString =
  "L: non-antipodal input directions -> Phi normalize-sum map -> pushforward output angular measure -> output projection compatibility -> future A4 transfer."

proposalString : String
proposalString =
  "P: Promote only after proving the antipodal null-set discard, off-antipodal Jacobian control, sheaf projection compatibility, and output-support lift in the analytic A4 framework."

governanceString : String
governanceString =
  "G: This is fail-closed theorem-contract bookkeeping; all proof, A4, Clay, and terminal promotion flags remain false."

gapString : String
gapString =
  "F: Remaining gaps are Sard/Fubini antipodal tube control, quantitative pushforward control, Whitney/frame physical-to-frequency coupling, Abel output-support lift, and Clay promotion."

------------------------------------------------------------------------
-- Canonical receipt.

record NSFourierOutputPushforwardBoundary : Set where
  constructor nsFourierOutputPushforwardBoundary
  field
    importedSupport :
      ImportedFourierOutputPushforwardSupport
    importedSupportIsCanonical :
      importedSupport ≡ canonicalImportedFourierOutputPushforwardSupport
    inputAngularPair :
      InputAngularPairCarrier
    inputAngularPairIsCanonical :
      inputAngularPair ≡ canonicalInputAngularPairCarrier
    antipodalExclusion :
      AntipodalExclusionCarrier
    antipodalExclusionIsCanonical :
      antipodalExclusion ≡ canonicalAntipodalExclusionCarrier
    PhiMap :
      FourierOutputPhiMap
    PhiMapIsCanonical :
      PhiMap ≡ canonicalFourierOutputPhiMap
    pushforwardMeasure :
      PushforwardAngularMeasureCarrier
    pushforwardMeasureIsCanonical :
      pushforwardMeasure ≡ canonicalPushforwardAngularMeasureCarrier
    halfAngleSanity :
      CoplanarHalfAngleSanityCheck
    halfAngleSanityIsCanonical :
      halfAngleSanity ≡ canonicalCoplanarHalfAngleSanityCheck
    offAntipodalLipschitz :
      OffAntipodalLipschitzControl
    offAntipodalLipschitzIsCanonical :
      offAntipodalLipschitz ≡ canonicalOffAntipodalLipschitzControl
    sardFubiniObligation :
      SardFubiniNullSetObligation
    sardFubiniObligationIsCanonical :
      sardFubiniObligation ≡ canonicalSardFubiniNullSetObligation
    outputProjectionCompatibility :
      OutputProjectionCompatibility
    outputProjectionCompatibilityIsCanonical :
      outputProjectionCompatibility ≡ canonicalOutputProjectionCompatibility
    pushforwardTarget :
      FourierOutputPushforwardTarget
    pushforwardTargetIsCanonical :
      pushforwardTarget ≡ canonicalFourierOutputPushforwardTarget
    obligations :
      List FourierOutputPushforwardObligation
    obligationsAreCanonical :
      obligations ≡ canonicalFourierOutputPushforwardObligations
    sanityRows :
      List PhiMapSanityRow
    sanityRowsAreCanonical :
      sanityRows ≡ canonicalPhiMapSanityRows
    blockers :
      List FourierOutputPushforwardBlocker
    blockersAreCanonical :
      blockers ≡ canonicalFourierOutputPushforwardBlockers
    statuses :
      List FourierOutputPushforwardStatusRow
    statusesAreCanonical :
      statuses ≡ canonicalFourierOutputPushforwardStatusRows
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString
    boundaryRecorded :
      NSFourierOutputPushforwardBoundaryRecorded ≡ true
    PhiMapRecorded :
      PhiNormalizeSumMapRecorded ≡ true
    antipodalNullSetRecorded :
      antipodalExclusionNullSetRecorded ≡ true
    pushforwardRecorded :
      pushforwardAngularMeasureRecorded ≡ true
    halfAngleRecorded :
      coplanarHalfAngleSanityCheckRecorded ≡ true
    lipschitzTargetRecorded :
      offAntipodalLipschitzBoundTargetRecorded ≡ true
    sardFubiniProofFalse :
      SardFubiniAntipodalNullSetProved ≡ false
    pushforwardEquivalenceProofFalse :
      PhiPushforwardMeasureEquivalenceProved ≡ false
    pushforwardTheoremFalse :
      FourierOutputPushforwardTheoremProved ≡ false
    A4CouplingProofFalse :
      A4LRTFourierOutputCouplingProved ≡ false
    claySolvedFalse :
      fullClayNSSolved ≡ false
    clayPromotionFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

open NSFourierOutputPushforwardBoundary public

canonicalNSFourierOutputPushforwardBoundary :
  NSFourierOutputPushforwardBoundary
canonicalNSFourierOutputPushforwardBoundary =
  nsFourierOutputPushforwardBoundary
    canonicalImportedFourierOutputPushforwardSupport
    refl
    canonicalInputAngularPairCarrier
    refl
    canonicalAntipodalExclusionCarrier
    refl
    canonicalFourierOutputPhiMap
    refl
    canonicalPushforwardAngularMeasureCarrier
    refl
    canonicalCoplanarHalfAngleSanityCheck
    refl
    canonicalOffAntipodalLipschitzControl
    refl
    canonicalSardFubiniNullSetObligation
    refl
    canonicalOutputProjectionCompatibility
    refl
    canonicalFourierOutputPushforwardTarget
    refl
    canonicalFourierOutputPushforwardObligations
    refl
    canonicalPhiMapSanityRows
    refl
    canonicalFourierOutputPushforwardBlockers
    refl
    canonicalFourierOutputPushforwardStatusRows
    refl
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

