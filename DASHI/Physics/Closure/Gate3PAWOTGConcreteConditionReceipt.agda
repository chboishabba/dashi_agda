module DASHI.Physics.Closure.Gate3PAWOTGConcreteConditionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3FiniteCutoffFrameLowerBoundProofReceipt
  as Finite
import DASHI.Physics.Closure.Gate3GershgorinFiniteFrameBoundReceipt
  as Gershgorin
import DASHI.Physics.Closure.Gate3UniformLowerBoundObstructionReceipt
  as Uniform
import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM15
import DASHI.Physics.Closure.SSP7Plus7Plus1AtomGrammarReceipt as Atom771

------------------------------------------------------------------------
-- Concrete PAWOTG condition for the Gate 3 frame lane.
--
-- The computational sprint made the formerly vague PAWOTG separation
-- condition explicit.  For BT-parameterised Gaussian atoms at prime p and
-- spread sigma, the leakage series is
--
--   sum_{d>=1} p^d exp(- (log p)^2 d^2 / (4 sigma^2)) < 1.
--
-- The binding computed threshold over the corrected inert-prime table is the
-- smallest listed inert prime p=3, with sigma_crit = 0.5052.  The computed
-- comparison table records p=5 at 0.6225, p=13 at 0.7891, p=17 at 0.8334,
-- and the p=19..59 block in the 0.86..1.05 range.  The finite frame claim is
-- conditional on the Gershgorin row-sum condition for normalized atoms:
-- (N - 1) * mu_N < 1 gives A_N >= 1 - (N - 1) * mu_N > 0.  Phase completeness
-- by itself is not sufficient.  The Weil-representation/theta-symbol route is
-- only the attack route for proving the missing Archimedean localization.
-- The p=2 Kozyrev/Haar sigma=0 case is related evidence only, not an SSP
-- p>=3 proof.  Uniform Gate 3, Mosco, no spectral pollution, and Clay
-- promotion remain false.

data PAWOTGConcreteConditionStatus : Set where
  pawotgConcreteGaussianBTConditionRecorded_failClosed :
    PAWOTGConcreteConditionStatus

data PAWOTGPrimeRole : Set where
  smallestInertPrimeP3Binding :
    PAWOTGPrimeRole

  computedInertPrimeThresholdTable :
    PAWOTGPrimeRole

  ramifiedPrimeP7Structural :
    PAWOTGPrimeRole

  correctedCMInertBlockOfNine :
    PAWOTGPrimeRole

canonicalPAWOTGPrimeRoles :
  List PAWOTGPrimeRole
canonicalPAWOTGPrimeRoles =
  smallestInertPrimeP3Binding
  ∷ computedInertPrimeThresholdTable
  ∷ ramifiedPrimeP7Structural
  ∷ correctedCMInertBlockOfNine
  ∷ []

data PAWOTGProofMethod : Set where
  gershgorinPlusBTGaussianLeakageSeries :
    PAWOTGProofMethod

  phaseCompleteDictionaryRequired :
    PAWOTGProofMethod

  phaseBlindDictionaryCollapseObserved :
    PAWOTGProofMethod

  weilRepresentationThetaSymbolAttackRoute :
    PAWOTGProofMethod

canonicalPAWOTGProofMethods :
  List PAWOTGProofMethod
canonicalPAWOTGProofMethods =
  gershgorinPlusBTGaussianLeakageSeries
  ∷ phaseCompleteDictionaryRequired
  ∷ phaseBlindDictionaryCollapseObserved
  ∷ weilRepresentationThetaSymbolAttackRoute
  ∷ []

data PAWOTGOpenObligation : Set where
  proveUniformGaussianBTSeparation :
    PAWOTGOpenObligation

  liftFiniteCutoffEvidenceToContinuum :
    PAWOTGOpenObligation

  proveMoscoAndNoSpectralPollution :
    PAWOTGOpenObligation

  provePGeThreeLocalizationNotJustP2Kozyrev :
    PAWOTGOpenObligation

canonicalPAWOTGOpenObligations :
  List PAWOTGOpenObligation
canonicalPAWOTGOpenObligations =
  proveUniformGaussianBTSeparation
  ∷ liftFiniteCutoffEvidenceToContinuum
  ∷ proveMoscoAndNoSpectralPollution
  ∷ provePGeThreeLocalizationNotJustP2Kozyrev
  ∷ []

data PAWOTGInertPrimeSigmaCritRow : Set where
  inertPrimeP3SigmaCrit05052 :
    PAWOTGInertPrimeSigmaCritRow

  inertPrimeP5SigmaCrit06225 :
    PAWOTGInertPrimeSigmaCritRow

  inertPrimeP13SigmaCrit07891 :
    PAWOTGInertPrimeSigmaCritRow

  inertPrimeP17SigmaCrit08334 :
    PAWOTGInertPrimeSigmaCritRow

  inertPrimeP19ToP59SigmaCrit086To105 :
    PAWOTGInertPrimeSigmaCritRow

canonicalPAWOTGInertPrimeSigmaCritTable :
  List PAWOTGInertPrimeSigmaCritRow
canonicalPAWOTGInertPrimeSigmaCritTable =
  inertPrimeP3SigmaCrit05052
  ∷ inertPrimeP5SigmaCrit06225
  ∷ inertPrimeP13SigmaCrit07891
  ∷ inertPrimeP17SigmaCrit08334
  ∷ inertPrimeP19ToP59SigmaCrit086To105
  ∷ []

data PAWOTGRelatedEvidence : Set where
  kozyrevP2HaarSigmaZero_relatedEvidenceOnly :
    PAWOTGRelatedEvidence

canonicalPAWOTGRelatedEvidence :
  List PAWOTGRelatedEvidence
canonicalPAWOTGRelatedEvidence =
  kozyrevP2HaarSigmaZero_relatedEvidenceOnly
  ∷ []

data Gate3PAWOTGPromotion : Set where

gate3PAWOTGPromotionImpossibleHere :
  Gate3PAWOTGPromotion →
  ⊥
gate3PAWOTGPromotionImpossibleHere ()

sigmaCritP3Milli :
  Nat
sigmaCritP3Milli =
  505

sigmaCritP3TenThousandths :
  Nat
sigmaCritP3TenThousandths =
  5052

sigmaCritP5TenThousandths :
  Nat
sigmaCritP5TenThousandths =
  6225

sigmaCritP13TenThousandths :
  Nat
sigmaCritP13TenThousandths =
  7891

sigmaCritP17TenThousandths :
  Nat
sigmaCritP17TenThousandths =
  8334

sigmaCritP19LowerTenThousandths :
  Nat
sigmaCritP19LowerTenThousandths =
  8600

sigmaCritP59UpperTenThousandths :
  Nat
sigmaCritP59UpperTenThousandths =
  10500

kozyrevP2SigmaTenThousandths :
  Nat
kozyrevP2SigmaTenThousandths =
  0

sigmaCritP7Milli :
  Nat
sigmaCritP7Milli =
  694

sigmaCritP3Decimal :
  String
sigmaCritP3Decimal =
  "0.5052"

sigmaCritP5Decimal :
  String
sigmaCritP5Decimal =
  "0.6225"

sigmaCritP13Decimal :
  String
sigmaCritP13Decimal =
  "0.7891"

sigmaCritP17Decimal :
  String
sigmaCritP17Decimal =
  "0.8334"

sigmaCritP19ToP59RangeDecimal :
  String
sigmaCritP19ToP59RangeDecimal =
  "0.86-1.05"

sigmaCritP7Decimal :
  String
sigmaCritP7Decimal =
  "0.694"

phaseCompleteOverBlindRatioAtN64Tenth :
  Nat
phaseCompleteOverBlindRatioAtN64Tenth =
  55

pawotgLeakageSeriesFormula :
  String
pawotgLeakageSeriesFormula =
  "sum_{d>=1} p^d exp(-((log p)^2 d^2)/(4 sigma^2)) < 1"

pawotgConcreteConditionStatement :
  String
pawotgConcreteConditionStatement =
  "Concrete PAWOTG condition: for BT Gaussian atoms, finite frame separation is conditional on normalized atoms and (N-1)*mu_N < 1; the binding inert-prime threshold is sigma < 0.5052 at p=3, with computed rows p=5 0.6225, p=13 0.7891, p=17 0.8334, and p=19-59 in the 0.86-1.05 range."

pawotgWeilAttackRouteStatement :
  String
pawotgWeilAttackRouteStatement =
  "Attack route only: use Weil-representation/theta-symbol computations to prove the missing Archimedean localization estimate for SSP p>=3 carrier atoms."

pawotgKozyrevP2EvidenceStatement :
  String
pawotgKozyrevP2EvidenceStatement =
  "Related evidence only: the p=2 Kozyrev/Haar model has sigma=0, but it does not prove the SSP p>=3 adelic-to-Archimedean PAWOTG localization theorem."

record Gate3PAWOTGConcreteConditionReceipt : Setω where
  field
    status :
      PAWOTGConcreteConditionStatus

    statusIsFailClosed :
      status ≡ pawotgConcreteGaussianBTConditionRecorded_failClosed

    finiteCutoffReceipt :
      Finite.Gate3FiniteCutoffFrameLowerBoundProofReceipt

    finiteCutoffANPositive :
      Finite.finiteLowerBoundANPositiveRecorded finiteCutoffReceipt
      ≡
      true

    uniformObstructionReceipt :
      Uniform.Gate3UniformLowerBoundObstructionReceipt

    uniformStillOpen :
      Uniform.uniformAOnInfiniteH uniformObstructionReceipt ≡ false

    gershgorinFiniteFrameReceipt :
      Gershgorin.Gate3GershgorinFiniteFrameBoundReceipt

    gershgorinFiniteFrameConditional :
      Gershgorin.finiteLowerBoundConditional
        gershgorinFiniteFrameReceipt
      ≡
      true

    gershgorinNoPhaseCompletenessAlone :
      Gershgorin.phaseCompletenessAloneImpliesA_NPositive
        gershgorinFiniteFrameReceipt
      ≡
      false

    gershgorinUniformSeparationObstructed :
      Gershgorin.uniformSeparationObtained gershgorinFiniteFrameReceipt
      ≡
      false

    cmSplittingReceipt :
      CM15.SSP15CMFieldSplittingCorrectionReceipt

    inertPrimeCountIsNine :
      CM15.inertCount cmSplittingReceipt
      ≡
      CM15.inertCount CM15.canonicalSSP15CMFieldSplittingCorrectionReceipt

    atomGrammarReceipt :
      Atom771.SSP7Plus7Plus1AtomGrammarReceipt

    atomGrammarNoClay :
      Atom771.clayPromoted atomGrammarReceipt ≡ false

    leakageSeriesFormula :
      String

    leakageSeriesFormulaIsCanonical :
      leakageSeriesFormula ≡ pawotgLeakageSeriesFormula

    sigmaCritP3 :
      Nat

    sigmaCritP3Is505Milli :
      sigmaCritP3 ≡ sigmaCritP3Milli

    sigmaCritP3Exact :
      Nat

    sigmaCritP3ExactIs5052TenThousandths :
      sigmaCritP3Exact ≡ sigmaCritP3TenThousandths

    sigmaCritP5 :
      Nat

    sigmaCritP5Is6225TenThousandths :
      sigmaCritP5 ≡ sigmaCritP5TenThousandths

    sigmaCritP13 :
      Nat

    sigmaCritP13Is7891TenThousandths :
      sigmaCritP13 ≡ sigmaCritP13TenThousandths

    sigmaCritP17 :
      Nat

    sigmaCritP17Is8334TenThousandths :
      sigmaCritP17 ≡ sigmaCritP17TenThousandths

    sigmaCritP19Lower :
      Nat

    sigmaCritP19LowerIs8600TenThousandths :
      sigmaCritP19Lower ≡ sigmaCritP19LowerTenThousandths

    sigmaCritP59Upper :
      Nat

    sigmaCritP59UpperIs10500TenThousandths :
      sigmaCritP59Upper ≡ sigmaCritP59UpperTenThousandths

    sigmaCritP7 :
      Nat

    sigmaCritP7Is694Milli :
      sigmaCritP7 ≡ sigmaCritP7Milli

    bindingConstraintFromP3 :
      Bool

    bindingConstraintFromP3IsTrue :
      bindingConstraintFromP3 ≡ true

    pawotgConditionSigmaBelowP3 :
      Bool

    pawotgConditionSigmaBelowP3IsConcreteTarget :
      pawotgConditionSigmaBelowP3 ≡ true

    computedBySeries :
      Bool

    computedBySeriesIsTrue :
      computedBySeries ≡ true

    inertPrimeSigmaCritTable :
      List PAWOTGInertPrimeSigmaCritRow

    inertPrimeSigmaCritTableIsCanonical :
      inertPrimeSigmaCritTable ≡ canonicalPAWOTGInertPrimeSigmaCritTable

    weilRepresentationAttackRoute :
      Bool

    weilRepresentationAttackRouteIsTrue :
      weilRepresentationAttackRoute ≡ true

    kozyrevP2Sigma :
      Nat

    kozyrevP2SigmaIsZero :
      kozyrevP2Sigma ≡ kozyrevP2SigmaTenThousandths

    kozyrevP2RelatedEvidenceOnly :
      Bool

    kozyrevP2RelatedEvidenceOnlyIsTrue :
      kozyrevP2RelatedEvidenceOnly ≡ true

    proofByGershgorinPlusBTGeometry :
      Bool

    proofByGershgorinPlusBTGeometryIsTrue :
      proofByGershgorinPlusBTGeometry ≡ true

    finiteCutoffFrameLowerBoundConditional :
      Bool

    finiteCutoffFrameLowerBoundConditionalIsTrue :
      finiteCutoffFrameLowerBoundConditional ≡ true

    uniformLowerBoundEquivalentToPAWOTG :
      Bool

    uniformLowerBoundEquivalentToPAWOTGIsFalse :
      uniformLowerBoundEquivalentToPAWOTG ≡ false

    phaseCompleteAloneImpliesFiniteLowerBound :
      Bool

    phaseCompleteAloneImpliesFiniteLowerBoundIsFalse :
      phaseCompleteAloneImpliesFiniteLowerBound ≡ false

    pawotgUniformityOpen :
      Bool

    pawotgUniformityOpenIsTrue :
      pawotgUniformityOpen ≡ true

    phaseCompleteVsBlindRatioAtN64 :
      Nat

    phaseCompleteVsBlindRatioAtN64Is55Tenths :
      phaseCompleteVsBlindRatioAtN64
      ≡
      phaseCompleteOverBlindRatioAtN64Tenth

    roles :
      List PAWOTGPrimeRole

    rolesAreCanonical :
      roles ≡ canonicalPAWOTGPrimeRoles

    proofMethods :
      List PAWOTGProofMethod

    proofMethodsAreCanonical :
      proofMethods ≡ canonicalPAWOTGProofMethods

    openObligations :
      List PAWOTGOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalPAWOTGOpenObligations

    relatedEvidence :
      List PAWOTGRelatedEvidence

    relatedEvidenceIsCanonical :
      relatedEvidence ≡ canonicalPAWOTGRelatedEvidence

    statement :
      String

    statementIsCanonical :
      statement ≡ pawotgConcreteConditionStatement

    weilAttackRouteStatement :
      String

    weilAttackRouteStatementIsCanonical :
      weilAttackRouteStatement ≡ pawotgWeilAttackRouteStatement

    kozyrevP2EvidenceStatement :
      String

    kozyrevP2EvidenceStatementIsCanonical :
      kozyrevP2EvidenceStatement ≡ pawotgKozyrevP2EvidenceStatement

    continuumGate3Promoted :
      Bool

    continuumGate3PromotedIsFalse :
      continuumGate3Promoted ≡ false

    clayGate3Promoted :
      Bool

    clayGate3PromotedIsFalse :
      clayGate3Promoted ≡ false

    promotions :
      List Gate3PAWOTGPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Gate3PAWOTGPromotion →
      ⊥

open Gate3PAWOTGConcreteConditionReceipt public

canonicalGate3PAWOTGConcreteConditionReceipt :
  Gate3PAWOTGConcreteConditionReceipt
canonicalGate3PAWOTGConcreteConditionReceipt =
  record
    { status =
        pawotgConcreteGaussianBTConditionRecorded_failClosed
    ; statusIsFailClosed =
        refl
    ; finiteCutoffReceipt =
        Finite.canonicalGate3FiniteCutoffFrameLowerBoundProofReceipt
    ; finiteCutoffANPositive =
        refl
    ; uniformObstructionReceipt =
        Uniform.canonicalGate3UniformLowerBoundObstructionReceipt
    ; uniformStillOpen =
        refl
    ; gershgorinFiniteFrameReceipt =
        Gershgorin.canonicalGate3GershgorinFiniteFrameBoundReceipt
    ; gershgorinFiniteFrameConditional =
        refl
    ; gershgorinNoPhaseCompletenessAlone =
        refl
    ; gershgorinUniformSeparationObstructed =
        refl
    ; cmSplittingReceipt =
        CM15.canonicalSSP15CMFieldSplittingCorrectionReceipt
    ; inertPrimeCountIsNine =
        refl
    ; atomGrammarReceipt =
        Atom771.canonicalSSP7Plus7Plus1AtomGrammarReceipt
    ; atomGrammarNoClay =
        refl
    ; leakageSeriesFormula =
        pawotgLeakageSeriesFormula
    ; leakageSeriesFormulaIsCanonical =
        refl
    ; sigmaCritP3 =
        sigmaCritP3Milli
    ; sigmaCritP3Is505Milli =
        refl
    ; sigmaCritP3Exact =
        sigmaCritP3TenThousandths
    ; sigmaCritP3ExactIs5052TenThousandths =
        refl
    ; sigmaCritP5 =
        sigmaCritP5TenThousandths
    ; sigmaCritP5Is6225TenThousandths =
        refl
    ; sigmaCritP13 =
        sigmaCritP13TenThousandths
    ; sigmaCritP13Is7891TenThousandths =
        refl
    ; sigmaCritP17 =
        sigmaCritP17TenThousandths
    ; sigmaCritP17Is8334TenThousandths =
        refl
    ; sigmaCritP19Lower =
        sigmaCritP19LowerTenThousandths
    ; sigmaCritP19LowerIs8600TenThousandths =
        refl
    ; sigmaCritP59Upper =
        sigmaCritP59UpperTenThousandths
    ; sigmaCritP59UpperIs10500TenThousandths =
        refl
    ; sigmaCritP7 =
        sigmaCritP7Milli
    ; sigmaCritP7Is694Milli =
        refl
    ; bindingConstraintFromP3 =
        true
    ; bindingConstraintFromP3IsTrue =
        refl
    ; pawotgConditionSigmaBelowP3 =
        true
    ; pawotgConditionSigmaBelowP3IsConcreteTarget =
        refl
    ; computedBySeries =
        true
    ; computedBySeriesIsTrue =
        refl
    ; inertPrimeSigmaCritTable =
        canonicalPAWOTGInertPrimeSigmaCritTable
    ; inertPrimeSigmaCritTableIsCanonical =
        refl
    ; weilRepresentationAttackRoute =
        true
    ; weilRepresentationAttackRouteIsTrue =
        refl
    ; kozyrevP2Sigma =
        kozyrevP2SigmaTenThousandths
    ; kozyrevP2SigmaIsZero =
        refl
    ; kozyrevP2RelatedEvidenceOnly =
        true
    ; kozyrevP2RelatedEvidenceOnlyIsTrue =
        refl
    ; proofByGershgorinPlusBTGeometry =
        true
    ; proofByGershgorinPlusBTGeometryIsTrue =
        refl
    ; finiteCutoffFrameLowerBoundConditional =
        true
    ; finiteCutoffFrameLowerBoundConditionalIsTrue =
        refl
    ; uniformLowerBoundEquivalentToPAWOTG =
        false
    ; uniformLowerBoundEquivalentToPAWOTGIsFalse =
        refl
    ; phaseCompleteAloneImpliesFiniteLowerBound =
        false
    ; phaseCompleteAloneImpliesFiniteLowerBoundIsFalse =
        refl
    ; pawotgUniformityOpen =
        true
    ; pawotgUniformityOpenIsTrue =
        refl
    ; phaseCompleteVsBlindRatioAtN64 =
        phaseCompleteOverBlindRatioAtN64Tenth
    ; phaseCompleteVsBlindRatioAtN64Is55Tenths =
        refl
    ; roles =
        canonicalPAWOTGPrimeRoles
    ; rolesAreCanonical =
        refl
    ; proofMethods =
        canonicalPAWOTGProofMethods
    ; proofMethodsAreCanonical =
        refl
    ; openObligations =
        canonicalPAWOTGOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; relatedEvidence =
        canonicalPAWOTGRelatedEvidence
    ; relatedEvidenceIsCanonical =
        refl
    ; statement =
        pawotgConcreteConditionStatement
    ; statementIsCanonical =
        refl
    ; weilAttackRouteStatement =
        pawotgWeilAttackRouteStatement
    ; weilAttackRouteStatementIsCanonical =
        refl
    ; kozyrevP2EvidenceStatement =
        pawotgKozyrevP2EvidenceStatement
    ; kozyrevP2EvidenceStatementIsCanonical =
        refl
    ; continuumGate3Promoted =
        false
    ; continuumGate3PromotedIsFalse =
        refl
    ; clayGate3Promoted =
        false
    ; clayGate3PromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        gate3PAWOTGPromotionImpossibleHere
    }
