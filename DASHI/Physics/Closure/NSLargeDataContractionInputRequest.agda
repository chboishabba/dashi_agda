module DASHI.Physics.Closure.NSLargeDataContractionInputRequest where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes large-data contraction input request.
--
-- This receipt records the requested C2 mathematical input only.  The
-- H^{11/8} large-data contraction route is stated as a target whose missing
-- ingredient is a low-frequency Lipschitz bound compatible with the
-- adjacent-only high-frequency damping and finite low-frequency ODE sector.
-- No contraction theorem, smooth global regularity theorem, or Clay
-- promotion is constructed here.

data NSLargeDataContractionInputStatus : Set where
  largeDataContractionInputRequested :
    NSLargeDataContractionInputStatus

  hElevenEighthsRouteRecorded :
    NSLargeDataContractionInputStatus

  lowFrequencyLipschitzBoundMissing :
    NSLargeDataContractionInputStatus

  noRegularityOrClayPromotion :
    NSLargeDataContractionInputStatus

canonicalNSLargeDataContractionInputStatus :
  List NSLargeDataContractionInputStatus
canonicalNSLargeDataContractionInputStatus =
  largeDataContractionInputRequested
  ∷ hElevenEighthsRouteRecorded
  ∷ lowFrequencyLipschitzBoundMissing
  ∷ noRegularityOrClayPromotion
  ∷ []

data NSLargeDataContractionMechanism : Set where
  adjacentOnlyHighFrequencyMechanism :
    NSLargeDataContractionMechanism

  lowFrequencyFiniteODEMechanism :
    NSLargeDataContractionMechanism

canonicalNSLargeDataContractionMechanisms :
  List NSLargeDataContractionMechanism
canonicalNSLargeDataContractionMechanisms =
  adjacentOnlyHighFrequencyMechanism
  ∷ lowFrequencyFiniteODEMechanism
  ∷ []

data NSLargeDataContractionMissingInput : Set where
  lowFrequencyLipschitzBound :
    NSLargeDataContractionMissingInput

canonicalNSLargeDataContractionMissingInputs :
  List NSLargeDataContractionMissingInput
canonicalNSLargeDataContractionMissingInputs =
  lowFrequencyLipschitzBound
  ∷ []

data NSLargeDataContractionPromotion : Set where

nsLargeDataContractionPromotionImpossibleHere :
  NSLargeDataContractionPromotion →
  ⊥
nsLargeDataContractionPromotionImpossibleHere ()

largeDataContractionH118Statement : String
largeDataContractionH118Statement =
  "Large-data contraction target: for carrier-structured 3D Navier-Stokes initial data u_0 in H^{11/8}, split u = P_low u + P_high u; adjacent-only high-frequency dissipation controls the high modes, the low modes form a finite ODE sector, and a uniform low-frequency Lipschitz bound L_low(T,R) compatible with high-mode damping would make the coupled Duhamel map a contraction on the H^{11/8} ball of radius R for arbitrary finite R."

smallDataContractionCondition : String
smallDataContractionCondition =
  "Small-data contraction condition: the standard local bilinear Duhamel map is contractive on H^{11/8} whenever its Lipschitz constant is < 1, recorded as C_NS T^theta ||u_0||_{H^{11/8}} < 1 on the selected time interval."

adjacentOnlyHighFrequencyMechanismStatement : String
adjacentOnlyHighFrequencyMechanismStatement =
  "Adjacent-only high-frequency mechanism: same-base adjacent-band vortex stretching is dominated by the H^{11/8} dissipative weight at high frequency, so the high-frequency tail is damped after the carrier projection error is controlled."

lowFrequencyFiniteODEMechanismStatement : String
lowFrequencyFiniteODEMechanismStatement =
  "Low-frequency finite ODE mechanism: after a frequency cutoff, finitely many low modes evolve by a smooth finite-dimensional polynomial ODE, so local existence is finite-dimensional and continuation reduces to a uniform growth/Lipschitz estimate."

missingLowFrequencyLipschitzBoundStatement : String
missingLowFrequencyLipschitzBoundStatement =
  "Key missing input: a uniform low-frequency Lipschitz bound for the finite ODE sector, L_low(T,R), strong enough to keep the coupled low/high Duhamel map contractive for large H^{11/8} data."

nsLargeDataContractionInputRequestStatement : String
nsLargeDataContractionInputRequestStatement =
  "C2 requests the missing large-data H^{11/8} contraction input: small data has the usual contraction condition, high frequency uses adjacent-only damping, low frequency is a finite ODE sector, and the key missing bound is the low-frequency Lipschitz estimate; no theorem or Clay promotion follows."

record NSLargeDataContractionInputRequest : Setω where
  field
    status :
      List NSLargeDataContractionInputStatus

    statusIsCanonical :
      status ≡ canonicalNSLargeDataContractionInputStatus

    largeDataContractionStatement :
      String

    largeDataContractionStatementIsCanonical :
      largeDataContractionStatement ≡ largeDataContractionH118Statement

    hElevenEighthsSobolevTargetRecorded :
      Bool

    hElevenEighthsSobolevTargetRecordedIsTrue :
      hElevenEighthsSobolevTargetRecorded ≡ true

    largeDataRouteRecorded :
      Bool

    largeDataRouteRecordedIsTrue :
      largeDataRouteRecorded ≡ true

    arbitraryFiniteRadiusRRecorded :
      Bool

    arbitraryFiniteRadiusRRecordedIsTrue :
      arbitraryFiniteRadiusRRecorded ≡ true

    smallDataCondition :
      String

    smallDataConditionIsCanonical :
      smallDataCondition ≡ smallDataContractionCondition

    smallDataContractionConditionRecorded :
      Bool

    smallDataContractionConditionRecordedIsTrue :
      smallDataContractionConditionRecorded ≡ true

    mechanisms :
      List NSLargeDataContractionMechanism

    mechanismsAreCanonical :
      mechanisms ≡ canonicalNSLargeDataContractionMechanisms

    highFrequencyMechanism :
      String

    highFrequencyMechanismIsCanonical :
      highFrequencyMechanism ≡ adjacentOnlyHighFrequencyMechanismStatement

    adjacentOnlyHighFrequencyMechanismRecorded :
      Bool

    adjacentOnlyHighFrequencyMechanismRecordedIsTrue :
      adjacentOnlyHighFrequencyMechanismRecorded ≡ true

    lowFrequencyMechanism :
      String

    lowFrequencyMechanismIsCanonical :
      lowFrequencyMechanism ≡ lowFrequencyFiniteODEMechanismStatement

    lowFrequencyFiniteODEMechanismRecorded :
      Bool

    lowFrequencyFiniteODEMechanismRecordedIsTrue :
      lowFrequencyFiniteODEMechanismRecorded ≡ true

    missingInputs :
      List NSLargeDataContractionMissingInput

    missingInputsAreCanonical :
      missingInputs ≡ canonicalNSLargeDataContractionMissingInputs

    keyMissingLowFrequencyLipschitzBound :
      String

    keyMissingLowFrequencyLipschitzBoundIsCanonical :
      keyMissingLowFrequencyLipschitzBound
      ≡
      missingLowFrequencyLipschitzBoundStatement

    lowFrequencyLipschitzBoundSupplied :
      Bool

    lowFrequencyLipschitzBoundSuppliedIsFalse :
      lowFrequencyLipschitzBoundSupplied ≡ false

    largeDataContractionTheoremConstructed :
      Bool

    largeDataContractionTheoremConstructedIsFalse :
      largeDataContractionTheoremConstructed ≡ false

    smoothGlobalRegularityPromoted :
      Bool

    smoothGlobalRegularityPromotedIsFalse :
      smoothGlobalRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsLargeDataContractionInputRequestStatement

    promotionFlags :
      List NSLargeDataContractionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSLargeDataContractionInputRequest public

canonicalNSLargeDataContractionInputRequest :
  NSLargeDataContractionInputRequest
canonicalNSLargeDataContractionInputRequest =
  record
    { status =
        canonicalNSLargeDataContractionInputStatus
    ; statusIsCanonical =
        refl
    ; largeDataContractionStatement =
        largeDataContractionH118Statement
    ; largeDataContractionStatementIsCanonical =
        refl
    ; hElevenEighthsSobolevTargetRecorded =
        true
    ; hElevenEighthsSobolevTargetRecordedIsTrue =
        refl
    ; largeDataRouteRecorded =
        true
    ; largeDataRouteRecordedIsTrue =
        refl
    ; arbitraryFiniteRadiusRRecorded =
        true
    ; arbitraryFiniteRadiusRRecordedIsTrue =
        refl
    ; smallDataCondition =
        smallDataContractionCondition
    ; smallDataConditionIsCanonical =
        refl
    ; smallDataContractionConditionRecorded =
        true
    ; smallDataContractionConditionRecordedIsTrue =
        refl
    ; mechanisms =
        canonicalNSLargeDataContractionMechanisms
    ; mechanismsAreCanonical =
        refl
    ; highFrequencyMechanism =
        adjacentOnlyHighFrequencyMechanismStatement
    ; highFrequencyMechanismIsCanonical =
        refl
    ; adjacentOnlyHighFrequencyMechanismRecorded =
        true
    ; adjacentOnlyHighFrequencyMechanismRecordedIsTrue =
        refl
    ; lowFrequencyMechanism =
        lowFrequencyFiniteODEMechanismStatement
    ; lowFrequencyMechanismIsCanonical =
        refl
    ; lowFrequencyFiniteODEMechanismRecorded =
        true
    ; lowFrequencyFiniteODEMechanismRecordedIsTrue =
        refl
    ; missingInputs =
        canonicalNSLargeDataContractionMissingInputs
    ; missingInputsAreCanonical =
        refl
    ; keyMissingLowFrequencyLipschitzBound =
        missingLowFrequencyLipschitzBoundStatement
    ; keyMissingLowFrequencyLipschitzBoundIsCanonical =
        refl
    ; lowFrequencyLipschitzBoundSupplied =
        false
    ; lowFrequencyLipschitzBoundSuppliedIsFalse =
        refl
    ; largeDataContractionTheoremConstructed =
        false
    ; largeDataContractionTheoremConstructedIsFalse =
        refl
    ; smoothGlobalRegularityPromoted =
        false
    ; smoothGlobalRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        nsLargeDataContractionInputRequestStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The large-data contraction target is stated in H^{11/8}"
        ∷ "The small-data contraction condition C_NS T^theta ||u_0||_{H^{11/8}} < 1 is recorded"
        ∷ "High-frequency control is the adjacent-only dissipative mechanism"
        ∷ "Low-frequency control is reduced to a finite ODE mechanism"
        ∷ "The key missing input is the uniform low-frequency Lipschitz bound"
        ∷ "No large-data contraction theorem, smooth global regularity theorem, or Clay promotion is asserted"
        ∷ []
    }

nsLargeDataContractionInputStillMissingLowFrequencyLipschitz :
  lowFrequencyLipschitzBoundSupplied
    canonicalNSLargeDataContractionInputRequest
  ≡
  false
nsLargeDataContractionInputStillMissingLowFrequencyLipschitz =
  refl

nsLargeDataContractionInputDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSLargeDataContractionInputRequest
  ≡
  false
nsLargeDataContractionInputDoesNotPromoteClay =
  refl

nsLargeDataContractionNoPromotion :
  NSLargeDataContractionPromotion →
  ⊥
nsLargeDataContractionNoPromotion =
  nsLargeDataContractionPromotionImpossibleHere
