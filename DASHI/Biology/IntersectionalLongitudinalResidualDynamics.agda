module DASHI.Biology.IntersectionalLongitudinalResidualDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)

------------------------------------------------------------------------
-- Intersectional longitudinal residual dynamics.
--
-- This module is candidate-only. It records a sharpened gap surface for
-- body-memory residuals that are indexed by time and situated through
-- body, place, relation, institution, and axis-bundle context. The carrier
-- is explicitly body × time × place × relation × institution × axis-bundle.
--
-- The surface remains fail-closed:
--   - no axis-neutral universalism,
--   - no axis-free body-memory residual,
--   - no causal certainty,
--   - no diagnosis,
--   - no treatment,
--   - no authority.

data Never : Set where

data LongitudinalResidualRoute : Set where
  candidateOnlyRoute : LongitudinalResidualRoute
  axisNeutralUniversalismRoute : LongitudinalResidualRoute
  causalCertaintyRoute : LongitudinalResidualRoute
  diagnosisRoute : LongitudinalResidualRoute
  treatmentRoute : LongitudinalResidualRoute
  authorityRoute : LongitudinalResidualRoute

AdmissibleLongitudinalResidualRoute :
  LongitudinalResidualRoute →
  Set
AdmissibleLongitudinalResidualRoute candidateOnlyRoute = ⊤
AdmissibleLongitudinalResidualRoute axisNeutralUniversalismRoute = Never
AdmissibleLongitudinalResidualRoute causalCertaintyRoute = Never
AdmissibleLongitudinalResidualRoute diagnosisRoute = Never
AdmissibleLongitudinalResidualRoute treatmentRoute = Never
AdmissibleLongitudinalResidualRoute authorityRoute = Never

axisNeutralUniversalismRouteRejected :
  AdmissibleLongitudinalResidualRoute axisNeutralUniversalismRoute →
  Never
axisNeutralUniversalismRouteRejected impossible = impossible

causalCertaintyRouteRejected :
  AdmissibleLongitudinalResidualRoute causalCertaintyRoute →
  Never
causalCertaintyRouteRejected impossible = impossible

diagnosisRouteRejected :
  AdmissibleLongitudinalResidualRoute diagnosisRoute →
  Never
diagnosisRouteRejected impossible = impossible

treatmentRouteRejected :
  AdmissibleLongitudinalResidualRoute treatmentRoute →
  Never
treatmentRouteRejected impossible = impossible

authorityRouteRejected :
  AdmissibleLongitudinalResidualRoute authorityRoute →
  Never
authorityRouteRejected impossible = impossible

data IntersectionalAxis : Set where
  raceAxis : IntersectionalAxis
  classAxis : IntersectionalAxis
  genderAxis : IntersectionalAxis
  sexualityAxis : IntersectionalAxis
  disabilityAxis : IntersectionalAxis
  neurotypeAxis : IntersectionalAxis
  religionAxis : IntersectionalAxis
  colonialityAxis : IntersectionalAxis
  lawAxis : IntersectionalAxis
  landAxis : IntersectionalAxis
  familyAxis : IntersectionalAxis
  institutionAxis : IntersectionalAxis

data LongitudinalResidualKind : Set where
  bodyTimePlaceRelationResidual : LongitudinalResidualKind
  bodyTimePlaceInstitutionResidual : LongitudinalResidualKind
  bodyTimeAxisBundleResidual : LongitudinalResidualKind
  bodyRelationInstitutionResidual : LongitudinalResidualKind
  longitudinalGapResidual : LongitudinalResidualKind

data ResidualThresholdKind : Set where
  safeThresholdKind : ResidualThresholdKind
  sharpenedGapThresholdKind : ResidualThresholdKind
  overThresholdCarryKind : ResidualThresholdKind

data BoundaryClaimKind : Set where
  axisNeutralUniversalismBlockedClaim : BoundaryClaimKind
  causalCertaintyBlockedClaim : BoundaryClaimKind
  diagnosisBlockedClaim : BoundaryClaimKind
  treatmentBlockedClaim : BoundaryClaimKind
  authorityBlockedClaim : BoundaryClaimKind

data HandleKind : Set where
  directHandleKind : HandleKind
  smallSafeJPlusOneHandleKind : HandleKind
  forcedHandleKind : HandleKind
  authorityHandleKind : HandleKind

canonicalIntersectionalAxes : List IntersectionalAxis
canonicalIntersectionalAxes =
  raceAxis
  ∷ classAxis
  ∷ genderAxis
  ∷ sexualityAxis
  ∷ disabilityAxis
  ∷ neurotypeAxis
  ∷ religionAxis
  ∷ colonialityAxis
  ∷ lawAxis
  ∷ landAxis
  ∷ familyAxis
  ∷ institutionAxis
  ∷ []

canonicalLongitudinalResidualKinds : List LongitudinalResidualKind
canonicalLongitudinalResidualKinds =
  bodyTimePlaceRelationResidual
  ∷ bodyTimePlaceInstitutionResidual
  ∷ bodyTimeAxisBundleResidual
  ∷ bodyRelationInstitutionResidual
  ∷ longitudinalGapResidual
  ∷ []

canonicalResidualThresholdKinds : List ResidualThresholdKind
canonicalResidualThresholdKinds =
  safeThresholdKind
  ∷ sharpenedGapThresholdKind
  ∷ overThresholdCarryKind
  ∷ []

canonicalBoundaryClaimKinds : List BoundaryClaimKind
canonicalBoundaryClaimKinds =
  axisNeutralUniversalismBlockedClaim
  ∷ causalCertaintyBlockedClaim
  ∷ diagnosisBlockedClaim
  ∷ treatmentBlockedClaim
  ∷ authorityBlockedClaim
  ∷ []

canonicalHandleKinds : List HandleKind
canonicalHandleKinds =
  directHandleKind
  ∷ smallSafeJPlusOneHandleKind
  ∷ forcedHandleKind
  ∷ authorityHandleKind
  ∷ []

canonicalIntersectionalResidualNotes : List String
canonicalIntersectionalResidualNotes =
  "Residuals are indexed longitudinally rather than treated as axis-free"
  ∷ "The carrier is body × time × place × relation × institution × axis-bundle"
  ∷ "Body, time, place, relation, institution, and axis-bundle stay explicit"
  ∷ "Intersectional axes remain concrete and non-collapsed"
  ∷ "A sharpened gap stays a residual gap and does not become certainty"
  ∷ "The small safe j+1 handle carries over-threshold residual pressure"
  ∷ "No diagnosis, no treatment, and no authority are promoted"
  ∷ []

record IntersectionalResidualCarrier : Set where
  constructor mkIntersectionalResidualCarrier
  field
    carrierBody :
      String

    carrierTime :
      Nat

    carrierPlace :
      String

    carrierRelation :
      String

    carrierInstitution :
      String

    carrierAxisBundle :
      List IntersectionalAxis

    carrierAxisFreeResidual :
      Bool

    carrierAxisFreeResidualIsFalse :
      carrierAxisFreeResidual ≡ false

    carrierReading :
      String

open IntersectionalResidualCarrier public

mkIntersectionalResidualCarrierOf :
  String →
  Nat →
  String →
  String →
  String →
  List IntersectionalAxis →
  String →
  IntersectionalResidualCarrier
mkIntersectionalResidualCarrierOf body time place relation institution axes reading =
  mkIntersectionalResidualCarrier
    body
    time
    place
    relation
    institution
    axes
    false
    refl
    reading

record LongitudinalResidualRow : Set where
  constructor mkLongitudinalResidualRow
  field
    rowIndex :
      Nat

    rowTime :
      Nat

    rowBody :
      String

    rowPlace :
      String

    rowRelation :
      String

    rowInstitution :
      String

    rowAxisBundle :
      List IntersectionalAxis

    rowCarrier :
      IntersectionalResidualCarrier

    rowResidualKind :
      LongitudinalResidualKind

    rowResidualKindIsCanonical :
      rowResidualKind ≡ longitudinalGapResidual

    rowResidualClaim :
      String

    rowCandidateOnly :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowAxisNeutralUniversalismBlocked :
      Bool

    rowAxisNeutralUniversalismBlockedIsFalse :
      rowAxisNeutralUniversalismBlocked ≡ false

    rowCausalCertaintyBlocked :
      Bool

    rowCausalCertaintyBlockedIsFalse :
      rowCausalCertaintyBlocked ≡ false

    rowDiagnosisBlocked :
      Bool

    rowDiagnosisBlockedIsFalse :
      rowDiagnosisBlocked ≡ false

    rowTreatmentBlocked :
      Bool

    rowTreatmentBlockedIsFalse :
      rowTreatmentBlocked ≡ false

    rowAuthorityBlocked :
      Bool

    rowAuthorityBlockedIsFalse :
      rowAuthorityBlocked ≡ false

    rowNoAxisFreeBodyMemoryResidual :
      Bool

    rowNoAxisFreeBodyMemoryResidualIsFalse :
      rowNoAxisFreeBodyMemoryResidual ≡ false

    rowReading :
      String

open LongitudinalResidualRow public

record LongitudinalResidualAtlas : Set where
  constructor mkLongitudinalResidualAtlas
  field
    atlasLabel :
      String

    atlasRoute :
      LongitudinalResidualRoute

    atlasRouteIsCandidateOnly :
      atlasRoute ≡ candidateOnlyRoute

    atlasRouteAdmissible :
      AdmissibleLongitudinalResidualRoute atlasRoute

    atlasRows :
      List LongitudinalResidualRow

    atlasRowsAreCanonical :
      atlasRows ≡ atlasRows

    atlasAxisBundle :
      List IntersectionalAxis

    atlasAxisBundleIsCanonical :
      atlasAxisBundle ≡ canonicalIntersectionalAxes

    atlasResidualKinds :
      List LongitudinalResidualKind

    atlasResidualKindsAreCanonical :
      atlasResidualKinds ≡ canonicalLongitudinalResidualKinds

    atlasBoundaryClaims :
      List BoundaryClaimKind

    atlasBoundaryClaimsAreCanonical :
      atlasBoundaryClaims ≡ canonicalBoundaryClaimKinds

    atlasHandleKinds :
      List HandleKind

    atlasHandleKindsAreCanonical :
      atlasHandleKinds ≡ canonicalHandleKinds

    atlasReading :
      String

open LongitudinalResidualAtlas public

record BoundaryCertificate : Set where
  constructor mkBoundaryCertificate
  field
    certificateLabel :
      String

    certificateRoute :
      LongitudinalResidualRoute

    certificateRouteIsCandidateOnly :
      certificateRoute ≡ candidateOnlyRoute

    certificateRouteAdmissible :
      AdmissibleLongitudinalResidualRoute certificateRoute

    certificateAxisNeutralUniversalismBlocked :
      Bool

    certificateAxisNeutralUniversalismBlockedIsFalse :
      certificateAxisNeutralUniversalismBlocked ≡ false

    certificateCausalCertaintyBlocked :
      Bool

    certificateCausalCertaintyBlockedIsFalse :
      certificateCausalCertaintyBlocked ≡ false

    certificateDiagnosisBlocked :
      Bool

    certificateDiagnosisBlockedIsFalse :
      certificateDiagnosisBlocked ≡ false

    certificateTreatmentBlocked :
      Bool

    certificateTreatmentBlockedIsFalse :
      certificateTreatmentBlocked ≡ false

    certificateAuthorityBlocked :
      Bool

    certificateAuthorityBlockedIsFalse :
      certificateAuthorityBlocked ≡ false

    certificateAxisBundle :
      List IntersectionalAxis

    certificateAxisBundleIsCanonical :
      certificateAxisBundle ≡ canonicalIntersectionalAxes

    certificateRows :
      List LongitudinalResidualRow

    certificateRowsAreCanonical :
      certificateRows ≡ certificateRows

    certificateBoundaryClaims :
      List BoundaryClaimKind

    certificateBoundaryClaimsAreCanonical :
      certificateBoundaryClaims ≡ canonicalBoundaryClaimKinds

    certificateReading :
      String

open BoundaryCertificate public

record IntersectionalLongitudinalResidualDynamics : Set where
  constructor mkIntersectionalLongitudinalResidualDynamics
  field
    longitudinalResidualAtlas :
      LongitudinalResidualAtlas

    boundaryCertificate :
      BoundaryCertificate

    dynamicsCandidateOnly :
      Bool

    dynamicsCandidateOnlyIsTrue :
      dynamicsCandidateOnly ≡ true

    dynamicsReading :
      String

    dynamicsNotes :
      List String

open IntersectionalLongitudinalResidualDynamics public

------------------------------------------------------------------------
-- Concrete row constructors.

mkRow :
  Nat →
  Nat →
  String →
  String →
  String →
  String →
  List IntersectionalAxis →
  String →
  LongitudinalResidualRow
mkRow index time body place relation institution axes reading =
  mkLongitudinalResidualRow
    index
    time
    body
    place
    relation
    institution
    axes
    (mkIntersectionalResidualCarrierOf
      body
      time
      place
      relation
      institution
      axes
      reading)
    longitudinalGapResidual
    refl
    "candidate-only longitudinal residual row"
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    reading

canonicalLongitudinalResidualRow :
  LongitudinalResidualRow
canonicalLongitudinalResidualRow =
  mkRow
    zero
    zero
    "body memory"
    "situated place"
    "interrelation"
    "social institution"
    canonicalIntersectionalAxes
    "The residual row remains candidate-only across time, body, place, relation, institution, and axis-bundle."

canonicalLongitudinalResidualRowTwo :
  LongitudinalResidualRow
canonicalLongitudinalResidualRowTwo =
  mkRow
    (suc zero)
    (suc zero)
    "body memory"
    "changed place"
    "changed relation"
    "changed institution"
    canonicalIntersectionalAxes
    "The second longitudinal row tracks the sharpened gap after one step of change."

canonicalLongitudinalResidualRowThree :
  LongitudinalResidualRow
canonicalLongitudinalResidualRowThree =
  mkRow
    (suc (suc zero))
    (suc (suc zero))
    "body memory"
    "relocated place"
    "rebound relation"
    "institutional setting"
    canonicalIntersectionalAxes
    "The third longitudinal row retains the same axis bundle while time advances."

canonicalLongitudinalResidualRows :
  List LongitudinalResidualRow
canonicalLongitudinalResidualRows =
  canonicalLongitudinalResidualRow
  ∷ canonicalLongitudinalResidualRowTwo
  ∷ canonicalLongitudinalResidualRowThree
  ∷ []

canonicalBoundaryCertificate :
  BoundaryCertificate
canonicalBoundaryCertificate =
  mkBoundaryCertificate
    "intersectional longitudinal residual boundary certificate"
    candidateOnlyRoute
    refl
    tt
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    canonicalIntersectionalAxes
    refl
    canonicalLongitudinalResidualRows
    refl
    canonicalBoundaryClaimKinds
    refl
    "The certificate is candidate-only and blocks axis-neutral universalism, causal certainty, diagnosis, treatment, authority, and any axis-free body-memory residual."

canonicalIntersectionalLongitudinalResidualDynamics :
  IntersectionalLongitudinalResidualDynamics
canonicalIntersectionalLongitudinalResidualDynamics =
  mkIntersectionalLongitudinalResidualDynamics
    (mkLongitudinalResidualAtlas
      "intersectional longitudinal residual atlas"
      candidateOnlyRoute
      refl
      tt
      canonicalLongitudinalResidualRows
      refl
      canonicalIntersectionalAxes
      refl
      canonicalLongitudinalResidualKinds
      refl
      canonicalBoundaryClaimKinds
      refl
      canonicalHandleKinds
      refl
      "Atlas of longitudinal residual rows over the bounded axis bundle.")
    canonicalBoundaryCertificate
    true
    refl
    "Candidate-only longitudinal dynamics keep residuals indexed in time and situated across body, place, relation, institution, and axis bundle."
    canonicalIntersectionalResidualNotes

------------------------------------------------------------------------
-- Reusable lemmas and canonical witnesses.

canonicalRouteIsCandidateOnly :
  atlasRoute
    (longitudinalResidualAtlas
      canonicalIntersectionalLongitudinalResidualDynamics)
  ≡
  candidateOnlyRoute
canonicalRouteIsCandidateOnly =
  atlasRouteIsCandidateOnly
    (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics)

canonicalRouteAdmissible :
  AdmissibleLongitudinalResidualRoute
    (atlasRoute (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics))
canonicalRouteAdmissible =
  atlasRouteAdmissible
    (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics)

canonicalAxisNeutralUniversalismBlocked :
  certificateAxisNeutralUniversalismBlocked canonicalBoundaryCertificate ≡ false
canonicalAxisNeutralUniversalismBlocked =
  certificateAxisNeutralUniversalismBlockedIsFalse canonicalBoundaryCertificate

canonicalCausalCertaintyBlocked :
  certificateCausalCertaintyBlocked canonicalBoundaryCertificate ≡ false
canonicalCausalCertaintyBlocked =
  certificateCausalCertaintyBlockedIsFalse canonicalBoundaryCertificate

canonicalDiagnosisBlocked :
  certificateDiagnosisBlocked canonicalBoundaryCertificate ≡ false
canonicalDiagnosisBlocked =
  certificateDiagnosisBlockedIsFalse canonicalBoundaryCertificate

canonicalTreatmentBlocked :
  certificateTreatmentBlocked canonicalBoundaryCertificate ≡ false
canonicalTreatmentBlocked =
  certificateTreatmentBlockedIsFalse canonicalBoundaryCertificate

canonicalAuthorityBlocked :
  certificateAuthorityBlocked canonicalBoundaryCertificate ≡ false
canonicalAuthorityBlocked =
  certificateAuthorityBlockedIsFalse canonicalBoundaryCertificate

canonicalLongitudinalResidualRowCarrierAxisFreeResidualIsFalse :
  carrierAxisFreeResidual
    (rowCarrier canonicalLongitudinalResidualRow)
  ≡
  false
canonicalLongitudinalResidualRowCarrierAxisFreeResidualIsFalse =
  refl

canonicalLongitudinalResidualRowNoAxisFreeBodyMemoryResidualIsFalse :
  rowNoAxisFreeBodyMemoryResidual canonicalLongitudinalResidualRow ≡ false
canonicalLongitudinalResidualRowNoAxisFreeBodyMemoryResidualIsFalse =
  refl

canonicalAxisBundleIsCanonical :
  certificateAxisBundle canonicalBoundaryCertificate ≡ canonicalIntersectionalAxes
canonicalAxisBundleIsCanonical =
  certificateAxisBundleIsCanonical canonicalBoundaryCertificate

canonicalBoundaryClaimsAreCanonical :
  certificateBoundaryClaims canonicalBoundaryCertificate ≡ canonicalBoundaryClaimKinds
canonicalBoundaryClaimsAreCanonical =
  certificateBoundaryClaimsAreCanonical canonicalBoundaryCertificate

canonicalDynamicsCandidateOnly :
  dynamicsCandidateOnly canonicalIntersectionalLongitudinalResidualDynamics ≡ true
canonicalDynamicsCandidateOnly =
  dynamicsCandidateOnlyIsTrue canonicalIntersectionalLongitudinalResidualDynamics

canonicalAtlasRowsAreCanonical :
  atlasRows (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics)
  ≡
  canonicalLongitudinalResidualRows
canonicalAtlasRowsAreCanonical = refl

canonicalAtlasAxisBundleIsCanonical :
  atlasAxisBundle (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics)
  ≡
  canonicalIntersectionalAxes
canonicalAtlasAxisBundleIsCanonical =
  atlasAxisBundleIsCanonical
    (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics)

canonicalAtlasResidualKindsAreCanonical :
  atlasResidualKinds (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics)
  ≡
  canonicalLongitudinalResidualKinds
canonicalAtlasResidualKindsAreCanonical =
  atlasResidualKindsAreCanonical
    (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics)

canonicalAtlasBoundaryClaimsAreCanonical :
  atlasBoundaryClaims (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics)
  ≡
  canonicalBoundaryClaimKinds
canonicalAtlasBoundaryClaimsAreCanonical =
  atlasBoundaryClaimsAreCanonical
    (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics)

canonicalAtlasHandleKindsAreCanonical :
  atlasHandleKinds (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics)
  ≡
  canonicalHandleKinds
canonicalAtlasHandleKindsAreCanonical =
  atlasHandleKindsAreCanonical
    (longitudinalResidualAtlas canonicalIntersectionalLongitudinalResidualDynamics)

canonicalLongitudinalResidualNotes :
  List String
canonicalLongitudinalResidualNotes =
  dynamicsNotes canonicalIntersectionalLongitudinalResidualDynamics
