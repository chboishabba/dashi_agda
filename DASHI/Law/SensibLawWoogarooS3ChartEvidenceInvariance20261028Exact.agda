module DASHI.Law.SensibLawWoogarooS3ChartEvidenceInvariance20261028Exact where

------------------------------------------------------------------------
-- Woogaroo 2019/8575: reuse finite S3 action from merged owners, with
-- #1414 (UNMERGED) as a proof-method donor, not an imported dependency.
--
-- X = stage of legal dialectic A, Y = stage of source/context
-- dialectic B, Z = THEIR interaction's stage. Presentation-chart
-- relabelling does NOT mean real Z progression or legal merits change.
--
-- Finite permutation and inverse ownership:
-- DASHI.Foundations.TernaryEndomorphismConjugacyExact.
-- Generic XY->Z geometry ownership:
-- DASHI.Reasoning.DialecticXYInteractionZTransportExact.
-- Woogaroo ground and provenance ownership stays with the preexisting
-- case modules, not polynomial/quaternion/Monster representations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Reasoning.DialecticXYInteractionZTransportExact as XY
import DASHI.Law.SensibLawWoogarooXYInteraction27TransportExact as Case
import DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact as Ground
import DASHI.Law.SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact as File
import DASHI.Law.SensibLawWoogarooStandingTimeInterimCounselTriage20261027Exact as Counsel

-- The sign -1 in a POSITIONAL chart means the first role. It does
-- not mean evidence for not(P), or that a source has been reviewed.
renameRole : Perm.TriPermutation → XY.DialecticPosition →
  XY.DialecticPosition
renameRole p role =
  XY.triToPosition
    (Perm.applyPermutation p (XY.positionToTri role))

renameRoleInverseLeft : (p : Perm.TriPermutation)
  (role : XY.DialecticPosition) →
  renameRole (Perm.inversePermutation p) (renameRole p role) ≡ role
renameRoleInverseLeft p role
  rewrite XY.triPositionRoundTrip
            (Perm.applyPermutation p (XY.positionToTri role))
        | Perm.inverseLeftAt p (XY.positionToTri role)
        | XY.positionTriRoundTrip role = refl

renameRoleInverseRight : (p : Perm.TriPermutation)
  (role : XY.DialecticPosition) →
  renameRole p (renameRole (Perm.inversePermutation p) role) ≡ role
renameRoleInverseRight p role
  rewrite XY.triPositionRoundTrip
            (Perm.applyPermutation (Perm.inversePermutation p)
              (XY.positionToTri role))
        | Perm.inverseRightAt p (XY.positionToTri role)
        | XY.positionTriRoundTrip role = refl

renameEncounter : Perm.TriPermutation →
  XY.DialecticEncounter27 → XY.DialecticEncounter27
renameEncounter p xyz =
  XY.dialectic-encounter
    (renameRole p (XY.xDialecticPosition xyz))
    (renameRole p (XY.yDialecticPosition xyz))
    (renameRole p (XY.zInteractionPosition xyz))

renameEncounterInverseLeft : (p : Perm.TriPermutation)
  (xyz : XY.DialecticEncounter27) →
  renameEncounter (Perm.inversePermutation p) (renameEncounter p xyz) ≡ xyz
renameEncounterInverseLeft p (XY.dialectic-encounter x y z)
  rewrite renameRoleInverseLeft p x
        | renameRoleInverseLeft p y
        | renameRoleInverseLeft p z = refl

renameEncounterInverseRight : (p : Perm.TriPermutation)
  (xyz : XY.DialecticEncounter27) →
  renameEncounter p (renameEncounter (Perm.inversePermutation p) xyz) ≡ xyz
renameEncounterInverseRight p (XY.dialectic-encounter x y z)
  rewrite renameRoleInverseRight p x
        | renameRoleInverseRight p y
        | renameRoleInverseRight p z = refl

-- A case presentation chart is a *paired* coordinate and decoding
-- legend. Its underlying evidence and canonical case remain unchanged.
record ChartedWoogaroo (g : Ground.Ground) : Set where
  constructor charted-woogaroo
  field
    sourceCase : Case.WoogarooAttachedInteraction27 g
    presentationPermutation : Perm.TriPermutation
open ChartedWoogaroo public

displayEncounter : ∀ {g} → ChartedWoogaroo g →
  XY.DialecticEncounter27
displayEncounter c =
  renameEncounter (presentationPermutation c)
    (Case.dialecticCell (sourceCase c))

decodeEncounter : ∀ {g} → ChartedWoogaroo g →
  XY.DialecticEncounter27
decodeEncounter c =
  renameEncounter
    (Perm.inversePermutation (presentationPermutation c))
    (displayEncounter c)

decodeIsUnderlyingEncounter : ∀ {g} →
  (c : ChartedWoogaroo g) →
  decodeEncounter c ≡ Case.dialecticCell (sourceCase c)
decodeIsUnderlyingEncounter (charted-woogaroo source p) =
  renameEncounterInverseLeft p (Case.dialecticCell source)

rechartCase : ∀ {g} →
  Perm.TriPermutation →
  Case.WoogarooAttachedInteraction27 g →
  ChartedWoogaroo g
rechartCase p source = charted-woogaroo source p

-- All the legally critical RECEIVERS remain fixed under every S3
-- presentation label. This is source preservation, not evidence payment.
fineEvidenceInvariant : ∀ {g} →
  (p : Perm.TriPermutation) (source : Case.WoogarooAttachedInteraction27 g) →
  Case.fineGroundEvidence (sourceCase (rechartCase p source))
  ≡ Case.fineGroundEvidence source
fineEvidenceInvariant p source = refl

scopeInvariant : ∀ {g} →
  (p : Perm.TriPermutation) (source : Case.WoogarooAttachedInteraction27 g) →
  Case.sourceScopeReference (sourceCase (rechartCase p source))
  ≡ Case.sourceScopeReference source
scopeInvariant p source = refl

candidateOnlyInvariant : ∀ {g} →
  (p : Perm.TriPermutation) (source : Case.WoogarooAttachedInteraction27 g) →
  Case.candidateOnly (sourceCase (rechartCase p source))
  ≡ Case.candidateOnly source
candidateOnlyInvariant p source = refl

unpaidMediationInvariant : ∀ {g} →
  (p : Perm.TriPermutation) (source : Case.WoogarooAttachedInteraction27 g) →
  Case.actualMediationReceipt (sourceCase (rechartCase p source))
  ≡ Case.actualMediationReceipt source
unpaidMediationInvariant p source = refl

-- No transported chart can convert the unreviewed decision-file
-- questions into paid facts. The existing original sources still
-- control the answer. These terms are owner locators, not receipts.
signedInstrumentStillRequested : File.DecisionFileReceipt
signedInstrumentStillRequested = File.signedApprovalMissing

secretary95CStillRequested : File.DecisionFileReceipt
secretary95CStillRequested = File.section95CRecommendation

applicantClockStillForCounsel : Counsel.LitigationGate
applicantClockStillForCounsel = Counsel.furnishingClock

-- Contrast: an identity of finite 27-state carriers, root monodromy
-- permutation, and an S3 chart of prose roles do not license
-- identification of paid source states, legal authority, or actor.
-- No unmerged #1414 module is imported; original proof ownership
-- and independent Ibrahim Monster 3B proofs remain untouched.
