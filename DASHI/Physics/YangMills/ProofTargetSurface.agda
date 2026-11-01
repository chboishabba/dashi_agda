module DASHI.Physics.YangMills.ProofTargetSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; eriksson-2602-0041
  ; eriksson-2602-0052
  ; eriksson-2602-0056
  ; eriksson-2602-0069
  ; eriksson-2602-0072
  ; eriksson-2602-0087
  ; eriksson-2602-0088
  ; eriksson-2602-0089
  ; eriksson-2602-0091
  ; eriksson-2602-0092
  ; eriksson-2602-0096
  ; balaban-cmp-095
  ; balaban-cmp-099
  ; balaban-cmp-109
  ; balaban-cmp-116
  ; balaban-cmp-122
  ; zenodo-18799942
  ; zenodo-18800920
  ; diestel-graph-theory
  ; dashi-internal-proof
  ; unknown-authority
  ; VerificationStatus
  ; proved
  ; standardWrapper
  ; paperImport
  ; auditTested
  ; openTarget
  ; mixedReducer
  ; provedConditionalReducer
  ; ClaimRole
  ; postulate-import
  ; consequence-proof
  ; convention-definition
  )

ProofStatus : Set
ProofStatus = VerificationStatus

proofStatusLabel : ProofStatus → String
proofStatusLabel proved = "proved"
proofStatusLabel standardWrapper = "standard-wrapper"
proofStatusLabel paperImport = "paper-import"
proofStatusLabel auditTested = "audit-tested"
proofStatusLabel openTarget = "open"
proofStatusLabel mixedReducer = "mixed-reducer"
proofStatusLabel provedConditionalReducer = "proved-conditional-reducer"

surfaceClosed : ProofStatus → Bool
surfaceClosed openTarget = false
surfaceClosed _ = true

record ProofTargetSurface : Set where
  field
    lemmaName : String
    sourceReference : String
    exactStatement : String
    assumptions : String
    outputConclusion : String
    consumingGate : String
    failureConsequence : String
    status : ProofStatus
    sourceAuthorityId  : SourceAuthorityId
    theoremLocator     : String
    claimRole          : ClaimRole
    verificationStatus : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

proofTargetIsClosed : ProofTargetSurface → Bool
proofTargetIsClosed target = surfaceClosed (ProofTargetSurface.status target)

mkProofTargetSurfaceWithAuthority :
  String →
  String →
  String →
  String →
  String →
  String →
  String →
  ProofStatus →
  SourceAuthorityId →
  String →
  ClaimRole →
  VerificationStatus →
  ProofTargetSurface
mkProofTargetSurfaceWithAuthority lemmaName sourceReference exactStatement assumptions outputConclusion consumingGate failureConsequence status sourceId locator role vStatus =
  record
    { lemmaName = lemmaName
    ; sourceReference = sourceReference
    ; exactStatement = exactStatement
    ; assumptions = assumptions
    ; outputConclusion = outputConclusion
    ; consumingGate = consumingGate
    ; failureConsequence = failureConsequence
    ; status = status
    ; sourceAuthorityId = sourceId
    ; theoremLocator = locator
    ; claimRole = role
    ; verificationStatus = vStatus
    ; noClayPromotion = refl
    }

mkProofTargetSurface :
  String →
  String →
  String →
  String →
  String →
  String →
  String →
  ProofStatus →
  ProofTargetSurface
mkProofTargetSurface lemmaName sourceReference exactStatement assumptions outputConclusion consumingGate failureConsequence status =
  mkProofTargetSurfaceWithAuthority lemmaName sourceReference exactStatement assumptions outputConclusion consumingGate failureConsequence status
    unknown-authority "" postulate-import status
