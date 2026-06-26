module DASHI.Physics.YangMills.ProofTargetSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

data ProofStatus : Set where
  proved : ProofStatus
  standardWrapper : ProofStatus
  paperImport : ProofStatus
  auditTested : ProofStatus
  openTarget : ProofStatus

proofStatusLabel : ProofStatus → String
proofStatusLabel proved = "proved"
proofStatusLabel standardWrapper = "standard-wrapper"
proofStatusLabel paperImport = "paper-import"
proofStatusLabel auditTested = "audit-tested"
proofStatusLabel openTarget = "open"

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
    noClayPromotion : clayYangMillsPromoted ≡ false

proofTargetIsClosed : ProofTargetSurface → Bool
proofTargetIsClosed target = surfaceClosed (ProofTargetSurface.status target)

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
  record
    { lemmaName = lemmaName
    ; sourceReference = sourceReference
    ; exactStatement = exactStatement
    ; assumptions = assumptions
    ; outputConclusion = outputConclusion
    ; consumingGate = consumingGate
    ; failureConsequence = failureConsequence
    ; status = status
    ; noClayPromotion = refl
    }
