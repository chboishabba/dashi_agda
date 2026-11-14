module DASHI.Research.OpenAIMath.OpenAIMathUpstreamReceiptExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.String using (String)

upstreamRepository : String
upstreamRepository = "https://github.com/openai/math"

upstreamCommit : String
upstreamCommit = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"

upstreamLicense : String
upstreamLicense = "Apache-2.0"

upstreamLeanToolchain : String
upstreamLeanToolchain = "leanprover/lean4:v4.34.1"

upstreamFormalizationCatalogue : String
upstreamFormalizationCatalogue = "lean/formalization.yaml"

upstreamLeanRoot : String
upstreamLeanRoot = "lean/OAI.lean"

-- Authority levels are intentionally non-collapsing.  Recording an upstream
-- Lean declaration in Agda is a source receipt, never an Agda proof.
data UpstreamAuthorityLevel : Set where
  manuscript : UpstreamAuthorityLevel
  catalogueEntry : UpstreamAuthorityLevel
  leanDeclaration : UpstreamAuthorityLevel
  upstreamKernelReceipt : UpstreamAuthorityLevel

data PromotionStatus : Set where
  manuscriptOnly : PromotionStatus
  catalogueIndexed : PromotionStatus
  upstreamDeclared : PromotionStatus
  upstreamKernelChecked : PromotionStatus
  dashiLeanPorted : PromotionStatus
  dashiLeanKernelChecked : PromotionStatus
  agdaImportedFormalSource : PromotionStatus
  agdaTheorem : PromotionStatus

record UpstreamFormalizationReceipt : Set where
  constructor mkUpstreamFormalizationReceipt
  field
    familyId : String
    manuscriptId : String
    declaration : String
    authority : UpstreamAuthorityLevel
    sourceSHA : String

record AgdaCrossProverReceipt : Set where
  constructor mkAgdaCrossProverReceipt
  field
    upstream : UpstreamFormalizationReceipt
    status : PromotionStatus
    sameObjectTransportDeclared : Bool

manuscriptClaimIsAgdaTheorem : Bool
manuscriptClaimIsAgdaTheorem = false

catalogueEntryIsKernelReceipt : Bool
catalogueEntryIsKernelReceipt = false

upstreamLeanTheoremIsAgdaTheorem : Bool
upstreamLeanTheoremIsAgdaTheorem = false

upstreamLeanTheoremIsDASHILeanPort : Bool
upstreamLeanTheoremIsDASHILeanPort = false

relevancePromotesSameObjectTransport : Bool
relevancePromotesSameObjectTransport = false
