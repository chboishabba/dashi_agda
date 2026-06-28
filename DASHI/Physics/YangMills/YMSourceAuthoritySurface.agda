module DASHI.Physics.YangMills.YMSourceAuthoritySurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

data SourceAuthorityId : Set where
  eriksson-2602-0041 : SourceAuthorityId
  eriksson-2602-0052 : SourceAuthorityId
  eriksson-2602-0056 : SourceAuthorityId
  eriksson-2602-0069 : SourceAuthorityId
  eriksson-2602-0072 : SourceAuthorityId
  eriksson-2602-0087 : SourceAuthorityId
  eriksson-2602-0088 : SourceAuthorityId
  eriksson-2602-0089 : SourceAuthorityId
  eriksson-2602-0091 : SourceAuthorityId
  eriksson-2602-0092 : SourceAuthorityId
  eriksson-2602-0096 : SourceAuthorityId
  balaban-cmp-095    : SourceAuthorityId
  balaban-cmp-099    : SourceAuthorityId
  balaban-cmp-109    : SourceAuthorityId
  balaban-cmp-116    : SourceAuthorityId
  balaban-cmp-122    : SourceAuthorityId
  zenodo-18799942    : SourceAuthorityId
  zenodo-18800920    : SourceAuthorityId
  diestel-graph-theory : SourceAuthorityId
  dashi-internal-proof : SourceAuthorityId
  unknown-authority    : SourceAuthorityId

data VerificationStatus : Set where
  proved : VerificationStatus
  standardWrapper : VerificationStatus
  paperImport : VerificationStatus
  auditTested : VerificationStatus
  openTarget : VerificationStatus
  mixedReducer : VerificationStatus
  provedConditionalReducer : VerificationStatus

data ClaimRole : Set where
  postulate-import : ClaimRole
  consequence-proof : ClaimRole
  convention-definition : ClaimRole

record SourceAuthorityDetails : Set where
  field
    sourceAuthorityId  : SourceAuthorityId
    theoremLocator     : String
    claimRole          : ClaimRole
    verificationStatus : VerificationStatus
    noClayPromotion    : clayYangMillsPromoted ≡ false
