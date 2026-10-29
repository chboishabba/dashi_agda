{-# OPTIONS --safe #-}
module DASHI.Interop.FileUrlRequestBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

-- A locator request is not a network response or a verified file receipt.
record FileUrlRequest : Set where
  constructor fileUrlRequest
  field
    fileLabel : String
    sourceUrl : String
    requestedAction : String

record PendingFileRequest : Set where
  constructor pendingFileRequest
  field
    request : FileUrlRequest
    fetched : Bool
    checksumVerified : Bool
    authorityAccepted : Bool

prepareFileRequest : FileUrlRequest → PendingFileRequest
prepareFileRequest req = pendingFileRequest req false false false

requestPreserved : (req : FileUrlRequest) →
  PendingFileRequest.request (prepareFileRequest req) ≡ req
requestPreserved req = refl

notFetched : (req : FileUrlRequest) →
  PendingFileRequest.fetched (prepareFileRequest req) ≡ false
notFetched req = refl

checksumNotVerified : (req : FileUrlRequest) →
  PendingFileRequest.checksumVerified (prepareFileRequest req) ≡ false
checksumNotVerified req = refl

authorityNotAccepted : (req : FileUrlRequest) →
  PendingFileRequest.authorityAccepted (prepareFileRequest req) ≡ false
authorityNotAccepted req = refl
