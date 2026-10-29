{-# OPTIONS --safe #-}
module DASHI.Interop.OpaqueRuntimeVersionBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

-- 0xffff1000 is an opaque input token, not a dereferenceable address.
record OpaqueRuntimeToken : Set where
  constructor opaqueRuntimeToken
  field
    token : String
    version : Nat
    executableVerified : Bool

unresolvedToken : Nat → OpaqueRuntimeToken
unresolvedToken version = opaqueRuntimeToken "0xffff1000" version false

reviseVersion : Nat → OpaqueRuntimeToken → OpaqueRuntimeToken
reviseVersion next item =
  opaqueRuntimeToken (OpaqueRuntimeToken.token item) next false

revisionPreservesToken : (next : Nat) (item : OpaqueRuntimeToken) →
  OpaqueRuntimeToken.token (reviseVersion next item) ≡
  OpaqueRuntimeToken.token item
revisionPreservesToken next item = refl

revisionDoesNotVerifyExecution : (next : Nat) (item : OpaqueRuntimeToken) →
  OpaqueRuntimeToken.executableVerified (reviseVersion next item) ≡ false
revisionDoesNotVerifyExecution next item = refl

unresolvedIsNotVerified : (version : Nat) →
  OpaqueRuntimeToken.executableVerified (unresolvedToken version) ≡ false
unresolvedIsNotVerified version = refl
