module DASHI.Unified.TOEImplementationStatus where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

sourceWritten : Bool
sourceWritten = false

kernelVerified : Bool
kernelVerified = false

kernelVerifiedIsFalse : kernelVerified ≡ false
kernelVerifiedIsFalse = refl

verificationBoundary : String
verificationBoundary =
  "TOE implementation is source-written and source-reviewed. No Agda executable was available in the execution environment, so no exact-head kernel verification is claimed."
