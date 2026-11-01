module Verification.LMFDB where

open import Verification.Prelude

postulate Statement : Set
postulate Cert      : Set

-- Checker is the trusted kernel that validates a certificate for a statement.
postulate check : Statement → Cert → Bool

record LMFDBVerified : Set₁ where
  field
    S    : Statement
    cert : Cert
    ok   : check S cert ≡ true
