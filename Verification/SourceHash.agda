module Verification.SourceHash where

open import Verification.Prelude

-- Abstract bytes; you can refine to Word8 later.
postulate Byte : Set
Bytes = List Byte

-- Cryptographic hash as a function (model-level).
postulate Hash : Set
postulate hash : Bytes → Hash

-- A repo snapshot is modeled as its bytes (tarball) + declared hash.
record Snapshot : Set where
  constructor snap
  field
    blob     : Bytes
    declared : Hash

-- Integrity proof obligation: declared equals computed.
record SourceIntegrity : Set where
  field
    S : Snapshot
    ok : Snapshot.declared S ≡ hash (Snapshot.blob S)
