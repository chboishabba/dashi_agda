module DASHI.Unified.QwenputerBinaryTernaryTOEExact where

-- Re-export ONLY actual finite DASHI witnesses to the TOE import graph.
-- External architecture: Divyansh Agrawal, Qwenputer (2026),
-- https://github.com/divagr18/qwenputer
-- The Agda results below are repo-native abstractions, not source binaries.
-- Existing binary/ternary owner is reused rather than replaced.

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (just)

import DASHI.ComputerScience.QwenputerGatedDeltaArchitectureExact as GDN
import DASHI.ComputerScience.QwenputerHybridStateAndFileStoreExact as Store
import DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact as Binary
import DASHI.ComputerScience.ShorStandardBinaryTernaryStoredProgramComputerExact as BinaryTernary

toeQwenputerSourceIdentity : GDN.SourceIdentity
toeQwenputerSourceIdentity = GDN.qwenputerSource

toeQwenputerSourceArchitecture : GDN.Rv32SourceParameters
toeQwenputerSourceArchitecture = GDN.rv32ReportedParameters

toeQwenputerProofBoundary : GDN.ArchitectureBoundary
toeQwenputerProofBoundary = GDN.canonicalArchitectureBoundary

toeQwenputerReadAfterWrite :
  (store : GDN.Ram Bool) (location : GDN.Location) (bit : Bool) →
  GDN.readRam (GDN.writeRam store location bit) location ≡ bit
toeQwenputerReadAfterWrite = GDN.readWriteSame

toeQwenputerDecodedTernaryWrite :
  (store : GDN.Ram Bool) (location : GDN.Location) (bit : Bool) →
  Binary.decodeEmbeddedBit
    (GDN.readRam
      (GDN.writeRam (GDN.embedBinaryRam store) location
        (Binary.embedBit bit))
      location)
  ≡ bit
toeQwenputerDecodedTernaryWrite = GDN.decodedEmbeddedWrite

toeQwenputerFiniteFileGetAfterPut :
  (store : Store.FileStore) (name : Store.FileName)
  (value : Store.FileContents) →
  Store.get (Store.put store name value) name ≡
    just value
toeQwenputerFiniteFileGetAfterPut = Store.getAfterPut

-- Refer to the real binary/ternary stored-program theorem owner.
toePriorBinaryTernaryOrder15Equal :
  BinaryTernary.order15BinaryFinal ≡ BinaryTernary.order15TernaryFinal
toePriorBinaryTernaryOrder15Equal =
  BinaryTernary.order15BinaryAndTernaryExecutionEqual
