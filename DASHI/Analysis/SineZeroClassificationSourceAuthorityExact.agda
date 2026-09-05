module DASHI.Analysis.SineZeroClassificationSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED SOURCE AUTHORITY FOR THE ZEROS OF SINE
--
-- SOURCE:
-- NIST Digital Library of Mathematical Functions, §4.14.
-- DLMF states that the zeros of sin(z) in C are exactly z = k*pi,
-- k in Z.
-- URL: https://dlmf.nist.gov/4.14
--
-- This is SOURCEBACKED theorem authority only; no internal DASHI proof of the
-- zero classification is claimed here.
------------------------------------------------------------------------

record SineZeroClassificationSourceAuthority : Set where
  field
    sourceName : String
    sourceLocator : String
    sourceClassifiesAllSineZeros : Set
    zerosAreIntegerMultiplesOfPi : Set
    sourceBackedOnly : Set
    reading : String

open SineZeroClassificationSourceAuthority public

nistDLMFSineZeroAuthority : SineZeroClassificationSourceAuthority
nistDLMFSineZeroAuthority = record
  { sourceName = "NIST DLMF §4.14"
  ; sourceLocator = "https://dlmf.nist.gov/4.14"
  ; sourceClassifiesAllSineZeros = ⊤
  ; zerosAreIntegerMultiplesOfPi = ⊤
  ; sourceBackedOnly = ⊤
  ; reading = "DLMF source-backs that sin(z)=0 iff z is an integer multiple of pi."
  }

data SourceClassificationAutomaticallyIsInternalProof : Set where

sourceClassificationIsNotMachineProof :
  SourceClassificationAutomaticallyIsInternalProof → ⊥
sourceClassificationIsNotMachineProof ()
