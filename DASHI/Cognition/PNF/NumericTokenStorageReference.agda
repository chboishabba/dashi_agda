module DASHI.Cognition.PNF.NumericTokenStorageReference where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Cognition.PNF.SpacyNumericProjection as Parser
import DASHI.Core.MultiscaleMDL as MDL

------------------------------------------------------------------------
-- Post-tokenisation storage reference.
--
-- The authoritative hot token stream is numeric.  A storage codec may encode
-- that stream for cold/archive transport, but exact decode(encode(stream)) is
-- required before it can be treated as lossless storage.  No radix, balanced
-- ternary packing, CRT packing, entropy code, PostgreSQL column type or other
-- physical layout is declared optimal by this interface.
------------------------------------------------------------------------

TokenSymbolStream : Set
TokenSymbolStream = List SymbolId

record LosslessTokenStreamCodec (Encoded : Set) : Set where
  constructor losslessTokenStreamCodec
  field
    encode : TokenSymbolStream → Encoded
    decode : Encoded → TokenSymbolStream
    decodeEncode :
      (stream : TokenSymbolStream) →
      decode (encode stream) ≡ stream

open LosslessTokenStreamCodec public

------------------------------------------------------------------------
-- Full compiled numeric observation tape.
--
-- A SymbolId stream is not enough to reconstruct parser structure.  The runtime
-- target for the packed execution representation is the complete committed
-- numeric spaCy observation carrier: token/sentence identity, offsets, orth,
-- lemma observation, POS/tag/dependency annotations, morphology, and committed
-- dependency head.  A packed/delta/varint/bit-coded representation is permitted
-- only when it reconstructs this tape exactly.
------------------------------------------------------------------------

NumericObservationTape : Set
NumericObservationTape = List Parser.NumericTokenRow

record LosslessNumericObservationTapeCodec (Encoded : Set) : Set where
  constructor losslessNumericObservationTapeCodec
  field
    encodeTape : NumericObservationTape → Encoded
    decodeTape : Encoded → NumericObservationTape
    decodeEncodeTape :
      (tape : NumericObservationTape) →
      decodeTape (encodeTape tape) ≡ tape

open LosslessNumericObservationTapeCodec public

record NumericObservationTapeMeasurement : Set where
  constructor numericObservationTapeMeasurement
  field
    tokenRows : Nat
    encodedBytes : Nat
    randomAccessWork : Nat
    sequentialDecodeWork : Nat

open NumericObservationTapeMeasurement public

------------------------------------------------------------------------
-- Reuse the existing multiscale residual/MDL spine when storage has an actual
-- coarse/fine tower.  The exact reconstruction theorem is inherited directly;
-- entropy, Kraft admissibility and rate-distortion optimality remain the
-- existing separate obligations rather than being silently inferred from a
-- short code or a number-theoretic address.
------------------------------------------------------------------------

record MultiscaleTokenStorageReference : Set₁ where
  constructor multiscaleTokenStorageReference
  field
    tower : MDL.MultiscaleCarrier
    codec : MDL.ResidualCodec tower
    cost : MDL.MDLCost tower codec

open MultiscaleTokenStorageReference public

multiscaleStorageJoinSplitExact :
  (reference : MultiscaleTokenStorageReference) →
  ∀ {j}
    (x : MDL.Carrier (tower reference) (suc j)) →
  MDL.join (codec reference) (MDL.split (codec reference) x) ≡ x
multiscaleStorageJoinSplitExact reference x =
  MDL.join-split (codec reference) x

------------------------------------------------------------------------
-- Physical storage is selected by measurement, not algebraic fashion.
--
-- Random-access working storage and cold compact storage optimise different
-- objectives.  This receipt can compare any supplied layouts without granting
-- semantic authority to the winner.
------------------------------------------------------------------------

data StorageUse : Set where
  hotRandomAccess coldArchive : StorageUse

record StorageMeasurement : Set where
  constructor storageMeasurement
  field
    use : StorageUse
    encodedBytes : Nat
    lookupWork : Nat
    decodeWork : Nat

open StorageMeasurement public

record StorageComparisonReceipt : Set where
  constructor storageComparisonReceipt
  field
    incumbent candidate : StorageMeasurement
    measurementSampleCount : Nat

open StorageComparisonReceipt public

data StorageOptimalityPermission : Set where

data NumberTheoreticLayoutAuthority : Set where

data LowPhysicalCodeAutomaticallyUsesFewerPostgresBytes : Set where

measurementDoesNotProveGlobalStorageOptimality :
  StorageOptimalityPermission → ⊥
measurementDoesNotProveGlobalStorageOptimality ()

numberTheoryAloneDoesNotSelectPhysicalLayout :
  NumberTheoreticLayoutAuthority → ⊥
numberTheoryAloneDoesNotSelectPhysicalLayout ()

lowCodeValueAloneDoesNotProveNarrowerPostgresStorage :
  LowPhysicalCodeAutomaticallyUsesFewerPostgresBytes → ⊥
lowCodeValueAloneDoesNotProveNarrowerPostgresStorage ()

record NumericTokenStorageBoundary : Set where
  constructor numericTokenStorageBoundary
  field
    hotSemanticCarrierIsNumeric : Bool
    hotSemanticCarrierIsNumericIsTrue :
      hotSemanticCarrierIsNumeric ≡ true
    coldCodecMayReplaceCanonicalOccurrenceIdentity : Bool
    coldCodecMayReplaceCanonicalOccurrenceIdentityIsFalse :
      coldCodecMayReplaceCanonicalOccurrenceIdentity ≡ false
    balancedTernaryPackingAutomaticallyOptimal : Bool
    balancedTernaryPackingAutomaticallyOptimalIsFalse :
      balancedTernaryPackingAutomaticallyOptimal ≡ false
    crtPackingAutomaticallyOptimal : Bool
    crtPackingAutomaticallyOptimalIsFalse :
      crtPackingAutomaticallyOptimal ≡ false
    entropyOptimalityRequiresSeparateModel : Bool
    entropyOptimalityRequiresSeparateModelIsTrue :
      entropyOptimalityRequiresSeparateModel ≡ true
    fullNumericObservationTapeMayBePacked : Bool
    fullNumericObservationTapeMayBePackedIsTrue :
      fullNumericObservationTapeMayBePacked ≡ true
    packedObservationTapeMustReconstructExactly : Bool
    packedObservationTapeMustReconstructExactlyIsTrue :
      packedObservationTapeMustReconstructExactly ≡ true
    lowPhysicalIntegerValueAloneImpliesNarrowerDatabaseStorage : Bool
    lowPhysicalIntegerValueAloneImpliesNarrowerDatabaseStorageIsFalse :
      lowPhysicalIntegerValueAloneImpliesNarrowerDatabaseStorage ≡ false

open NumericTokenStorageBoundary public

canonicalNumericTokenStorageBoundary : NumericTokenStorageBoundary
canonicalNumericTokenStorageBoundary =
  numericTokenStorageBoundary
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
