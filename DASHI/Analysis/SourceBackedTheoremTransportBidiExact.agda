module DASHI.Analysis.SourceBackedTheoremTransportBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-BACKED THEOREM TRANSPORT, BIDI
--
-- A published/source theorem is not definitionally a theorem on a local DASHI
-- carrier.  The forward direction therefore requires an explicit semantic
-- transport from the bounded source claim into the local claim.  The reverse
-- direction exposes exactly what local theorem a consumer is asking the source
-- weld to justify.
------------------------------------------------------------------------

record SourceBackedClaim : Set₁ where
  field
    SourceClaim : Set
    sourceReceipt : SourceClaim
    sourceName : String
    sourceLocator : String
    reading : String

open SourceBackedClaim public

record LocalTheoremTarget (S : SourceBackedClaim) : Set₁ where
  field
    LocalClaim : Set
    sameMathematicalObject : Set
    sourceSemanticsToLocal : SourceClaim S → sameMathematicalObject → LocalClaim
    reading : String

open LocalTheoremTarget public

record SourceTransportReceipt
    (S : SourceBackedClaim)
    (T : LocalTheoremTarget S) : Set where
  field
    objectWeld : sameMathematicalObject T

open SourceTransportReceipt public

transportSourceBackedTheorem :
  (S : SourceBackedClaim) →
  (T : LocalTheoremTarget S) →
  SourceTransportReceipt S T →
  LocalClaim T
transportSourceBackedTheorem S T W =
  sourceSemanticsToLocal T (sourceReceipt S) (objectWeld W)

record ReverseConsumerObligation : Set₁ where
  field
    DesiredLocalClaim : Set
    sourceCandidateIdentified : Set
    sameCarrierOrRepresentationWeld : Set
    sameOperationOrFunctionWeld : Set
    sameParametersAndNormalisation : Set
    sourceClaimCoversDesiredDirection : Set
    reading : String

open ReverseConsumerObligation public

data SourceNameMatchAutomaticallyTransportsTheorem : Set where

data EqualNumericalValueAutomaticallyIdentifiesObjects : Set where

sourceNameIsNotTransport :
  SourceNameMatchAutomaticallyTransportsTheorem → ⊥
sourceNameIsNotTransport ()

valueMatchIsNotObjectWeld :
  EqualNumericalValueAutomaticallyIdentifiesObjects → ⊥
valueMatchIsNotObjectWeld ()

record BidiStatus : Set where
  field
    sourceReceiptDistinctFromLocalTheorem : Bool
    explicitSameObjectWeldRequired : Bool
    forwardTransportCompilerOwned : Bool
    reverseConsumerObligationsOwned : Bool

    sourceReceiptDistinctFromLocalTheoremIsTrue :
      sourceReceiptDistinctFromLocalTheorem ≡ true
    explicitSameObjectWeldRequiredIsTrue :
      explicitSameObjectWeldRequired ≡ true
    forwardTransportCompilerOwnedIsTrue :
      forwardTransportCompilerOwned ≡ true
    reverseConsumerObligationsOwnedIsTrue :
      reverseConsumerObligationsOwned ≡ true

open BidiStatus public

canonicalBidiStatus : BidiStatus
canonicalBidiStatus = record
  { sourceReceiptDistinctFromLocalTheorem = true
  ; explicitSameObjectWeldRequired = true
  ; forwardTransportCompilerOwned = true
  ; reverseConsumerObligationsOwned = true
  ; sourceReceiptDistinctFromLocalTheoremIsTrue = refl
  ; explicitSameObjectWeldRequiredIsTrue = refl
  ; forwardTransportCompilerOwnedIsTrue = refl
  ; reverseConsumerObligationsOwnedIsTrue = refl
  }
