module Ontology.DNA.ChemistryAdaptiveReferenceCodec where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Codec.DNAFirstFormalism using (Base; Generable)
open import DASHI.Codec.DNAConcreteReference using
  (referenceMachine; encode; decode; encoded-is-generable; decode-encode)
open import Ontology.DNA.ChemistryTernaryQuantizer using
  (Trit; minus; neutral; plus)

------------------------------------------------------------------------
-- The verified two-choice reference channel from DASHI.Codec is reused as the
-- adaptive primitive.  One ternary symbol is represented by two legal binary
-- choices; 11 is reserved as an escape word.

tritBits : Trit → List Bool
tritBits minus = false ∷ false ∷ []
tritBits neutral = false ∷ true ∷ []
tritBits plus = true ∷ false ∷ []

encodeTrit : Trit → List Base
encodeTrit t = encode (tritBits t)

data TritDecode : Set where
  decoded : Trit → TritDecode
  escape : TritDecode
  malformed : TritDecode

decodeBits : List Bool → TritDecode
decodeBits (false ∷ false ∷ []) = decoded minus
decodeBits (false ∷ true ∷ []) = decoded neutral
decodeBits (true ∷ false ∷ []) = decoded plus
decodeBits (true ∷ true ∷ []) = escape
decodeBits _ = malformed

decodeTrit : List Base → TritDecode
decodeTrit xs = decodeBits (decode xs)

trit-channel-roundtrip : ∀ t → decodeTrit (encodeTrit t) ≡ decoded t
trit-channel-roundtrip minus = refl
trit-channel-roundtrip neutral = refl
trit-channel-roundtrip plus = refl

encodedTritIsGenerable : ∀ t → Generable referenceMachine (encodeTrit t)
encodedTritIsGenerable t = encoded-is-generable (tritBits t)

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

tritRateExactlyTwoBases : ∀ t → length (encodeTrit t) ≡ suc (suc zero)
tritRateExactlyTwoBases minus = refl
tritRateExactlyTwoBases neutral = refl
tritRateExactlyTwoBases plus = refl

payloadChecksum : List Bool → Nat
payloadChecksum [] = zero
payloadChecksum (false ∷ xs) = payloadChecksum xs
payloadChecksum (true ∷ xs) = suc (payloadChecksum xs)

checksumRecovered : ∀ bits →
  payloadChecksum (decode (encode bits)) ≡ payloadChecksum bits
checksumRecovered bits = cong payloadChecksum (decode-encode bits)

identityPhysicalChannel : List Base → List Base
identityPhysicalChannel xs = xs

identityChannelRecovery : ∀ bits →
  decode (identityPhysicalChannel (encode bits)) ≡ bits
identityChannelRecovery = decode-encode

data BinaryChoiceArity : Set where
  exactlyTwo : BinaryChoiceArity

data PacketAction : Set where
  consumeTwoChoices reserveEscape : PacketAction

record ChemistryAdaptiveCodecReceipt : Set₁ where
  field
    arity : BinaryChoiceArity
    packetAction : PacketAction
    chemistryGenerable : ∀ t → Generable referenceMachine (encodeTrit t)
    localInverse : ∀ t → decodeTrit (encodeTrit t) ≡ decoded t
    checksumCorrect : ∀ bits →
      payloadChecksum (decode (encode bits)) ≡ payloadChecksum bits
    payloadRate : ∀ t → length (encodeTrit t) ≡ suc (suc zero)
    noErrorChannelRecovery : ∀ bits →
      decode (identityPhysicalChannel (encode bits)) ≡ bits

chemistryAdaptiveCodecReceipt : ChemistryAdaptiveCodecReceipt
chemistryAdaptiveCodecReceipt = record
  { arity = exactlyTwo
  ; packetAction = reserveEscape
  ; chemistryGenerable = encodedTritIsGenerable
  ; localInverse = trit-channel-roundtrip
  ; checksumCorrect = checksumRecovered
  ; payloadRate = tritRateExactlyTwoBases
  ; noErrorChannelRecovery = identityChannelRecovery
  }

------------------------------------------------------------------------
-- Stronger production promotion: the reference machine proves its own chemical
-- pair alternation and exact codec laws.  The full operational motif/hairpin
-- screen and a noisy indel/substitution channel require separate witnesses.

record FullChemistryAndNoisyChannelPromotion : Set₁ where
  field
    fullOperationalAdmissibility : Set
    substitutionCorrection : Set
    insertionCorrection : Set
    deletionCorrection : Set
    strandDropoutRecovery : Set
    rateAfterRedundancy : Set
