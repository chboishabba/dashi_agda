module DASHI.Crypto.PassiveEncapsulationFibreInvariantExact where

------------------------------------------------------------------------
-- PASSIVE ENCAPSULATION FIBRE INVARIANT
--
-- For an honest KEM encapsulator, ciphertext generation consumes the public
-- encapsulation key and fresh coins, not the decapsulation key.  Therefore two
-- hidden key states with the same public key remain observationally identical
-- under the same honest encapsulation coins.  Passive honest ciphertexts do not
-- split a public-key fibre; a secret-dependent oracle/side condition is needed.
--
-- Reference:
-- Gorjan Alagic, Elaine Barker, Lily Chen, Dustin Moody, Angela Robinson,
-- Hamilton Silberg, Noah Waller,
-- "Recommendations for Key-Encapsulation Mechanisms", NIST SP 800-227,
-- 2025. DOI: 10.6028/NIST.SP.800-227.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

record PublicOnlyEncapsulation : Set₁ where
  constructor publicOnlyEncapsulation
  field
    HiddenKey PublicKey Coins Ciphertext : Set
    derivePublic : HiddenKey → PublicKey
    encapsulateCiphertext : PublicKey → Coins → Ciphertext

open PublicOnlyEncapsulation public

samePublicKeySameHonestCiphertext :
  ∀ {system : PublicOnlyEncapsulation}
    {left right : HiddenKey system} →
  derivePublic system left ≡ derivePublic system right →
  ∀ coins →
  encapsulateCiphertext system (derivePublic system left) coins
  ≡ encapsulateCiphertext system (derivePublic system right) coins
samePublicKeySameHonestCiphertext {system} samePublic coins =
  cong (λ public → encapsulateCiphertext system public coins) samePublic

honestTranscript :
  (system : PublicOnlyEncapsulation) →
  PublicKey system →
  List (Coins system) →
  List (Ciphertext system)
honestTranscript system public [] = []
honestTranscript system public (coin ∷ coins) =
  encapsulateCiphertext system public coin
  ∷ honestTranscript system public coins

samePublicKeySameHonestTranscript :
  ∀ {system : PublicOnlyEncapsulation}
    {left right : HiddenKey system} →
  derivePublic system left ≡ derivePublic system right →
  ∀ coins →
  honestTranscript system (derivePublic system left) coins
  ≡ honestTranscript system (derivePublic system right) coins
samePublicKeySameHonestTranscript {system} samePublic [] = refl
samePublicKeySameHonestTranscript {system} samePublic (coin ∷ coins) =
  cong₂ _∷_
    (samePublicKeySameHonestCiphertext samePublic coin)
    (samePublicKeySameHonestTranscript samePublic coins)
