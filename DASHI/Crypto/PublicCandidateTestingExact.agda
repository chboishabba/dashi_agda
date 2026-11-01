module DASHI.Crypto.PublicCandidateTestingExact where

------------------------------------------------------------------------
-- PUBLIC CANDIDATE TESTING != CANDIDATE SEARCH
--
-- Many public-key systems make a forward relation cheap to evaluate.  That can
-- provide an exact test for a supplied candidate without providing a search
-- algorithm.  This is the common statewise pattern behind the MLWE residual
-- test, public exponentiation/scalar multiplication, and re-encryption checks.
--
-- Reference for the computational-model boundary:
-- Peter W. Shor, "Polynomial-Time Algorithms for Prime Factorization and
-- Discrete Logarithms on a Quantum Computer", SIAM J. Comput. 26(5), 1997.
-- DOI: 10.1137/S0097539795293172.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Deterministic forward maps.
------------------------------------------------------------------------

record PublicForwardMap : Set₁ where
  constructor publicForwardMap
  field
    Hidden Public : Set
    forward : Hidden → Public

open PublicForwardMap public

CandidateMatches :
  (system : PublicForwardMap) →
  Public system → Hidden system → Set
CandidateMatches system public candidate =
  forward system candidate ≡ public

trueHiddenStatePassesForwardTest :
  ∀ {system : PublicForwardMap} (hidden : Hidden system) →
  CandidateMatches system (forward system hidden) hidden
trueHiddenStatePassesForwardTest hidden = refl

record ForwardInjective (system : PublicForwardMap) : Set₁ where
  constructor forwardInjective
  field
    injective :
      ∀ {left right} →
      forward system left ≡ forward system right → left ≡ right

open ForwardInjective public

candidateMatchUniqueUnderInjectivity :
  ∀ {system : PublicForwardMap}
    (oneToOne : ForwardInjective system)
    {hidden candidate : Hidden system} →
  CandidateMatches system (forward system hidden) candidate →
  candidate ≡ hidden
candidateMatchUniqueUnderInjectivity oneToOne match =
  injective oneToOne match

-- Search is a strictly separate object: no constructor is derived from the
-- existence of CandidateMatches.
record ForwardPreimageSearch (system : PublicForwardMap) : Set₁ where
  constructor forwardPreimageSearch
  field
    search : Public system → Hidden system
    searchCorrectOnImage :
      ∀ hidden → search (forward system hidden) ≡ hidden

open ForwardPreimageSearch public

------------------------------------------------------------------------
-- Randomized public encryption/re-encryption checks.
------------------------------------------------------------------------

record RandomizedPublicTransform : Set₁ where
  constructor randomizedPublicTransform
  field
    PublicKey Message Coins Ciphertext : Set
    transform : PublicKey → Coins → Message → Ciphertext

open RandomizedPublicTransform public

RandomizedCandidateMatches :
  (system : RandomizedPublicTransform) →
  PublicKey system → Ciphertext system →
  Message system → Coins system → Set
RandomizedCandidateMatches system public ciphertext message coins =
  transform system public coins message ≡ ciphertext

trueMessageAndCoinsPassReencryptionTest :
  ∀ {system : RandomizedPublicTransform}
    (public : PublicKey system)
    (coins : Coins system)
    (message : Message system) →
  RandomizedCandidateMatches system public
    (transform system public coins message) message coins
trueMessageAndCoinsPassReencryptionTest public coins message = refl

-- Candidate message and randomness form one witness; recovering either from a
-- ciphertext is not supplied by the verifier.
CandidateWitness :
  (system : RandomizedPublicTransform) → Set
CandidateWitness system = Message system × Coins system
