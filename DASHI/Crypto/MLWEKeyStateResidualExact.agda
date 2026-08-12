module DASHI.Crypto.MLWEKeyStateResidualExact where

------------------------------------------------------------------------
-- MLWE KEY-STATE RESIDUAL TEST
--
-- Primary references:
-- Oded Regev, "On lattices, learning with errors, random linear codes, and
-- cryptography", STOC 2005. DOI: 10.1145/1060590.1060603.
--
-- Roberto Avanzi, Joppe Bos, Leo Ducas, Eike Kiltz, Tancrede Lepoint,
-- Vadim Lyubashevsky, John M. Schanck, Peter Schwabe, Gregor Seiler,
-- Damien Stehle, "CRYSTALS-Kyber: Algorithm Specifications and Supporting
-- Documentation", version 3.02, 2021. No DOI asserted for the specification.
--
-- The point is statewise and exact: public noisy-linear structure gives a
-- candidate-secret *test*.  The correct secret induces the original small
-- residual.  This does not construct the secret and does not prove an attack.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

record NoisyLinearKeyState : Set₁ where
  constructor noisyLinearKeyState
  field
    Secret Error Public : Set
    publish : Secret → Error → Public
    candidateResidual : Public → Secret → Error
    Small : Error → Set

    correctResidual :
      ∀ secret error →
      candidateResidual (publish secret error) secret ≡ error

open NoisyLinearKeyState public

CandidatePlausible :
  (state : NoisyLinearKeyState) →
  Public state → Secret state → Set
CandidatePlausible state public candidate =
  Small state (candidateResidual state public candidate)

trueSecretPassesResidualTest :
  ∀ {state : NoisyLinearKeyState}
    {secret : Secret state}
    {error : Error state} →
  Small state error →
  CandidatePlausible state (publish state secret error) secret
trueSecretPassesResidualTest {state} {secret} {error} small =
  let open import Relation.Binary.PropositionalEquality using (subst; sym)
  in subst (Small state) (sym (correctResidual state secret error)) small

------------------------------------------------------------------------
-- Search remains separate from testing.
------------------------------------------------------------------------

record CandidateSearch (state : NoisyLinearKeyState) : Set₁ where
  constructor candidateSearch
  field
    search : Public state → Secret state
    searchAlwaysPlausible :
      ∀ public → CandidatePlausible state public (search public)

open CandidateSearch public

record UniqueResidualIdentification (state : NoisyLinearKeyState) : Set₁ where
  constructor uniqueResidualIdentification
  field
    public : Public state
    intendedSecret : Secret state
    intendedPlausible : CandidatePlausible state public intendedSecret
    uniqueness :
      ∀ candidate →
      CandidatePlausible state public candidate →
      candidate ≡ intendedSecret

open UniqueResidualIdentification public
