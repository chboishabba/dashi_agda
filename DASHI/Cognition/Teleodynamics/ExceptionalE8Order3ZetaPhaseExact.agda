module DASHI.Cognition.Teleodynamics.ExceptionalE8Order3ZetaPhaseExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Moonshine.C3FourierConjugationExact as Fourier

------------------------------------------------------------------------
-- E8 ORDER-THREE KERNEL AS THE REPO-NATIVE C3 PHASE CARRIER
--
-- The E8 quotient computation isolates the literal cyclic kernel
--   <w> = { I , w , w^2 }.
-- This file identifies only its abstract C3 multiplication/inversion law with
-- the repo's symbolic cyclotomic phase carrier
--   { 1 , zeta , zeta^2 = zeta^-1 }.
--
-- No equality between an E8 Weyl matrix and a complex number is asserted.
-- The statement is an exact finite-group/phase-coordinate equivalence.
------------------------------------------------------------------------

data E8Order3Phase : Set where
  e8I : E8Order3Phase
  e8W : E8Order3Phase
  e8W2 : E8Order3Phase

multiplyE8Phase : E8Order3Phase → E8Order3Phase → E8Order3Phase
multiplyE8Phase e8I b = b
multiplyE8Phase e8W e8I = e8W
multiplyE8Phase e8W e8W = e8W2
multiplyE8Phase e8W e8W2 = e8I
multiplyE8Phase e8W2 e8I = e8W2
multiplyE8Phase e8W2 e8W = e8I
multiplyE8Phase e8W2 e8W2 = e8W

inverseE8Phase : E8Order3Phase → E8Order3Phase
inverseE8Phase e8I = e8I
inverseE8Phase e8W = e8W2
inverseE8Phase e8W2 = e8W

e8PhaseToC3 : E8Order3Phase → C3.C3Phase
e8PhaseToC3 e8I = C3.phase0
e8PhaseToC3 e8W = C3.phase1
e8PhaseToC3 e8W2 = C3.phase2

c3ToE8Phase : C3.C3Phase → E8Order3Phase
c3ToE8Phase C3.phase0 = e8I
c3ToE8Phase C3.phase1 = e8W
c3ToE8Phase C3.phase2 = e8W2

e8C3RoundTrip : (p : E8Order3Phase) → c3ToE8Phase (e8PhaseToC3 p) ≡ p
e8C3RoundTrip e8I = refl
e8C3RoundTrip e8W = refl
e8C3RoundTrip e8W2 = refl

c3E8RoundTrip : (p : C3.C3Phase) → e8PhaseToC3 (c3ToE8Phase p) ≡ p
c3E8RoundTrip C3.phase0 = refl
c3E8RoundTrip C3.phase1 = refl
c3E8RoundTrip C3.phase2 = refl

multiplicationIntertwines :
  (a b : E8Order3Phase) →
  e8PhaseToC3 (multiplyE8Phase a b)
  ≡ C3.multiplyPhase (e8PhaseToC3 a) (e8PhaseToC3 b)
multiplicationIntertwines e8I b = refl
multiplicationIntertwines e8W e8I = refl
multiplicationIntertwines e8W e8W = refl
multiplicationIntertwines e8W e8W2 = refl
multiplicationIntertwines e8W2 e8I = refl
multiplicationIntertwines e8W2 e8W = refl
multiplicationIntertwines e8W2 e8W2 = refl

inverseIntertwines :
  (p : E8Order3Phase) →
  e8PhaseToC3 (inverseE8Phase p)
  ≡ C3.conjugatePhase (e8PhaseToC3 p)
inverseIntertwines e8I = refl
inverseIntertwines e8W = refl
inverseIntertwines e8W2 = refl

-- The repo Fourier owner calls the same involution inversePhase.
inverseMatchesFourierConjugation :
  (p : E8Order3Phase) →
  e8PhaseToC3 (inverseE8Phase p)
  ≡ Fourier.inversePhase (e8PhaseToC3 p)
inverseMatchesFourierConjugation e8I = refl
inverseMatchesFourierConjugation e8W = refl
inverseMatchesFourierConjugation e8W2 = refl

record E8ZetaPhaseBoundary : Set where
  constructor e8-zeta-phase-boundary
  field
    threePhaseCarrierExact : Bool
    multiplicationIntertwinerExact : Bool
    inversionConjugationIntertwinerExact : Bool
    nontrivialPairMatchesZetaInversePair : Bool
    e8WeylMatrixEqualsComplexZetaClaimed : Bool
    zeta54CarrierAutomaticallyConstructed : Bool
    provenance : String

canonicalE8ZetaPhaseBoundary : E8ZetaPhaseBoundary
canonicalE8ZetaPhaseBoundary = e8-zeta-phase-boundary
  true true true true false false
  "DASHI exact finite C3 phase recognition: I/w/w^2 is identified with 1/zeta/zeta^-1 only as a cyclic phase carrier with multiplication and inversion/conjugation intertwined"
