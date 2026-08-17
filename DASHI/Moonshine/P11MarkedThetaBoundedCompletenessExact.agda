module DASHI.Moonshine.P11MarkedThetaBoundedCompletenessExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Definite reduced norms make fixed-norm representation problems finite.
--
-- DASHI CONTRIBUTION / EXACT SCOPE
--
-- P11MarkedQuaternionThetaExact reduces the two explicit definite norm forms at
-- norm <=5 to six candidate coordinates each.  This module proves COMPLETE
-- classification inside those reduced domains; it does not silently upgrade
-- that finite case split into a generic arbitrary-Z^4 enumeration theorem.
--
-- Exact result:
--
--   j=0 bounded domain:
--     norm 3  -> exactly two candidates,
--     norm 5  -> impossible;
--
--   j=1728 bounded domain:
--     norm 3  -> impossible,
--     norm 5  -> exactly four candidates.
--
-- These are exactly the raw theta cells (2,0;0,4) consumed downstream.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11MarkedQuaternionThetaExact as Theta

------------------------------------------------------------------------
-- j=0 norm-3 solution codes and complete classifier.
------------------------------------------------------------------------

data J0Norm3Code : Set where
  j0Minus j0Plus : J0Norm3Code

j0Norm3CodeCandidate : J0Norm3Code → Theta.J0BoundedCandidate
j0Norm3CodeCandidate j0Minus = Theta.aNeg1d1
j0Norm3CodeCandidate j0Plus = Theta.a0dNeg1

j0Norm3CodeIsSolution :
  (c : J0Norm3Code) → Theta.j0CandidateNorm (j0Norm3CodeCandidate c) ≡ 3
j0Norm3CodeIsSolution j0Minus = refl
j0Norm3CodeIsSolution j0Plus = refl

j0Norm3CandidateComplete :
  (x : Theta.J0BoundedCandidate) →
  Theta.j0CandidateNorm x ≡ 3 →
  J0Norm3Code
j0Norm3CandidateComplete Theta.aNeg1dNeg1 ()
j0Norm3CandidateComplete Theta.aNeg1d0 ()
j0Norm3CandidateComplete Theta.aNeg1d1 refl = j0Minus
j0Norm3CandidateComplete Theta.a0dNeg1 refl = j0Plus
j0Norm3CandidateComplete Theta.a0d0 ()
j0Norm3CandidateComplete Theta.a0d1 ()

j0Norm5CandidateImpossible :
  (x : Theta.J0BoundedCandidate) → Theta.j0CandidateNorm x ≡ 5 → ⊥
j0Norm5CandidateImpossible Theta.aNeg1dNeg1 ()
j0Norm5CandidateImpossible Theta.aNeg1d0 ()
j0Norm5CandidateImpossible Theta.aNeg1d1 ()
j0Norm5CandidateImpossible Theta.a0dNeg1 ()
j0Norm5CandidateImpossible Theta.a0d0 ()
j0Norm5CandidateImpossible Theta.a0d1 ()

------------------------------------------------------------------------
-- j=1728 norm-5 solution codes and complete classifier.
------------------------------------------------------------------------

data J1728Norm5Code : Set where
  nMinusBMinus nMinusBPlus nZeroBMinus nZeroBPlus : J1728Norm5Code

j1728Norm5CodeCandidate : J1728Norm5Code → Theta.J1728BoundedCandidate
j1728Norm5CodeCandidate nMinusBMinus = Theta.aNeg1bNeg1
j1728Norm5CodeCandidate nMinusBPlus = Theta.aNeg1b1
j1728Norm5CodeCandidate nZeroBMinus = Theta.a0bNeg1
j1728Norm5CodeCandidate nZeroBPlus = Theta.a0b1

j1728Norm5CodeIsSolution :
  (c : J1728Norm5Code) →
  Theta.j1728CandidateNorm (j1728Norm5CodeCandidate c) ≡ 5
j1728Norm5CodeIsSolution nMinusBMinus = refl
j1728Norm5CodeIsSolution nMinusBPlus = refl
j1728Norm5CodeIsSolution nZeroBMinus = refl
j1728Norm5CodeIsSolution nZeroBPlus = refl

j1728Norm5CandidateComplete :
  (x : Theta.J1728BoundedCandidate) →
  Theta.j1728CandidateNorm x ≡ 5 →
  J1728Norm5Code
j1728Norm5CandidateComplete Theta.aNeg1bNeg1 refl = nMinusBMinus
j1728Norm5CandidateComplete Theta.aNeg1b0 ()
j1728Norm5CandidateComplete Theta.aNeg1b1 refl = nMinusBPlus
j1728Norm5CandidateComplete Theta.a0bNeg1 refl = nZeroBMinus
j1728Norm5CandidateComplete Theta.a0b0 ()
j1728Norm5CandidateComplete Theta.a0b1 refl = nZeroBPlus

j1728Norm3CandidateImpossible :
  (x : Theta.J1728BoundedCandidate) → Theta.j1728CandidateNorm x ≡ 3 → ⊥
j1728Norm3CandidateImpossible Theta.aNeg1bNeg1 ()
j1728Norm3CandidateImpossible Theta.aNeg1b0 ()
j1728Norm3CandidateImpossible Theta.aNeg1b1 ()
j1728Norm3CandidateImpossible Theta.a0bNeg1 ()
j1728Norm3CandidateImpossible Theta.a0b0 ()
j1728Norm3CandidateImpossible Theta.a0b1 ()

------------------------------------------------------------------------
-- Counts of the COMPLETE finite solution-code carriers.
------------------------------------------------------------------------

j0Norm3CompleteCount : Nat
j0Norm3CompleteCount = 2

j0Norm5CompleteCount : Nat
j0Norm5CompleteCount = 0

j1728Norm3CompleteCount : Nat
j1728Norm3CompleteCount = 0

j1728Norm5CompleteCount : Nat
j1728Norm5CompleteCount = 4

completeCountsRecoverRawTheta :
  (j0Norm3CompleteCount , j1728Norm3CompleteCount)
    ≡ Theta.rawThetaTable Theta.ell3
  ×
  (j0Norm5CompleteCount , j1728Norm5CompleteCount)
    ≡ Theta.rawThetaTable Theta.ell5
completeCountsRecoverRawTheta = refl , refl

record P11MarkedThetaBoundedCompletenessBoundary : Set where
  field
    j0Norm3FiniteDomainComplete : Bool
    j0Norm3FiniteDomainCompleteIsTrue : j0Norm3FiniteDomainComplete ≡ true

    j0Norm5FiniteDomainEmpty : Bool
    j0Norm5FiniteDomainEmptyIsTrue : j0Norm5FiniteDomainEmpty ≡ true

    j1728Norm3FiniteDomainEmpty : Bool
    j1728Norm3FiniteDomainEmptyIsTrue : j1728Norm3FiniteDomainEmpty ≡ true

    j1728Norm5FiniteDomainComplete : Bool
    j1728Norm5FiniteDomainCompleteIsTrue : j1728Norm5FiniteDomainComplete ≡ true

    genericUnboundedIntegerLatticeEnumeratorClaimed : Bool
    genericUnboundedIntegerLatticeEnumeratorClaimedIsFalse :
      genericUnboundedIntegerLatticeEnumeratorClaimed ≡ false

canonicalP11MarkedThetaBoundedCompletenessBoundary :
  P11MarkedThetaBoundedCompletenessBoundary
canonicalP11MarkedThetaBoundedCompletenessBoundary = record
  { j0Norm3FiniteDomainComplete = true
  ; j0Norm3FiniteDomainCompleteIsTrue = refl
  ; j0Norm5FiniteDomainEmpty = true
  ; j0Norm5FiniteDomainEmptyIsTrue = refl
  ; j1728Norm3FiniteDomainEmpty = true
  ; j1728Norm3FiniteDomainEmptyIsTrue = refl
  ; j1728Norm5FiniteDomainComplete = true
  ; j1728Norm5FiniteDomainCompleteIsTrue = refl
  ; genericUnboundedIntegerLatticeEnumeratorClaimed = false
  ; genericUnboundedIntegerLatticeEnumeratorClaimedIsFalse = refl
  }
