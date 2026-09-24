module DASHI.Mathematics.Complexity.PNotEqualsNPBooleanResidualFingerprintExact where

------------------------------------------------------------------------
-- BOOLEAN ALGEBRAIC FINGERPRINT OF MANY LOCAL FAILURES
--
-- Let e_1,...,e_n be Boolean residual bits, where e_i=true means local gate
-- obligation i is violated.
--
-- For a Boolean challenge vector r define the GF(2)-style fingerprint
--
--   <r,e> = XOR_i (r_i AND e_i).
--
-- This is a genuine nonlocal summary:
--
--   * if e is the zero residual vector, every challenge fingerprints to false;
--   * if e has a true coordinate i, the all-zero challenge accepts while the
--     unit challenge at i rejects.
--
-- Thus a nonzero residual has both accepting and rejecting challenges.  This
-- provides a concrete algebraic/randomized verification primitive, but also
-- reproduces the PCP existential-randomness seam: existentially choosing r is
-- unsound, because the all-zero challenge always accepts.
--
-- Moreover the direct fingerprint computation structurally consumes one term
-- per residual coordinate.  A sub-|C| verifier therefore still needs a
-- separately certified aggregate/low-degree representation rather than merely
-- replacing n local Boolean checks by one XOR expression.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_)
open import Data.Vec.Base using (Vec; []; _∷_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit

------------------------------------------------------------------------
-- GF(2)-style Boolean arithmetic.
------------------------------------------------------------------------

xorBool : Bool → Bool → Bool
xorBool false right =
  right
xorBool true right =
  Cook.notBool right

xorFalseRight :
  (value : Bool) →
  xorBool value false ≡ value
xorFalseRight false =
  refl
xorFalseRight true =
  refl

dotParity :
  ∀ {n : Nat} →
  Vec Bool n →
  Vec Bool n →
  Bool
dotParity [] [] =
  false
dotParity (weight ∷ weights) (residual ∷ residuals) =
  xorBool
    (Cook.andBool weight residual)
    (dotParity weights residuals)

------------------------------------------------------------------------
-- Zero and unit challenge vectors.
------------------------------------------------------------------------

zeroWeights :
  (n : Nat) →
  Vec Bool n
zeroWeights zero =
  []
zeroWeights (suc n) =
  false ∷ zeroWeights n

unitWeight :
  ∀ {n : Nat} →
  Fin n →
  Vec Bool n
unitWeight {suc n} fzero =
  true ∷ zeroWeights n
unitWeight {suc n} (fsuc index) =
  false ∷ unitWeight index

zeroChallengeFingerprintIsZero :
  ∀ {n : Nat}
    (residuals : Vec Bool n) →
  dotParity (zeroWeights n) residuals
  ≡ false
zeroChallengeFingerprintIsZero [] =
  refl
zeroChallengeFingerprintIsZero (residual ∷ residuals)
    rewrite zeroChallengeFingerprintIsZero residuals =
  refl

unitChallengeReadsCoordinate :
  ∀ {n : Nat}
    (index : Fin n)
    (residuals : Vec Bool n) →
  dotParity
    (unitWeight index)
    residuals
  ≡ Circuit.lookupVec index residuals
unitChallengeReadsCoordinate
    fzero
    (residual ∷ residuals)
    rewrite zeroChallengeFingerprintIsZero residuals
          | xorFalseRight residual =
  refl
unitChallengeReadsCoordinate
    (fsuc index)
    (residual ∷ residuals) =
  unitChallengeReadsCoordinate index residuals

------------------------------------------------------------------------
-- Nonzero residual witness.
------------------------------------------------------------------------

NonZeroResidual :
  ∀ {n : Nat} →
  Vec Bool n →
  Set
NonZeroResidual {n} residuals =
  Σ (Fin n) λ index →
    Circuit.lookupVec index residuals ≡ true

record FingerprintChallengeSplit
    {n : Nat}
    (residuals : Vec Bool n) : Set where
  constructor fingerprint-challenge-split
  field
    acceptingChallenge :
      Vec Bool n

    rejectingChallenge :
      Vec Bool n

    acceptingFingerprint :
      dotParity acceptingChallenge residuals
      ≡ false

    rejectingFingerprint :
      dotParity rejectingChallenge residuals
      ≡ true

open FingerprintChallengeSplit public

nonzeroResidualHasAcceptingAndRejectingChallenges :
  ∀ {n : Nat}
    (residuals : Vec Bool n) →
  NonZeroResidual residuals →
  FingerprintChallengeSplit residuals
nonzeroResidualHasAcceptingAndRejectingChallenges
    {n} residuals (index , residualTrue) =
  fingerprint-challenge-split
    (zeroWeights n)
    (unitWeight index)
    (zeroChallengeFingerprintIsZero residuals)
    rejecting
  where
    rejecting :
      dotParity (unitWeight index) residuals
      ≡ true
    rejecting =
      transitive
        (unitChallengeReadsCoordinate index residuals)
        residualTrue

    transitive :
      ∀ {A : Set} {left middle right : A} →
      left ≡ middle →
      middle ≡ right →
      left ≡ right
    transitive refl refl =
      refl

------------------------------------------------------------------------
-- Direct aggregate cost still touches every residual.
------------------------------------------------------------------------

dotParityTermCount :
  ∀ {n : Nat} →
  Vec Bool n →
  Nat
dotParityTermCount [] =
  zero
dotParityTermCount (residual ∷ residuals) =
  suc (dotParityTermCount residuals)

dotParityTouchesEveryResidual :
  ∀ {n : Nat}
    (residuals : Vec Bool n) →
  dotParityTermCount residuals
  ≡ n
dotParityTouchesEveryResidual [] =
  refl
dotParityTouchesEveryResidual (residual ∷ residuals)
    rewrite dotParityTouchesEveryResidual residuals =
  refl

------------------------------------------------------------------------
-- Consequence.
--
-- Algebraic fingerprinting identifies the right shape of a nonlocal check, but
-- the direct evaluator still scans all n residuals.  The next positive theorem
-- must therefore provide a reusable/succinct authority for the aggregate
-- itself (e.g. a low-degree or recursively certified representation) while
-- preserving soundness under the existential SAT embedding.
------------------------------------------------------------------------
