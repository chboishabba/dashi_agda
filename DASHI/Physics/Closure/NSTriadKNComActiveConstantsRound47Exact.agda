module DASHI.Physics.Closure.NSTriadKNComActiveConstantsRound47Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- After the common-hat support identification, the infinite shell-pair problem
-- has only two active distances.  Make the two cutoff-uniform constants
-- explicit instead of baking the target into every q:
--
--   A0 >= P(q,q),
--   A1 >= P(q,q+1), P(q+1,q),
--
-- and then ask only
--
--   A0 <= 17/64,
--   A1 <= 65/512.
--
-- This is the falsifiable finite-constant formulation proposed in the Round-47
-- analysis.  It derives the direct same/adjacent bounds and therefore the full
-- Boolean support / Cotlar envelope through the existing Round-47 reducer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Active
import DASHI.Physics.Closure.NSTriadKNComBooleanSupportActiveReductionRound45Exact as BoolSupport
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as Support

record PhysicalComTwoActiveConstants
    (skeleton : Active.PhysicalOddPQSupportSkeleton)
    (identification : Active.PhysicalOddPQHatIdentification skeleton) : Set where
  field
    sameShellConstant adjacentShellConstant : ℚ

    sameShellDistance : ∀ q →
      Active.shellDistance skeleton q q ≡ Agda.Builtin.Nat.zero

    forwardAdjacentDistance : ∀ q →
      Active.shellDistance skeleton q (Agda.Builtin.Nat.suc q)
      ≡ Agda.Builtin.Nat.suc Agda.Builtin.Nat.zero

    backwardAdjacentDistance : ∀ q →
      Active.shellDistance skeleton (Agda.Builtin.Nat.suc q) q
      ≡ Agda.Builtin.Nat.suc Agda.Builtin.Nat.zero

    sameShellUniformBound : ∀ q →
      Active.supportActive skeleton q q ≡ true →
      Active.physicalPairProduct skeleton q q ≤ sameShellConstant

    forwardAdjacentUniformBound : ∀ q →
      Active.supportActive skeleton q (Agda.Builtin.Nat.suc q) ≡ true →
      Active.physicalPairProduct skeleton q (Agda.Builtin.Nat.suc q)
      ≤ adjacentShellConstant

    backwardAdjacentUniformBound : ∀ q →
      Active.supportActive skeleton (Agda.Builtin.Nat.suc q) q ≡ true →
      Active.physicalPairProduct skeleton (Agda.Builtin.Nat.suc q) q
      ≤ adjacentShellConstant

    sameShellConstantFitsTarget :
      sameShellConstant ≤ Active.sameShellTarget

    adjacentShellConstantFitsTarget :
      adjacentShellConstant ≤ Active.adjacentShellTarget

open PhysicalComTwoActiveConstants public

asSameAdjacentPhysicalComBounds :
  ∀ {skeleton identification} →
  PhysicalComTwoActiveConstants skeleton identification →
  Active.SameAdjacentPhysicalComBounds skeleton identification
asSameAdjacentPhysicalComBounds constants = record
  { sameShellDistance = sameShellDistance constants
  ; forwardAdjacentDistance = forwardAdjacentDistance constants
  ; backwardAdjacentDistance = backwardAdjacentDistance constants
  ; physicalComSameShellActiveBound = λ q active →
      ℚP.≤-trans
        (sameShellUniformBound constants q active)
        (sameShellConstantFitsTarget constants)
  ; physicalComAdjacentShellActiveBound = λ q active →
      ℚP.≤-trans
        (forwardAdjacentUniformBound constants q active)
        (adjacentShellConstantFitsTarget constants)
  ; physicalComReverseAdjacentShellActiveBound = λ q active →
      ℚP.≤-trans
        (backwardAdjacentUniformBound constants q active)
        (adjacentShellConstantFitsTarget constants)
  }

physicalBooleanSupportInputFromTwoConstants :
  ∀ {skeleton}
    (identification : Active.PhysicalOddPQHatIdentification skeleton) →
  PhysicalComTwoActiveConstants skeleton identification →
  BoolSupport.PhysicalOddPQBooleanSupportInput
physicalBooleanSupportInputFromTwoConstants identification constants =
  Active.physicalBooleanSupportInputFromSameAdjacent
    identification
    (asSameAdjacentPhysicalComBounds constants)

physicalComEnvelopeFromTwoConstants :
  ∀ {skeleton}
    (identification : Active.PhysicalOddPQHatIdentification skeleton) →
  PhysicalComTwoActiveConstants skeleton identification →
  Support.PhysicalComSupportOverlapEnvelope
physicalComEnvelopeFromTwoConstants identification constants =
  Active.physicalComEnvelopeFromSameAdjacent
    identification
    (asSameAdjacentPhysicalComBounds constants)

comReducedToTwoCutoffUniformActiveConstants : Bool
comReducedToTwoCutoffUniformActiveConstants = true

physicalComTwoActiveConstantsConstructed : Bool
physicalComTwoActiveConstantsConstructed = false

comReducedToTwoCutoffUniformActiveConstantsIsTrue :
  comReducedToTwoCutoffUniformActiveConstants ≡ true
comReducedToTwoCutoffUniformActiveConstantsIsTrue = refl
