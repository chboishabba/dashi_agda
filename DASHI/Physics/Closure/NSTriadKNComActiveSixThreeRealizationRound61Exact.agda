module DASHI.Physics.Closure.NSTriadKNComActiveSixThreeRealizationRound61Exact where

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
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- ROUND 61 CONTRIBUTION
--
-- Round60's lightweight B source still accepted the desired 17/64 and 65/512
-- inequalities as three fields.  That is stronger than the genuine physical
-- frontier and duplicates arithmetic already proved in Round35/47.
--
-- The only new analytic/same-object input here is instead:
--
--   on an ACTIVE literal odd-(P/Q) fibre,
--   normalized pair product
--     = pairProduct (sixThreeGramCell shellDistance).
--
-- Off support the literal pair product is exactly zero.  Common-hat geometry
-- supplies |q-r|<=1.  The existing six-three cell then gives, as theorems,
--
--   same shell       <= 17/64,
--   forward adjacent <= 65/512,
--   reverse adjacent <= 65/512.
--
-- Thus B3 is no longer an independent premise once B1+B2 are proved on the
-- physical normalized carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as LightGram
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreSourceRound60Exact as Source
import DASHI.Physics.Closure.NSTriadKNComGramInterferenceRound35Exact as Gram
import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Legacy
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as HatWidth

record PhysicalActiveSixThreeOddPQSource : Set₁ where
  field
    support : Hat.PhysicalOddPQCommonHatIdentification

    -- This is the normalized squared physical T* T / T T* fibre mass, not a
    -- raw velocity-linear transport coefficient.
    normalizedPairProduct : Nat → Nat → ℚ
    normalizedPairProductNonnegative : ∀ q r →
      0ℚ ≤ normalizedPairProduct q r

    shellDistance : Nat → Nat → Nat
    sameShellDistance : ∀ q → shellDistance q q ≡ zero
    forwardAdjacentDistance : ∀ q →
      shellDistance q (suc q) ≡ suc zero
    reverseAdjacentDistance : ∀ q →
      shellDistance (suc q) q ≡ suc zero

    inactivePairProductZero : ∀ q r →
      Hat.supportActive support q r ≡ false →
      normalizedPairProduct q r ≡ 0ℚ

    -- The single genuine B same-object theorem.  It is required only on the
    -- active output fibre; demanding it off support would contradict exact
    -- support annihilation because the model six-three kernel has a nonzero
    -- tail.
    activeProductIsSixThreeGram : ∀ q r →
      Hat.supportActive support q r ≡ true →
      normalizedPairProduct q r
      ≡ Gram.pairProduct (Gram.sixThreeGramCell (shellDistance q r))

open PhysicalActiveSixThreeOddPQSource public

asNormalizedRealization :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  LightGram.PhysicalNormalizedOddPQGramRealization (support physical)
asNormalizedRealization physical = record
  { normalizedSquaredGramEnergy = normalizedPairProduct physical
  ; normalizedSquaredGramEnergyNonnegative =
      normalizedPairProductNonnegative physical
  }

activeWithinOne :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  ∀ q r → Hat.supportActive (support physical) q r ≡ true →
  HatWidth.WithinOne q r
activeWithinOne physical = Hat.commonHatWidthOne (support physical)

sameShellBoundDerived :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  ∀ q →
  Hat.supportActive (support physical) q q ≡ true →
  LightGram.pairProduct (asNormalizedRealization physical) q q
  ≤ LightGram.sameShellTarget
sameShellBoundDerived physical q active
  rewrite activeProductIsSixThreeGram physical q q active
        | sameShellDistance physical q
        | Legacy.sixThreeSameShellExact =
  ℚP.≤-refl

forwardAdjacentBoundDerived :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  ∀ q →
  Hat.supportActive (support physical) q (suc q) ≡ true →
  LightGram.pairProduct (asNormalizedRealization physical) q (suc q)
  ≤ LightGram.adjacentShellTarget
forwardAdjacentBoundDerived physical q active
  rewrite activeProductIsSixThreeGram physical q (suc q) active
        | forwardAdjacentDistance physical q
        | Legacy.sixThreeAdjacentShellExact =
  ℚP.≤-refl

reverseAdjacentBoundDerived :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  ∀ q →
  Hat.supportActive (support physical) (suc q) q ≡ true →
  LightGram.pairProduct (asNormalizedRealization physical) (suc q) q
  ≤ LightGram.adjacentShellTarget
reverseAdjacentBoundDerived physical q active
  rewrite activeProductIsSixThreeGram physical (suc q) q active
        | reverseAdjacentDistance physical q
        | Legacy.sixThreeAdjacentShellExact =
  ℚP.≤-refl

asSameAdjacentBounds :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  LightGram.SameAdjacentNormalizedFibreMassBounds
    (asNormalizedRealization physical)
asSameAdjacentBounds physical = record
  { sameShellBound = sameShellBoundDerived physical
  ; forwardAdjacentBound = forwardAdjacentBoundDerived physical
  ; reverseAdjacentBound = reverseAdjacentBoundDerived physical
  }

asPhysicalNormalizedOddPQSource :
  PhysicalActiveSixThreeOddPQSource → Source.PhysicalNormalizedOddPQSource
asPhysicalNormalizedOddPQSource physical = record
  { support = support physical
  ; realization = asNormalizedRealization physical
  ; bounds = asSameAdjacentBounds physical
  ; shellDistance = shellDistance physical
  ; sameShellDistance = sameShellDistance physical
  ; forwardAdjacentDistance = forwardAdjacentDistance physical
  ; reverseAdjacentDistance = reverseAdjacentDistance physical
  ; inactiveSupportAnnihilatesPairProduct = inactivePairProductZero physical
  }

b3DerivedFromActiveSixThreeSameObject : Bool
b3DerivedFromActiveSixThreeSameObject = true

b3DerivedFromActiveSixThreeSameObjectIsTrue :
  b3DerivedFromActiveSixThreeSameObject ≡ true
b3DerivedFromActiveSixThreeSameObjectIsTrue = refl
