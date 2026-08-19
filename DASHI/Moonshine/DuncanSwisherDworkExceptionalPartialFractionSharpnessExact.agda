module DASHI.Moonshine.DuncanSwisherDworkExceptionalPartialFractionSharpnessExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Proposition 3.1 and Propositions 3.2--3.3.
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publ. Math. IHES 37 (1969), 27--115.
-- DOI: 10.1007/BF02684886.
--
-- DASHI CONTRIBUTION
--
-- The older exceptional partial-fraction adapter imported an
-- `ExactLeadingDepth` whose leading valuation was already numerically 3 or 2.
-- This module lowers that boundary.
--
-- The source now supplies only:
--
--   p J_1|U_p = A_1 + remainder,
--   valuation(remainder) > ramification index,
--   compatibility of the additive and multiplicative p-adic valuations.
--
-- The leading A_1 depth is supplied by the separate Dwork ramified-sharpness
-- theorem, so the total exceptional depth is derived rather than imported.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_<_)

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Algebra.SeparatedLeadingValuationExact as Leading
import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Aut
import DASHI.Moonshine.DuncanSwisherDelignePartialFractionMechanismExact as PF
import DASHI.Moonshine.DuncanSwisherDworkRamifiedA1SharpnessExact as Dwork
import DASHI.Moonshine.DuncanSwisherLegendreRamificationDepthExact as Legendre

exceptionalAutType : PF.ExceptionalDelignePrime → Aut.SupersingularAutomorphismType
exceptionalAutType PF.prime5 = Aut.jZeroExceptional
exceptionalAutType PF.prime7 = Aut.j1728Exceptional
exceptionalAutType PF.prime11 = Aut.j1728Exceptional

exceptionalRamificationDepth : PF.ExceptionalDelignePrime → Nat
exceptionalRamificationDepth regime =
  Legendre.legendreJRamificationIndex (exceptionalAutType regime)

exceptionalRamificationMatchesLegacyDepth :
  (regime : PF.ExceptionalDelignePrime) →
  exceptionalRamificationDepth regime ≡ PF.exceptionalLeadingDepth regime
exceptionalRamificationMatchesLegacyDepth PF.prime5 = refl
exceptionalRamificationMatchesLegacyDepth PF.prime7 = refl
exceptionalRamificationMatchesLegacyDepth PF.prime11 = refl

record ExceptionalDworkPartialFractionSeparation
    (regime : PF.ExceptionalDelignePrime) : Set₁ where
  field
    additiveValuation :
      Leading.StrictMinimumValuation
        (Dwork.PadicLocal
          (Dwork.publishedDworkLocalSharpnessData (exceptionalAutType regime)))

    valuationCompatibility :
      (x : Dwork.PadicLocal
        (Dwork.publishedDworkLocalSharpnessData (exceptionalAutType regime))) →
      Leading.valuation additiveValuation x
      ≡ Ramified.valuation
          (Dwork.padicValuation
            (Dwork.publishedDworkLocalSharpnessData (exceptionalAutType regime)))
          x

    pJ1Up :
      Dwork.PadicLocal
        (Dwork.publishedDworkLocalSharpnessData (exceptionalAutType regime))

    remainder :
      Dwork.PadicLocal
        (Dwork.publishedDworkLocalSharpnessData (exceptionalAutType regime))

    partialFractionDecomposition :
      pJ1Up
      ≡ Leading.add additiveValuation
          (Dwork.A1Coefficient
            (Dwork.publishedDworkLocalSharpnessData (exceptionalAutType regime)))
          remainder

    remainderStrictlyDeeper :
      exceptionalRamificationDepth regime
      < Leading.valuation additiveValuation remainder

open ExceptionalDworkPartialFractionSeparation public

postulate
  publishedExceptionalDworkPartialFractionSeparation :
    (regime : PF.ExceptionalDelignePrime) →
    ExceptionalDworkPartialFractionSeparation regime

exceptionalA1DepthIsRamification :
  (regime : PF.ExceptionalDelignePrime) →
  let S = publishedExceptionalDworkPartialFractionSeparation regime
      A = Dwork.publishedDworkLocalSharpnessData (exceptionalAutType regime)
  in Leading.valuation (additiveValuation S) (Dwork.A1Coefficient A)
      ≡ exceptionalRamificationDepth regime
exceptionalA1DepthIsRamification regime =
  let S = publishedExceptionalDworkPartialFractionSeparation regime
      A = Dwork.publishedDworkLocalSharpnessData (exceptionalAutType regime)
  in trans
      (valuationCompatibility S (Dwork.A1Coefficient A))
      (Dwork.sharpA1DepthIsRamification (exceptionalAutType regime))

exceptionalSeparatedLeadingTerm :
  (regime : PF.ExceptionalDelignePrime) →
  let S = publishedExceptionalDworkPartialFractionSeparation regime
  in Leading.SeparatedLeadingTerm (additiveValuation S) (pJ1Up S)
exceptionalSeparatedLeadingTerm regime =
  let S = publishedExceptionalDworkPartialFractionSeparation regime
  in record
    { Leading.leading =
        Dwork.A1Coefficient
          (Dwork.publishedDworkLocalSharpnessData (exceptionalAutType regime))
    ; Leading.remainder = remainder S
    ; Leading.decomposition = partialFractionDecomposition S
    ; Leading.leadingStrictlyShallower =
        let a1Exact = exceptionalA1DepthIsRamification regime
        in subst
          (λ d → d < Leading.valuation (additiveValuation S) (remainder S))
          (sym a1Exact)
          (remainderStrictlyDeeper S)
    }

exceptionalExactLeadingDepthDerived :
  (regime : PF.ExceptionalDelignePrime) →
  let S = publishedExceptionalDworkPartialFractionSeparation regime
  in Leading.ExactLeadingDepth
      (additiveValuation S)
      (pJ1Up S)
      (exceptionalRamificationDepth regime)
exceptionalExactLeadingDepthDerived regime = record
  { Leading.separation = exceptionalSeparatedLeadingTerm regime
  ; Leading.leadingDepthExact = exceptionalA1DepthIsRamification regime
  }

exceptionalTotalDepthIsRamification :
  (regime : PF.ExceptionalDelignePrime) →
  let S = publishedExceptionalDworkPartialFractionSeparation regime
  in Leading.valuation (additiveValuation S) (pJ1Up S)
      ≡ exceptionalRamificationDepth regime
exceptionalTotalDepthIsRamification regime =
  let S = publishedExceptionalDworkPartialFractionSeparation regime
  in Leading.exactLeadingDepthDeterminesTotal
      (additiveValuation S)
      (pJ1Up S)
      (exceptionalRamificationDepth regime)
      (exceptionalExactLeadingDepthDerived regime)

p5TotalDepthIsThree :
  let S = publishedExceptionalDworkPartialFractionSeparation PF.prime5
  in Leading.valuation (additiveValuation S) (pJ1Up S) ≡ 3
p5TotalDepthIsThree = exceptionalTotalDepthIsRamification PF.prime5

p7TotalDepthIsTwo :
  let S = publishedExceptionalDworkPartialFractionSeparation PF.prime7
  in Leading.valuation (additiveValuation S) (pJ1Up S) ≡ 2
p7TotalDepthIsTwo = exceptionalTotalDepthIsRamification PF.prime7

p11TotalDepthIsTwo :
  let S = publishedExceptionalDworkPartialFractionSeparation PF.prime11
  in Leading.valuation (additiveValuation S) (pJ1Up S) ≡ 2
p11TotalDepthIsTwo = exceptionalTotalDepthIsRamification PF.prime11

record DuncanSwisherDworkExceptionalPartialFractionSharpnessBoundary : Set where
  field
    numericLeadingDepthImported : Bool
    dworkA1SharpnessConsumed : Bool
    strictRemainderSeparationImported : Bool
    exceptionalTotalDepthDerived : Bool
    p5DepthThreeDerived : Bool
    p7DepthTwoDerived : Bool
    p11DepthTwoDerived : Bool
    fullPartialFractionSeriesConstructedHere : Bool

canonicalDuncanSwisherDworkExceptionalPartialFractionSharpnessBoundary :
  DuncanSwisherDworkExceptionalPartialFractionSharpnessBoundary
canonicalDuncanSwisherDworkExceptionalPartialFractionSharpnessBoundary = record
  { numericLeadingDepthImported = false
  ; dworkA1SharpnessConsumed = true
  ; strictRemainderSeparationImported = true
  ; exceptionalTotalDepthDerived = true
  ; p5DepthThreeDerived = true
  ; p7DepthTwoDerived = true
  ; p11DepthTwoDerived = true
  ; fullPartialFractionSeriesConstructedHere = false
  }
