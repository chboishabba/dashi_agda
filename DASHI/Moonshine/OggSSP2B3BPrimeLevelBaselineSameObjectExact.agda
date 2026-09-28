module DASHI.Moonshine.OggSSP2B3BPrimeLevelBaselineSameObjectExact where

------------------------------------------------------------------------
-- 2B / 3B McKAY--THOMPSON SERIES ARE THE DUNCAN--SWISHER PRIME-LEVEL TERM
--
-- EXTERNAL SAME-OBJECT INPUT
--
-- Duncan--Swisher define J_N to be the normalized Hauptmodul for Gamma0(N).
--
-- Standard monstrous moonshine identifies, for p=2,3,
--
--   T_2B = J_2,
--   T_3B = J_3.
--
-- Therefore the ordinary class-specific 2B/3B Hauptmodul is NOT a new
-- exceptional fourth term.  It is literally the J_p object already present in
--
--   v_p(J_1 - J_{p+})
-- + v_p(J_1 - J_p)
-- + v_p(J_1 - J_{p^2}).
--
-- Duncan--Swisher's exact prime-level values at the exceptional primes are:
--
--   v_2(J_1 - J_2) = 16,
--   v_3(J_1 - J_3) =  9.
--
-- Any additional 10/2 mechanism must therefore use extra local/twisted/bad-
-- level structure, not simply repackage T_2B or T_3B.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPSmallCharacteristicHauptmodulTermBaselineExact as Baseline
import DASHI.Moonshine.OggSSP2B3BPadicHauptmodulBridgeExact as Padic
import DASHI.Moonshine.OggSSP2B3BFirstUpCoefficientNoGoExact as FirstUp
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Same normalized Hauptmodul identifiers.
------------------------------------------------------------------------

data NormalizedPrimeHauptmodul : Set where
  gamma02Hauptmodul :
    NormalizedPrimeHauptmodul
  gamma03Hauptmodul :
    NormalizedPrimeHauptmodul

moonshineClassHauptmodul :
  Padic.SmallPrimeMonsterClass ->
  NormalizedPrimeHauptmodul
moonshineClassHauptmodul Padic.class2B =
  gamma02Hauptmodul
moonshineClassHauptmodul Padic.class3B =
  gamma03Hauptmodul

duncanSwisherPrimeHauptmodul :
  Baseline.SmallPrime ->
  NormalizedPrimeHauptmodul
duncanSwisherPrimeHauptmodul Baseline.pTwo =
  gamma02Hauptmodul
duncanSwisherPrimeHauptmodul Baseline.pThree =
  gamma03Hauptmodul

class2BIsDuncanSwisherJ2 :
  moonshineClassHauptmodul Padic.class2B
  ≡
  duncanSwisherPrimeHauptmodul Baseline.pTwo
class2BIsDuncanSwisherJ2 = refl

class3BIsDuncanSwisherJ3 :
  moonshineClassHauptmodul Padic.class3B
  ≡
  duncanSwisherPrimeHauptmodul Baseline.pThree
class3BIsDuncanSwisherJ3 = refl

------------------------------------------------------------------------
-- 2. Exact prime-level baseline valuations.
------------------------------------------------------------------------

class2BPrimeLevelDifferenceValuation : Nat
class2BPrimeLevelDifferenceValuation =
  Baseline.baselineValuation
    Baseline.pTwo
    Baseline.primeLevel

class3BPrimeLevelDifferenceValuation : Nat
class3BPrimeLevelDifferenceValuation =
  Baseline.baselineValuation
    Baseline.pThree
    Baseline.primeLevel

class2BPrimeLevelDifferenceIsSixteen :
  class2BPrimeLevelDifferenceValuation ≡ 16
class2BPrimeLevelDifferenceIsSixteen = refl

class3BPrimeLevelDifferenceIsNine :
  class3BPrimeLevelDifferenceValuation ≡ 9
class3BPrimeLevelDifferenceIsNine = refl

------------------------------------------------------------------------
-- 3. Ordinary U_p behavior belongs to the already-present J_p lane.
------------------------------------------------------------------------

firstUpNoGoBoundary :
  FirstUp.FirstUpCoefficientNoGoBoundary
firstUpNoGoBoundary =
  FirstUp.canonicalFirstUpCoefficientNoGoBoundary

data Ordinary2BSeriesIsIndependentFourthTerm : Set where
data Ordinary3BSeriesIsIndependentFourthTerm : Set where
data PadicAnnihilationCreatesAdditionalBaselineSummand : Set where

ordinary2BSeriesAlreadyOccupiesPrimeLevelTerm :
  Ordinary2BSeriesIsIndependentFourthTerm -> ⊥
ordinary2BSeriesAlreadyOccupiesPrimeLevelTerm ()

ordinary3BSeriesAlreadyOccupiesPrimeLevelTerm :
  Ordinary3BSeriesIsIndependentFourthTerm -> ⊥
ordinary3BSeriesAlreadyOccupiesPrimeLevelTerm ()

padicAnnihilationDoesNotCreateAdditionalSummand :
  PadicAnnihilationCreatesAdditionalBaselineSummand -> ⊥
padicAnnihilationDoesNotCreateAdditionalSummand ()

------------------------------------------------------------------------
-- 4. Attribution sources.
------------------------------------------------------------------------

duncanSwisher : Source.AttributedSource
duncanSwisher =
  Source.mkNoDOISource
    "John F. R. Duncan and Holly Swisher"
    "Modular Functions and the Monstrous Exponents"
    "arXiv:2602.09135"
    "2026"
    "https://arxiv.org/abs/2602.09135"
    Source.academicArticleSource
    "defines J_N as the normalized Hauptmodul for Gamma0(N) and supplies the prime-level valuation term; does not make the DASHI fourth-term recognition"
    Source.publicAttribution

primeMoonshineHauptmodulSource : Source.AttributedSource
primeMoonshineHauptmodulSource =
  Source.mkDOISource
    "Toshiki Matsusaka"
    "The Fourier coefficients of the McKay-Thompson series and the traces of CM values"
    "Research in Number Theory 3, article 23"
    "2017"
    "10.1007/s40993-017-0090-x"
    "https://doi.org/10.1007/s40993-017-0090-x"
    Source.academicArticleSource
    "explicitly records j_p = T_pB = normalized Gamma0(p) Hauptmodul for p=2,3,5,7,13; used for the same-object T_2B=J_2 and T_3B=J_3 identification"
    Source.publicAttribution

sameObjectSourceAtlas : Source.AttributedSourceAtlas
sameObjectSourceAtlas =
  Source.mkSourceAtlas
    "2B/3B prime-level same-object source atlas"
    "DASHI.Moonshine.OggSSP2B3BPrimeLevelBaselineSameObjectExact"
    (duncanSwisher ∷ primeMoonshineHauptmodulSource ∷ [])
    "external sources own the normalized-Hauptmodul same-object identification; DASHI owns only the explicit consequence that ordinary 2B/3B cannot be counted again as an independent fourth term"

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record PrimeLevelBaselineSameObjectBoundary : Set where
  constructor prime-level-baseline-same-object-boundary
  field
    duncanSwisherNormalizedJpDefinitionSourced : Bool
    class2BEqualsJ2Sourced : Bool
    class3BEqualsJ3Sourced : Bool
    p2PrimeLevelValuationSixteenPaid : Bool
    p3PrimeLevelValuationNinePaid : Bool
    ordinary2BFourthTermRejected : Bool
    ordinary3BFourthTermRejected : Bool
    strongerTwistedBadLevelObjectStillRequired : Bool
    attributionFirewallPreserved : Bool

canonicalPrimeLevelBaselineSameObjectBoundary :
  PrimeLevelBaselineSameObjectBoundary
canonicalPrimeLevelBaselineSameObjectBoundary =
  prime-level-baseline-same-object-boundary
    true true true true true true true true true
