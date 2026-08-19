module DASHI.Moonshine.DuncanSwisherDelignePartialFractionMechanismExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Proposition 3.1, equations (3.1)--(3.7), Propositions 3.2--3.3.
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publications Mathematiques de l'IHES 37 (1969),
-- 27--115. DOI: 10.1007/BF02684886.
--
-- Masao Koike,
-- "Congruences between modular forms and functions and applications to the
-- conjecture of Atkin", J. Fac. Sci. Univ. Tokyo Sect. IA Math. 20 (1973),
-- 129--169. Repository DOI/identifier: 10.15083/00039793.
--
-- Holly Swisher,
-- "A remark on Hecke operators and a theorem of Dwork and Koike",
-- Illinois J. Math. 48 (2004), 353--356. DOI: 10.1215/ijm/1258136188.
--
-- SOURCE MECHANISM
--
-- Duncan--Swisher Proposition 3.1 gives
--
--   p J_1|U_p
--     = - sum_alpha sum_{n>=1}
--           A_n(alpha^) (J_1-alpha^)^{-n},
--
-- with sharp n=1 p-adic depths for p>3:
--
--   j=0        : 3,
--   j=1728     : 2,
--   ordinary   : 1.
--
-- For p=5,7,11 the required valuation follows from a strictly shallower
-- exceptional leading part than the remaining terms.  For p>=13 on the
-- Fricke-genus-zero branch, ordinary depth-one poles exist.  Equation (3.7)
-- sends their first-pole coefficient vector to power moments; if an extra
-- factor p occurred, every moment would vanish modulo p^2.  The distinct pole
-- values give an invertible Vandermonde transform, contradicting exact depth 1.
--
-- DASHI CONTRIBUTION
--
-- Formalize those TWO noncancellation mechanisms and derive the output depths
-- instead of importing Propositions 3.2/3.3 as numeric receipts.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; _<_; suc; z≤n; s≤s)
open import Data.Nat.Primality using (Prime)

import DASHI.Algebra.SeparatedLeadingValuationExact as Leading
import DASHI.Algebra.VandermondeMomentNonCancellationExact as Moment
import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Fricke
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector

------------------------------------------------------------------------
-- Exceptional Ogg primes p=5,7,11: the source partial-fraction truncation has
-- a unique minimum-depth leading stratum.
------------------------------------------------------------------------

data ExceptionalDelignePrime : Set where
  prime5 prime7 prime11 : ExceptionalDelignePrime

exceptionalPrimeValue : ExceptionalDelignePrime → Nat
exceptionalPrimeValue prime5 = 5
exceptionalPrimeValue prime7 = 7
exceptionalPrimeValue prime11 = 11

exceptionalLeadingDepth : ExceptionalDelignePrime → Nat
exceptionalLeadingDepth prime5 = 3
exceptionalLeadingDepth prime7 = 2
exceptionalLeadingDepth prime11 = 2

record ExceptionalPartialFractionAuthority
    (regime : ExceptionalDelignePrime) : Set₁ where
  field
    PadicSeries : Set
    valuationStructure : Leading.StrictMinimumValuation PadicSeries
    pJ1Up : PadicSeries

    -- Raw Proposition-3.1 truncation data: the leading contribution has the
    -- sharp first-pole depth and the sum of every remaining contribution is
    -- strictly deeper.
    leadingDepthMechanism :
      Leading.ExactLeadingDepth
        valuationStructure
        pJ1Up
        (exceptionalLeadingDepth regime)

open ExceptionalPartialFractionAuthority public

postulate
  publishedExceptionalPartialFractionAuthority :
    (regime : ExceptionalDelignePrime) →
    ExceptionalPartialFractionAuthority regime

exceptionalPartialFractionDepth :
  (regime : ExceptionalDelignePrime) →
  let A = publishedExceptionalPartialFractionAuthority regime
  in
  Leading.valuation (valuationStructure A) (pJ1Up A)
  ≡ exceptionalLeadingDepth regime
exceptionalPartialFractionDepth regime =
  let A = publishedExceptionalPartialFractionAuthority regime
  in
  Leading.exactLeadingDepthDeterminesTotal
    (valuationStructure A)
    (pJ1Up A)
    (exceptionalLeadingDepth regime)
    (leadingDepthMechanism A)

p5PartialFractionDepthIsThree :
  let A = publishedExceptionalPartialFractionAuthority prime5
  in Leading.valuation (valuationStructure A) (pJ1Up A) ≡ 3
p5PartialFractionDepthIsThree = exceptionalPartialFractionDepth prime5

p7PartialFractionDepthIsTwo :
  let A = publishedExceptionalPartialFractionAuthority prime7
  in Leading.valuation (valuationStructure A) (pJ1Up A) ≡ 2
p7PartialFractionDepthIsTwo = exceptionalPartialFractionDepth prime7

p11PartialFractionDepthIsTwo :
  let A = publishedExceptionalPartialFractionAuthority prime11
  in Leading.valuation (valuationStructure A) (pJ1Up A) ≡ 2
p11PartialFractionDepthIsTwo = exceptionalPartialFractionDepth prime11

------------------------------------------------------------------------
-- p>=13 Fricke-genus-zero branch: finite Vandermonde noncancellation.
------------------------------------------------------------------------

record Pge13FrickeZeroPrime : Set₁ where
  field
    p : Nat
    prime : Prime p
    ge5 : 5 ≤ p
    ge13 : 13 ≤ p
    frickeGenusZero :
      Selector.genericFrickeGenus (Fricke.publishedAuthorityAt p prime ge5) ≡ 0

open Pge13FrickeZeroPrime public

record OrdinaryPoleMomentAuthority (P : Pge13FrickeZeroPrime) : Set₁ where
  field
    CoefficientLayer : Set
    MomentLayer : Set

    vandermonde :
      Moment.VandermondeMomentSeparation CoefficientLayer MomentLayer

    firstPoleResidues : CoefficientLayer
    firstPoleResiduesNonzero :
      Moment.NonzeroCoefficientVector
        (Moment.transform vandermonde)
        firstPoleResidues

    -- v_p(p J_1|U_p) is already >=1 from Proposition 3.1.
    totalDepth : Nat
    totalDepthAtLeastOne : 1 ≤ totalDepth

    -- Equation (3.7): if total depth were >=2, every first-pole power moment
    -- would vanish in the p^2 residue layer.
    extraDepthForcesAllMomentsZero :
      2 ≤ totalDepth →
      Moment.momentTransform (Moment.transform vandermonde) firstPoleResidues
      ≡ Moment.zeroMoment (Moment.transform vandermonde)

open OrdinaryPoleMomentAuthority public

postulate
  publishedOrdinaryPoleMomentAuthority :
    (P : Pge13FrickeZeroPrime) → OrdinaryPoleMomentAuthority P

------------------------------------------------------------------------
-- Pure finite proof of Proposition 3.3's valuation conclusion.
------------------------------------------------------------------------

ordinaryPoleTotalDepthIsOne :
  (P : Pge13FrickeZeroPrime) →
  let A = publishedOrdinaryPoleMomentAuthority P
  in totalDepth A ≡ 1
ordinaryPoleTotalDepthIsOne P
  with totalDepth (publishedOrdinaryPoleMomentAuthority P)
     | totalDepthAtLeastOne (publishedOrdinaryPoleMomentAuthority P)
... | 0 | ()
... | 1 | lower = refl
... | suc (suc n) | lower =
  ⊥-elim
    (Moment.vandermondeNoncancellation
      (vandermonde (publishedOrdinaryPoleMomentAuthority P))
      (firstPoleResidues (publishedOrdinaryPoleMomentAuthority P))
      (firstPoleResiduesNonzero (publishedOrdinaryPoleMomentAuthority P))
      (extraDepthForcesAllMomentsZero
        (publishedOrdinaryPoleMomentAuthority P)
        (s≤s (s≤s z≤n))))

------------------------------------------------------------------------
-- Unified p>3 genus-zero depth code for the four source mechanisms.
------------------------------------------------------------------------

data DelignePartialFractionDepthCode : Set where
  exceptionalDepth : ExceptionalDelignePrime → DelignePartialFractionDepthCode
  ordinaryDepth : Nat → DelignePartialFractionDepthCode

partialFractionDepthValue : DelignePartialFractionDepthCode → Nat
partialFractionDepthValue (exceptionalDepth regime) = exceptionalLeadingDepth regime
partialFractionDepthValue (ordinaryDepth p) = 1

record DuncanSwisherDelignePartialFractionBoundary : Set where
  field
    dworkKoikePartialFractionShapePinned : Bool
    exceptionalLeadingDepthMechanismImported : Bool
    exceptionalOutputDepthDerived : Bool
    pge13MomentExtractionImported : Bool
    vandermondeInverseCarriesNoncancellation : Bool
    pge13OutputDepthOneDerived : Bool
    propositions32And33ImportedAsNumericReceipts : Bool
    fullPadicAnalyticConstructionReproved : Bool
    lowPrimeTwoThreePromoted : Bool

canonicalDuncanSwisherDelignePartialFractionBoundary :
  DuncanSwisherDelignePartialFractionBoundary
canonicalDuncanSwisherDelignePartialFractionBoundary = record
  { dworkKoikePartialFractionShapePinned = true
  ; exceptionalLeadingDepthMechanismImported = true
  ; exceptionalOutputDepthDerived = true
  ; pge13MomentExtractionImported = true
  ; vandermondeInverseCarriesNoncancellation = true
  ; pge13OutputDepthOneDerived = true
  ; propositions32And33ImportedAsNumericReceipts = false
  ; fullPadicAnalyticConstructionReproved = false
  ; lowPrimeTwoThreePromoted = false
  }
