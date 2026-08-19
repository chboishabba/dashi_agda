module DASHI.Moonshine.DuncanSwisherFaberDelignePartialFractionWeldExact where

------------------------------------------------------------------------
-- Faber V_p discrepancy <-> Deligne partial-fraction depth weld
--
-- PRIMARY SOURCE
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Proposition 3.1 identifies the n=1 p-adic depths 3,2,1 with the three
-- supersingular automorphism types.  Remark 1.4 independently gives
--
--   v_p(j|V_p-Phi_p(j)) = m_p.
--
-- The earlier repo weld proves
--
--   2 * d_min = m_p.
--
-- DuncanSwisherDelignePartialFractionMechanismExact now DERIVES the valuation
-- of p J_1|U_p from the partial-fraction mechanism rather than importing the
-- output number.  This file records the resulting common scale:
--
--   Faber depth = full minimum automorphism order = 2 * partial-fraction depth.
--
-- The equality is at a declared consumer.  Faber Laurent coefficients,
-- supersingular automorphism geometry and p-adic partial fractions remain
-- distinct source carriers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.SeparatedLeadingValuationExact as Leading
import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Deligne
import DASHI.Moonshine.DuncanSwisherDelignePartialFractionMechanismExact as Partial
import DASHI.Moonshine.DuncanSwisherFaberVpDepthExact as Faber

------------------------------------------------------------------------
-- The source's three automorphism types supply the exact minimum witness for
-- each exceptional Ogg regime.
------------------------------------------------------------------------

exceptionalMinimumWitness :
  Partial.ExceptionalDelignePrime → Deligne.MinimumAutomorphismWitness
exceptionalMinimumWitness Partial.prime5 =
  Deligne.minimum-automorphism-witness Deligne.jZeroExceptional 6 refl
exceptionalMinimumWitness Partial.prime7 =
  Deligne.minimum-automorphism-witness Deligne.j1728Exceptional 4 refl
exceptionalMinimumWitness Partial.prime11 =
  Deligne.minimum-automorphism-witness Deligne.j1728Exceptional 4 refl

exceptionalPartialDepthEqualsDeligneMinimum :
  (r : Partial.ExceptionalDelignePrime) →
  Partial.exceptionalLeadingDepth r
  ≡ Deligne.minimumFirstPoleDepth (exceptionalMinimumWitness r)
exceptionalPartialDepthEqualsDeligneMinimum Partial.prime5 = refl
exceptionalPartialDepthEqualsDeligneMinimum Partial.prime7 = refl
exceptionalPartialDepthEqualsDeligneMinimum Partial.prime11 = refl

exceptionalDoublePartialDepthEqualsMinimumAut :
  (r : Partial.ExceptionalDelignePrime) →
  2 * Partial.exceptionalLeadingDepth r
  ≡ Deligne.minimumFullOrder (exceptionalMinimumWitness r)
exceptionalDoublePartialDepthEqualsMinimumAut r =
  trans
    (cong (λ d → 2 * d) (exceptionalPartialDepthEqualsDeligneMinimum r))
    (Deligne.minimumDepthDoublesToMinimumFullOrder (exceptionalMinimumWitness r))

------------------------------------------------------------------------
-- For the p>=13 Fricke-zero regime, existence of an ordinary supersingular
-- pole is exactly the generic automorphism type: depth 1, full order 2.
------------------------------------------------------------------------

ordinaryMinimumWitness : Deligne.MinimumAutomorphismWitness
ordinaryMinimumWitness =
  Deligne.minimum-automorphism-witness Deligne.ordinaryType 2 refl

ordinaryPartialDepthEqualsDeligneMinimum :
  1 ≡ Deligne.minimumFirstPoleDepth ordinaryMinimumWitness
ordinaryPartialDepthEqualsDeligneMinimum = refl

ordinaryDoublePartialDepthEqualsMinimumAut :
  2 * 1 ≡ Deligne.minimumFullOrder ordinaryMinimumWitness
ordinaryDoublePartialDepthEqualsMinimumAut =
  Deligne.minimumDepthDoublesToMinimumFullOrder ordinaryMinimumWitness

------------------------------------------------------------------------
-- One generic scale object.  It can be instantiated by the exceptional or
-- ordinary mechanisms without identifying their carriers.
------------------------------------------------------------------------

record PartialFractionAutomorphismScale : Set where
  constructor partial-fraction-automorphism-scale
  field
    partialFractionDepth : Nat
    minimumFullAutomorphismOrder : Nat
    doubleDepthIsMinimumAut :
      2 * partialFractionDepth ≡ minimumFullAutomorphismOrder

open PartialFractionAutomorphismScale public

exceptionalScale :
  Partial.ExceptionalDelignePrime → PartialFractionAutomorphismScale
exceptionalScale r = partial-fraction-automorphism-scale
  (Partial.exceptionalLeadingDepth r)
  (Deligne.minimumFullOrder (exceptionalMinimumWitness r))
  (exceptionalDoublePartialDepthEqualsMinimumAut r)

ordinaryScale : PartialFractionAutomorphismScale
ordinaryScale = partial-fraction-automorphism-scale
  1
  2
  ordinaryDoublePartialDepthEqualsMinimumAut

------------------------------------------------------------------------
-- The scale values are not free labels: connect them to the ACTUAL derived
-- partial-fraction output valuations from the new mechanism module.
------------------------------------------------------------------------

exceptionalDerivedValuationEqualsScale :
  (r : Partial.ExceptionalDelignePrime) →
  let A = Partial.publishedExceptionalPartialFractionAuthority r
  in
  Leading.valuation (Partial.valuationStructure A) (Partial.pJ1Up A)
  ≡ partialFractionDepth (exceptionalScale r)
exceptionalDerivedValuationEqualsScale r =
  Partial.exceptionalPartialFractionDepth r

ordinaryDerivedValuationEqualsScale :
  (P : Partial.Pge13FrickeZeroPrime) →
  let A = Partial.publishedOrdinaryPoleMomentAuthority P
  in
  Partial.totalDepth A ≡ partialFractionDepth ordinaryScale
ordinaryDerivedValuationEqualsScale P =
  Partial.ordinaryPoleTotalDepthIsOne P

------------------------------------------------------------------------
-- Faber + partial-fraction comparison through the SAME minimum automorphism
-- scale.  The Faber authority owns its Laurent valuation witness; this record
-- supplies only the source equality to the already-derived geometric scale.
------------------------------------------------------------------------

record FaberPartialFractionSameScale
    (p : Nat)
    (S : PartialFractionAutomorphismScale) : Set₁ where
  field
    faberAuthority : Faber.DuncanSwisherFaberVpAuthority p
    faberDepthIsMinimumAut :
      Faber.discrepancyDepth faberAuthority
      ≡ minimumFullAutomorphismOrder S

open FaberPartialFractionSameScale public

faberDepthEqualsDoublePartialFractionDepth :
  {p : Nat} →
  {S : PartialFractionAutomorphismScale} →
  (W : FaberPartialFractionSameScale p S) →
  Faber.discrepancyDepth (faberAuthority W)
  ≡ 2 * partialFractionDepth S
faberDepthEqualsDoublePartialFractionDepth {S = S} W =
  trans
    (faberDepthIsMinimumAut W)
    (sym (doubleDepthIsMinimumAut S))

------------------------------------------------------------------------
-- Explicit numerical scale regressions from the mechanism, not Monster table.
------------------------------------------------------------------------

p5Scale :
  partialFractionDepth (exceptionalScale Partial.prime5) ≡ 3
p5Scale = refl

p7Scale :
  partialFractionDepth (exceptionalScale Partial.prime7) ≡ 2
p7Scale = refl

p11Scale :
  partialFractionDepth (exceptionalScale Partial.prime11) ≡ 2
p11Scale = refl

pge13Scale : partialFractionDepth ordinaryScale ≡ 1
pge13Scale = refl

record DuncanSwisherFaberDelignePartialFractionBoundary : Set where
  field
    exceptionalAutDepthScaleDerived : Bool
    ordinaryAutDepthScaleDerived : Bool
    exceptionalOutputValuationTiedToScale : Bool
    ordinaryOutputValuationTiedToScale : Bool
    faberDepthMeetsPartialFractionThroughAutScale : Bool
    faberAndPartialFractionCarriersIdentified : Bool
    monsterExponentTableUsedToSetScale : Bool
    lowPrimeTwoThreePromoted : Bool

canonicalDuncanSwisherFaberDelignePartialFractionBoundary :
  DuncanSwisherFaberDelignePartialFractionBoundary
canonicalDuncanSwisherFaberDelignePartialFractionBoundary = record
  { exceptionalAutDepthScaleDerived = true
  ; ordinaryAutDepthScaleDerived = true
  ; exceptionalOutputValuationTiedToScale = true
  ; ordinaryOutputValuationTiedToScale = true
  ; faberDepthMeetsPartialFractionThroughAutScale = true
  ; faberAndPartialFractionCarriersIdentified = false
  ; monsterExponentTableUsedToSetScale = false
  ; lowPrimeTwoThreePromoted = false
  }
