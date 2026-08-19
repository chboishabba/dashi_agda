module DASHI.Moonshine.DuncanSwisherFaberPrimeIndexedMinimumWeldExact where

------------------------------------------------------------------------
-- FABER/V_p DEPTH <-> GENUINE PRIME-INDEXED MINIMUM
--
-- PRIMARY SOURCE
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Remark 1.4:
--
--   m_p = v_p(j|V_p - Phi_p(j))
--
-- for every prime p.
--
-- DASHI CONTRIBUTION
--
-- The earlier Faber bridge used the old type-only `MinimumAutomorphismWitness`.
-- This owner replaces that comparison surface by the genuine locus-indexed
-- minimum witness carrying attainment + a lower bound over every point.
-- Thus equality with the Faber defect is equality with an ACTUAL minimum, not
-- with a selected automorphism type that happened to have the desired order.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.DuncanSwisherFaberVpDepthExact as Faber
import DASHI.Moonshine.DuncanSwisherPrimeIndexedMinimumAutomorphismExact as Minimum
import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Deligne

record FaberPrimeIndexedSameMinimum
    (p : Nat)
    (Point : Set)
    (autType : Point → Deligne.SupersingularAutomorphismType)
    (W : Minimum.SupersingularMinimumAutWitness Point
      (λ x → Deligne.fullAutomorphismOrder (autType x))) : Set₁ where
  field
    faberAuthority : Faber.DuncanSwisherFaberVpAuthority p
    sameMinimum :
      Faber.discrepancyDepth faberAuthority ≡ Minimum.minimumOrder W

open FaberPrimeIndexedSameMinimum public

faberDepthEqualsTwiceActualMinimumDeligneDepth :
  ∀ {p : Nat} {Point : Set}
    {autType : Point → Deligne.SupersingularAutomorphismType}
    {W : Minimum.SupersingularMinimumAutWitness Point
      (λ x → Deligne.fullAutomorphismOrder (autType x))} →
  (A : FaberPrimeIndexedSameMinimum p Point autType W) →
  Faber.discrepancyDepth (faberAuthority A)
  ≡ 2 * Minimum.minimumDepth autType W
faberDepthEqualsTwiceActualMinimumDeligneDepth {autType = autType} {W = W} A =
  trans
    (sameMinimum A)
    (sym (Minimum.minimumDepthDoublesToMinimumAut autType W))

-- Concrete shape the theorem supplies at p=11 once the published Faber
-- authority is paired with the actual two-point supersingular minimum.
record P11FaberActualMinimumAuthority : Set₁ where
  field
    faberAuthority : Faber.DuncanSwisherFaberVpAuthority 11
    faberDepthIsActualMp :
      Faber.discrepancyDepth faberAuthority
      ≡ Minimum.minimumOrder Minimum.p11Minimum

open P11FaberActualMinimumAuthority public

p11FaberDepthEqualsFour :
  (A : P11FaberActualMinimumAuthority) →
  Faber.discrepancyDepth (P11FaberActualMinimumAuthority.faberAuthority A) ≡ 4
p11FaberDepthEqualsFour A =
  trans
    (P11FaberActualMinimumAuthority.faberDepthIsActualMp A)
    Minimum.p11MinimumOrderIsFour

record DuncanSwisherFaberPrimeIndexedMinimumBoundary : Set where
  field
    faberCarrierRetained : Bool
    genuineMinimumWitnessConsumed : Bool
    attainmentRequired : Bool
    locusWideLowerBoundRequired : Bool
    faberEqualsTwiceMinimumDeligneDepthDerived : Bool
    typeOnlyMinimumWitnessCanonicalHere : Bool
    faberCarrierIdentifiedWithSupersingularCarrier : Bool

canonicalDuncanSwisherFaberPrimeIndexedMinimumBoundary :
  DuncanSwisherFaberPrimeIndexedMinimumBoundary
canonicalDuncanSwisherFaberPrimeIndexedMinimumBoundary = record
  { faberCarrierRetained = true
  ; genuineMinimumWitnessConsumed = true
  ; attainmentRequired = true
  ; locusWideLowerBoundRequired = true
  ; faberEqualsTwiceMinimumDeligneDepthDerived = true
  ; typeOnlyMinimumWitnessCanonicalHere = false
  ; faberCarrierIdentifiedWithSupersingularCarrier = false
  }
