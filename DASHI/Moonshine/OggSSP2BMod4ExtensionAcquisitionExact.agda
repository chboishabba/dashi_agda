module DASHI.Moonshine.OggSSP2BMod4ExtensionAcquisitionExact where

------------------------------------------------------------------------
-- MOD-4 EXTENSION ACQUISITION ROUTE
--
-- The post-Brauer obstruction is intrinsically characteristic two:
-- semisimplification forgets the extension/Jordan data and mod-2 reduction
-- also identifies +1 and -1.  A stronger source-backed route is to retain the
-- integral lattice modulo 4.
--
-- Source authority: modern 2-adic lattice methods (Maranda/lattice method;
-- see e.g. Eisele--Margolis, BLMS 2025, DOI 10.1112/blms.70164) explicitly use
-- reduction modulo 4 at p=2 because reduction modulo 2 loses sign data.  Their
-- C2-lattice discussion records the indecomposable integral C2 lattices:
--   E+ : rank-one trivial,
--   E- : rank-one sign,
--   E0 : rank-two regular/free.
--
-- For the finite duad model and the relevant M24-2B involution, the natural
-- permutation lattice has exact C2 decomposition
--
--   Z[duads] = E+^12 + E0^132,
--
-- with no E- summands.  This is an integral extension fingerprint stronger
-- than its mod-2 semisimplification.
--
-- Firewall: this does not assert that the first-stage 2B Tate fibre has this
-- integral lift.  The actual Moonshine V_Z restriction/mod-4 calculation is
-- still required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

trivialRankOneCount : Nat
trivialRankOneCount = 12

signRankOneCount : Nat
signRankOneCount = 0

regularRankTwoCount : Nat
regularRankTwoCount = 132

integralRank : Nat
integralRank = trivialRankOneCount + signRankOneCount + (2 * regularRankTwoCount)

integralRankIs276 : integralRank ≡ 276
integralRankIs276 = refl

mod2FixedDimension : Nat
mod2FixedDimension = trivialRankOneCount + regularRankTwoCount

mod2FixedDimensionIs144 : mod2FixedDimension ≡ 144
mod2FixedDimensionIs144 = refl

mod2TateDefect : Nat
mod2TateDefect = trivialRankOneCount + signRankOneCount

mod2TateDefectIsTwelve : mod2TateDefect ≡ 12
mod2TateDefectIsTwelve = refl

record Mod4ExtensionAcquisitionBoundary : Set where
  constructor mod4-extension-acquisition-boundary
  field
    modTwoSignLossProblemSourced : Bool
    modFourLatticeMethodSourced : Bool
    finiteDuadIntegralC2FingerprintPaid : Bool
    actualMoonshineCommutingPairClassProbeImplemented : Bool
    actualMoonshineModFourRestrictionComputed : Bool
    actualTateExtensionFingerprintMatched : Bool

canonicalMod4ExtensionAcquisitionBoundary : Mod4ExtensionAcquisitionBoundary
canonicalMod4ExtensionAcquisitionBoundary =
  mod4-extension-acquisition-boundary
    true true true true false false
