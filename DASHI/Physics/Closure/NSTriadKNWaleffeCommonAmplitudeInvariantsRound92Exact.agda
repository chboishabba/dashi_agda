module DASHI.Physics.Closure.NSTriadKNWaleffeCommonAmplitudeInvariantsRound92Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND92 / COMMON-AMPLITUDE INVARIANT KERNEL
--
-- In the helical triad representation, one triad has a common scalar amplitude
-- A and three cyclic signed-eigenvalue differences.  Abstract the signed curl
-- eigenvalues as
--
--      a = s_p |p|,  b = s_q |q|,  c = s_r |r|.
--
-- The three modal nonlinear energy transfers have the common-amplitude form
--
--      T_p = (b-c) A,
--      T_q = (c-a) A,
--      T_r = (a-b) A.
--
-- The two Euler invariants are then pure ring identities:
--
--      T_p + T_q + T_r = 0,
--      a T_p + b T_q + c T_r = 0.
--
-- Therefore a PHYSICAL proof need not establish energy and helicity
-- conservation independently on every helical class.  It is enough to prove
-- the same-object Waleffe common-amplitude representation for the literal
-- Fourier triad transfer.  The two invariant laws then follow automatically.
--
-- No statistical cascade claim is used here.  This file proves only the exact
-- cyclic algebra that the cited helical triad formula exposes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

record WaleffeCommonAmplitudeTriad : Set where
  constructor waleffe-common-amplitude-triad
  field
    signedP signedQ signedR amplitude : ℚ

open WaleffeCommonAmplitudeTriad public

transferP transferQ transferR : WaleffeCommonAmplitudeTriad → ℚ
transferP triad = (signedQ triad - signedR triad) * amplitude triad
transferQ triad = (signedR triad - signedP triad) * amplitude triad
transferR triad = (signedP triad - signedQ triad) * amplitude triad

energyTransferSum : WaleffeCommonAmplitudeTriad → ℚ
energyTransferSum triad =
  transferP triad + transferQ triad + transferR triad

signedHelicityTransferSum : WaleffeCommonAmplitudeTriad → ℚ
signedHelicityTransferSum triad =
  signedP triad * transferP triad
  + signedQ triad * transferQ triad
  + signedR triad * transferR triad

commonAmplitudeEnergyConservation :
  (triad : WaleffeCommonAmplitudeTriad) →
  energyTransferSum triad ≡ 0ℚ
commonAmplitudeEnergyConservation triad =
  solve
    ( signedP triad ∷ signedQ triad ∷ signedR triad
    ∷ amplitude triad ∷ [])

commonAmplitudeSignedHelicityConservation :
  (triad : WaleffeCommonAmplitudeTriad) →
  signedHelicityTransferSum triad ≡ 0ℚ
commonAmplitudeSignedHelicityConservation triad =
  solve
    ( signedP triad ∷ signedQ triad ∷ signedR triad
    ∷ amplitude triad ∷ [])

record LiteralHelicalTriadCommonAmplitudeTarget : Set₁ where
  field
    LiteralTriad : Set
    signedP signedQ signedR : LiteralTriad → ℚ
    literalTransferP literalTransferQ literalTransferR : LiteralTriad → ℚ
    commonAmplitude : LiteralTriad → ℚ

    transferPCommonAmplitude : ∀ triad →
      literalTransferP triad
      ≡ (signedQ triad - signedR triad) * commonAmplitude triad

    transferQCommonAmplitude : ∀ triad →
      literalTransferQ triad
      ≡ (signedR triad - signedP triad) * commonAmplitude triad

    transferRCommonAmplitude : ∀ triad →
      literalTransferR triad
      ≡ (signedP triad - signedQ triad) * commonAmplitude triad

open LiteralHelicalTriadCommonAmplitudeTarget public

literalTargetEnergyConservation :
  (target : LiteralHelicalTriadCommonAmplitudeTarget) →
  (triad : LiteralTriad target) →
  literalTransferP target triad
    + literalTransferQ target triad
    + literalTransferR target triad
  ≡ 0ℚ
literalTargetEnergyConservation target triad
  rewrite transferPCommonAmplitude target triad
        | transferQCommonAmplitude target triad
        | transferRCommonAmplitude target triad =
  solve
    ( signedP target triad ∷ signedQ target triad ∷ signedR target triad
    ∷ commonAmplitude target triad ∷ [])

literalTargetSignedHelicityConservation :
  (target : LiteralHelicalTriadCommonAmplitudeTarget) →
  (triad : LiteralTriad target) →
  signedP target triad * literalTransferP target triad
    + signedQ target triad * literalTransferQ target triad
    + signedR target triad * literalTransferR target triad
  ≡ 0ℚ
literalTargetSignedHelicityConservation target triad
  rewrite transferPCommonAmplitude target triad
        | transferQCommonAmplitude target triad
        | transferRCommonAmplitude target triad =
  solve
    ( signedP target triad ∷ signedQ target triad ∷ signedR target triad
    ∷ commonAmplitude target triad ∷ [])

round92CommonAmplitudeImpliesTriadEnergyConservation : Bool
round92CommonAmplitudeImpliesTriadEnergyConservation = true

round92CommonAmplitudeImpliesTriadSignedHelicityConservation : Bool
round92CommonAmplitudeImpliesTriadSignedHelicityConservation = true

round92LiteralFourierWaleffeCommonAmplitudeIdentified : Bool
round92LiteralFourierWaleffeCommonAmplitudeIdentified = false

round92CommonAmplitudeImpliesTriadEnergyConservationIsTrue :
  round92CommonAmplitudeImpliesTriadEnergyConservation ≡ true
round92CommonAmplitudeImpliesTriadEnergyConservationIsTrue = refl

round92CommonAmplitudeImpliesTriadSignedHelicityConservationIsTrue :
  round92CommonAmplitudeImpliesTriadSignedHelicityConservation ≡ true
round92CommonAmplitudeImpliesTriadSignedHelicityConservationIsTrue = refl
