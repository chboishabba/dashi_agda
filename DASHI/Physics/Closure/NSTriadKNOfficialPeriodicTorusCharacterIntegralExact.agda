module DASHI.Physics.Closure.NSTriadKNOfficialPeriodicTorusCharacterIntegralExact where

------------------------------------------------------------------------
-- TIMESTAMP
-- 2026-09-11 20:46 AEST (UTC+10)
--
-- PURPOSE
-- Thin official-carrier adaptor for the periodic torus character integral.
--
-- The repository already proves the finite trigonometric-polynomial
-- coefficient extractor and the finite weighted-character -> canonical
-- increment-multiplier bridge.  This owner does NOT restate that algebra.
-- It isolates the remaining standard analytic authority needed to select the
-- official normalized periodic Haar/Bochner integral and exponential
-- characters, then constructs the existing TorusCharacterIntegral record.
--
-- Boundary discipline:
--   * finite character algebra: machine checked in existing owners;
--   * normalized Haar/Bochner + exponential-character realization:
--       standard imported authority, explicit below;
--   * no NS estimate, radial gain, R568 payment, or Clay promotion here.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Relation.Nullary using (Dec)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoTorusTrigonometricPolynomialExact as Torus
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCharacterWeightedIncrementExact as Finite
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCharacterMultiplierBridgeExact as Bridge
import DASHI.Physics.Closure.NSTriadKNLuoIncrementKernelFourierMultiplierExact as Multiplier
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- 1. Standard imported analytic authority on the official periodic carrier.
--
-- This is intentionally the ONLY non-algebraic input owned by this module.
-- It is shaped exactly strongly enough to construct TorusCharacterIntegral.
------------------------------------------------------------------------

record OfficialPeriodicHaarCharacterAuthority
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    Point Mode : Set

    decideModeEquality :
      (left right : Mode) → Dec (left ≡ right)

    integral :
      (Point → C3.Complex F) → C3.Complex F

    integralCong :
      ∀ {f g : Point → C3.Complex F} →
      (∀ point → f point ≡ g point) →
      integral f ≡ integral g

    integralZero :
      integral (λ _ → C3.complexZero F) ≡ C3.complexZero F

    integralAdd :
      (f g : Point → C3.Complex F) →
      integral (λ point → C3.complexAdd (f point) (g point))
      ≡ C3.complexAdd (integral f) (integral g)

    integralScale :
      (scalar : C3.Complex F) →
      (f : Point → C3.Complex F) →
      integral (λ point → C3.complexMultiply scalar (f point))
      ≡ C3.complexMultiply scalar (integral f)

    character : Mode → Point → C3.Complex F
    zeroMode : Mode
    characterProduct : Mode → Mode → Point → C3.Complex F
    conjugateCharacter : Mode → Point → C3.Complex F

    characterMultiply :
      (left right : Mode) →
      (point : Point) →
      C3.complexMultiply (character left point) (character right point)
      ≡ characterProduct left right point

    characterZero :
      (point : Point) →
      character zeroMode point ≡ C3.complexOne F

    characterConjugate :
      (mode : Mode) →
      (point : Point) →
      C3.complexConjugate (character mode point)
      ≡ conjugateCharacter mode point

    normalizedOrthogonality :
      (left right : Mode) →
      integral
        (λ point →
          C3.complexMultiply
            (character left point)
            (conjugateCharacter right point))
      ≡ Torus.kroneckerComplex decideModeEquality left right

open OfficialPeriodicHaarCharacterAuthority public

------------------------------------------------------------------------
-- 2. Construct the existing official theorem carrier from that authority.
------------------------------------------------------------------------

officialPeriodicTorusCharacterIntegral :
  ∀ {r} {F : C3.RealField r} →
  OfficialPeriodicHaarCharacterAuthority F →
  Torus.TorusCharacterIntegral F
officialPeriodicTorusCharacterIntegral A = record
  { Point = Point A
  ; Mode = Mode A
  ; decideModeEquality = decideModeEquality A
  ; integral = integral A
  ; integralCong = integralCong A
  ; integralZero = integralZero A
  ; integralAdd = integralAdd A
  ; integralScale = integralScale A
  ; character = character A
  ; zeroMode = zeroMode A
  ; characterProduct = characterProduct A
  ; conjugateCharacter = conjugateCharacter A
  ; characterMultiply = characterMultiply A
  ; characterZero = characterZero A
  ; characterConjugate = characterConjugate A
  ; orthogonality = normalizedOrthogonality A
  }

------------------------------------------------------------------------
-- 3. Reuse the already-proved finite polynomial coefficient extractor.
------------------------------------------------------------------------

officialPolynomialCoefficientExtraction :
  ∀ {r} {F : C3.RealField r}
    (A : OfficialPeriodicHaarCharacterAuthority F)
    (terms : List
      (Torus.TorusTerm F
        (Torus.Mode (officialPeriodicTorusCharacterIntegral A))))
    (target : Torus.Mode (officialPeriodicTorusCharacterIntegral A)) →
  Torus.coefficientIntegral
      (officialPeriodicTorusCharacterIntegral A) terms target
  ≡
  Torus.selectedCoefficient
      (officialPeriodicTorusCharacterIntegral A) terms target
officialPolynomialCoefficientExtraction A terms target =
  Torus.polynomialCoefficientExtraction
    (officialPeriodicTorusCharacterIntegral A) terms target

------------------------------------------------------------------------
-- 4. Re-export, do not re-prove, the finite weighted-character multiplier weld.
------------------------------------------------------------------------

officialFiniteWeightedIncrementEqualsPairMultiplier :
  (system : Finite.FiniteCharacterSystem) →
  (left right : Finite.Mode system) →
  Finite.finiteWeightedIncrement system left right
  ≡ Multiplier.pairMultiplier
      (Bridge.finitePeriodicIncrementMultiplierData system)
      left right
officialFiniteWeightedIncrementEqualsPairMultiplier =
  Bridge.finiteWeightedIncrementEqualsPairMultiplier

------------------------------------------------------------------------
-- Status / proof-level receipts.
------------------------------------------------------------------------

officialPeriodicHaarBochnerRealizationLevel : ProofLevel
officialPeriodicHaarBochnerRealizationLevel = standardImported

officialFiniteCharacterAlgebraLevel : ProofLevel
officialFiniteCharacterAlgebraLevel = machineChecked

officialPeriodicTorusCharacterIntegralRealizationClosed : Bool
officialPeriodicTorusCharacterIntegralRealizationClosed = true

officialPeriodicHaarBochnerRealizationStandardImported : Bool
officialPeriodicHaarBochnerRealizationStandardImported = true

officialFiniteCharacterAlgebraReprovedHere : Bool
officialFiniteCharacterAlgebraReprovedHere = false

officialPeriodicTorusCharacterIntegralRealizationClosedIsTrue :
  officialPeriodicTorusCharacterIntegralRealizationClosed ≡ true
officialPeriodicTorusCharacterIntegralRealizationClosedIsTrue = refl

officialFiniteCharacterAlgebraReprovedHereIsFalse :
  officialFiniteCharacterAlgebraReprovedHere ≡ false
officialFiniteCharacterAlgebraReprovedHereIsFalse = refl
