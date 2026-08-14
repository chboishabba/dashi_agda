module DASHI.Physics.Closure.NSTriadKNHHBadNormalizedDuhamelLeafRound58 where

------------------------------------------------------------------------
-- Lightweight normalized A leaf.  It contains only the algebraic
-- normalization of the raw Duhamel terms and its exact component split.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; _*_; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadRawDuhamelSurfaceRound58 as Raw
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale
import DASHI.Physics.Closure.NSTriadKNHHBadPositiveThresholdRound58 as Threshold

distributeScalar :
  (factor inherited generated leakage : ℚ) →
  factor * (inherited + generated + leakage)
  ≡ factor * inherited + factor * generated + factor * leakage
distributeScalar factor inherited generated leakage =
  solve (factor ∷ inherited ∷ generated ∷ leakage ∷ [])

normalizedDefect : Raw.PhysicalGeneralVariableDefectDuhamel → Nat → ℚ
normalizedDefect physical q =
  Threshold.thresholdInverse (Raw.parameter physical)
    * Scale.dyadicScale q * Raw.defectRate physical q

normalizationFactor : Raw.PhysicalGeneralVariableDefectDuhamel → Nat → ℚ
normalizationFactor physical q =
  Threshold.thresholdInverse (Raw.parameter physical) * Scale.dyadicScale q

normalizedInherited :
  Raw.PhysicalGeneralVariableDefectDuhamel → Nat → ℚ
normalizedInherited physical q =
  normalizationFactor physical (suc q) * Raw.inherited physical q

normalizedGenerated :
  Raw.PhysicalGeneralVariableDefectDuhamel → Nat → ℚ
normalizedGenerated physical q =
  normalizationFactor physical (suc q) * Raw.generated physical q

normalizedLeakage :
  Raw.PhysicalGeneralVariableDefectDuhamel → Nat → ℚ
normalizedLeakage physical q =
  normalizationFactor physical (suc q) * Raw.leakage physical q

normalizedSuccessorComponentsExact :
  (physical : Raw.PhysicalGeneralVariableDefectDuhamel) →
  ∀ q →
  normalizedDefect physical (suc q)
  ≡ normalizedInherited physical q
    + normalizedGenerated physical q
    + normalizedLeakage physical q
normalizedSuccessorComponentsExact physical q =
  let
    factor = normalizationFactor physical (suc q)
    inherited = Raw.inherited physical q
    generated = Raw.generated physical q
    leakage = Raw.leakage physical q
  in
  trans
    (cong (factor *_) (Raw.successorDecomposition physical q))
    (distributeScalar factor inherited generated leakage)
