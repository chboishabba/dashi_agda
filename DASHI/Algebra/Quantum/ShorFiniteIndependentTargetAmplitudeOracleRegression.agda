module DASHI.Algebra.Quantum.ShorFiniteIndependentTargetAmplitudeOracleRegression where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Algebra.Quantum.ShorFiniteIndependentTargetAmplitudeOracleExact as Target

------------------------------------------------------------------------
-- RED regression: the preferred Shor amplitude register must use an
-- independent finite residue target Fin N while still inhabiting the existing
-- exact oracle-weld interface.
------------------------------------------------------------------------

finiteTargetWeldExists :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Prefix.ShorAmplitudeOracleWeld
    B base modulus modulusNonZero
    (Target.finiteIndependentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
finiteTargetWeldExists = Target.finiteIndependentTargetAmplitudeOracleWeld

finiteTargetCoordinateIsFin :
  ∀ {B : Finite.FiniteBasis} {base modulus modulusNonZero} →
  Target.FiniteIndependentTargetState B base modulus modulusNonZero → Set
finiteTargetCoordinateIsFin {modulus = modulus} state = Fin modulus
