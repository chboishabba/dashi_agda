module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseHistoricalMechanicsExact as Mechanics

boundary = Mechanics.canonicalAdKHistoricalMechanicsBoundary

_ : Mechanics.gromacsPaid boundary ≡ true
_ = refl

_ : Mechanics.ffamber03Paid boundary ≡ true
_ = refl

_ : Mechanics.tip3pPaid boundary ≡ true
_ = refl

_ : Mechanics.pmeLincsThermostatBarostatPaid boundary ≡ true
_ = refl

_ : Mechanics.twoFemtosecondTimestepPaid boundary ≡ true
_ = refl

_ : Mechanics.exactParameterFileBytesPaid boundary ≡ false
_ = refl

_ : Mechanics.methodCitationCreatesExecutableReproduction boundary ≡ false
_ = refl
