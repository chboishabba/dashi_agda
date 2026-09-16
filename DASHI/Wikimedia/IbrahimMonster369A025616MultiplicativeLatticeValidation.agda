module DASHI.Wikimedia.IbrahimMonster369A025616MultiplicativeLatticeValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_*_)

import DASHI.Wikimedia.IbrahimMonster369A025616MultiplicativeLatticeExact as L

ninetyRegression : L.semigroupValue 2 1 ≡ 90
ninetyRegression = L.ninetyInA025616

heisenbergRegression : L.semigroupValue 6 0 ≡ 729
heisenbergRegression = L.sevenTwentyNineInA025616

zetaRegression : L.semigroupValue 8 1 ≡ 65610
zetaRegression = L.sixFiveSixOneZeroInA025616

bulkRegression : L.semigroupValue 9 1 ≡ 196830
bulkRegression = L.oneNineSixEightThreeZeroInA025616

multiplicativeLiftRegression :
  L.semigroupValue 2 1 * L.semigroupValue 6 0 ≡ L.semigroupValue 8 1
multiplicativeLiftRegression = L.ninetyTimesSevenTwentyNineIsSixFiveSixOneZero

positiveStructureRegression :
  L.positiveArithmeticLatticeRetained L.currentA025616Monster369Boundary ≡ true
positiveStructureRegression = refl

authorityFirewallRegression :
  L.a025616CreatesMonsterRepresentation L.currentA025616Monster369Boundary ≡ false
authorityFirewallRegression = refl
