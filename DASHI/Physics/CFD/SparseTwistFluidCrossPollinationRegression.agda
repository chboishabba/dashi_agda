module DASHI.Physics.CFD.SparseTwistFluidCrossPollinationRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

open import Base369 using (tri-low; tri-mid; tri-high)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.InvolutiveTernaryDynamics as Ternary
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Physics.CFD.SparseTwistLESOperator as Sparse
import DASHI.Physics.CFD.SparseTwistFluidCrossPollination as Cross
import DASHI.Physics.Fluid.BandedVorticitySpinTwist as Fluid
import DASHI.Physics.Closure.NSFilamentFiningCore as Filament

------------------------------------------------------------------------
-- Carrier-permutation regressions.
------------------------------------------------------------------------

filament-zero-maps-to-trit-zero :
  Cross.filamentToTrit tri-low ≡ Trit.zer
filament-zero-maps-to-trit-zero = refl

filament-positive-maps-to-trit-positive :
  Cross.filamentToTrit tri-mid ≡ Trit.pos
filament-positive-maps-to-trit-positive = refl

filament-negative-maps-to-trit-negative :
  Cross.filamentToTrit tri-high ≡ Trit.neg
filament-negative-maps-to-trit-negative = refl

filament-zero-support-is-false :
  Ternary.support (Cross.filamentToTrit tri-low) ≡ false
filament-zero-support-is-false = refl

filament-positive-support-is-true :
  Ternary.support (Cross.filamentToTrit tri-mid) ≡ true
filament-positive-support-is-true = refl

filament-negative-support-is-true :
  Ternary.support (Cross.filamentToTrit tri-high) ≡ true
filament-negative-support-is-true = refl

------------------------------------------------------------------------
-- Banded atom embedding regression.
------------------------------------------------------------------------

negativeAtom : Fluid.VortexAtom
negativeAtom =
  Fluid.vortexAtom
    Fluid.midBand
    (Fluid.site 12 17)
    SSP.sspNegOne
    refl
    2
    7

embeddedNegativeAtom :
  Sparse.SparseTwistAtom
    Fluid.PeriodicSite
    Agda.Builtin.Nat.Nat
    Fluid.ScaleBand
    SSP.SSPTrit
embeddedNegativeAtom = Cross.bandedAtomToSparseAtom negativeAtom

embedded-negative-sign :
  Sparse.sign embeddedNegativeAtom ≡ Trit.neg
embedded-negative-sign = refl

embedded-circulation-strength :
  Sparse.strength embeddedNegativeAtom ≡ 7
embedded-circulation-strength = refl

------------------------------------------------------------------------
-- Fining-policy regressions.
------------------------------------------------------------------------

accepted-positive-increments-lifetime :
  FilamentAdmissibilityAdapter.accept
    Cross.canonicalFilamentAdmissibilityAdapter
    true
    (Filament.filamentCell tri-mid zero)
  ≡ Filament.filamentCell tri-mid (suc zero)
accepted-positive-increments-lifetime = refl
  where
  open Cross using (FilamentAdmissibilityAdapter)

rejected-negative-is-annihilated :
  Cross.FilamentAdmissibilityAdapter.accept
    Cross.canonicalFilamentAdmissibilityAdapter
    false
    (Filament.filamentCell tri-high (suc zero))
  ≡ Filament.annihilatedCell
rejected-negative-is-annihilated = refl

annihilated-remains-annihilated :
  Cross.FilamentAdmissibilityAdapter.accept
    Cross.canonicalFilamentAdmissibilityAdapter
    true
    (Filament.filamentCell tri-low (suc zero))
  ≡ Filament.annihilatedCell
annihilated-remains-annihilated = refl
