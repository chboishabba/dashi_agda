module DASHI.Physics.CondensedMatter.AltermagnetCrystalActionBridgeExact where

------------------------------------------------------------------------
-- DASHI native owners
--
-- DASHI.Mathematics.Symmetry.KleinGroupActionInvariantExact:
--   reusable GroupAction / SameOrbit interfaces.
-- DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact:
--   finite signed-coordinate / momentum-cell symmetry precedent.
-- DASHI.Physics.CondensedMatter.AltermagnetCoQuarterTaSeTwo:
--   the two-momentum/two-spin illustrative spectral model.
--
-- Experimental source:
-- Sprague et al. (2026), Nature Communications.
-- DOI 10.1038/s41467-026-76784-x.
--
-- IMPORTANT: the abstract two-point involution below has NOT been
-- identified with a particular crystallographic space-group generator
-- of Co1/4TaSe2.  No experimentally calibrated band function or
-- spin-resolved photocurrent is claimed.  The chosen two-site exchange
-- is a finite mathematical candidate only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Symmetry.KleinGroupActionInvariantExact as Native
import DASHI.Physics.CondensedMatter.AltermagnetCoQuarterTaSeTwo as AM

-- A two-sublattice crystal carrier.  This is NOT an experimentally
-- reconstructed fractional-occupancy unit cell.
data Sublattice : Set where
  siteA siteB : Sublattice

swapSite : Sublattice → Sublattice
swapSite siteA = siteB
swapSite siteB = siteA

siteInvolution : (a : Sublattice) →
  swapSite (swapSite a) ≡ a
siteInvolution siteA = refl
siteInvolution siteB = refl

-- The representative state carries an electronic momentum and spin
-- as well as a site label, keeping crystal and spin operations separate.
record CrystalSpinState : Set where
  constructor state
  field
    site : Sublattice
    momentum : AM.Momentum
    spin : AM.Spin

open CrystalSpinState public

crystalSpinExchange : CrystalSpinState → CrystalSpinState
crystalSpinExchange (state a k s) =
  state (swapSite a) (AM.rotateMomentum k) (AM.reverseSpin s)

exchangeInvolution : (x : CrystalSpinState) →
  crystalSpinExchange (crystalSpinExchange x) ≡ x
exchangeInvolution (state siteA AM.kA AM.up) = refl
exchangeInvolution (state siteA AM.kA AM.down) = refl
exchangeInvolution (state siteA AM.kB AM.up) = refl
exchangeInvolution (state siteA AM.kB AM.down) = refl
exchangeInvolution (state siteB AM.kA AM.up) = refl
exchangeInvolution (state siteB AM.kA AM.down) = refl
exchangeInvolution (state siteB AM.kB AM.up) = refl
exchangeInvolution (state siteB AM.kB AM.down) = refl

-- The two-element group C2 is the strictly finite symmetry group used
-- here, not the full spin-space group of the actual compound.
_xor_ : Bool → Bool → Bool
false xor b = b
true xor false = true
true xor true = false

actC2 : Bool → CrystalSpinState → CrystalSpinState
actC2 false x = x
actC2 true x = crystalSpinExchange x

composeAction : (g h : Bool) (x : CrystalSpinState) →
  actC2 (g xor h) x ≡ actC2 g (actC2 h x)
composeAction false false x = refl
composeAction false true x = refl
composeAction true false x = refl
composeAction true true x = exchangeInvolution x

nativeCrystalSpinAction : Native.GroupAction
nativeCrystalSpinAction = record
  { G = Bool
  ; X = CrystalSpinState
  ; identity = false
  ; compose = _xor_
  ; act = actC2
  ; identityActs = λ x → refl
  ; composeActs = composeAction
  }

-- A concrete native orbit witness: a combined spin-space exchange
-- relates a siteA state to its siteB partner.
pairedOrbit : (k : AM.Momentum) (s : AM.Spin) →
  Native.SameOrbit nativeCrystalSpinAction
    (state siteA k s)
    (state siteB (AM.rotateMomentum k) (AM.reverseSpin s))
pairedOrbit k s = record
  { transform = true
  ; reaches = refl
  }

-- The sample dispersion is a scalar observable on the state carrier.
-- A spin-space action can preserve energy while NOT preserving spin
-- separately at fixed momentum.
bandEnergy : CrystalSpinState → Nat
bandEnergy (state a k s) = AM.energy k s

bandInvariant : (g : Bool) (x : CrystalSpinState) →
  bandEnergy (Native.act nativeCrystalSpinAction g x)
    ≡ bandEnergy x
bandInvariant false x = refl
bandInvariant true (state a k s) = AM.combined-symmetry k s

orbitEnergyAgreement : (k : AM.Momentum) (s : AM.Spin) →
  bandEnergy (state siteB (AM.rotateMomentum k) (AM.reverseSpin s))
  ≡ bandEnergy (state siteA k s)
orbitEnergyAgreement = AM.combined-symmetry

-- This witnesses the *abstract* exchange geometry only.  To apply it
-- to the experiment one must construct and check: actual atomic basis,
-- space-group/magnetic-space-group symmetry, reciprocal-space action,
-- a measured or computed band model, and ARPES observation map.
