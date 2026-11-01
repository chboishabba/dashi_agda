module DASHI.Physics.CFD.SparseTwistFluidCrossPollination where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.InvolutiveTernaryDynamics as Ternary
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Physics.CFD.SparseTwistLESOperator as Sparse
import DASHI.Physics.Fluid.BandedVorticitySpinTwist as Fluid
import DASHI.Physics.Closure.NSFilamentFiningCore as Filament

------------------------------------------------------------------------
-- Cross-pollination of the three fluid-facing signed carriers.
--
-- There are three existing surfaces:
--
--   * the generic Trit-based sparse/twist LES contract;
--   * the SSPTrit-based low/mid/high banded vorticity carrier;
--   * the TriTruth-based filament-fining runtime kernel.
--
-- SSPTrit already has a canonical isomorphism to Trit.  The filament lane,
-- however, uses TriTruth as an application-labelled three-state carrier:
-- tri-low is annihilated/absent, tri-mid is positive support, and tri-high is
-- negative support.  This is deliberately NOT the canonical SSP
-- TriTruth interpretation (tri-low=-1, tri-mid=0, tri-high=+1).  The explicit
-- permutation below prevents those two meanings from being silently conflated.
------------------------------------------------------------------------

filamentToTrit : TriTruth → Trit.Trit
filamentToTrit tri-low = Trit.zer
filamentToTrit tri-mid = Trit.pos
filamentToTrit tri-high = Trit.neg

tritToFilament : Trit.Trit → TriTruth
tritToFilament Trit.neg = tri-high
tritToFilament Trit.zer = tri-low
tritToFilament Trit.pos = tri-mid

filamentToTrit-tritToFilament :
  ∀ t → filamentToTrit (tritToFilament t) ≡ t
filamentToTrit-tritToFilament Trit.neg = refl
filamentToTrit-tritToFilament Trit.zer = refl
filamentToTrit-tritToFilament Trit.pos = refl

tritToFilament-filamentToTrit :
  ∀ t → tritToFilament (filamentToTrit t) ≡ t
tritToFilament-filamentToTrit tri-low = refl
tritToFilament-filamentToTrit tri-mid = refl
tritToFilament-filamentToTrit tri-high = refl

filament-support-agrees :
  ∀ t → Filament.signedSupport t ≡ Ternary.support (filamentToTrit t)
filament-support-agrees tri-low = refl
filament-support-agrees tri-mid = refl
filament-support-agrees tri-high = refl

------------------------------------------------------------------------
-- The canonical SSPTrit bridge used by the banded vorticity lane agrees with
-- the generic sparse/twist support quotient.
------------------------------------------------------------------------

ssp-support-agrees :
  ∀ t → Fluid.spinSupport t ≡ Ternary.support (SSP.toTrit t)
ssp-support-agrees SSP.sspNegOne = refl
ssp-support-agrees SSP.sspZero = refl
ssp-support-agrees SSP.sspPosOne = refl

------------------------------------------------------------------------
-- A concrete banded vortex atom embeds into the generic sparse/twist atom.
--
-- Circulation level supplies generic strength, the spectral band supplies
-- scale, and SSP polarity supplies both orientation metadata and canonical
-- Trit sign.  Core scale remains available in the source atom and can be
-- carried by a richer Strength/Scale product in a numerical instantiation.
------------------------------------------------------------------------

bandedAtomToSparseAtom :
  Fluid.VortexAtom →
  Sparse.SparseTwistAtom
    Fluid.PeriodicSite Nat Fluid.ScaleBand SSP.SSPTrit
bandedAtomToSparseAtom a = record
  { position = Fluid.atomSite a
  ; strength = Fluid.atomCirculationLevel a
  ; scale = Fluid.atomBand a
  ; orientation = Fluid.atomSpin a
  ; sign = SSP.toTrit (Fluid.atomSpin a)
  }

banded-atom-sign-is-canonical :
  ∀ a →
  Sparse.sign (bandedAtomToSparseAtom a) ≡ SSP.toTrit (Fluid.atomSpin a)
banded-atom-sign-is-canonical a = refl

------------------------------------------------------------------------
-- Fining is an admissibility/projection policy, not twist transport itself.
--
-- This record makes the ordering explicit: a twist/update proposes transported
-- signed structure; a coherence test then either retains it and increments its
-- lifetime or projects it to the absorbing zero state.  Consequently the
-- fining kernel can be consumed as an atom-retention policy by either the fast
-- or vortex-faithful solver, but it cannot reconstruct geometry erased by the
-- faithful-to-fast quotient.
------------------------------------------------------------------------

record FilamentAdmissibilityAdapter : Set where
  field
    accept : Bool → Filament.FilamentCell → Filament.FilamentCell
    accept-is-fining :
      ∀ coherent cell → accept coherent cell ≡ Filament.fineCell coherent cell
    zero-is-absorbing :
      ∀ coherent n →
      accept coherent (Filament.filamentCell tri-low n) ≡
      Filament.annihilatedCell

canonicalFilamentAdmissibilityAdapter : FilamentAdmissibilityAdapter
canonicalFilamentAdmissibilityAdapter = record
  { accept = Filament.fineCell
  ; accept-is-fining = λ _ _ → refl
  ; zero-is-absorbing = Filament.annihilated-support-is-absorbing
  }

------------------------------------------------------------------------
-- Integrated theorem-facing surface.
------------------------------------------------------------------------

record SparseTwistFluidCrossPollination : Setω where
  field
    filamentCarrierToTrit : TriTruth → Trit.Trit
    tritToFilamentCarrier : Trit.Trit → TriTruth
    filamentRoundtrip :
      ∀ t → filamentCarrierToTrit (tritToFilamentCarrier t) ≡ t
    filamentSupportCompatibility :
      ∀ t →
      Filament.signedSupport t ≡
      Ternary.support (filamentCarrierToTrit t)

    sspSupportCompatibility :
      ∀ t → Fluid.spinSupport t ≡ Ternary.support (SSP.toTrit t)

    atomEmbedding :
      Fluid.VortexAtom →
      Sparse.SparseTwistAtom
        Fluid.PeriodicSite Nat Fluid.ScaleBand SSP.SSPTrit

    finingPolicy : FilamentAdmissibilityAdapter
    claimBoundary : List String

canonicalSparseTwistFluidCrossPollination :
  SparseTwistFluidCrossPollination
canonicalSparseTwistFluidCrossPollination = record
  { filamentCarrierToTrit = filamentToTrit
  ; tritToFilamentCarrier = tritToFilament
  ; filamentRoundtrip = filamentToTrit-tritToFilament
  ; filamentSupportCompatibility = filament-support-agrees
  ; sspSupportCompatibility = ssp-support-agrees
  ; atomEmbedding = bandedAtomToSparseAtom
  ; finingPolicy = canonicalFilamentAdmissibilityAdapter
  ; claimBoundary =
      "SSPTrit and generic Trit are canonically bridged"
      ∷ "Filament TriTruth uses an explicit application permutation, not the SSP semantic map"
      ∷ "Banded vortex atoms embed into the generic sparse/twist atom carrier"
      ∷ "Filament fining is a post-transport admissibility projection with absorbing zero"
      ∷ "Fast-mode erasure cannot be inverted by fining or random-phase texture synthesis"
      ∷ "No continuum-vorticity, fidelity, speedup, or Navier--Stokes theorem is promoted"
      ∷ []
  }
