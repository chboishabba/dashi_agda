module DASHI.Moonshine.VNaturalOriginalFTToTFSkewFiniteExact where

------------------------------------------------------------------------
-- ORIGINAL VNATURAL PAIRED SECTORS: CONSTRUCT THE TF MODE FAMILY FROM
-- THE ACTUAL FIXED->TWISTED (FT) SOURCE, NOT A SECOND ARBITRARY TF.
--
-- For VOA modes a_(m)t, skew symmetry forces the coefficient:
--
--  t_(n) a = sum_{j >= 0} (-1)^(n+j+1)/j!
--                   T^j (a_(n+j) t).
--
-- At each mode n, upper truncation makes this a FINITE sum. The
-- source-scalar signed-factorial coefficients, valid truncation bound,
-- and true Leech twisted translation are the remaining source data.
-- This file constructs the finite operator, but does not claim that
-- the ORIGINAL twisted-even source currently pays those axioms.
--
-- TT : twisted x twisted -> fixed remains a separate genuine
-- Leech intertwiner. Mixed Jacobi/locality remain original gates.
--
-- Attribution: FLM skew-symmetry, original Leech theta-twisted module;
-- DASHI source-specific finite coefficient constructor.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; _+_)

import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN
import DASHI.Moonshine.VNaturalOriginalPairedFourSectorModesExact as Paired

module Selected
  (construction : VN.VNaturalConstruction)
  (source :
    VN.SelectedPairedGradedModule.OriginalFixedVOAAndTwistedEvenSource
      construction) where

  module N = VN.SelectedPairedGradedModule construction
  module P = Paired.Selected construction source

  -- Never invent a new FT operation: all coefficients use the
  -- SAME original selected fixed/twisted mode.
  record OriginalFTSkewData : Setω where
    field
      originalTwistIndex :
        ℤ → VN.TwistedModule.TwistIndex N.twisted

      fixedTwisted : N.Fixed → ℤ → N.Twisted → N.Twisted

      fixedTwistedIsOriginal :
        (a : N.Fixed) (n : ℤ) (t : N.Twisted) →
        VN.TwistedEvenSector.includePlus N.plus
          (fixedTwisted a n t)
        ≡
        VN.TwistedModule.twistedMode N.twisted
          (VN.FixedPointVOA.includeFixed N.fixed a)
          (originalTwistIndex n)
          (VN.TwistedEvenSector.includePlus N.plus t)

      -- The original twisted-even translation is the one acting on
      -- the exact selected plus sector, not a free formal variable.
      twistedTranslation : N.Twisted → N.Twisted

      -- Must be instantiated by the ORIGINAL characteristic-zero
      -- scalar coefficients (-1)^(n+j+1)/j!, including correct
      -- integer parity. We do not assert such values exist.
      signedFactorialCoefficient : ℤ → Nat → N.Scalar

      -- For each a,t,n, the ORIGINAL FT mode is zero above this
      -- source-derived upper bound. It is NOT automatically paid by
      -- the weak Core.LowerTruncation Set-valued field.
      finiteTruncationBound :
        N.Fixed → ℤ → N.Twisted → Nat

      -- The bound must be a TRUE original FT upper-truncation
      -- certificate, not merely a chosen finite length.
      originalFTVanishesAtAndAboveBound :
        (a : N.Fixed) (n : ℤ) (t : N.Twisted) (j : Nat) →
        finiteTruncationBound a n t ≤ j →
        fixedTwisted a (n + (+ j)) t
          ≡ N.twistedZeroOriginal source

  open OriginalFTSkewData public

  module Derive (dataFT : OriginalFTSkewData) where

    iterateTranslation : Nat → N.Twisted → N.Twisted
    iterateTranslation zero t = t
    iterateTranslation (suc k) t =
      twistedTranslation dataFT (iterateTranslation k t)

    -- Source FT mode at shifted integer n+j.
    originalShiftedFT :
      N.Fixed → ℤ → Nat → N.Twisted → N.Twisted
    originalShiftedFT a n j t =
      fixedTwisted dataFT a (n + (+ j)) t

    -- Construct TF by finite sum of actual original FT modes.
    -- The bound is selected from the original fixed/twisted source.
    finiteSkewSum :
      N.Twisted → ℤ → N.Fixed → Nat → N.Twisted
    finiteSkewSum t n a zero =
      N.twistedZeroOriginal source
    finiteSkewSum t n a (suc j) =
      N.twistedAddOriginal source
        (finiteSkewSum t n a j)
        (N.twistedScaleOriginal source
          (signedFactorialCoefficient dataFT n j)
          (iterateTranslation j (originalShiftedFT a n j t)))

    -- This is an ACTUAL constructed TF operation, not a record field.
    derivedTwistedFixed :
      N.Twisted → ℤ → N.Fixed → N.Twisted
    derivedTwistedFixed t n a =
      finiteSkewSum t n a
        (finiteTruncationBound dataFT a n t)

    derivedTFIsOriginalFiniteSkew :
      (t : N.Twisted) (n : ℤ) (a : N.Fixed) →
      derivedTwistedFixed t n a
      ≡
      finiteSkewSum t n a
        (finiteTruncationBound dataFT a n t)
    derivedTFIsOriginalFiniteSkew t n a = refl

    -- Assemble directly into the existing source-native four-sector
    -- carrier. Only the genuinely independent TT channel remains
    -- an unfilled Leech intertwiner input.
    withOriginalTT :
      (twistedTwisted :
        N.Twisted → ℤ → N.Twisted → N.Fixed) →
      P.OriginalMixedSectorIntertwiners
    withOriginalTT twistedTwisted = record
      { P.OriginalMixedSectorIntertwiners.originalTwistIndex =
          originalTwistIndex dataFT
      ; P.OriginalMixedSectorIntertwiners.fixedTwisted =
          fixedTwisted dataFT
      ; P.OriginalMixedSectorIntertwiners.fixedTwistedIsOriginal =
          fixedTwistedIsOriginal dataFT
      ; P.OriginalMixedSectorIntertwiners.twistedFixed =
          derivedTwistedFixed
      ; P.OriginalMixedSectorIntertwiners.twistedTwisted =
          twistedTwisted
      ; P.OriginalMixedSectorIntertwiners.twistedTranslation =
          twistedTranslation dataFT
      }

    -- Original FF and FT are not replaced: this is the same
    -- Paired.Selected.pairedMode and native orbifold carrier.
    actualPairedTFBlockIsSkewFinite :
      (tt : N.Twisted → ℤ → N.Twisted → N.Fixed) →
      (t : N.Twisted) (n : ℤ) (a : N.Fixed) →
      P.twistedFixed (withOriginalTT tt) t n a
      ≡ derivedTwistedFixed t n a
    actualPairedTFBlockIsSkewFinite tt t n a = refl
