{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCanonicalDyadicTraversalShellExact where

------------------------------------------------------------------------
-- Canonical dyadic instance of the traversal-shell ABI.
--
-- This removes a directionality mismatch when a source theorem produces the
-- concrete majorant
--
--   (1/4) (1/2)^depth.
--
-- Rather than trying to infer a bound by an arbitrary smaller rooted shell,
-- instantiate the existing TraversalShellData with this majorant itself.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; NonNegative; nonNegative; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

canonicalRootedShell : Nat → ℚ
canonicalRootedShell depth =
  Shell.quarter * Geo.halfPower depth

canonicalExtensionActivity : Nat → ℚ
canonicalExtensionActivity depth =
  Shell.oneSixteenth * canonicalRootedShell depth

canonicalTraversalShell :
  ∀ {Scale Volume Root : Set} →
  Shell.TraversalShellData Scale Volume Root
canonicalTraversalShell = record
  { Shell.TraversalShellData.rootedShell =
      λ scale volume root depth → canonicalRootedShell depth
  ; Shell.TraversalShellData.extensionActivity =
      λ scale volume root depth → canonicalExtensionActivity depth
  ; Shell.TraversalShellData.reflexive =
      λ value → ℚP.≤-refl
  ; Shell.TraversalShellData.transitive =
      ℚP.≤-trans
  ; Shell.TraversalShellData.addMonotone =
      ℚP.+-mono-≤
  ; Shell.TraversalShellData.multiplyByEightMonotone =
      λ {left} {right} order →
        let
          instance
            eightNN : NonNegative Shell.eight
            eightNN = nonNegative (ℚP.nonNegative⁻¹ Shell.eight)
        in
        ℚP.*-monoˡ-≤-nonNeg Shell.eight order
  ; Shell.TraversalShellData.multiplyByHalfMonotone =
      λ {left} {right} order →
        let
          instance
            halfNN : NonNegative Geo.half
            halfNN = nonNegative Geo.halfNonnegative
        in
        ℚP.*-monoˡ-≤-nonNeg Geo.half order
  ; Shell.TraversalShellData.rootNormalization =
      λ scale volume root → ℚP.≤-refl
  ; Shell.TraversalShellData.atMostEightExtensions =
      λ scale volume root depth →
        ℚP.≤-reflexive
          (canonicalStepIsEightExtensions depth)
  ; Shell.TraversalShellData.activityPerExtensionBelowOneSixteenth =
      λ scale volume root depth → ℚP.≤-refl
  }
  where
  canonicalStepIsEightExtensions :
    ∀ depth →
    canonicalRootedShell (suc depth)
    ≡ Shell.eight * canonicalExtensionActivity depth
  canonicalStepIsEightExtensions depth =
    ℚRing.solve-∀ (Geo.halfPower depth)

canonicalRootedShellExact :
  ∀ {Scale Volume Root}
    (scale : Scale) (volume : Volume) (root : Root) depth →
  Shell.rootedShell canonicalTraversalShell scale volume root depth
  ≡ Shell.quarter * Geo.halfPower depth
canonicalRootedShellExact scale volume root depth = refl

canonicalOneStepExact :
  ∀ depth →
  canonicalRootedShell (suc depth)
  ≡ Geo.half * canonicalRootedShell depth
canonicalOneStepExact depth =
  ℚRing.solve-∀ (Geo.halfPower depth)
