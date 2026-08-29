{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PhysicalCompositeHessianMarkedShellRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1: SAME DIFFERENTIATED OBJECT != ITS SHELL MAJORANT
--
-- The Round103 carrier proves the scalar/tensor identity between CMP109 D²E and
-- the finite sum of CMP116 physical composite Hessians.  Separately, CMP116's
-- Cauchy/localization theorem controls a NONNEGATIVE shell magnitude of those
-- differentiated localized pieces.  This file makes that norm/majorant binding
-- explicit and reuses the existing hessianMark; no second Hessian is invented.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geom
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Radius

record PhysicalCompositeHessianMarkedShell
    (Scale Volume Root : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    radiusData : Radius.CMP116CommonAnalyticRadius Scale Volume

    -- Magnitude of the actual physical B-Hessian contributions obtained after
    -- CMP116's source substitutions and two differentiations.
    physicalCompositeHessianShell :
      Scale → Volume → Root → Nat → ℚ
    physicalCompositeHessianShellNonnegative :
      ∀ scale volume root depth →
      0ℚ ≤ physicalCompositeHessianShell scale volume root depth

    -- Same-object identification: this is the quantity represented by the
    -- hessian response slot of the shared marked source theorem.
    physicalShellIsSharedHessianShell : ∀ scale volume root depth →
      physicalCompositeHessianShell scale volume root depth
      ≡ Shared.hessianInfluenceShell shared scale volume root depth

    -- The same common source radius is used by this differentiated response.
    physicalHessianUsesCommonRadius : Scale → Volume → Set

open PhysicalCompositeHessianMarkedShell public

physicalCompositeHessianBelowMarkedAnalytic :
  ∀ {Scale Volume Root}
    (dataSet : PhysicalCompositeHessianMarkedShell Scale Volume Root)
    scale volume root depth →
  physicalCompositeHessianShell dataSet scale volume root depth
  ≤ Shared.markedAnalyticShell
      (shared dataSet) Shared.hessianMark scale volume root depth
physicalCompositeHessianBelowMarkedAnalytic dataSet scale volume root depth
  rewrite physicalShellIsSharedHessianShell dataSet scale volume root depth =
  Shared.hessianBelowAnalytic (shared dataSet) scale volume root depth

physicalCompositeHessianGeometricHalf :
  ∀ {Scale Volume Root}
    (dataSet : PhysicalCompositeHessianMarkedShell Scale Volume Root)
    scale volume root depth →
  physicalCompositeHessianShell dataSet scale volume root depth
  ≤ Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark
      * DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact.halfPower depth
physicalCompositeHessianGeometricHalf dataSet scale volume root depth =
  Geom.responseGeometricHalf
    (shared dataSet) Shared.hessianMark
    (physicalCompositeHessianShell dataSet)
    (physicalCompositeHessianBelowMarkedAnalytic dataSet)
    scale volume root depth

physicalCompositeHessianMarkedShellCompilerLevel : ProofLevel
physicalCompositeHessianMarkedShellCompilerLevel = machineChecked

-- CMP116 Sect.1 provides differentiated localization by Cauchy formula.  The
-- physical repository binding is the exact shell/norm interpretation after the
-- literal A(B) substitutions and common-radius instantiation.
literalCMP116PhysicalCompositeHessianShellIdentificationLevel : ProofLevel
literalCMP116PhysicalCompositeHessianShellIdentificationLevel = conditional
