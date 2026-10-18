{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SymmetricFiniteTangentBasisFromCarrierEqualityExact where

------------------------------------------------------------------------
-- MAX-CUT: IF THE PRESENT-CUT TANGENT CARRIER IS THE TEN-SLOT CARRIER, THE
-- COMPONENT -> FINITE-TANGENT MAP IS NOT A PHYSICAL INPUT.
--
-- `CMP119SymmetricPresentCutCarrierCompilerExact` proves exactly that carrier
-- equality (definitionally, by construction).  This module compiles the carrier
-- equality plus one selected reference background into the older
-- `SymmetricFiniteSourceTangentBasis` package.  No ten component maps remain.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119SymmetricFiniteTangentBasisCompilerExact as Basis
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source

compileTenSlotCarrierToFiniteTangentBasis :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws
      composite C S Y group Scale Volume domain representation coordinate selected}
    {attachment} →
  (referenceBackground :
    Source.Background (Carrier.source (Present.bc1Carrier present))) →
  Finite.Tangent (Carrier.finiteAction (Present.bc1Carrier present))
    ≡ K.SymmetricTensorComponent4 →
  Basis.SymmetricFiniteSourceTangentBasis
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} {actionWeld = actionWeld} {laws = laws}
    {composite = composite}
    {C = C} {S = S} {Y = Y} {group = group}
    {Scale = Scale} {Volume = Volume}
    {domain = domain} {representation = representation}
    {coordinate = coordinate} {selected = selected}
    attachment
compileTenSlotCarrierToFiniteTangentBasis
    {present = present} referenceBackground tangentIsTenSlot = record
  { Basis.SymmetricFiniteSourceTangentBasis.referenceBackground =
      referenceBackground
  ; Basis.SymmetricFiniteSourceTangentBasis.componentFiniteTangent =
      subst
        (λ Tangent → K.SymmetricTensorComponent4 → Tangent)
        (sym tangentIsTenSlot)
        (λ component → component)
  }

tenIndependentFiniteTangentChoicesRequired : Bool
tenIndependentFiniteTangentChoicesRequired = false

onlyReferenceBackgroundRemainsAfterTenSlotCarrierChoice : Bool
onlyReferenceBackgroundRemainsAfterTenSlotCarrierChoice = true
