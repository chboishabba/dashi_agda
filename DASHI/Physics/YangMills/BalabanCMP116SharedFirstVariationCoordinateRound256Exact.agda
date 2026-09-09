{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SharedFirstVariationCoordinateRound256Exact where

------------------------------------------------------------------------
-- ROUND256 CORRECTION / DO NOT IDENTIFY TWO DIFFERENT TANGENT FIBRES
--
-- Round228's prose could be read as saying that Round118.toPhysicalTangent is
-- the first variation of the CMP116 substitution A=A(B).  The types show that
-- this is not correct:
--
--   Source.Tangent
--     -- toPhysicalTangent --> Chain.BackgroundTangent
--     -- firstSubstitutionVariation --> Chain.LocalTangent.
--
-- These are sequential maps.  The local substitution direction is therefore
-- obtained by composing the already-existing maps; it is not a second object
-- that should be equated with `toPhysicalTangent`.
--
-- The genuine D1 semantic seam is instead that `toPhysicalTangent` is the
-- derivative/tangent transport of `toPhysicalBackground`, together with the
-- ordinary derivative semantics of the source-side firstVariation operator.
-- A generic DerivativeOf relation is not invented here because the repository
-- does not currently own a concrete Fréchet/directional-derivative carrier for
-- this transport.
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeChainRuleRound118Exact as R118
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanBC1PhysicalCompositeD1ReductionRound152Exact as R152

sourceBackgroundTangent :
  ∀ {inputs : BC1.BC1CanonicalPhysicalInputs}
    (family : R118.BC1PhysicalCompositeComponentFamily inputs)
    (component : Source.Component (BC1.source inputs)) →
  Source.Tangent (BC1.source inputs) →
  Chain.BackgroundTangent (R118.physicalActivity family component)
sourceBackgroundTangent family component =
  R118.toPhysicalTangent family component

localSubstitutionTangent :
  ∀ {inputs : BC1.BC1CanonicalPhysicalInputs}
    (family : R118.BC1PhysicalCompositeComponentFamily inputs)
    (component : Source.Component (BC1.source inputs)) →
  Source.Background (BC1.source inputs) →
  Source.Tangent (BC1.source inputs) →
  Chain.LocalTangent (R118.physicalActivity family component)
localSubstitutionTangent family component background tangent =
  let activity = R118.physicalActivity family component
  in
  Chain.firstSubstitutionVariation activity
    (R118.toPhysicalBackground family component background)
    (R118.toPhysicalTangent family component tangent)

sourceCompositeFirstVariation :
  ∀ {inputs : BC1.BC1CanonicalPhysicalInputs}
    (family : R118.BC1PhysicalCompositeComponentFamily inputs)
    (component : Source.Component (BC1.source inputs)) →
  Source.Background (BC1.source inputs) →
  Source.Tangent (BC1.source inputs) → ℝ
sourceCompositeFirstVariation family component background tangent =
  let activity = R118.physicalActivity family component
  in
  First.substitutedFirstVariation activity
    (R118.toPhysicalBackground family component background)
    (R118.toPhysicalTangent family component tangent)

-- The sequential tangent composition above is definitional/compiler plumbing.
round256TangentFibreCorrectionCompilerLevel : ProofLevel
round256TangentFibreCorrectionCompilerLevel = machineChecked

-- The remaining physical theorem is not an equality between BackgroundTangent
-- and LocalTangent.  It is the genuine first-order derivative semantics of the
-- source composite, represented historically by Round152's coarse chain-rule
-- leaf until a concrete derivative calculus for `toPhysicalBackground` is
-- instantiated.
literalPhysicalBackgroundTransportDerivativeLevel : ProofLevel
literalPhysicalBackgroundTransportDerivativeLevel =
  R152.literalPhysicalCompositeD1ChainRuleLevel
