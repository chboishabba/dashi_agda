{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1MassGapSemanticAttachmentRound458Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND458: MODERN R454/R455 MASS GAP -> LITERAL CLAY T2 SEMANTICS.
--
-- R454/R455 already produce the mathematical positive transfer-gap theorem on
-- the SAME continuum/OS spectral object.  The top-down Clay constructor uses
-- semantic predicates such as IsStrictlyPositiveFiniteMassGap.  Those opaque
-- predicates cannot be manufactured by algebra; the only remaining bridge is
-- to assert that the proved gap object is the literal physical Hamiltonian/gap
-- object selected by the construction.
--
-- This owner packages exactly that semantic attachment for every group and
-- compiles it to Five.CutoffUniformPhysicalMassGap.  No spectral estimate,
-- clustering theorem, or continuum limit is re-proved here.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five

record Goal1MassGapSemanticAttachment
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    -- The mathematical R454/R455/Common-OS route has already produced the
    -- physical gap conclusion.  These five fields state that its objects are
    -- exactly the literal Clay Y projections and interpret its consequences in
    -- the endpoint semantic vocabulary.
    vacuumSectorAndPositiveEnergyComplement :
      ∀ group →
      Top.IsVacuumSectorAndPositiveEnergyComplement S
        (Top.hilbertSpace Y group)
        (Top.hamiltonian Y group)
        (Top.vacuum Y group)

    strictlyPositiveFiniteMassGap :
      ∀ group →
      Top.IsStrictlyPositiveFiniteMassGap S
        (Top.hamiltonian Y group)
        (Top.massGap Y group)

    physicalScaleLowerBoundUniform :
      ∀ group →
      Top.PhysicalScaleLowerBoundUniform S group
        (Top.massGap Y group)

    noSpectralPollutionBelowGap :
      ∀ group →
      Top.NoSpectralPollutionBelowGap S group
        (Top.hamiltonian Y group)
        (Top.massGap Y group)

    gapAndClusteringDerived :
      ∀ group →
      Top.GapAndClusteringAreDerivedNotAssumed S group

open Goal1MassGapSemanticAttachment public

asCutoffUniformPhysicalMassGap :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  Goal1MassGapSemanticAttachment Y →
  Five.CutoffUniformPhysicalMassGap Y
asCutoffUniformPhysicalMassGap attachment = record
  { Five.CutoffUniformPhysicalMassGap.vacuumSectorAndPositiveEnergyComplement =
      vacuumSectorAndPositiveEnergyComplement attachment
  ; Five.CutoffUniformPhysicalMassGap.strictlyPositiveFiniteMassGap =
      strictlyPositiveFiniteMassGap attachment
  ; Five.CutoffUniformPhysicalMassGap.physicalScaleLowerBoundUniform =
      physicalScaleLowerBoundUniform attachment
  ; Five.CutoffUniformPhysicalMassGap.noSpectralPollutionBelowGap =
      noSpectralPollutionBelowGap attachment
  ; Five.CutoffUniformPhysicalMassGap.gapAndClusteringDerived =
      gapAndClusteringDerived attachment
  }

round458T2SemanticCompilerLevel : ProofLevel
round458T2SemanticCompilerLevel = machineChecked

-- The mathematics of the gap is not open here.  The remaining theorem is a
-- same-object semantic interpretation of the already-proved R454/R455/Common-OS
-- gap on the literal Y.hamiltonian/Y.massGap/vacuum projections.
literalRound458MassGapSameObjectSemanticsLevel : ProofLevel
literalRound458MassGapSameObjectSemanticsLevel = conditional
