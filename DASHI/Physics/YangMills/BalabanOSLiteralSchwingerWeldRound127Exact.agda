{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanOSLiteralSchwingerWeldRound127Exact where

------------------------------------------------------------------------
-- ROUND127: SOURCE OS SCHWINGER SYSTEM IS THE LITERAL CLAY SCHWINGER FAMILY
--
-- `BalabanOSMassGapClosure` carries the source-facing OS axioms/reconstruction
-- object.  The literal Clay construction carries an opaque `SchwingerFamily`.
-- A physical same-family theorem must weld them explicitly; otherwise OS
-- reconstruction and stress/OPE could live on parallel continuum objects.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record OSLiteralSchwingerWeld
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C) : Set₁ where
  field
    Observable Point Scalar : Set
    sourceOSSystem : OS.ContinuumSchwingerSystem Observable Point Scalar

    sourceSystemToLiteralSchwinger :
      OS.ContinuumSchwingerSystem Observable Point Scalar →
      Top.SchwingerFamily C

    sourceOSSystemIsLiteralSchwinger :
      sourceSystemToLiteralSchwinger sourceOSSystem
      ≡ Top.schwinger Y group
open OSLiteralSchwingerWeld public

literalSchwingerFromSourceOS :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (dataSet : OSLiteralSchwingerWeld Y group) →
  sourceSystemToLiteralSchwinger dataSet (sourceOSSystem dataSet)
  ≡ Top.schwinger Y group
literalSchwingerFromSourceOS = sourceOSSystemIsLiteralSchwinger

osLiteralSchwingerWeldCompilerLevel : ProofLevel
osLiteralSchwingerWeldCompilerLevel = machineChecked

-- Physical same-family input: instantiate the adapter from the actual Balaban
-- continuum Schwinger functions into the literal Clay carrier.  OS reconstruction
-- and stress/OPE must use this same welded object.
literalBalabanOSSystemIsClaySchwingerLevel : ProofLevel
literalBalabanOSSystemIsClaySchwingerLevel = conditional
