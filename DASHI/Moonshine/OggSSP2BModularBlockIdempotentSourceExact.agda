module DASHI.Moonshine.OggSSP2BModularBlockIdempotentSourceExact where

------------------------------------------------------------------------
-- MODULAR BLOCK IDEMPOTENT SOURCE AUTHORITY FOR THE 2B NORM WELD
--
-- Standard modular block theory decomposes the group algebra in characteristic
-- p as a direct sum of block algebras cut out by central primitive idempotents.
-- Consequently every module decomposes into its block summands, and every
-- module homomorphism preserves that decomposition because it commutes with
-- the action of each central block idempotent.
--
-- SOURCES / TOOLING
--   Markus Linckelmann, The Block Theory of Finite Group Algebras,
--   Cambridge University Press, 2018 (standard block-algebra decomposition).
--   Peter Schneider, Modular Representation Theory of Finite Groups,
--   Springer, 2013, chapter "Blocks".
--   GAP/CTblLib supplies the concrete 2-block labels used by the runtime
--   decomposition screen; DASHI separately verifies that the residual 24-simple
--   lies in a block disjoint from the common 98280 support.
--
-- IMPORTANT BOUNDARY
-- This source theorem removes "discover whether a block projector exists" from
-- the roadmap.  It does NOT instantiate the corresponding group-algebra action
-- on DASHI's formal source-native norm carrier.  The remaining same-object leaf
-- is therefore:
--
--   actual centralizer module action + runtime residual block label
--     -> canonical central block idempotent action on the actual norm carrier.
--
-- Once instantiated, existing Lean `map_smul` / block-naturality owners make
-- norm/projector commutation formal.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record ModularBlockIdempotentSourceStatus : Set where
  constructor modular-block-idempotent-source-status
  field
    blockAlgebraDecompositionSourced : Bool
    centralPrimitiveIdempotentsSourced : Bool
    everyModuleHasCanonicalBlockSummandsSourced : Bool
    moduleHomomorphismsPreserveBlocksSourced : Bool
    ctblocksResidualBlockLabelRuntimePaid : Bool
    residual24BlockSeparatedFromCommon98280Paid : Bool

    actualGroupAlgebraActionInstantiatedInFormalCarrier : Bool
    actualResidualBlockIdempotentActionInstantiated : Bool

    linckelmannReference : String
    schneiderReference : String

canonicalModularBlockIdempotentSourceStatus : ModularBlockIdempotentSourceStatus
canonicalModularBlockIdempotentSourceStatus =
  modular-block-idempotent-source-status
    true true true true true true
    false false
    "Linckelmann, The Block Theory of Finite Group Algebras, CUP 2018"
    "Schneider, Modular Representation Theory of Finite Groups, Springer 2013, Blocks"

record BlockProjectorAcquisitionBoundary : Set where
  constructor block-projector-acquisition-boundary
  field
    projectorExistenceIsDiscoveryProblem : Bool
    residualBlockChoiceIsDiscoveryProblem : Bool
    sameObjectActionInstantiationStillOpen : Bool

canonicalBlockProjectorAcquisitionBoundary : BlockProjectorAcquisitionBoundary
canonicalBlockProjectorAcquisitionBoundary =
  block-projector-acquisition-boundary false false true
