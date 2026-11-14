module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoSpinSpaceGeneratorBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SPIN-SPACE <-> MAGNETIC-SPACE GENERATOR CROSSWALK
--
-- Source: Sah et al., npj Quantum Materials 11, 63 (2026),
-- DOI 10.1038/s41535-026-00885-5.
--
-- Sah et al. identify two real-space operations exchanging the opposite-spin
-- magnetic layers: mirror M_z and the sixfold screw C_6z t.  In the
-- nonrelativistic spin-space-group description they are combined with a pi
-- spin rotation, written [C2 || M_z] and [C2 || C_6z t].
--
-- The independently acquired BNS 194.268 table on this branch contains the
-- corresponding coordinate maps as antiunitary operations:
--   M_z      : x,y,-z+1/2
--   C_6z t   : x-y,x,z+1/2
--
-- This is a same-coordinate-operation bridge.  It deliberately does NOT
-- identify a nonrelativistic unitary spin-space pi rotation with the
-- relativistic antiunitary magnetic-space representation, especially after
-- SOC is switched on.
------------------------------------------------------------------------

record SpinSpaceGeneratorCrosswalk : Set where
  constructor spin-space-generator-crosswalk
  field
    sourceDOI : String
    bnsNumber : String
    mirrorTriplet : String
    screwTriplet : String
    mirrorAntiunitaryPresent : Bool
    screwAntiunitaryPresent : Bool
    oppositeSpinLayerExchangeSourceSupported : Bool
    nonrelativisticSpinSpaceGeneratorSourceSupported : Bool
    representationIdentityWithSOCClaimed : Bool

open SpinSpaceGeneratorCrosswalk public

canonicalSpinSpaceGeneratorCrosswalk : SpinSpaceGeneratorCrosswalk
canonicalSpinSpaceGeneratorCrosswalk =
  spin-space-generator-crosswalk
    "10.1038/s41535-026-00885-5"
    "194.268"
    "x,y,-z+1/2"
    "x-y,x,z+1/2"
    true true true true false

record SpinSpacePromotionBoundary : Set where
  constructor spin-space-promotion-boundary
  field
    coordinateCrosswalkPaid : Bool
    spinSpaceOperationEqualsAntiunitaryMSGRepresentation : Bool
    noSOCSpinLabelTransfersUnchangedThroughSOC : Bool
    fullSpinSpaceGroupRepresentationPaid : Bool
    literalRelativisticHamiltonianStillRequired : Bool

open SpinSpacePromotionBoundary public

canonicalSpinSpacePromotionBoundary : SpinSpacePromotionBoundary
canonicalSpinSpacePromotionBoundary =
  spin-space-promotion-boundary
    true false false false true
