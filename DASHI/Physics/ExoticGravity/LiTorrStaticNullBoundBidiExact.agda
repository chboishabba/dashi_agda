module DASHI.Physics.ExoticGravity.LiTorrStaticNullBoundBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LI-TORR MEMORIAL PHYSICS: STATIC NULL-BOUND DISCRIMINATOR
--
-- Source-backed experimental constraint from Li et al., Physica C 281
-- (1997), DOI 10.1016/S0921-4534(97)01462-7 / NASA NTRS 19990039542.
-- The reported static YBCO gravimeter configuration found acceleration
-- changes below 2 parts in 10^8 of normal g.  This constrains model classes;
-- it does not by itself identify the correct microscopic mechanism.
------------------------------------------------------------------------

record StaticNullBoundReceipt : Set where
  constructor static-null-bound-receipt
  field
    sourceTitle : String
    doi : String
    nasaDocumentId : String
    material : String
    apparatusRegime : String
    reportedBound : String
    staticConfiguration : Bool

open StaticNullBoundReceipt public

canonicalStaticNullBoundReceipt : StaticNullBoundReceipt
canonicalStaticNullBoundReceipt =
  static-null-bound-receipt
    "Static test for a gravitational force coupled to type II YBCO superconductors"
    "10.1016/S0921-4534(97)01462-7"
    "19990039542"
    "bulk type-II YBCO superconductor"
    "sensitive gravimeter; superconductors stably levitated in a DC magnetic field"
    "change in acceleration < 2 parts in 10^8 of normal gravitational acceleration"
    true

data CandidateRegime : Set where
  genericStaticWeightReduction : CandidateRegime
  transitionLockedResponse : CandidateRegime
  drivenMassCurrentResponse : CandidateRegime
  geometryDependentResponse : CandidateRegime
  ordinaryNullModel : CandidateRegime

record NullBoundCompatibility : Set where
  constructor null-bound-compatibility
  field
    candidate : CandidateRegime
    mustRespectStaticBound : Bool
    requiresNewSameApparatusTest : Bool

staticGenericReductionCompatibility : NullBoundCompatibility
staticGenericReductionCompatibility =
  null-bound-compatibility genericStaticWeightReduction true true

drivenMassCurrentCompatibility : NullBoundCompatibility
drivenMassCurrentCompatibility =
  null-bound-compatibility drivenMassCurrentResponse true true

record StaticNullBoundary : Set where
  constructor static-null-bound-boundary
  field
    staticNullProvesNoSuperconductorGravityCouplingAnywhere : Bool
    staticNullConstrainsGenericStaticModels : Bool
    drivenOrTransitionModelStillNeedsItsOwnTest : Bool
    historicalNullMayPayNewSameApparatusReceipt : Bool
    exactGeometryAndPhaseStateRemainRequired : Bool

canonicalStaticNullBoundary : StaticNullBoundary
canonicalStaticNullBoundary =
  static-null-bound-boundary false true true false true
