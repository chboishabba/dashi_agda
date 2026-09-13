module DASHI.Physics.ExoticGravity.NingLiYBCOGravityConstraintBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact as Theory
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti

------------------------------------------------------------------------
-- NING LI / YBCO STATIC GRAVITY CONSTRAINT
--
-- Li et al., Physica C 281 (1997) 260-267 tested a static type-II YBCO
-- superconductor with a sensitive gravimeter.  The reported acceleration change
-- was below 2 parts in 10^8 of ordinary g.  This is a constraint on the tested
-- static configuration, not positive evidence for antigravity and not a test of
-- every rotating/dynamic/coherent-superconductor hypothesis.
------------------------------------------------------------------------

record NingLiYBCOConstraintReceipt : Set where
  constructor ning-li-ybco-constraint-receipt
  field
    authors : String
    title : String
    publication : String
    doi : String
    material : String
    apparatus : String
    configuration : String
    reportedBound : String
    boundInterpretation : String
    sourceReference : String
    samePersonAsLiTorrTheoryAuthor : Bool
    positiveStaticGravityAnomalyObserved : Bool
    constrainsStaticCoupling : Bool
    generalisesToAllSuperconductorGravityClaims : Bool

open NingLiYBCOConstraintReceipt public

staticYBCO1997Constraint : NingLiYBCOConstraintReceipt
staticYBCO1997Constraint = ning-li-ybco-constraint-receipt
  "Ning Li; David Noever; Tony Robertson; Ron Koczor; Whitt Brantley"
  "Static test for a gravitational force coupled to type II YBCO superconductors"
  "Physica C: Superconductivity 281 (1997) 260-267"
  "10.1016/S0921-4534(97)01462-7"
  "bulk type-II YBCO superconductor"
  "sensitive gravimeter; YBCO stably levitated in a DC magnetic field"
  "static/non-rotating superconducting test configuration"
  "measured acceleration changes less than 2 parts in 10^8 of normal gravitational acceleration"
  "places a strong source-bounded limit on the strength/range of the proposed coupling in the tested static configuration"
  "Elsevier / Physica C article DOI 10.1016/S0921-4534(97)01462-7"
  true false true false

lessThanTwoPartsIn100MillionG : String
lessThanTwoPartsIn100MillionG =
  NingLiYBCOConstraintReceipt.reportedBound staticYBCO1997Constraint

------------------------------------------------------------------------
-- Link to already-owned Li/Torr theory identities without manufacturing an
-- apparatus/theory equivalence beyond shared Ning Li authorship and domain.
------------------------------------------------------------------------

liTorr1991TheoryIdentityPresent :
  Theory.prd1991Candidate ≡ Theory.prd1991Candidate
liTorr1991TheoryIdentityPresent = refl

liTorr1992TheoryIdentityPresent :
  Theory.prb1992Candidate ≡ Theory.prb1992Candidate
liTorr1992TheoryIdentityPresent = refl

liTorr1993TheoryIdentityPresent :
  Theory.fopl1993Candidate ≡ Theory.fopl1993Candidate
liTorr1993TheoryIdentityPresent = refl

existingAntigravityBoundary : Anti.AntigravityPromotionBoundary
existingAntigravityBoundary = Anti.canonicalAntigravityPromotionBoundary

------------------------------------------------------------------------
-- BIDI reading.
--
-- Forward: the experiment constrains one static material/apparatus regime.
-- Reverse: surviving stronger claims must specify the changed coordinate
-- (rotation, time dependence, material state, field drive, external test mass,
-- momentum closure, etc.) rather than ignore the negative constraint.
------------------------------------------------------------------------

record NingLiConstraintBoundary : Set where
  constructor ning-li-constraint-boundary
  field
    negativeConstraintIsPositiveAntigravityEvidence : Bool
    staticNullResultRefutesEveryDynamicClaim : Bool
    exactMaterialAndDriveRegimeMatter : Bool
    theoryBibliographyAlonePaysApparatusResult : Bool
    constraintShouldRouteNextDiscriminator : Bool

canonicalNingLiConstraintBoundary : NingLiConstraintBoundary
canonicalNingLiConstraintBoundary = ning-li-constraint-boundary
  false false true false true

negativeConstraintIsNotPositiveAntigravityEvidence : Bool
negativeConstraintIsNotPositiveAntigravityEvidence = true
