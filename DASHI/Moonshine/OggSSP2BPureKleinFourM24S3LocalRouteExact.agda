module DASHI.Moonshine.OggSSP2BPureKleinFourM24S3LocalRouteExact where

------------------------------------------------------------------------
-- 2B-PURE KLEIN-FOUR LOCAL ROUTE
--
-- External source authority:
-- CTblLib worked computations record a Monster local subgroup of shape
--
--   2^(2+11+22).(M24 x S3)
--
-- normalizing a 2B-pure Klein four group.  The same source distinguishes this
-- from the centralizer of a single 2B element, whose relevant quotient lane is
-- Co1.
--
-- This local subgroup is highly relevant to the Completion10 programme:
--
--   * M24 supplies the sourced duad / Pair24 degree-276 action;
--   * S3 supplies a sourced three-phase / reflection-capable factor;
--   * the two structures occur in one Monster-local object rather than being
--     multiplied together only inside the repo ontology.
--
-- Semantic firewall:
-- this file does NOT identify the Carnahan--Urano 2B Tate 276 with the M24
-- duad module, nor does it identify the S3 factor with the repo's C3/S3 phase
-- carrier.  It records the exact source-local group shape and the new
-- recognition target.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSP2BM24DuadPair24AuthorityExact as Duad
import DASHI.Moonshine.OggP31CompletionTenTwoSevenNineCrossPollinationExact as P279

------------------------------------------------------------------------
-- 1. Sourced local shape.
------------------------------------------------------------------------

record TwoBPureKleinFourLocalSource : Set where
  constructor twoB-pure-klein-four-local-source
  field
    sourceURL : String
    ambientGroup : String
    localShape : String
    normalTwoGroupShape : String
    quotientShape : String
    mathieuFactor : String
    symmetricFactor : String

    normalizesTwoBPureKleinFour : Bool
    mathieuFactorIsM24 : Bool
    symmetricFactorIsS3 : Bool
    availableThroughAtlasRep : Bool

open TwoBPureKleinFourLocalSource public

canonicalTwoBPureKleinFourLocalSource :
  TwoBPureKleinFourLocalSource
canonicalTwoBPureKleinFourLocalSource =
  twoB-pure-klein-four-local-source
    "https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/doc2/chap6_mj.html"
    "Monster"
    "2^(2+11+22).(M24 x S3)"
    "2^(2+11+22)"
    "M24 x S3"
    "M24"
    "S3"
    true
    true
    true
    true

------------------------------------------------------------------------
-- 2. Typed relation to the already-paid M24 duad carrier.
------------------------------------------------------------------------

m24DuadCarrierPaidInSeparateAuthority : Bool
m24DuadCarrierPaidInSeparateAuthority =
  Duad.carrierSameObjectPaid Duad.canonicalM24DuadActionAuthority

m24DuadCarrierPaidIsTrue :
  m24DuadCarrierPaidInSeparateAuthority ≡ true
m24DuadCarrierPaidIsTrue = refl

------------------------------------------------------------------------
-- 3. The source now supplies a genuine "3 next to M24" local geometry.
--
-- This is stronger than the purely arithmetic identity 3 * 10 = 30:
-- the Monster-local quotient itself contains an S3 factor.  We still do NOT
-- identify its C3 subgroup with Completion10's regular phase action here.
------------------------------------------------------------------------

sourcedS3PhaseCount : Nat
sourcedS3PhaseCount = 3

completionTenCount : Nat
completionTenCount = P279.completionTen

sourcedThreeTimesCompletionTen : Nat
sourcedThreeTimesCompletionTen = sourcedS3PhaseCount * completionTenCount

sourcedThreeTimesCompletionTenIsThirty :
  sourcedThreeTimesCompletionTen ≡ 30
sourcedThreeTimesCompletionTenIsThirty = refl

pointedThirtyIsP31 :
  1 + sourcedThreeTimesCompletionTen ≡ P279.p31Value
pointedThirtyIsP31 = refl

nonaryPointedLocalCompositeIs279 :
  P279.nonaryScale * (1 + sourcedThreeTimesCompletionTen) ≡ 279
nonaryPointedLocalCompositeIs279 = refl

------------------------------------------------------------------------
-- 4. Promotion firewalls.
------------------------------------------------------------------------

data LocalM24FactorIsActualTwoBTateAction : Set where
data LocalS3FactorIsCompletion10PhaseAction : Set where
data LocalProductAlreadySelectsQ10 : Set where

localM24FactorDoesNotIdentifyTateAction :
  LocalM24FactorIsActualTwoBTateAction → ⊥
localM24FactorDoesNotIdentifyTateAction ()

localS3FactorDoesNotIdentifyCompletionPhase :
  LocalS3FactorIsCompletion10PhaseAction → ⊥
localS3FactorDoesNotIdentifyCompletionPhase ()

localProductDoesNotAutomaticallySelectQ10 :
  LocalProductAlreadySelectsQ10 → ⊥
localProductDoesNotAutomaticallySelectQ10 ()

------------------------------------------------------------------------
-- 5. Revised highest-alpha recognition target.
------------------------------------------------------------------------

record TwoBPureLocalRecognitionFrontier : Set where
  constructor twoB-pure-local-recognition-frontier
  field
    twoBPureKleinFourLocalSubgroupSourced : Bool
    m24FactorSourced : Bool
    s3FactorSourced : Bool
    m24DuadActionSameObjectPaid : Bool

    actualTwoBTateRestrictionToLocalComputed : Bool
    actualTateM24DuadIdentificationPaid : Bool
    actualTateS3PhaseIdentificationPaid : Bool
    tenDimensionalLocalSubquotientObserved : Bool
    completion10EquivariantRecognitionPaid : Bool
    downstreamP31And279Available : Bool

    nextResidual : String

canonicalTwoBPureLocalRecognitionFrontier :
  TwoBPureLocalRecognitionFrontier
canonicalTwoBPureLocalRecognitionFrontier =
  twoB-pure-local-recognition-frontier
    true
    true
    true
    true
    false
    false
    false
    false
    false
    true
    "construct or acquire the actual 2^(2+11+22).(M24 x S3) Monster-local action, restrict the source 2B Tate multiplicity to its M24 x S3 quotient, compute the characteristic-two subquotients, and test whether a 10d factor carries both the M22 Completion10 involution and a compatible C3 phase action"

