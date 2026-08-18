module DASHI.Moonshine.P37NonOggFullLevel2DeckCharacterControlExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
-- The regular representation and restriction/character multiplicities.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full-level-2 frame torsor with GL_2(F_2) ~= S3.
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163, Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- CROSS-POLLINATION
-- PR #572's Phase3 character carrier is reused exactly.  The transferable
-- method also appears independently in PRs #574/#575: act by the ACTUAL finite
-- group first, then project to characters; do not identify unrelated finite
-- carriers merely because their cardinalities coincide.
--
-- DASHI CONTRIBUTION
--
-- The p=37 control already proves three coarse supersingular classes and
-- monodromy weight one on each.  Therefore every coarse class carries the full
-- six-element level-2 frame torsor, i.e. one regular S3 action.  The complete
-- marked carrier is consequently three regular S3 permutation modules:
--
--   3 Q[S3] = 3*1 + 3*sgn + 6*std.
--
-- Restricting to the rotation C3 gives, per regular S3 copy, two copies of the
-- regular C3 representation.  Across all three coarse classes the Phase3
-- character multiplicities are therefore
--
--   chi_0 = chi_1 = chi_2 = 6.
--
-- This is a representation-theoretic CONTROL PREDICTION available before the
-- still-open p=37 marked T3/T5 quaternion computation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.Phase3RootCharacterWeldExact as Root
import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37

------------------------------------------------------------------------
-- Regular right S3 action on the same six frame labels used by the p=37
-- full-level-2 carrier.
------------------------------------------------------------------------

frameR : P37.Frame6 → P37.Frame6
frameR P37.frame0 = P37.frame1
frameR P37.frame1 = P37.frame2
frameR P37.frame2 = P37.frame0
frameR P37.frame3 = P37.frame5
frameR P37.frame5 = P37.frame4
frameR P37.frame4 = P37.frame3

frameS : P37.Frame6 → P37.Frame6
frameS P37.frame0 = P37.frame3
frameS P37.frame3 = P37.frame0
frameS P37.frame1 = P37.frame4
frameS P37.frame4 = P37.frame1
frameS P37.frame2 = P37.frame5
frameS P37.frame5 = P37.frame2

frameR3IsIdentity : (x : P37.Frame6) → frameR (frameR (frameR x)) ≡ x
frameR3IsIdentity P37.frame0 = refl
frameR3IsIdentity P37.frame1 = refl
frameR3IsIdentity P37.frame2 = refl
frameR3IsIdentity P37.frame3 = refl
frameR3IsIdentity P37.frame4 = refl
frameR3IsIdentity P37.frame5 = refl

frameS2IsIdentity : (x : P37.Frame6) → frameS (frameS x) ≡ x
frameS2IsIdentity P37.frame0 = refl
frameS2IsIdentity P37.frame1 = refl
frameS2IsIdentity P37.frame2 = refl
frameS2IsIdentity P37.frame3 = refl
frameS2IsIdentity P37.frame4 = refl
frameS2IsIdentity P37.frame5 = refl

frameSRSIsRInverse : (x : P37.Frame6) →
  frameS (frameR (frameS x)) ≡ frameR (frameR x)
frameSRSIsRInverse P37.frame0 = refl
frameSRSIsRInverse P37.frame1 = refl
frameSRSIsRInverse P37.frame2 = refl
frameSRSIsRInverse P37.frame3 = refl
frameSRSIsRInverse P37.frame4 = refl
frameSRSIsRInverse P37.frame5 = refl

p37DeckR : P37.P37FullLevel2Point → P37.P37FullLevel2Point
p37DeckR (P37.p37MarkedPoint j frame) = P37.p37MarkedPoint j (frameR frame)

p37DeckS : P37.P37FullLevel2Point → P37.P37FullLevel2Point
p37DeckS (P37.p37MarkedPoint j frame) = P37.p37MarkedPoint j (frameS frame)

p37DeckR3IsIdentity : (x : P37.P37FullLevel2Point) →
  p37DeckR (p37DeckR (p37DeckR x)) ≡ x
p37DeckR3IsIdentity (P37.p37MarkedPoint j frame) =
  cong (P37.p37MarkedPoint j) (frameR3IsIdentity frame)

p37DeckS2IsIdentity : (x : P37.P37FullLevel2Point) → p37DeckS (p37DeckS x) ≡ x
p37DeckS2IsIdentity (P37.p37MarkedPoint j frame) =
  cong (P37.p37MarkedPoint j) (frameS2IsIdentity frame)

------------------------------------------------------------------------
-- Exact representation multiplicities.
------------------------------------------------------------------------

record S3IrrepMultiplicity : Set where
  constructor s3Multiplicity
  field
    trivialMultiplicity signMultiplicity standardMultiplicity : Nat

open S3IrrepMultiplicity public

oneRegularS3Multiplicity : S3IrrepMultiplicity
oneRegularS3Multiplicity = s3Multiplicity 1 1 2

p37MarkedS3Multiplicity : S3IrrepMultiplicity
p37MarkedS3Multiplicity = s3Multiplicity 3 3 6

p37MarkedS3DimensionCheck :
  trivialMultiplicity p37MarkedS3Multiplicity
  + signMultiplicity p37MarkedS3Multiplicity
  + 2 * standardMultiplicity p37MarkedS3Multiplicity
  ≡ 18
p37MarkedS3DimensionCheck = refl

record C3CharacterMultiplicity : Set where
  constructor c3Multiplicity
  field
    chi0Multiplicity chi1Multiplicity chi2Multiplicity : Nat

open C3CharacterMultiplicity public

oneRegularS3RestrictedC3 : C3CharacterMultiplicity
oneRegularS3RestrictedC3 = c3Multiplicity 2 2 2

p37MarkedC3Multiplicity : C3CharacterMultiplicity
p37MarkedC3Multiplicity = c3Multiplicity 6 6 6

p37MarkedC3DimensionCheck :
  chi0Multiplicity p37MarkedC3Multiplicity
  + chi1Multiplicity p37MarkedC3Multiplicity
  + chi2Multiplicity p37MarkedC3Multiplicity
  ≡ 18
p37MarkedC3DimensionCheck = refl

------------------------------------------------------------------------
-- Root labels use the same Phase3 character table as PR #572 / p=11.
------------------------------------------------------------------------

chi0AtR : Phase.Phase3
chi0AtR = Root.character Phase.phase0 Phase.phase1

chi1AtR : Phase.Phase3
chi1AtR = Root.character Phase.phase1 Phase.phase1

chi2AtR : Phase.Phase3
chi2AtR = Root.character Phase.phase2 Phase.phase1

chi0AtRIsOne : chi0AtR ≡ Phase.phase0
chi0AtRIsOne = refl

chi1AtRIsZeta : chi1AtR ≡ Phase.phase1
chi1AtRIsZeta = refl

chi2AtRIsZetaSquared : chi2AtR ≡ Phase.phase2
chi2AtRIsZetaSquared = refl

------------------------------------------------------------------------
-- Boundary: this is a carrier/deck representation theorem and a target for the
-- future p=37 marked-Hecke producer, not a fabricated Hecke decomposition.
------------------------------------------------------------------------

record P37DeckCharacterControlBoundary : Set where
  field
    threeRegularS3DeckCopiesConstructed : Bool
    threeRegularS3DeckCopiesConstructedIsTrue :
      threeRegularS3DeckCopiesConstructed ≡ true

    exactS3MultiplicityPredictionConstructed : Bool
    exactS3MultiplicityPredictionConstructedIsTrue :
      exactS3MultiplicityPredictionConstructed ≡ true

    phase3C3MultiplicityPredictionConstructed : Bool
    phase3C3MultiplicityPredictionConstructedIsTrue :
      phase3C3MultiplicityPredictionConstructed ≡ true

    p37MarkedT3T5DiagonalizationClaimed : Bool
    p37MarkedT3T5DiagonalizationClaimedIsFalse :
      p37MarkedT3T5DiagonalizationClaimed ≡ false

    p37FrobeniusIdentifiedWithDeckGenerator : Bool
    p37FrobeniusIdentifiedWithDeckGeneratorIsFalse :
      p37FrobeniusIdentifiedWithDeckGenerator ≡ false

    c9OrF9IdentifiedWithP37MarkedCarrier : Bool
    c9OrF9IdentifiedWithP37MarkedCarrierIsFalse :
      c9OrF9IdentifiedWithP37MarkedCarrier ≡ false

canonicalP37DeckCharacterControlBoundary : P37DeckCharacterControlBoundary
canonicalP37DeckCharacterControlBoundary = record
  { threeRegularS3DeckCopiesConstructed = true
  ; threeRegularS3DeckCopiesConstructedIsTrue = refl
  ; exactS3MultiplicityPredictionConstructed = true
  ; exactS3MultiplicityPredictionConstructedIsTrue = refl
  ; phase3C3MultiplicityPredictionConstructed = true
  ; phase3C3MultiplicityPredictionConstructedIsTrue = refl
  ; p37MarkedT3T5DiagonalizationClaimed = false
  ; p37MarkedT3T5DiagonalizationClaimedIsFalse = refl
  ; p37FrobeniusIdentifiedWithDeckGenerator = false
  ; p37FrobeniusIdentifiedWithDeckGeneratorIsFalse = refl
  ; c9OrF9IdentifiedWithP37MarkedCarrier = false
  ; c9OrF9IdentifiedWithP37MarkedCarrierIsFalse = refl
  }
