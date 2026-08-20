module DASHI.Moonshine.P11MarkedObservationRefinementExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- David Blackwell,
-- "Equivalent Comparisons of Experiments",
-- Annals of Mathematical Statistics 24(2) (1953), 265--272.
-- DOI: 10.1214/aoms/1177729032.
-- Used only as observation/comparison vocabulary: the exact finite refinement
-- theorem below is a DASHI construction.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
-- Character restriction / representation-type context.
--
-- CROSS-POLLINATION
-- PR #573/#560 isolate the generic information lesson that a coarse observation
-- can identify states separated by a richer admissible coordinate.  PR #575
-- independently uses actual finite-group characters to annihilate/resolve
-- symmetry sectors before later analysis.  Here that architecture is applied to
-- the source-native marked-X(2) arithmetic geometry.
--
-- DASHI CONTRIBUTION
--
-- The arithmetic observer
--
--   O0 = (T3 eigenvalue, T5 eigenvalue, Frobenius eigenvalue)
--
-- identifies the Brandt-newform line with the deck-standard plane.  Adding the
-- independently defined deck-character coordinate gives
--
--   O1 = (O0, deck C3/S3 type)
--
-- and strictly refines O0: the same pair that collides under O0 is separated by
-- O1.  This formally blocks later code from treating deck character as a
-- redundant annotation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as Dec
import DASHI.Moonshine.P11MarkedX2DeckCharacterSeparationExact as Char

------------------------------------------------------------------------
-- Two-sector witness carrying the exact known collision.
------------------------------------------------------------------------

data CollisionSector : Set where
  brandtSector standardSector : CollisionSector

coarseObservation : CollisionSector → Dec.JointEigenFingerprint
coarseObservation brandtSector = Dec.brandtNewformFingerprint
coarseObservation standardSector = Dec.standardFingerprint

richObservation : CollisionSector → Char.ExtendedMarkedFingerprint
richObservation brandtSector = Char.brandtExtendedFingerprint
richObservation standardSector = Char.standardExtendedFingerprint

coarseObservationCollides :
  coarseObservation brandtSector ≡ coarseObservation standardSector
coarseObservationCollides = Dec.brandtAndStandardFingerprintsCoincide

richObservationSeparates :
  richObservation brandtSector ≡ richObservation standardSector → ⊥
richObservationSeparates = Char.extendedFingerprintsSeparate

------------------------------------------------------------------------
-- The rich observer projects back exactly to the coarse observer.
------------------------------------------------------------------------

forgetDeckCharacter :
  Char.ExtendedMarkedFingerprint → Dec.JointEigenFingerprint
forgetDeckCharacter = Char.ExtendedMarkedFingerprint.arithmeticFingerprint

richProjectsToCoarse :
  (sector : CollisionSector) →
  forgetDeckCharacter (richObservation sector) ≡ coarseObservation sector
richProjectsToCoarse brandtSector = refl
richProjectsToCoarse standardSector = refl

record DeterministicObservationRefinement : Set where
  field
    coarse : CollisionSector → Dec.JointEigenFingerprint
    rich : CollisionSector → Char.ExtendedMarkedFingerprint
    forget : Char.ExtendedMarkedFingerprint → Dec.JointEigenFingerprint
    commutes : (x : CollisionSector) → forget (rich x) ≡ coarse x

markedDeckCharacterRefinement : DeterministicObservationRefinement
markedDeckCharacterRefinement = record
  { DeterministicObservationRefinement.coarse = coarseObservation
  ; DeterministicObservationRefinement.rich = richObservation
  ; DeterministicObservationRefinement.forget = forgetDeckCharacter
  ; DeterministicObservationRefinement.commutes = richProjectsToCoarse
  }

------------------------------------------------------------------------
-- Strictness witness: no decoder from the coarse observation can reconstruct
-- the sector identity on this two-sector carrier.
------------------------------------------------------------------------

record SectorDecoder : Set where
  field
    decode : Dec.JointEigenFingerprint → CollisionSector
    exact : (x : CollisionSector) → decode (coarseObservation x) ≡ x

brandtAndStandardCannotBeEqual : brandtSector ≡ standardSector → ⊥
brandtAndStandardCannotBeEqual ()

coarseObservationHasNoExactSectorDecoder : SectorDecoder → ⊥
coarseObservationHasNoExactSectorDecoder decoder =
  brandtAndStandardCannotBeEqual
    (trans
      (sym (SectorDecoder.exact decoder brandtSector))
      (trans
        (cong (SectorDecoder.decode decoder) coarseObservationCollides)
        (SectorDecoder.exact decoder standardSector)))

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record P11MarkedObservationRefinementBoundary : Set where
  field
    coarseHeckeFrobeniusCollisionConstructed : Bool
    coarseHeckeFrobeniusCollisionConstructedIsTrue :
      coarseHeckeFrobeniusCollisionConstructed ≡ true

    deckCharacterRefinementCommutes : Bool
    deckCharacterRefinementCommutesIsTrue : deckCharacterRefinementCommutes ≡ true

    refinementStrictOnKnownCollision : Bool
    refinementStrictOnKnownCollisionIsTrue : refinementStrictOnKnownCollision ≡ true

    coarseObservationCanRecoverExactSector : Bool
    coarseObservationCanRecoverExactSectorIsFalse :
      coarseObservationCanRecoverExactSector ≡ false

    deckCharacterPromotedToArithmeticHeckeEigenvalue : Bool
    deckCharacterPromotedToArithmeticHeckeEigenvalueIsFalse :
      deckCharacterPromotedToArithmeticHeckeEigenvalue ≡ false

canonicalP11MarkedObservationRefinementBoundary : P11MarkedObservationRefinementBoundary
canonicalP11MarkedObservationRefinementBoundary = record
  { coarseHeckeFrobeniusCollisionConstructed = true
  ; coarseHeckeFrobeniusCollisionConstructedIsTrue = refl
  ; deckCharacterRefinementCommutes = true
  ; deckCharacterRefinementCommutesIsTrue = refl
  ; refinementStrictOnKnownCollision = true
  ; refinementStrictOnKnownCollisionIsTrue = refl
  ; coarseObservationCanRecoverExactSector = false
  ; coarseObservationCanRecoverExactSectorIsFalse = refl
  ; deckCharacterPromotedToArithmeticHeckeEigenvalue = false
  ; deckCharacterPromotedToArithmeticHeckeEigenvalueIsFalse = refl
  }
