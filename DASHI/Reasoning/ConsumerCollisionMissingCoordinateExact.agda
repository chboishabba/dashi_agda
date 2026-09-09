module DASHI.Reasoning.ConsumerCollisionMissingCoordinateExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression

------------------------------------------------------------------------
-- CONSUMER COLLISION -> MISSING TYPED COORDINATE
--
-- Canonical invariant:
--
--   observationally identical upstream
--   + different consumer result
--   => the retained upstream representation is insufficient for that consumer.
--
-- The collision does NOT magically construct the missing coordinate.  The exact
-- stronger statement proved here is that every proposed refinement which really
-- makes the consumer descend must separate the particular colliding witnesses.
-- This turns a collision into a typed refinement obligation without inventing
-- semantics or promoting an unverified discriminator.
------------------------------------------------------------------------

record ConsumerCollision
    {Fine Coarse Output : Set}
    (observe : Fine → Coarse)
    (consumer : Fine → Output) : Set where
  constructor consumerCollision
  field
    witness : Compression.CompressionFailureWitness observe consumer
    reading : String

open ConsumerCollision public

coarseObservationCannotDetermineConsumer :
  ∀ {Fine Coarse Output : Set}
    {observe : Fine → Coarse}
    {consumer : Fine → Output} →
  ConsumerCollision observe consumer →
  NonFactor.FactorsThrough observe consumer →
  ⊥
coarseObservationCannotDetermineConsumer collision =
  Compression.compressionFailureBlocksDescent (witness collision)

------------------------------------------------------------------------
-- A typed repair proposal.
--
-- `refine` may retain any richer carrier.  We require only that the consumer
-- actually factors through it.  No claim is made that the refinement is
-- minimal, unique, source-authoritative, or globally sufficient.
------------------------------------------------------------------------

record ConsumerAdequateRefinement
    {Fine Refined Output : Set}
    (refine : Fine → Refined)
    (consumer : Fine → Output) : Set₁ where
  constructor consumerAdequateRefinement
  field
    consumeRefined : Refined → Output
    consumerFactorises : (fine : Fine) → consumer fine ≡ consumeRefined (refine fine)
    refinementReading : String

open ConsumerAdequateRefinement public

refinementMustSeparateCollision :
  ∀ {Fine Coarse Refined Output : Set}
    {observe : Fine → Coarse}
    {consumer : Fine → Output}
    {refine : Fine → Refined} →
  (collision : ConsumerCollision observe consumer) →
  ConsumerAdequateRefinement refine consumer →
  refine (Compression.leftFine (witness collision))
    ≡ refine (Compression.rightFine (witness collision)) →
  ⊥
refinementMustSeparateCollision collision repair sameRefined =
  Compression.consumerOutputsDiffer (witness collision)
    (let
       left = Compression.leftFine (witness collision)
       right = Compression.rightFine (witness collision)
     in
     transEq
       (consumerFactorises repair left)
       (transEq
         (congEq (consumeRefined repair) sameRefined)
         (symEq (consumerFactorises repair right))))
  where
  congEq : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  congEq f refl = refl

  symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  symEq refl = refl

  transEq : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  transEq refl refl = refl

------------------------------------------------------------------------
-- Coordinate-shaped refinement.
--
-- This is the reusable form needed by introspective search: retain the coarse
-- observation and add exactly one typed coordinate.  A successful coordinate
-- repair must distinguish the colliding worlds on that added coordinate.
------------------------------------------------------------------------

record CoarsePlusCoordinate (Coarse Coordinate : Set) : Set where
  constructor coarsePlusCoordinate
  field
    coarse : Coarse
    coordinate : Coordinate

open CoarsePlusCoordinate public

addCoordinate :
  ∀ {Fine Coarse Coordinate : Set} →
  (Fine → Coarse) →
  (Fine → Coordinate) →
  Fine → CoarsePlusCoordinate Coarse Coordinate
addCoordinate observe inspect fine =
  coarsePlusCoordinate (observe fine) (inspect fine)

coordinateRepairMustDistinguishCollision :
  ∀ {Fine Coarse Coordinate Output : Set}
    {observe : Fine → Coarse}
    {consumer : Fine → Output}
    {inspect : Fine → Coordinate} →
  (collision : ConsumerCollision observe consumer) →
  ConsumerAdequateRefinement (addCoordinate observe inspect) consumer →
  inspect (Compression.leftFine (witness collision))
    ≡ inspect (Compression.rightFine (witness collision)) →
  ⊥
coordinateRepairMustDistinguishCollision collision repair sameCoordinate =
  refinementMustSeparateCollision collision repair fullSame
  where
  fullSame :
    addCoordinate _ _ (Compression.leftFine (witness collision))
      ≡ addCoordinate _ _ (Compression.rightFine (witness collision))
  fullSame rewrite Compression.sameCompressedRepresentation (witness collision)
                 | sameCoordinate = refl

------------------------------------------------------------------------
-- Boundary: collision proves inadequacy and constrains every valid repair;
-- it does not itself certify which domain coordinate is legally/physically/etc.
-- correct.  Source realization remains application-owned.
------------------------------------------------------------------------

data CollisionAutomaticallyConstructsAuthoritativeCoordinate : Set where

data AnySeparatingCoordinateIsSemanticallyValid : Set where

collisionDoesNotConstructAuthority :
  CollisionAutomaticallyConstructsAuthoritativeCoordinate → ⊥
collisionDoesNotConstructAuthority ()

separationAloneDoesNotValidateSemantics :
  AnySeparatingCoordinateIsSemanticallyValid → ⊥
separationAloneDoesNotValidateSemantics ()
