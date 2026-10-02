{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.SingularBasinCompressionBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Cognition.CompressionAttractor as CA
import DASHI.Physics.Dynamics.SingularBasinReductionExact as SBR

------------------------------------------------------------------------
-- Cross-pollination with the repository's existing compression-attractor
-- machinery.
--
-- CompressionAttractor already separates microstate, compressed code, basin,
-- centre, and settling.  A singular-basin style collision is exactly the case
-- where two microstates share one compressed code while selected basin
-- membership differs.  The generic projection theorem then says that basin
-- membership cannot be reconstructed as a predicate of compressed code alone.
------------------------------------------------------------------------

record CompressionBasinCollision
  {State Code : Set}
  (A : CA.CompressionAttractor State Code)
  (selectedCode : Code) : Set where
  field
    inside : State
    outside : State
    sameCompressedCode :
      CA.compress A inside ≡ CA.compress A outside
    insideSelectedBasin :
      CA.Basin A selectedCode inside
    outsideSelectedBasin :
      ¬ CA.Basin A selectedCode outside

open CompressionBasinCollision public

asProjectionPredicateCollision :
  ∀ {State Code : Set}
    {A : CA.CompressionAttractor State Code}
    {selectedCode : Code} →
  CompressionBasinCollision A selectedCode →
  SBR.ProjectionPredicateCollision
    (CA.compress A)
    (CA.Basin A selectedCode)
asProjectionPredicateCollision collision =
  record
    { left = inside collision
    ; right = outside collision
    ; sameProjection = sameCompressedCode collision
    ; leftHas = insideSelectedBasin collision
    ; rightLacks = outsideSelectedBasin collision
    }

compression-basin-collision-refutes-factorisation :
  ∀ {State Code : Set}
    {A : CA.CompressionAttractor State Code}
    {selectedCode : Code} →
  CompressionBasinCollision A selectedCode →
  ¬ SBR.PredicateFactorisation
      (CA.compress A)
      (CA.Basin A selectedCode)
compression-basin-collision-refutes-factorisation collision =
  SBR.collision-refutes-factorisation
    (asProjectionPredicateCollision collision)

------------------------------------------------------------------------
-- Boundary theorem:
--
-- A strict compression witness by itself does NOT imply basin information
-- loss.  The additional inside/outside basin distinction is the exact missing
-- premise.  This keeps the existing block-strict-compression result from being
-- over-promoted.
------------------------------------------------------------------------

record StrictCompressionWithBasinSeparation
  {State Code : Set}
  (A : CA.CompressionAttractor State Code)
  (selectedCode : Code) : Set where
  field
    strictCompression :
      CA.StrictCompressionWitness (CA.compress A)
    leftInSelectedBasin :
      CA.Basin A selectedCode
        (CA.leftMicrostate strictCompression)
    rightOutsideSelectedBasin :
      ¬ CA.Basin A selectedCode
          (CA.rightMicrostate strictCompression)

open StrictCompressionWithBasinSeparation public

strict-compression-with-basin-separation-refutes-factorisation :
  ∀ {State Code : Set}
    {A : CA.CompressionAttractor State Code}
    {selectedCode : Code} →
  StrictCompressionWithBasinSeparation A selectedCode →
  ¬ SBR.PredicateFactorisation
      (CA.compress A)
      (CA.Basin A selectedCode)
strict-compression-with-basin-separation-refutes-factorisation witness =
  compression-basin-collision-refutes-factorisation
    record
      { inside =
          CA.leftMicrostate
            (strictCompression witness)
      ; outside =
          CA.rightMicrostate
            (strictCompression witness)
      ; sameCompressedCode =
          CA.sameCompressedCode
            (strictCompression witness)
      ; insideSelectedBasin =
          leftInSelectedBasin witness
      ; outsideSelectedBasin =
          rightOutsideSelectedBasin witness
      }
