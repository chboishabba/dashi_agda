module DASHI.Physics.Closure.SectorProjectionType where

open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- A3-only abstract sector-projection surface.
--
-- This module records only the type shape and opaque witnesses requested for
-- Manager A / A3.  The sector, projection, idempotence, and admissibility
-- inhabitants below are postulated tokens.  They do not construct a runtime
-- projection map, do not discharge a promotion gate, and do not edit or import
-- B/C sector material.

abstract
  record SectorProjectionType : Setω where
    field
      sourceSector :
        Set

      targetSector :
        Set

      projectionMapToken :
        Set

      idempotenceToken :
        Set

      contractionAdmissibilityToken :
        Set

      abstractPostulatedNonPromotingBoundary :
        List String

  postulate
    A3SourceSector :
      Set

    A3TargetSector :
      Set

    A3ProjectionMapToken :
      Set

    A3IdempotenceToken :
      Set

    A3ContractionAdmissibilityToken :
      Set

    A3ProjectionMapTokenInhabitant :
      A3ProjectionMapToken

    A3IdempotenceTokenInhabitant :
      A3IdempotenceToken

    A3ContractionAdmissibilityTokenInhabitant :
      A3ContractionAdmissibilityToken

  A3SectorProjectionBoundary :
    List String
  A3SectorProjectionBoundary =
    "abstract/postulated sector projection surface only"
    ∷ "source sector and target sector are opaque A3 tokens"
    ∷ "projection map token is not a runtime map"
    ∷ "idempotence token is postulated, not proved here"
    ∷ "contraction/admissibility token is postulated, not promoted"
    ∷ "no B/C sector material, aggregator edit, or closure promotion is supplied"
    ∷ []

  A3SectorProjectionType :
    SectorProjectionType
  A3SectorProjectionType =
    record
      { sourceSector =
          A3SourceSector
      ; targetSector =
          A3TargetSector
      ; projectionMapToken =
          A3ProjectionMapToken
      ; idempotenceToken =
          A3IdempotenceToken
      ; contractionAdmissibilityToken =
          A3ContractionAdmissibilityToken
      ; abstractPostulatedNonPromotingBoundary =
          A3SectorProjectionBoundary
      }
