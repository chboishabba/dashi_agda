module DASHI.Physics.YangMills.SourceEntityQidBindingsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.ScientificCitationQidBindingsExact as Citation

------------------------------------------------------------------------
-- YANG-MILLS SOURCE <-> ENTITY ALIGNMENTS
--
-- The citation/source identifier remains authoritative for bibliographic
-- identity. These bindings attach related external entities to the source
-- surface without importing Wikidata authority into the physical theorem lane.
------------------------------------------------------------------------

data YMReferenceKey : Set where
  os1973 os1975 grossWilczek1973 politzer1973 seiler1982 : YMReferenceKey
  balaban1987 balaban1988 faddeevPopov1967 federbushPhaseCellIV : YMReferenceKey
  jaffeWittenClayYM : YMReferenceKey

bindingForYM : YMReferenceKey → Citation.CitationEntityBinding
bindingForYM os1973 = Citation.os1973
bindingForYM os1975 = Citation.os1975
bindingForYM grossWilczek1973 = Citation.grossWilczek1973
bindingForYM politzer1973 = Citation.politzer1973
bindingForYM seiler1982 = Citation.seiler1982
bindingForYM balaban1987 = Citation.balaban1987
bindingForYM balaban1988 = Citation.balaban1988
bindingForYM faddeevPopov1967 = Citation.faddeevPopov1967
bindingForYM federbushPhaseCellIV = Citation.federbush1988PhaseCellIV
bindingForYM jaffeWittenClayYM = Citation.jaffeWittenClayYM

record YMReferenceEntityBoundary : Set where
  constructor ym-reference-entity-boundary
  field
    qidsAnnotateSourceSurface : Bool
    doiOrOfficialSourceRemainsBibliographicIdentity : Bool
    qidCreatesPhysicalTheorem : Bool
    qidClosesClayObligation : Bool

canonicalYMReferenceEntityBoundary : YMReferenceEntityBoundary
canonicalYMReferenceEntityBoundary =
  ym-reference-entity-boundary true true false false

data QidClosesYangMillsPhysicalLeaf : Set where
qidDoesNotCloseYangMillsPhysicalLeaf : QidClosesYangMillsPhysicalLeaf → ⊥
qidDoesNotCloseYangMillsPhysicalLeaf ()
