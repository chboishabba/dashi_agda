module DASHI.Foundations.RelationalStageTwelveSiteExact where

------------------------------------------------------------------------
-- NONTRIVIAL RELATIONAL COVER COMPANION TO STAGE TWELVE
--
-- DASHI CONTRIBUTION
--
-- StageTwelveGrothendieckRelationHyperformExact already owns a genuine generic
-- Grothendieck-topology interface and a conservative discrete/maximal concrete
-- site.  This file does not rewrite that theorem.  It adds the nontrivial
-- three-dyad cover needed by relational/trialectic work:
--
--             U_AB   U_BC   U_CA
-- overlaps:      A      B      C
--
-- Compatibility is paid on all three overlaps before gluing.  The local edge
-- sections are therefore not glued merely by being supplied as a tuple.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Stage12

record TriadicLocals (EdgeSection : Set) : Set where
  constructor triadic-locals
  field
    localAB : EdgeSection
    localBC : EdgeSection
    localCA : EdgeSection

open TriadicLocals public

record TriadicOverlapSystem
    (EdgeSection VertexSection : Set) : Set₁ where
  constructor triadic-overlap-system
  field
    abAtA : EdgeSection → VertexSection
    caAtA : EdgeSection → VertexSection
    abAtB : EdgeSection → VertexSection
    bcAtB : EdgeSection → VertexSection
    bcAtC : EdgeSection → VertexSection
    caAtC : EdgeSection → VertexSection

open TriadicOverlapSystem public

record CompatibleOnTriadicCover
    {EdgeSection VertexSection : Set}
    (overlaps : TriadicOverlapSystem EdgeSection VertexSection)
    (locals : TriadicLocals EdgeSection) : Set where
  constructor compatible-on-triadic-cover
  field
    agreesAtA :
      abAtA overlaps (localAB locals)
      ≡ caAtA overlaps (localCA locals)
    agreesAtB :
      abAtB overlaps (localAB locals)
      ≡ bcAtB overlaps (localBC locals)
    agreesAtC :
      bcAtC overlaps (localBC locals)
      ≡ caAtC overlaps (localCA locals)

open CompatibleOnTriadicCover public

record TriadicRelationalSheaf
    (EdgeSection VertexSection GlobalSection : Set) : Set₁ where
  field
    overlaps : TriadicOverlapSystem EdgeSection VertexSection

    restrictGlobalAB : GlobalSection → EdgeSection
    restrictGlobalBC : GlobalSection → EdgeSection
    restrictGlobalCA : GlobalSection → EdgeSection

    glue :
      (locals : TriadicLocals EdgeSection) →
      CompatibleOnTriadicCover overlaps locals →
      GlobalSection

    glueRestrictsAB :
      (locals : TriadicLocals EdgeSection) →
      (compatibility : CompatibleOnTriadicCover overlaps locals) →
      restrictGlobalAB (glue locals compatibility) ≡ localAB locals

    glueRestrictsBC :
      (locals : TriadicLocals EdgeSection) →
      (compatibility : CompatibleOnTriadicCover overlaps locals) →
      restrictGlobalBC (glue locals compatibility) ≡ localBC locals

    glueRestrictsCA :
      (locals : TriadicLocals EdgeSection) →
      (compatibility : CompatibleOnTriadicCover overlaps locals) →
      restrictGlobalCA (glue locals compatibility) ≡ localCA locals

open TriadicRelationalSheaf public

------------------------------------------------------------------------
-- A concrete non-vacuous finite instance: Bool-valued edge sections must
-- literally agree at every shared vertex before the triple can glue.
------------------------------------------------------------------------

data DemoGlobal : Set where
  allFalse : DemoGlobal
  allTrue : DemoGlobal

demoEdgeAB : DemoGlobal → Bool
demoEdgeAB allFalse = false
demoEdgeAB allTrue = true

demoEdgeBC : DemoGlobal → Bool
demoEdgeBC allFalse = false
demoEdgeBC allTrue = true

demoEdgeCA : DemoGlobal → Bool
demoEdgeCA allFalse = false
demoEdgeCA allTrue = true

demoOverlaps : TriadicOverlapSystem Bool Bool
demoOverlaps =
  triadic-overlap-system
    (λ x → x) (λ x → x)
    (λ x → x) (λ x → x)
    (λ x → x) (λ x → x)

demoGlue :
  (locals : TriadicLocals Bool) →
  CompatibleOnTriadicCover demoOverlaps locals →
  DemoGlobal
demoGlue (triadic-locals false false false) compatibility = allFalse
demoGlue (triadic-locals false false true)
  (compatible-on-triadic-cover () _ _)
demoGlue (triadic-locals false true false)
  (compatible-on-triadic-cover _ () _)
demoGlue (triadic-locals false true true)
  (compatible-on-triadic-cover () _ _)
demoGlue (triadic-locals true false false)
  (compatible-on-triadic-cover () _ _)
demoGlue (triadic-locals true false true)
  (compatible-on-triadic-cover _ () _)
demoGlue (triadic-locals true true false)
  (compatible-on-triadic-cover () _ _)
demoGlue (triadic-locals true true true) compatibility = allTrue

demoGlueAB :
  (locals : TriadicLocals Bool) →
  (compatibility : CompatibleOnTriadicCover demoOverlaps locals) →
  demoEdgeAB (demoGlue locals compatibility) ≡ localAB locals
demoGlueAB (triadic-locals false false false) compatibility = refl
demoGlueAB (triadic-locals false false true)
  (compatible-on-triadic-cover () _ _)
demoGlueAB (triadic-locals false true false)
  (compatible-on-triadic-cover _ () _)
demoGlueAB (triadic-locals false true true)
  (compatible-on-triadic-cover () _ _)
demoGlueAB (triadic-locals true false false)
  (compatible-on-triadic-cover () _ _)
demoGlueAB (triadic-locals true false true)
  (compatible-on-triadic-cover _ () _)
demoGlueAB (triadic-locals true true false)
  (compatible-on-triadic-cover () _ _)
demoGlueAB (triadic-locals true true true) compatibility = refl

demoGlueBC :
  (locals : TriadicLocals Bool) →
  (compatibility : CompatibleOnTriadicCover demoOverlaps locals) →
  demoEdgeBC (demoGlue locals compatibility) ≡ localBC locals
demoGlueBC (triadic-locals false false false) compatibility = refl
demoGlueBC (triadic-locals false false true)
  (compatible-on-triadic-cover () _ _)
demoGlueBC (triadic-locals false true false)
  (compatible-on-triadic-cover _ () _)
demoGlueBC (triadic-locals false true true)
  (compatible-on-triadic-cover () _ _)
demoGlueBC (triadic-locals true false false)
  (compatible-on-triadic-cover () _ _)
demoGlueBC (triadic-locals true false true)
  (compatible-on-triadic-cover _ () _)
demoGlueBC (triadic-locals true true false)
  (compatible-on-triadic-cover () _ _)
demoGlueBC (triadic-locals true true true) compatibility = refl

demoGlueCA :
  (locals : TriadicLocals Bool) →
  (compatibility : CompatibleOnTriadicCover demoOverlaps locals) →
  demoEdgeCA (demoGlue locals compatibility) ≡ localCA locals
demoGlueCA (triadic-locals false false false) compatibility = refl
demoGlueCA (triadic-locals false false true)
  (compatible-on-triadic-cover () _ _)
demoGlueCA (triadic-locals false true false)
  (compatible-on-triadic-cover _ () _)
demoGlueCA (triadic-locals false true true)
  (compatible-on-triadic-cover () _ _)
demoGlueCA (triadic-locals true false false)
  (compatible-on-triadic-cover () _ _)
demoGlueCA (triadic-locals true false true)
  (compatible-on-triadic-cover _ () _)
demoGlueCA (triadic-locals true true false)
  (compatible-on-triadic-cover () _ _)
demoGlueCA (triadic-locals true true true) compatibility = refl

demoTriadicSheaf : TriadicRelationalSheaf Bool Bool DemoGlobal
demoTriadicSheaf = record
  { overlaps = demoOverlaps
  ; restrictGlobalAB = demoEdgeAB
  ; restrictGlobalBC = demoEdgeBC
  ; restrictGlobalCA = demoEdgeCA
  ; glue = demoGlue
  ; glueRestrictsAB = demoGlueAB
  ; glueRestrictsBC = demoGlueBC
  ; glueRestrictsCA = demoGlueCA
  }

StageTwelveAnchoredGlobal : Set → Set
StageTwelveAnchoredGlobal Global =
  Stage12.StageRelation144 × Global

record RelationalStageTwelveSiteBoundary : Set where
  constructor relational-stage-twelve-site-boundary
  field
    compatibilityIsTrivialTop : Bool
    allThreeOverlapAgreementsRequired : Bool
    stage12RelationCarrierRetainedAsAnchor : Bool
    relationalCoverEqualsAnalyticModularCover : Bool
    empiricalRelationalSelfTheoryProvesThisSheaf : Bool

canonicalRelationalStageTwelveSiteBoundary :
  RelationalStageTwelveSiteBoundary
canonicalRelationalStageTwelveSiteBoundary =
  relational-stage-twelve-site-boundary false true true false false
