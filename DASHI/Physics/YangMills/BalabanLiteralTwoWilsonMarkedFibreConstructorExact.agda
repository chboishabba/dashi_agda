{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedFibreConstructorExact where

------------------------------------------------------------------------
-- Structural constructor for literal twice-Wilson retained fibres.
--
-- A retained raw CMP116 term that carries both selected Wilson/source links is
-- definitionally a Round434 TwiceMarkedTerm.  Mapping this constructor over the
-- raw common-Y fibre makes "both marks" compiler data rather than an additional
-- theorem on the downstream cluster carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _,_)

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedSupportRound434Exact as R434

record RawTwoWilsonFibre
    (Domain RawTerm : Set)
    (CarriesLink : RawTerm → Support.Link → Set)
    (leftMark rightMark : Support.Link) : Set₁ where
  field
    rawTerms : Domain → List RawTerm

    rawCarriesLeft :
      ∀ domain raw →
      raw ∈ rawTerms domain →
      CarriesLink raw leftMark

    rawCarriesRight :
      ∀ domain raw →
      raw ∈ rawTerms domain →
      CarriesLink raw rightMark

    rawHead : Domain → RawTerm
    rawTail : Domain → List RawTerm
    rawTermsAreHeadTail :
      ∀ domain →
      rawTerms domain ≡ rawHead domain ∷ rawTail domain

open RawTwoWilsonFibre public

markTerm :
  ∀ {RawTerm : Set}
    {CarriesLink : RawTerm → Support.Link → Set}
    {leftMark rightMark : Support.Link} →
  (raw : RawTerm) →
  CarriesLink raw leftMark →
  CarriesLink raw rightMark →
  R434.TwiceMarkedTerm RawTerm CarriesLink leftMark rightMark
markTerm raw left right =
  R434.twice-marked raw left right

markRawMembership :
  ∀ {Domain RawTerm CarriesLink leftMark rightMark}
    (fibre :
      RawTwoWilsonFibre
        Domain RawTerm CarriesLink leftMark rightMark)
    domain raw →
  raw ∈ rawTerms fibre domain →
  R434.TwiceMarkedTerm
    RawTerm CarriesLink leftMark rightMark
markRawMembership fibre domain raw membership =
  markTerm raw
    (rawCarriesLeft fibre domain raw membership)
    (rawCarriesRight fibre domain raw membership)

markListWithMembership :
  ∀ {Domain RawTerm CarriesLink leftMark rightMark}
    (fibre :
      RawTwoWilsonFibre
        Domain RawTerm CarriesLink leftMark rightMark)
    domain
    (terms : List RawTerm) →
  (∀ raw → raw ∈ terms → raw ∈ rawTerms fibre domain) →
  List
    (R434.TwiceMarkedTerm
      RawTerm CarriesLink leftMark rightMark)
markListWithMembership fibre domain [] inclusion = []
markListWithMembership fibre domain (raw ∷ raws) inclusion =
  markRawMembership fibre domain raw (inclusion raw (here refl))
  ∷
  markListWithMembership fibre domain raws
    (λ item membership →
      inclusion item (there membership))

rawTailMembership :
  ∀ {Domain RawTerm CarriesLink leftMark rightMark}
    (fibre :
      RawTwoWilsonFibre
        Domain RawTerm CarriesLink leftMark rightMark)
    domain raw →
  raw ∈ rawTail fibre domain →
  raw ∈ rawTerms fibre domain
rawTailMembership fibre domain raw membership
  rewrite rawTermsAreHeadTail fibre domain =
  there membership

markedHead :
  ∀ {Domain RawTerm CarriesLink leftMark rightMark}
    (fibre :
      RawTwoWilsonFibre
        Domain RawTerm CarriesLink leftMark rightMark) →
  Domain →
  R434.TwiceMarkedTerm RawTerm CarriesLink leftMark rightMark
markedHead fibre domain =
  let
    headMembership : rawHead fibre domain ∈ rawTerms fibre domain
    headMembership
      rewrite rawTermsAreHeadTail fibre domain = here refl
  in
  markRawMembership fibre domain (rawHead fibre domain) headMembership

markedTail :
  ∀ {Domain RawTerm CarriesLink leftMark rightMark}
    (fibre :
      RawTwoWilsonFibre
        Domain RawTerm CarriesLink leftMark rightMark) →
  Domain →
  List (R434.TwiceMarkedTerm RawTerm CarriesLink leftMark rightMark)
markedTail fibre domain =
  markListWithMembership fibre domain (rawTail fibre domain)
    (rawTailMembership fibre domain)

markedTerms :
  ∀ {Domain RawTerm CarriesLink leftMark rightMark}
    (fibre :
      RawTwoWilsonFibre
        Domain RawTerm CarriesLink leftMark rightMark) →
  Domain →
  List (R434.TwiceMarkedTerm RawTerm CarriesLink leftMark rightMark)
markedTerms fibre domain =
  markedHead fibre domain ∷ markedTail fibre domain

canonicalTwiceMarkedSupport :
  ∀ {Domain RawTerm CarriesLink leftMark rightMark}
    (fibre :
      RawTwoWilsonFibre
        Domain RawTerm CarriesLink leftMark rightMark) →
  R434.CanonicalTwiceMarkedSupport Domain RawTerm CarriesLink
canonicalTwiceMarkedSupport {leftMark = leftMark} {rightMark = rightMark}
    fibre = record
  { R434.CanonicalTwiceMarkedSupport.leftMark = leftMark
  ; R434.CanonicalTwiceMarkedSupport.rightMark = rightMark
  ; R434.CanonicalTwiceMarkedSupport.termsWithCommonY =
      markedTerms fibre
  }
