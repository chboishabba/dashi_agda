module DASHI.Foundations.WetteHistoricalSourceAtlasExact where

------------------------------------------------------------------------
-- EDUARD WETTE HISTORICAL SOURCE ATLAS
--
-- Purpose: keep primary construction sources, later metamathematical claims,
-- contemporary commentary, and contemporary review literature visibly distinct.
-- A bibliographic source record is provenance, not a proof certificate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source roles.
------------------------------------------------------------------------

data WetteSourceRole : Set where
  earlyConstruction : WetteSourceRole
  constructiveArithmetic : WetteSourceRole
  programmaticRetrospective : WetteSourceRole
  laterContradictionClaim : WetteSourceRole
  contemporaryCommentary : WetteSourceRole
  contemporaryReview : WetteSourceRole

record WetteSource : Set where
  constructor wetteSource
  field
    author : String
    title : String
    year : Nat
    venue : String
    stableIdentifier : String
    role : WetteSourceRole

open WetteSource public

------------------------------------------------------------------------
-- Primary Wette sources.
------------------------------------------------------------------------

wette1959SetTheory : WetteSource
wette1959SetTheory =
  wetteSource
    "Eduard Wette"
    "Von Operativen Modellen der Axiomatischen Mengenlehre"
    1959
    "Berkeley Logic Library catalogue record"
    "https://logic-library.berkeley.edu/"
    earlyConstruction

wette1960SetTheoryConsistency : WetteSource
wette1960SetTheoryConsistency =
  wetteSource
    "Eduard Wette"
    "Intuitionistic-Recursive Consistency Proof for the Axiomatic Set Theory"
    1960
    "Berkeley Logic Library catalogue record"
    "https://logic-library.berkeley.edu/"
    earlyConstruction

wette1969ConstructiveArithmetic : WetteSource
wette1969ConstructiveArithmetic =
  wetteSource
    "Eduard Wette"
    "Definition eines (relativ vollstaendigen) formalen Systems konstruktiver Arithmetik"
    1969
    "Foundations of Mathematics, pp. 130--195"
    "doi:10.1007/978-3-642-86745-3_9"
    constructiveArithmetic

wette1970InfiniteFinite : WetteSource
wette1970InfiniteFinite =
  wetteSource
    "Eduard Wette"
    "Vom Unendlichen zum Endlichen"
    1970
    "Dialectica 24(4), 303--324"
    "doi:10.1111/j.1746-8361.1970.tb01221.x"
    programmaticRetrospective

wette1974Contradiction : WetteSource
wette1974Contradiction =
  wetteSource
    "Eduard Wette"
    "Contradiction within pure number theory because of a system-internal 'consistency'-deduction"
    1974
    "International Logic Review 5(9), 51--62"
    "bibliographic-record:no-verified-doi"
    laterContradictionClaim

------------------------------------------------------------------------
-- Contemporary audit sources.
------------------------------------------------------------------------

bernays1971Commentary : WetteSource
bernays1971Commentary =
  wetteSource
    "Paul Bernays"
    "Zum Symposium ueber die Grundlagen der Mathematik"
    1971
    "Dialectica 25, 171--195"
    "doi:10.1111/j.1746-8361.1971.tb00598.x"
    contemporaryCommentary

kreiselZucker1972Review : WetteSource
kreiselZucker1972Review =
  wetteSource
    "G. Kreisel and J. Zucker"
    "Review of Eduard Wette, Definition eines (relativ vollstaendigen) formalen Systems konstruktiver Arithmetik"
    1972
    "Journal of Symbolic Logic 37(1), 203--204"
    "doi:10.2307/2272630"
    contemporaryReview

------------------------------------------------------------------------
-- Provenance boundary.
------------------------------------------------------------------------

record WetteHistoricalSourceBoundary : Set where
  constructor wetteHistoricalSourceBoundary
  field
    primaryConstructionSeparatedFromLaterClaim : Bool
    primaryConstructionSeparatedFromLaterClaimIsTrue :
      primaryConstructionSeparatedFromLaterClaim ≡ true

    contemporaryReviewTypedSeparately : Bool
    contemporaryReviewTypedSeparatelyIsTrue :
      contemporaryReviewTypedSeparately ≡ true

    stableIdentifiersAttachedWhereVerified : Bool
    stableIdentifiersAttachedWhereVerifiedIsTrue :
      stableIdentifiersAttachedWhereVerified ≡ true

    unverified1974DOIFabricated : Bool
    unverified1974DOIFabricatedIsFalse :
      unverified1974DOIFabricated ≡ false

    bibliographyByItselfEstablishesHistoricalFormalSemantics : Bool
    bibliographyByItselfEstablishesHistoricalFormalSemanticsIsFalse :
      bibliographyByItselfEstablishesHistoricalFormalSemantics ≡ false

canonicalWetteHistoricalSourceBoundary : WetteHistoricalSourceBoundary
canonicalWetteHistoricalSourceBoundary =
  wetteHistoricalSourceBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
