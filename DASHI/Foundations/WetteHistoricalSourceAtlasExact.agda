module DASHI.Foundations.WetteHistoricalSourceAtlasExact where

------------------------------------------------------------------------
-- EDUARD WETTE HISTORICAL SOURCE ATLAS
--
-- Purpose: keep primary construction sources, later metamathematical claims,
-- contemporary commentary, and secondary reports visibly distinct.
--
-- A bibliographic source record is provenance, not a proof certificate.  In
-- particular, titles/pages reported by a secondary bibliography are kept
-- distinct from records independently verified against a stable catalogue,
-- journal page, DOI, or archive.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source roles and verification levels.
------------------------------------------------------------------------

data WetteSourceRole : Set where
  earlyConstruction : WetteSourceRole
  constructiveArithmetic : WetteSourceRole
  programmaticRetrospective : WetteSourceRole
  laterContradictionClaim : WetteSourceRole
  laterCanonicalSystemClaim : WetteSourceRole
  laterRevisionClaim : WetteSourceRole
  contemporaryCommentary : WetteSourceRole
  contemporaryReview : WetteSourceRole
  laterSecondaryReception : WetteSourceRole

data SourceVerification : Set where
  stablePrimaryRecord : SourceVerification
  stableArchiveRecord : SourceVerification
  independentlyVerifiedSecondaryRecord : SourceVerification
  secondaryReportedPendingPrimaryCheck : SourceVerification

record WetteSource : Set where
  constructor wetteSource
  field
    author : String
    title : String
    year : Nat
    venue : String
    stableIdentifier : String
    role : WetteSourceRole
    verification : SourceVerification

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
    stableArchiveRecord

wette1960SetTheoryConsistency : WetteSource
wette1960SetTheoryConsistency =
  wetteSource
    "Eduard Wette"
    "Intuitionistic-Recursive Consistency Proof for the Axiomatic Set Theory"
    1960
    "Berkeley Logic Library catalogue record"
    "https://logic-library.berkeley.edu/"
    earlyConstruction
    stableArchiveRecord

-- Berkeley's Logic Library separately catalogues two 1966 Wette items.  They
-- are important because they predate the 1969 Springer chapter and explicitly
-- use both the English 'relatively complete formal system' wording and the
-- German 'relativ vollstaendiger kanonischer Kalkuel' wording.
wette1966EnglishConstructiveArithmetic : WetteSource
wette1966EnglishConstructiveArithmetic =
  wetteSource
    "Eduard Wette"
    "Definition of a (Relatively Complete) Formal System of Constructive Arithmetic"
    1966
    "Berkeley Logic Library catalogue record"
    "https://logic-library.berkeley.edu/"
    constructiveArithmetic
    stableArchiveRecord

wette1966CanonicalCalculus : WetteSource
wette1966CanonicalCalculus =
  wetteSource
    "Eduard Wette"
    "Ein (relativ vollstaendiger) kanonischer Kalkuel konstruktiver Arithmetik"
    1966
    "Berkeley Logic Library catalogue record"
    "https://logic-library.berkeley.edu/"
    constructiveArithmetic
    stableArchiveRecord

wette1969ConstructiveArithmetic : WetteSource
wette1969ConstructiveArithmetic =
  wetteSource
    "Eduard Wette"
    "Definition eines (relativ vollstaendigen) formalen Systems konstruktiver Arithmetik"
    1969
    "Foundations of Mathematics, pp. 130--195"
    "doi:10.1007/978-3-642-86745-3_9"
    constructiveArithmetic
    stablePrimaryRecord

wette1970InfiniteFinite : WetteSource
wette1970InfiniteFinite =
  wetteSource
    "Eduard Wette"
    "Vom Unendlichen zum Endlichen"
    1970
    "Dialectica 24(4), 303--323"
    "doi:10.1111/j.1746-8361.1970.tb01221.x"
    programmaticRetrospective
    stablePrimaryRecord

wette1971NewParadoxes : WetteSource
wette1971NewParadoxes =
  wetteSource
    "Eduard Wette"
    "On new paradoxes in formalized mathematics"
    1971
    "Journal of Symbolic Logic 36, 376--377"
    "bibliographic-record:jsl-36-376-377"
    laterContradictionClaim
    independentlyVerifiedSecondaryRecord

wette1974Contradiction : WetteSource
wette1974Contradiction =
  wetteSource
    "Eduard Wette"
    "Contradiction within pure number theory because of a system-internal 'consistency'-deduction"
    1974
    "International Logic Review, no. 9, 51--62"
    "bibliographic-record:no-verified-doi"
    laterContradictionClaim
    independentlyVerifiedSecondaryRecord

-- These two later items are now useful recovery targets because they are
-- reported as the canonical-system abstract and a subsequent simplification of
-- the inconsistency deduction.  Until a JSL issue/backfile record is checked
-- directly, keep the metadata explicitly secondary-reported rather than
-- silently promoting it to primary verification.
wette1974CanonicalSystemAbstract : WetteSource
wette1974CanonicalSystemAbstract =
  wetteSource
    "Eduard Wette"
    "A Canonical System for the Operative Translation of Formalized Number Theory as a Tool for the Refutation of Arithmetic (Abstract)"
    1974
    "Journal of Symbolic Logic 39, 387--388 (secondary bibliographic report)"
    "secondary-report:jsl-39-387-388"
    laterCanonicalSystemClaim
    secondaryReportedPendingPrimaryCheck

wette1976SimplifyingComplicationAbstract : WetteSource
wette1976SimplifyingComplicationAbstract =
  wetteSource
    "Eduard Wette"
    "A Simplifying Complication Concerning My Inconsistency-Deduction within Formalized Arithmetic (Abstract)"
    1976
    "Journal of Symbolic Logic 41, 272--273 (secondary bibliographic report)"
    "secondary-report:jsl-41-272-273"
    laterRevisionClaim
    secondaryReportedPendingPrimaryCheck

------------------------------------------------------------------------
-- Contemporary and later audit sources.
------------------------------------------------------------------------

bernays1971Commentary : WetteSource
bernays1971Commentary =
  wetteSource
    "Paul Bernays"
    "Zum Symposium ueber die Grundlagen der Mathematik"
    1971
    "Dialectica 25, 171--195; Bernays Project English translation"
    "doi:10.1111/j.1746-8361.1971.tb00598.x"
    contemporaryCommentary
    stablePrimaryRecord

kreiselZucker1972Review : WetteSource
kreiselZucker1972Review =
  wetteSource
    "G. Kreisel and J. Zucker"
    "Review of Eduard Wette, Definition eines (relativ vollstaendigen) formalen Systems konstruktiver Arithmetik"
    1972
    "Journal of Symbolic Logic 37(1), 203--204"
    "doi:10.2307/2272630"
    contemporaryReview
    stablePrimaryRecord

yesseninVolpinHennix2001 : WetteSource
yesseninVolpinHennix2001 =
  wetteSource
    "Alexander S. Yessenin-Volpin and Christer Hennix"
    "Beware of the Goedel-Wette paradox"
    2001
    "arXiv:math/0110094"
    "arxiv:math/0110094"
    laterSecondaryReception
    stableArchiveRecord

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

    secondaryReportedJSLItemsPromotedToPrimaryWithoutCheck : Bool
    secondaryReportedJSLItemsPromotedToPrimaryWithoutCheckIsFalse :
      secondaryReportedJSLItemsPromotedToPrimaryWithoutCheck ≡ false

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
    false refl
