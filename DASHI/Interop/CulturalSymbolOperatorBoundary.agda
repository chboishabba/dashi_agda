module DASHI.Interop.CulturalSymbolOperatorBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Culture.CulturalTriadOperatorBoundary as Triad
import DASHI.Culture.QiOperatorTheoryBoundary as QiTheory
import DASHI.Culture.TaoOperatorGrammar as TaoGrammar
import DASHI.Culture.YinYangPolarityBoundary as YinYang

------------------------------------------------------------------------
-- Cultural symbol / operator boundary.
--
-- This module is candidate-only.  It records how religious and cultural
-- symbols can expose operator structure in a society's grammar while keeping
-- nationalism, monoculture, enemy-coding, domination, and authority
-- promotion blocked.  Dialectics, hooks, Nietzsche, Zizek, and Foucault are
-- treated as interpretive lenses only; they do not supply formal, legal,
-- political, theological, or social-science authority here.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data Never : Set where

data CulturalSymbolKind : Set where
  religiousSymbolKind : CulturalSymbolKind
  culturalSymbolKind : CulturalSymbolKind
  trinitySymbolKind : CulturalSymbolKind
  yinYangSymbolKind : CulturalSymbolKind
  dialecticalDiagramSymbolKind : CulturalSymbolKind
  criticalTheorySymbolKind : CulturalSymbolKind
  boundaryGlyphSymbolKind : CulturalSymbolKind
  civicSymbolKind : CulturalSymbolKind
  ancestralSymbolKind : CulturalSymbolKind

symbolKindLabel : CulturalSymbolKind → String
symbolKindLabel religiousSymbolKind = "religious symbol"
symbolKindLabel culturalSymbolKind = "cultural symbol"
symbolKindLabel trinitySymbolKind = "trinity symbol"
symbolKindLabel yinYangSymbolKind = "yin-yang symbol"
symbolKindLabel dialecticalDiagramSymbolKind = "dialectical diagram"
symbolKindLabel criticalTheorySymbolKind = "critical theory symbol"
symbolKindLabel boundaryGlyphSymbolKind = "boundary glyph"
symbolKindLabel civicSymbolKind = "civic symbol"
symbolKindLabel ancestralSymbolKind = "ancestral symbol"

data InterpretiveLensKind : Set where
  dialecticsLensKind : InterpretiveLensKind
  hooksLensKind : InterpretiveLensKind
  nietzscheLensKind : InterpretiveLensKind
  zizekLensKind : InterpretiveLensKind
  foucaultLensKind : InterpretiveLensKind
  genealogyLensKind : InterpretiveLensKind
  powerCritiqueLensKind : InterpretiveLensKind
  relationLensKind : InterpretiveLensKind
  translationLensKind : InterpretiveLensKind

lensKindLabel : InterpretiveLensKind → String
lensKindLabel dialecticsLensKind = "dialectics"
lensKindLabel hooksLensKind = "hooks"
lensKindLabel nietzscheLensKind = "nietzsche"
lensKindLabel zizekLensKind = "zizek"
lensKindLabel foucaultLensKind = "foucault"
lensKindLabel genealogyLensKind = "genealogy"
lensKindLabel powerCritiqueLensKind = "power critique"
lensKindLabel relationLensKind = "relation"
lensKindLabel translationLensKind = "translation"

data SocietalOperatorStructureKind : Set where
  operatorStructureVisibleKind : SocietalOperatorStructureKind
  selfOtherRelationStructureKind : SocietalOperatorStructureKind
  polarityThresholdStructureKind : SocietalOperatorStructureKind
  powerBoundaryStructureKind : SocietalOperatorStructureKind
  genealogicalCritiqueStructureKind : SocietalOperatorStructureKind
  pluralCivicStructureKind : SocietalOperatorStructureKind
  dominationBoundaryStructureKind : SocietalOperatorStructureKind

structureKindLabel : SocietalOperatorStructureKind → String
structureKindLabel operatorStructureVisibleKind = "operator-structure visible"
structureKindLabel selfOtherRelationStructureKind = "self-other-relation"
structureKindLabel polarityThresholdStructureKind = "polarity-threshold"
structureKindLabel powerBoundaryStructureKind = "power-boundary"
structureKindLabel genealogicalCritiqueStructureKind = "genealogical critique"
structureKindLabel pluralCivicStructureKind = "plural civic"
structureKindLabel dominationBoundaryStructureKind = "domination boundary"

data CulturalOperatorClaimKind : Set where
  candidateSymbolStructureClaim : CulturalOperatorClaimKind
  candidateLensOnlyClaim : CulturalOperatorClaimKind
  nationalismReadingClaim : CulturalOperatorClaimKind
  monocultureCompressionClaim : CulturalOperatorClaimKind
  enemyCodingDominationClaim : CulturalOperatorClaimKind
  dominationReadingClaim : CulturalOperatorClaimKind
  formalAuthorityClaim : CulturalOperatorClaimKind
  legalAuthorityClaim : CulturalOperatorClaimKind
  politicalAuthorityClaim : CulturalOperatorClaimKind
  theologicalAuthorityClaim : CulturalOperatorClaimKind
  socialScienceAuthorityClaim : CulturalOperatorClaimKind

claimKindLabel : CulturalOperatorClaimKind → String
claimKindLabel candidateSymbolStructureClaim =
  "candidate symbol-structure claim"
claimKindLabel candidateLensOnlyClaim =
  "candidate lens-only claim"
claimKindLabel nationalismReadingClaim =
  "nationalism reading claim"
claimKindLabel monocultureCompressionClaim =
  "monoculture compression claim"
claimKindLabel enemyCodingDominationClaim =
  "enemy-coding domination claim"
claimKindLabel dominationReadingClaim =
  "domination reading claim"
claimKindLabel formalAuthorityClaim =
  "formal authority claim"
claimKindLabel legalAuthorityClaim =
  "legal authority claim"
claimKindLabel politicalAuthorityClaim =
  "political authority claim"
claimKindLabel theologicalAuthorityClaim =
  "theological authority claim"
claimKindLabel socialScienceAuthorityClaim =
  "social-science authority claim"

AdmissibleCulturalOperatorClaim :
  CulturalOperatorClaimKind →
  Set
AdmissibleCulturalOperatorClaim candidateSymbolStructureClaim = ⊤
AdmissibleCulturalOperatorClaim candidateLensOnlyClaim = ⊤
AdmissibleCulturalOperatorClaim nationalismReadingClaim = Never
AdmissibleCulturalOperatorClaim monocultureCompressionClaim = Never
AdmissibleCulturalOperatorClaim enemyCodingDominationClaim = Never
AdmissibleCulturalOperatorClaim dominationReadingClaim = Never
AdmissibleCulturalOperatorClaim formalAuthorityClaim = Never
AdmissibleCulturalOperatorClaim legalAuthorityClaim = Never
AdmissibleCulturalOperatorClaim politicalAuthorityClaim = Never
AdmissibleCulturalOperatorClaim theologicalAuthorityClaim = Never
AdmissibleCulturalOperatorClaim socialScienceAuthorityClaim = Never

nationalismReadingClaimRejected :
  AdmissibleCulturalOperatorClaim nationalismReadingClaim →
  Never
nationalismReadingClaimRejected impossible = impossible

monocultureCompressionClaimRejected :
  AdmissibleCulturalOperatorClaim monocultureCompressionClaim →
  Never
monocultureCompressionClaimRejected impossible = impossible

enemyCodingDominationClaimRejected :
  AdmissibleCulturalOperatorClaim enemyCodingDominationClaim →
  Never
enemyCodingDominationClaimRejected impossible = impossible

dominationReadingClaimRejected :
  AdmissibleCulturalOperatorClaim dominationReadingClaim →
  Never
dominationReadingClaimRejected impossible = impossible

formalAuthorityClaimRejected :
  AdmissibleCulturalOperatorClaim formalAuthorityClaim →
  Never
formalAuthorityClaimRejected impossible = impossible

legalAuthorityClaimRejected :
  AdmissibleCulturalOperatorClaim legalAuthorityClaim →
  Never
legalAuthorityClaimRejected impossible = impossible

politicalAuthorityClaimRejected :
  AdmissibleCulturalOperatorClaim politicalAuthorityClaim →
  Never
politicalAuthorityClaimRejected impossible = impossible

theologicalAuthorityClaimRejected :
  AdmissibleCulturalOperatorClaim theologicalAuthorityClaim →
  Never
theologicalAuthorityClaimRejected impossible = impossible

socialScienceAuthorityClaimRejected :
  AdmissibleCulturalOperatorClaim socialScienceAuthorityClaim →
  Never
socialScienceAuthorityClaimRejected impossible = impossible

data CulturalOperatorLaw : Set where
  symbolRevealsOperatorStructureLaw : CulturalOperatorLaw
  lensIsInterpretiveOnlyLaw : CulturalOperatorLaw
  nationalismBlockedLaw : CulturalOperatorLaw
  monocultureBlockedLaw : CulturalOperatorLaw
  enemyCodingBlockedLaw : CulturalOperatorLaw
  dominationBlockedLaw : CulturalOperatorLaw
  formalAuthorityBlockedLaw : CulturalOperatorLaw
  legalAuthorityBlockedLaw : CulturalOperatorLaw
  politicalAuthorityBlockedLaw : CulturalOperatorLaw
  theologicalAuthorityBlockedLaw : CulturalOperatorLaw
  socialScienceAuthorityBlockedLaw : CulturalOperatorLaw

lawLabel : CulturalOperatorLaw → String
lawLabel symbolRevealsOperatorStructureLaw =
  "symbol reveals operator structure"
lawLabel lensIsInterpretiveOnlyLaw =
  "lens is interpretive only"
lawLabel nationalismBlockedLaw =
  "nationalism blocked"
lawLabel monocultureBlockedLaw =
  "monoculture blocked"
lawLabel enemyCodingBlockedLaw =
  "enemy-coding blocked"
lawLabel dominationBlockedLaw =
  "domination blocked"
lawLabel formalAuthorityBlockedLaw =
  "formal authority blocked"
lawLabel legalAuthorityBlockedLaw =
  "legal authority blocked"
lawLabel politicalAuthorityBlockedLaw =
  "political authority blocked"
lawLabel theologicalAuthorityBlockedLaw =
  "theological authority blocked"
lawLabel socialScienceAuthorityBlockedLaw =
  "social-science authority blocked"

canonicalCulturalOperatorLaws : List CulturalOperatorLaw
canonicalCulturalOperatorLaws =
  symbolRevealsOperatorStructureLaw
  ∷ lensIsInterpretiveOnlyLaw
  ∷ nationalismBlockedLaw
  ∷ monocultureBlockedLaw
  ∷ enemyCodingBlockedLaw
  ∷ dominationBlockedLaw
  ∷ formalAuthorityBlockedLaw
  ∷ legalAuthorityBlockedLaw
  ∷ politicalAuthorityBlockedLaw
  ∷ theologicalAuthorityBlockedLaw
  ∷ socialScienceAuthorityBlockedLaw
  ∷ []

canonicalCulturalOperatorLawCount : Nat
canonicalCulturalOperatorLawCount =
  listCount canonicalCulturalOperatorLaws

data CulturalOperatorRoute : Set where
  candidateOnlySymbolRoute : CulturalOperatorRoute
  nationalismRoute : CulturalOperatorRoute
  monocultureRoute : CulturalOperatorRoute
  enemyCodingRoute : CulturalOperatorRoute
  dominationRoute : CulturalOperatorRoute
  formalAuthorityRoute : CulturalOperatorRoute
  legalAuthorityRoute : CulturalOperatorRoute
  politicalAuthorityRoute : CulturalOperatorRoute
  theologicalAuthorityRoute : CulturalOperatorRoute
  socialScienceAuthorityRoute : CulturalOperatorRoute

routeLabel : CulturalOperatorRoute → String
routeLabel candidateOnlySymbolRoute = "candidate-only symbol route"
routeLabel nationalismRoute = "nationalism route"
routeLabel monocultureRoute = "monoculture route"
routeLabel enemyCodingRoute = "enemy-coding route"
routeLabel dominationRoute = "domination route"
routeLabel formalAuthorityRoute = "formal authority route"
routeLabel legalAuthorityRoute = "legal authority route"
routeLabel politicalAuthorityRoute = "political authority route"
routeLabel theologicalAuthorityRoute = "theological authority route"
routeLabel socialScienceAuthorityRoute = "social-science authority route"

AdmissibleCulturalOperatorRoute :
  CulturalOperatorRoute →
  Set
AdmissibleCulturalOperatorRoute candidateOnlySymbolRoute = ⊤
AdmissibleCulturalOperatorRoute nationalismRoute = Never
AdmissibleCulturalOperatorRoute monocultureRoute = Never
AdmissibleCulturalOperatorRoute enemyCodingRoute = Never
AdmissibleCulturalOperatorRoute dominationRoute = Never
AdmissibleCulturalOperatorRoute formalAuthorityRoute = Never
AdmissibleCulturalOperatorRoute legalAuthorityRoute = Never
AdmissibleCulturalOperatorRoute politicalAuthorityRoute = Never
AdmissibleCulturalOperatorRoute theologicalAuthorityRoute = Never
AdmissibleCulturalOperatorRoute socialScienceAuthorityRoute = Never

nationalismRouteRejected :
  AdmissibleCulturalOperatorRoute nationalismRoute →
  Never
nationalismRouteRejected impossible = impossible

monocultureRouteRejected :
  AdmissibleCulturalOperatorRoute monocultureRoute →
  Never
monocultureRouteRejected impossible = impossible

enemyCodingRouteRejected :
  AdmissibleCulturalOperatorRoute enemyCodingRoute →
  Never
enemyCodingRouteRejected impossible = impossible

dominationRouteRejected :
  AdmissibleCulturalOperatorRoute dominationRoute →
  Never
dominationRouteRejected impossible = impossible

formalAuthorityRouteRejected :
  AdmissibleCulturalOperatorRoute formalAuthorityRoute →
  Never
formalAuthorityRouteRejected impossible = impossible

legalAuthorityRouteRejected :
  AdmissibleCulturalOperatorRoute legalAuthorityRoute →
  Never
legalAuthorityRouteRejected impossible = impossible

politicalAuthorityRouteRejected :
  AdmissibleCulturalOperatorRoute politicalAuthorityRoute →
  Never
politicalAuthorityRouteRejected impossible = impossible

theologicalAuthorityRouteRejected :
  AdmissibleCulturalOperatorRoute theologicalAuthorityRoute →
  Never
theologicalAuthorityRouteRejected impossible = impossible

socialScienceAuthorityRouteRejected :
  AdmissibleCulturalOperatorRoute socialScienceAuthorityRoute →
  Never
socialScienceAuthorityRouteRejected impossible = impossible

record CulturalOperatorAuthorityBits : Set where
  constructor culturalOperatorAuthorityBits
  field
    culturalAuthority : Bool
    empiricalAuthority : Bool
    spiritualAuthority : Bool
    mysticalAuthority : Bool
    canonicalTextAuthority : Bool
    formalAuthority : Bool
    legalAuthority : Bool
    politicalAuthority : Bool
    theologicalAuthority : Bool
    socialScienceAuthority : Bool
    nationalismReading : Bool
    monocultureReading : Bool
    enemyCodingReading : Bool
    dominationReading : Bool
    interpretiveOnly : Bool
    candidateOnly : Bool
    promoted : Bool

open CulturalOperatorAuthorityBits public

canonicalCulturalOperatorAuthorityBits : CulturalOperatorAuthorityBits
canonicalCulturalOperatorAuthorityBits =
  culturalOperatorAuthorityBits
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    true
    true
    false

record CulturalOperatorAuthorityFailClosed : Set where
  constructor culturalOperatorAuthorityFailClosed
  field
    culturalAuthorityFalse :
      culturalAuthority canonicalCulturalOperatorAuthorityBits ≡ false
    empiricalAuthorityFalse :
      empiricalAuthority canonicalCulturalOperatorAuthorityBits ≡ false
    spiritualAuthorityFalse :
      spiritualAuthority canonicalCulturalOperatorAuthorityBits ≡ false
    mysticalAuthorityFalse :
      mysticalAuthority canonicalCulturalOperatorAuthorityBits ≡ false
    canonicalTextAuthorityFalse :
      canonicalTextAuthority canonicalCulturalOperatorAuthorityBits ≡ false
    formalAuthorityFalse :
      formalAuthority canonicalCulturalOperatorAuthorityBits ≡ false
    legalAuthorityFalse :
      legalAuthority canonicalCulturalOperatorAuthorityBits ≡ false
    politicalAuthorityFalse :
      politicalAuthority canonicalCulturalOperatorAuthorityBits ≡ false
    theologicalAuthorityFalse :
      theologicalAuthority canonicalCulturalOperatorAuthorityBits ≡ false
    socialScienceAuthorityFalse :
      socialScienceAuthority canonicalCulturalOperatorAuthorityBits ≡ false
    nationalismReadingFalse :
      nationalismReading canonicalCulturalOperatorAuthorityBits ≡ false
    monocultureReadingFalse :
      monocultureReading canonicalCulturalOperatorAuthorityBits ≡ false
    enemyCodingReadingFalse :
      enemyCodingReading canonicalCulturalOperatorAuthorityBits ≡ false
    dominationReadingFalse :
      dominationReading canonicalCulturalOperatorAuthorityBits ≡ false
    interpretiveOnlyTrue :
      interpretiveOnly canonicalCulturalOperatorAuthorityBits ≡ true
    candidateOnlyTrue :
      candidateOnly canonicalCulturalOperatorAuthorityBits ≡ true
    promotedFalse :
      promoted canonicalCulturalOperatorAuthorityBits ≡ false

canonicalCulturalOperatorAuthorityFailClosed :
  CulturalOperatorAuthorityFailClosed
canonicalCulturalOperatorAuthorityFailClosed =
  culturalOperatorAuthorityFailClosed
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record CulturalOperatorRow : Set where
  constructor culturalOperatorRow
  field
    rowId : Nat
    symbolKind : CulturalSymbolKind
    lensKind : InterpretiveLensKind
    structureKind : SocietalOperatorStructureKind
    claimKind : CulturalOperatorClaimKind
    routeKind : CulturalOperatorRoute
    authorityBits : CulturalOperatorAuthorityBits
    rowStatement : String

open CulturalOperatorRow public

mkCandidateOnlyCulturalOperatorRow :
  Nat →
  CulturalSymbolKind →
  InterpretiveLensKind →
  SocietalOperatorStructureKind →
  CulturalOperatorClaimKind →
  CulturalOperatorRoute →
  String →
  CulturalOperatorRow
mkCandidateOnlyCulturalOperatorRow rowId symbolKind lensKind structureKind claimKind routeKind rowStatement =
  culturalOperatorRow
    rowId
    symbolKind
    lensKind
    structureKind
    claimKind
    routeKind
    canonicalCulturalOperatorAuthorityBits
    rowStatement

record CulturalOperatorRowReceipt (row : CulturalOperatorRow) : Set where
  constructor culturalOperatorRowReceipt
  field
    rowClaimAdmissible :
      AdmissibleCulturalOperatorClaim (claimKind row)
    rowRouteAdmissible :
      AdmissibleCulturalOperatorRoute (routeKind row)
    rowAuthorityFailClosed :
      CulturalOperatorAuthorityFailClosed
    rowAuthorityFailClosedIsCanonical :
      rowAuthorityFailClosed ≡ canonicalCulturalOperatorAuthorityFailClosed
    rowStatementSummary :
      String

open CulturalOperatorRowReceipt public

religiousOperatorRow : CulturalOperatorRow
religiousOperatorRow =
  mkCandidateOnlyCulturalOperatorRow
    zero
    religiousSymbolKind
    relationLensKind
    selfOtherRelationStructureKind
    candidateSymbolStructureClaim
    candidateOnlySymbolRoute
    "Religious symbols can reveal operator structure in a society's self/other/relation grammar without becoming doctrine."

religiousOperatorRowReceipt :
  CulturalOperatorRowReceipt religiousOperatorRow
religiousOperatorRowReceipt =
  culturalOperatorRowReceipt
    tt
    tt
    canonicalCulturalOperatorAuthorityFailClosed
    refl
    "Religious-symbol candidate reading"

culturalOperatorRow1 : CulturalOperatorRow
culturalOperatorRow1 =
  mkCandidateOnlyCulturalOperatorRow
    (suc zero)
    culturalSymbolKind
    translationLensKind
    pluralCivicStructureKind
    candidateSymbolStructureClaim
    candidateOnlySymbolRoute
    "Cultural symbols are read as candidate operator surfaces that braid local charts without collapsing them into one culture."

culturalOperatorRow1Receipt :
  CulturalOperatorRowReceipt culturalOperatorRow1
culturalOperatorRow1Receipt =
  culturalOperatorRowReceipt
    tt
    tt
    canonicalCulturalOperatorAuthorityFailClosed
    refl
    "Cultural-symbol candidate reading"

trinityOperatorRow : CulturalOperatorRow
trinityOperatorRow =
  mkCandidateOnlyCulturalOperatorRow
    (suc (suc zero))
    trinitySymbolKind
    dialecticsLensKind
    selfOtherRelationStructureKind
    candidateSymbolStructureClaim
    candidateOnlySymbolRoute
    "Trinity language is read as a candidate self/other/relation operator rather than as theological authority."

trinityOperatorRowReceipt :
  CulturalOperatorRowReceipt trinityOperatorRow
trinityOperatorRowReceipt =
  culturalOperatorRowReceipt
    tt
    tt
    canonicalCulturalOperatorAuthorityFailClosed
    refl
    "Trinity candidate operator reading"

yinYangOperatorRow : CulturalOperatorRow
yinYangOperatorRow =
  mkCandidateOnlyCulturalOperatorRow
    (suc (suc (suc zero)))
    yinYangSymbolKind
    relationLensKind
    polarityThresholdStructureKind
    candidateSymbolStructureClaim
    candidateOnlySymbolRoute
    "Yin/yang language is read as polarity and threshold operator grammar without metaphysical promotion."

yinYangOperatorRowReceipt :
  CulturalOperatorRowReceipt yinYangOperatorRow
yinYangOperatorRowReceipt =
  culturalOperatorRowReceipt
    tt
    tt
    canonicalCulturalOperatorAuthorityFailClosed
    refl
    "Yin-yang candidate operator reading"

dialecticsLensRow : CulturalOperatorRow
dialecticsLensRow =
  mkCandidateOnlyCulturalOperatorRow
    (suc (suc (suc (suc zero))))
    dialecticalDiagramSymbolKind
    dialecticsLensKind
    powerBoundaryStructureKind
    candidateLensOnlyClaim
    candidateOnlySymbolRoute
    "Dialectics is treated as an interpretive lens only, not as formal, legal, political, theological, or social-science authority."

dialecticsLensRowReceipt :
  CulturalOperatorRowReceipt dialecticsLensRow
dialecticsLensRowReceipt =
  culturalOperatorRowReceipt
    tt
    tt
    canonicalCulturalOperatorAuthorityFailClosed
    refl
    "Dialectics lens candidate reading"

hooksLensRow : CulturalOperatorRow
hooksLensRow =
  mkCandidateOnlyCulturalOperatorRow
    (suc (suc (suc (suc (suc zero)))))
    criticalTheorySymbolKind
    hooksLensKind
    pluralCivicStructureKind
    candidateLensOnlyClaim
    candidateOnlySymbolRoute
    "hooks is carried as an interpretive lens only, with no formal, legal, political, theological, or social-science authority."

hooksLensRowReceipt :
  CulturalOperatorRowReceipt hooksLensRow
hooksLensRowReceipt =
  culturalOperatorRowReceipt
    tt
    tt
    canonicalCulturalOperatorAuthorityFailClosed
    refl
    "hooks lens candidate reading"

nietzscheLensRow : CulturalOperatorRow
nietzscheLensRow =
  mkCandidateOnlyCulturalOperatorRow
    (suc (suc (suc (suc (suc (suc zero))))))
    criticalTheorySymbolKind
    nietzscheLensKind
    dominationBoundaryStructureKind
    candidateLensOnlyClaim
    candidateOnlySymbolRoute
    "Nietzsche is carried as an interpretive lens only, not as authority for law, politics, theology, or social science."

nietzscheLensRowReceipt :
  CulturalOperatorRowReceipt nietzscheLensRow
nietzscheLensRowReceipt =
  culturalOperatorRowReceipt
    tt
    tt
    canonicalCulturalOperatorAuthorityFailClosed
    refl
    "Nietzsche lens candidate reading"

zizekLensRow : CulturalOperatorRow
zizekLensRow =
  mkCandidateOnlyCulturalOperatorRow
    (suc (suc (suc (suc (suc (suc (suc zero)))))))
    criticalTheorySymbolKind
    zizekLensKind
    powerBoundaryStructureKind
    candidateLensOnlyClaim
    candidateOnlySymbolRoute
    "Zizek is carried as an interpretive lens only, not as formal, legal, political, theological, or social-science authority."

zizekLensRowReceipt :
  CulturalOperatorRowReceipt zizekLensRow
zizekLensRowReceipt =
  culturalOperatorRowReceipt
    tt
    tt
    canonicalCulturalOperatorAuthorityFailClosed
    refl
    "Zizek lens candidate reading"

foucaultLensRow : CulturalOperatorRow
foucaultLensRow =
  mkCandidateOnlyCulturalOperatorRow
    (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    criticalTheorySymbolKind
    foucaultLensKind
    genealogicalCritiqueStructureKind
    candidateLensOnlyClaim
    candidateOnlySymbolRoute
    "Foucault is carried as an interpretive lens only, with genealogy and power analysis kept descriptive rather than authoritative."

foucaultLensRowReceipt :
  CulturalOperatorRowReceipt foucaultLensRow
foucaultLensRowReceipt =
  culturalOperatorRowReceipt
    tt
    tt
    canonicalCulturalOperatorAuthorityFailClosed
    refl
    "Foucault lens candidate reading"

canonicalCulturalOperatorRows : List CulturalOperatorRow
canonicalCulturalOperatorRows =
  religiousOperatorRow
  ∷ culturalOperatorRow1
  ∷ trinityOperatorRow
  ∷ yinYangOperatorRow
  ∷ dialecticsLensRow
  ∷ hooksLensRow
  ∷ nietzscheLensRow
  ∷ zizekLensRow
  ∷ foucaultLensRow
  ∷ []

canonicalCulturalOperatorRowCount : Nat
canonicalCulturalOperatorRowCount =
  listCount canonicalCulturalOperatorRows

canonicalBlockedCulturalOperatorClaims : List CulturalOperatorClaimKind
canonicalBlockedCulturalOperatorClaims =
  nationalismReadingClaim
  ∷ monocultureCompressionClaim
  ∷ enemyCodingDominationClaim
  ∷ dominationReadingClaim
  ∷ formalAuthorityClaim
  ∷ legalAuthorityClaim
  ∷ politicalAuthorityClaim
  ∷ theologicalAuthorityClaim
  ∷ socialScienceAuthorityClaim
  ∷ []

canonicalBlockedCulturalOperatorClaimCount : Nat
canonicalBlockedCulturalOperatorClaimCount =
  listCount canonicalBlockedCulturalOperatorClaims

record CulturalOperatorBoundaryReceipt : Setω where
  constructor culturalOperatorBoundaryReceipt
  field
    taoOperatorGrammarReceipt :
      TaoGrammar.TaoOperatorGrammarReceipt
    yinYangPolarityBoundaryReceipt :
      YinYang.YinYangPolarityBoundaryReceipt
    qiOperatorTheoryBoundaryReceipt :
      QiTheory.QiOperatorTheoryBoundaryReceipt
    culturalTriadOperatorBoundaryReceipt :
      Triad.CulturalTriadOperatorBoundary
    rows :
      List CulturalOperatorRow
    rowCount :
      Nat
    rowCountMatches :
      rowCount ≡ canonicalCulturalOperatorRowCount
    blockedClaims :
      List CulturalOperatorClaimKind
    blockedClaimCount :
      Nat
    blockedClaimCountMatches :
      blockedClaimCount ≡ canonicalBlockedCulturalOperatorClaimCount
    laws :
      List CulturalOperatorLaw
    lawCount :
      Nat
    lawCountMatches :
      lawCount ≡ canonicalCulturalOperatorLawCount
    authorityBits :
      CulturalOperatorAuthorityBits
    authorityBitsAreCanonical :
      authorityBits ≡ canonicalCulturalOperatorAuthorityBits
    authorityFailClosed :
      CulturalOperatorAuthorityFailClosed
    authorityFailClosedIsCanonical :
      authorityFailClosed ≡ canonicalCulturalOperatorAuthorityFailClosed
    candidateOnly :
      Bool
    candidateOnlyTrue :
      candidateOnly ≡ true
    promoted :
      Bool
    promotedFalse :
      promoted ≡ false
    boundarySummary :
      String

open CulturalOperatorBoundaryReceipt public

canonicalCulturalOperatorBoundaryReceipt :
  CulturalOperatorBoundaryReceipt
canonicalCulturalOperatorBoundaryReceipt =
  culturalOperatorBoundaryReceipt
    TaoGrammar.canonicalTaoOperatorGrammarReceipt
    YinYang.canonicalYinYangPolarityBoundaryReceipt
    QiTheory.canonicalQiOperatorTheoryBoundaryReceipt
    Triad.canonicalCulturalTriadOperatorBoundary
    canonicalCulturalOperatorRows
    canonicalCulturalOperatorRowCount
    refl
    canonicalBlockedCulturalOperatorClaims
    canonicalBlockedCulturalOperatorClaimCount
    refl
    canonicalCulturalOperatorLaws
    canonicalCulturalOperatorLawCount
    refl
    canonicalCulturalOperatorAuthorityBits
    refl
    canonicalCulturalOperatorAuthorityFailClosed
    refl
    true
    refl
    false
    refl
    "Candidate-only cultural symbol/operator boundary: religious and cultural symbols can reveal operator structure in societies, while nationalism, monoculture, enemy-coding, domination, and formal/legal/political/theological/social-science authority remain blocked; dialectics, hooks, Nietzsche, Zizek, and Foucault are interpretive lenses only."
