module DASHI.Core.CriticalRelationalGrammarSourceRegistryExact where

------------------------------------------------------------------------
-- SOURCE REGISTRY: RELATIONAL GRAMMAR / THIRDNESS / HIERARCHY
--
-- Every row has a bounded source role.  Historical/theoretical provenance is
-- not proof authority for DASHI's finite theorem constructions.  DOI is used
-- where verified; otherwise a stable book ISBN is retained and no DOI is
-- invented.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record SourceReference : Set where
  constructor source-reference
  field
    authorsOrInstitution : String
    title : String
    venueOrPublisher : String
    year : Nat
    doiOrIdentifier : String
    sourceClass : String
    boundedRole : String

open SourceReference public

beauvoirSecondSex : SourceReference
beauvoirSecondSex = source-reference
  "Simone de Beauvoir; English trans. Constance Borde and Sheila Malovany-Chevallier"
  "The Second Sex"
  "Vintage"
  2011
  "ISBN 9780307277787; original French work 1949"
  "feminist/existentialist monograph"
  "source context for asymmetric Subject/Other constitution; DASHI dependency graph is a bounded formal reconstruction"

lacanIdentification : SourceReference
lacanIdentification = source-reference
  "Jacques Lacan"
  "Seminar IX: L'identification"
  "seminar, 1961-1962"
  1961
  "no DOI asserted"
  "psychoanalytic seminar"
  "source context for zero/one, unary-trait and Frege-derived identification/count material; not a DASHI ternary theorem"

lacanDiscourse : SourceReference
lacanDiscourse = source-reference
  "Jacques Lacan"
  "Seminar XVII: L'envers de la psychanalyse"
  "seminar, 1969-1970"
  1969
  "no DOI asserted"
  "psychoanalytic seminar"
  "source context for S1/S2 discourse roles; kept distinct from Frege-genesis numeral two"

lacanOuPire : SourceReference
lacanOuPire = source-reference
  "Jacques Lacan"
  "Seminar XIX: ...ou pire"
  "seminar, 1971-1972"
  1971
  "no DOI asserted"
  "psychoanalytic seminar"
  "later source context for the One/count material; not identified with formulas of sexuation"

irigarayThisSex : SourceReference
irigarayThisSex = source-reference
  "Luce Irigaray; trans. Catherine Porter with Carolyn Burke"
  "This Sex Which Is Not One"
  "Cornell University Press"
  1985
  "ISBN 9780801493317"
  "feminist/psychoanalytic monograph"
  "source context for phallocentric critique, two-lips reciprocal morphology and neither-one-nor-two wording; no universal biological ontology inferred"

scottEqualityDifference : SourceReference
scottEqualityDifference = source-reference
  "Joan W. Scott"
  "Deconstructing Equality-versus-Difference: Or, the Uses of Poststructuralist Theory for Feminism"
  "Feminist Studies 14(1):32-50"
  1988
  "10.2307/3177997"
  "peer-reviewed feminist theory"
  "source context for separating equality from sameness/difference; DASHI observational/standing mathematics is original formal extension"

crenshawMargins : SourceReference
crenshawMargins = source-reference
  "Kimberle Crenshaw"
  "Mapping the Margins: Intersectionality, Identity Politics, and Violence against Women of Color"
  "Stanford Law Review 43(6):1241-1299"
  1991
  "10.2307/1229039"
  "legal/critical theory"
  "source context for structural intersectionality and anti-single-axis analysis; rectangle algebra is not attributed to Crenshaw"

anzalduaBorderlands : SourceReference
anzalduaBorderlands = source-reference
  "Gloria Anzaldua"
  "Borderlands / La Frontera: The New Mestiza"
  "Aunt Lute Books"
  1987
  "ISBN 9781879960138"
  "Chicana feminist/queer theoretical-literary monograph"
  "source context for mestiza consciousness, borderlands and pluralistic contradiction-holding; DASHI ternary address is an interpretive device"

lugonesPurity : SourceReference
lugonesPurity = source-reference
  "Maria Lugones"
  "Purity, Impurity, and Separation"
  "Signs 19(2)"
  1994
  "10.1086/494893"
  "peer-reviewed feminist philosophy"
  "source context for purity/impurity and multiplicity; used to motivate anti-pure-factorisation, not an attribution of DASHI rectangle algebra"

bhabhaLocation : SourceReference
bhabhaLocation = source-reference
  "Homi K. Bhabha"
  "The Location of Culture"
  "Routledge"
  1994
  "ISBN 9780415016353"
  "postcolonial theory monograph"
  "source context for hybridity, interstice and Third Space; DASHI generative-direction graph is a bounded interpretation"

badiouBeingEvent : SourceReference
badiouBeingEvent = source-reference
  "Alain Badiou; trans. Oliver Feltham"
  "Being and Event"
  "Continuum"
  2005
  "ISBN 9780826458315"
  "philosophy/set-theoretic ontology monograph"
  "source context for void and count-as-one as operation; kept separate from Lacanian zero and Irigarayan classification refusal"

bookchinEcologyFreedom : SourceReference
bookchinEcologyFreedom = source-reference
  "Murray Bookchin"
  "The Ecology of Freedom: The Emergence and Dissolution of Hierarchy"
  "AK Press edition"
  2005
  "ISBN 9781904859260; original work 1982"
  "social ecology monograph"
  "source context for hierarchy/domination as social-ecological relations; no natural or numeric rank is inferred from DASHI carriers"

kingHealingWounds : SourceReference
kingHealingWounds = source-reference
  "Ynestra King"
  "Healing the Wounds: Feminism, Ecology, and the Nature/Culture Dualism"
  "in Gender/Body/Knowledge, eds. Alison M. Jaggar and Susan Bordo, Rutgers University Press"
  1989
  "ISBN 9780813513799; no chapter DOI asserted"
  "ecofeminist theory chapter"
  "source context for ecofeminist critique of hierarchy/nature-culture dualism; no deterministic political ranking theorem inferred"

record RegistryBoundary : Set where
  constructor registry-boundary
  field
    sourceRoleSeparatedFromFormalTheorem : Bool
    sourceRoleSeparatedFromFormalTheoremIsTrue :
      sourceRoleSeparatedFromFormalTheorem ≡ true
    missingDOIReplacedByInventedDOI : Bool
    missingDOIReplacedByInventedDOIIsFalse :
      missingDOIReplacedByInventedDOI ≡ false
    sameKeywordImpliesSameHistoricalGrammar : Bool
    sameKeywordImpliesSameHistoricalGrammarIsFalse :
      sameKeywordImpliesSameHistoricalGrammar ≡ false
    criticalTheorySourceProvesEmpiricalPopulationLaw : Bool
    criticalTheorySourceProvesEmpiricalPopulationLawIsFalse :
      criticalTheorySourceProvesEmpiricalPopulationLaw ≡ false

canonicalRegistryBoundary : RegistryBoundary
canonicalRegistryBoundary =
  registry-boundary true refl false refl false refl false refl
