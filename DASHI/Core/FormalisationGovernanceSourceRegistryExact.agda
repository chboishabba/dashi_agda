module DASHI.Core.FormalisationGovernanceSourceRegistryExact where

------------------------------------------------------------------------
-- SOURCE REGISTRY: AFFORDANCE / CAPABILITY / FORMALISATION GOVERNANCE
--
-- DOI is recorded where established; otherwise ISBN/stable bibliographic
-- identifiers are retained and no DOI is invented. Every row has a bounded
-- role; none is proof authority for DASHI's finite constructions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record SourceReference : Set where
  constructor source-reference
  field
    author : String
    title : String
    venueOrPublisher : String
    identifier : String
    boundedRole : String

open SourceReference public

gibsonAffordance : SourceReference
gibsonAffordance = source-reference
  "James J. Gibson"
  "The Ecological Approach to Visual Perception"
  "Houghton Mifflin, 1979; later classic editions"
  "ISBN 9781848725782 (2015 classic edition); no DOI asserted"
  "organism-environment relational affordance provenance; no attribution of DASHI factorisation algebra"

senCapability : SourceReference
senCapability = source-reference
  "Amartya Sen"
  "Commodities and Capabilities"
  "North-Holland, 1985"
  "ISBN 9780444877307; no DOI asserted"
  "capability/functioning distinction; finite option-cone countermodels are DASHI constructions"

fraserParticipation : SourceReference
fraserParticipation = source-reference
  "Nancy Fraser"
  "Redistribution or Recognition? / Scales of Justice"
  "Verso 2003; Columbia University Press 2009"
  "ISBN 9781859844922; ISBN 9780231146807"
  "redistribution/recognition/representation separation; no scalar justice equation inferred"

beethamLegitimacy : SourceReference
beethamLegitimacy = source-reference
  "David Beetham"
  "The Legitimation of Power"
  "Macmillan 1991; Palgrave Macmillan 2nd ed. 2013"
  "ISBN 9780230279337; no DOI asserted"
  "rule-conformity, justificatory belief and consent as distinct legitimacy evidence dimensions"

plumwoodMastery : SourceReference
plumwoodMastery = source-reference
  "Val Plumwood"
  "Feminism and the Mastery of Nature"
  "Routledge, 1993"
  "ISBN 9780415068109; no DOI asserted"
  "backgrounding/hyperseparation/incorporation/instrumentalism/homogenisation operation family"

mccallComplexity : SourceReference
mccallComplexity = source-reference
  "Leslie McCall"
  "The Complexity of Intersectionality"
  "Signs 30(3):1771-1800, 2005"
  "DOI 10.1086/426800"
  "anti/intra/intercategorical methodological strategy separation"

butlerGenderTrouble : SourceReference
butlerGenderTrouble = source-reference
  "Judith Butler"
  "Gender Trouble: Feminism and the Subversion of Identity"
  "Routledge, 1990"
  "ISBN 9780415389556 (2006 edition); no DOI asserted"
  "performative/iterative genesis provenance; present-category/history theorem is DASHI"

collinsBlackFeministThought : SourceReference
collinsBlackFeministThought = source-reference
  "Patricia Hill Collins"
  "Black Feminist Thought: Knowledge, Consciousness, and the Politics of Empowerment"
  "Routledge, 2nd ed. 2000"
  "ISBN 9780415924849; no DOI asserted"
  "interlocking domination and standpoint/knowledge-position provenance; no rectangle theorem attribution"

merchantDeathNature : SourceReference
merchantDeathNature = source-reference
  "Carolyn Merchant"
  "The Death of Nature: Women, Ecology, and the Scientific Revolution"
  "Harper & Row, 1980"
  "ISBN 9780062505958; no DOI asserted"
  "historical critique of mechanistic/decompositional worldview; not source of endpoint-additive algebra"

harawaySituated : SourceReference
harawaySituated = source-reference
  "Donna Haraway"
  "Situated Knowledges: The Science Question in Feminism and the Privilege of Partial Perspective"
  "Feminist Studies 14(3):575-599, 1988"
  "DOI/JSTOR stable 10.2307/3178066"
  "situated/partial knowledge provenance; domain-uncommitted formalism is not promoted to view-from-nowhere"

harawayTrouble : SourceReference
harawayTrouble = source-reference
  "Donna J. Haraway"
  "Staying with the Trouble: Making Kin in the Chthulucene"
  "Duke University Press, 2016"
  "ISBN 9780822362241; no DOI asserted for book"
  "sympoiesis/making-with conceptual provenance only; no nonseparability algebra attribution"

frickerEpistemicInjustice : SourceReference
frickerEpistemicInjustice = source-reference
  "Miranda Fricker"
  "Epistemic Injustice: Power and the Ethics of Knowing"
  "Oxford University Press, 2007"
  "DOI 10.1093/acprof:oso/9780198237907.001.0001"
  "testimonial/hermeneutical injustice calibration for proof-authority and vocabulary-provenance boundaries"

sokalBricmont : SourceReference
sokalBricmont = source-reference
  "Alan Sokal and Jean Bricmont"
  "Fashionable Nonsense: Postmodern Intellectuals' Abuse of Science"
  "Picador, 1998"
  "ISBN 9780312204075; no DOI asserted"
  "critical motivation for anti-promotion lint; not theorem authority over source traditions"

lordeMastersTools : SourceReference
lordeMastersTools = source-reference
  "Audre Lorde"
  "The Master's Tools Will Never Dismantle the Master's House"
  "1979 remarks; collected in Sister Outsider"
  "ISBN 9781580911863 (2007 edition); no DOI asserted"
  "methodological-tension provenance; formal compatibility is not presumed"

adornoNegativeDialectics : SourceReference
adornoNegativeDialectics = source-reference
  "Theodor W. Adorno"
  "Negative Dialectics"
  "Suhrkamp 1966; English trans. Continuum 1973"
  "ISBN 9780826401328; no DOI asserted"
  "non-identity/anti-totalisation calibration for kernel-closure versus semantic-closure boundary"

lugonesPurityVerified : SourceReference
lugonesPurityVerified = source-reference
  "Maria Lugones"
  "Purity, Impurity, and Separation"
  "Signs 19(2):458-479, Winter 1994"
  "DOI 10.1086/494893; JSTOR stable 3174808"
  "verified purity/impurity provenance; DASHI anti-factorisation remains separately owned"

record RegistryBoundary : Set where
  constructor registry-boundary
  field
    sourceCitationIsProofAuthority : Bool
    sourceCitationIsProofAuthorityIsFalse : sourceCitationIsProofAuthority ≡ false
    missingDOIIsReplacedByInventedDOI : Bool
    missingDOIIsReplacedByInventedDOIIsFalse : missingDOIIsReplacedByInventedDOI ≡ false
    conceptualProvenanceEqualsMathematicalAttribution : Bool
    conceptualProvenanceEqualsMathematicalAttributionIsFalse :
      conceptualProvenanceEqualsMathematicalAttribution ≡ false

canonicalRegistryBoundary : RegistryBoundary
canonicalRegistryBoundary = registry-boundary false refl false refl false refl
