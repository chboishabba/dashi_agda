module DASHI.Biology.NeurodivergentSocialEcologySourceRegistryExact where

------------------------------------------------------------------------
-- SOURCE REGISTRY: NEURODIVERGENT PROCESSING, FRIENDSHIP, QUEERING,
-- BUILT ENVIRONMENT, HOMELESSNESS, AND SOCIAL ECOLOGY
--
-- Every source has a bounded role.  Empirical, theoretical, qualitative,
-- policy, and user-supplied conceptual material are kept distinct.  A citation
-- in this registry never promotes a source into a universal biological law.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record SourceReference : Set where
  constructor sourceReference
  field
    authorsOrInstitution : String
    title : String
    venue : String
    year : Nat
    doiOrIdentifier : String
    sourceClass : String
    boundedRole : String

open SourceReference public

processingHierarchy2025 : SourceReference
processingHierarchy2025 = sourceReference
  "Meng-Chuan Lai et al."
  "Autism-related shifts in the brain's information processing hierarchy"
  "Trends in Cognitive Sciences 29(10):942-955"
  2025
  "10.1016/j.tics.2025.04.008"
  "peer-reviewed review/theory"
  "motivates sensory-to-transmodal hierarchy and multilevel processing allocation; not a universal autistic transition law"

hyperfocus2025 : SourceReference
hyperfocus2025 = sourceReference
  "Patrick Dwyer; Andre Sillas; Clifford D. Saron; Susan M. Rivera"
  "Investigating autistic hyperfocus and monotropism: Limited convergence of event-related potentials, laboratory tasks, and questionnaire responses"
  "Research in Autism 127:202683"
  2025
  "10.1016/j.reia.2025.202683"
  "peer-reviewed empirical study"
  "supports representing depth/persistence or hyperfocus as measurement-dependent candidate axes, not universal traits"

systemizing2009 : SourceReference
systemizing2009 = sourceReference
  "Simon Baron-Cohen; Emma Ashwin; Chris Ashwin; Teresa Tavassoli; Bhismadev Chakrabarti"
  "Talent in autism: hyper-systemizing, hyper-attention to detail and sensory hypersensitivity"
  "Philosophical Transactions of the Royal Society B 364(1522):1377-1383"
  2009
  "10.1098/rstb.2008.0337"
  "peer-reviewed historical theory/review"
  "motivates explicit rule-search/systemizing as one candidate axis; not an essence of autism"

statisticalLearning2026 : SourceReference
statisticalLearning2026 = sourceReference
  "Rebecca R. Bell; Hannah R. Thomas; Jenny R. Saffran; Inge-Marie Eigsti"
  "A systematic review of statistical learning in autism spectrum disorder"
  "Molecular Autism 17:2"
  2026
  "10.1186/s13229-025-00697-7"
  "peer-reviewed systematic review"
  "bounds claims about learning-rate deficits; behavioral differences are limited/mixed and task conditions matter"

autismADHD2024 : SourceReference
autismADHD2024 = sourceReference
  "Michael J. Kofler et al."
  "Executive function deficits in attention-deficit/hyperactivity disorder and autism spectrum disorder"
  "Nature Reviews Psychology 3:701-719"
  2024
  "10.1038/s44159-024-00350-9"
  "peer-reviewed review"
  "motivates separating autism, ADHD, co-occurrence, task constructs, and heterogeneity rather than assuming diagnostic additivity"

audhd2026 : SourceReference
audhd2026 = sourceReference
  "Ting Wang; Min Bai; Zhe Zhang; Feiyong Jia"
  "The unique cognitive phenotype of ASD + ADHD co-occurrence: evidence for planning and attention deficits as a differentiating approach"
  "Frontiers in Pediatrics 13:1703264"
  2026
  "10.3389/fped.2025.1703264"
  "peer-reviewed empirical study"
  "supports treating autism+ADHD co-occurrence as an empirical coordinate whose combined pattern should not be assumed additive"

sensoryMeta2024 : SourceReference
sensoryMeta2024 = sourceReference
  "Yixin Chen; Zhenyang Xi; Rob Saunders; David Simmons; Vasiliki Totsika; Will Mandy"
  "A systematic review and meta-analysis of the relationship between sensory processing differences and internalising/externalising problems in autism"
  "Clinical Psychology Review 114:102516"
  2024
  "10.1016/j.cpr.2024.102516"
  "peer-reviewed systematic review/meta-analysis"
  "motivates multidimensional sensory weighting and context-dependent load; does not identify one scalar sensory deficit"

interoception2025 : SourceReference
interoception2025 = sourceReference
  "Marlene Klein; Michael Witthoeft; Stefanie Maria Jungmann"
  "Interoception in individuals with autism spectrum disorder: a systematic literature review and meta-analysis"
  "Frontiers in Psychiatry 16:1573263"
  2025
  "10.3389/fpsyt.2025.1573263"
  "peer-reviewed systematic review/meta-analysis"
  "motivates keeping interoception separate from exteroceptive sensory weighting because findings are mixed"

builtEnvironment2026 : SourceReference
builtEnvironment2026 = sourceReference
  "Zhihao Wang; Siti Sarah Herman; Noranita Mansor; Shuaijie Yan"
  "Sensory stimuli in the built environment for autistic people: A scoping review"
  "Building and Environment 292:114271"
  2026
  "10.1016/j.buildenv.2026.114271"
  "peer-reviewed scoping review"
  "supports safety, sensory balance, adjustability, predictability, controllability and recovery as built-environment design qualities"

publicLandscape2026 : SourceReference
publicLandscape2026 = sourceReference
  "multi-author public landscape study"
  "Autism-friendly public landscape architecture"
  "Urban Forestry & Urban Greening 115:129181"
  2026
  "10.1016/j.ufug.2025.129181"
  "peer-reviewed review/case-study article"
  "motivates treating ordinary public landscape access as an ecological affordance question rather than limiting accessibility to dedicated clinical spaces"

friendship2024 : SourceReference
friendship2024 = sourceReference
  "Karri Gillespie-Smith; Ally Pax Arcari Mair; Aljawharah Alabtullatif; Helen Pain; Doug McConachie"
  "A Spectrum of Understanding: A Qualitative Exploration of Autistic Adults' Understandings and Perceptions of Friendship(s)"
  "Autism in Adulthood 6(4)"
  2024
  "10.1089/aut.2023.0051"
  "peer-reviewed qualitative study"
  "supports positive friendship constructs including identity with others, shared value and shared presence"

friendshipTrust2025 : SourceReference
friendshipTrust2025 = sourceReference
  "Jad Brake"
  "Understanding Friendship Among Autistic Adults: Insights From Narratives of Everyday and Social Life"
  "Sociological Forum"
  2025
  "10.1111/socf.70005"
  "peer-reviewed qualitative sociological study"
  "supports comfort, acceptance and trust as central friendship values embedded in physical-social environments and lived experience"

supportTranslation2024 : SourceReference
supportTranslation2024 = sourceReference
  "Yunhe Huang; Samuel R. C. Arnold; Kitty-Rose Foley; Julian N. Trollor"
  "A Qualitative Study of Adults' and Support Persons' Experiences of Support After Autism Diagnosis"
  "Journal of Autism and Developmental Disorders 54:1157-1170"
  2024
  "10.1007/s10803-022-05828-0"
  "peer-reviewed qualitative study"
  "documents informal supporters helping autistic adults contextualise social situations in real time and autistic peer support fostering belonging/self-acceptance; does not imply supporters replace agency"

ndFriendship2025 : SourceReference
ndFriendship2025 = sourceReference
  "Samara M. Wolpe; Ingrid S. Tien; Maxwell N. Lee; Sila Sozeri; Iman M. Humphrey"
  "Neurodivergent people just get each other: Navigating friendship and community in the transition to adulthood for autistic adults"
  "Research in Autism 128:202692"
  2025
  "10.1016/j.reia.2025.202692"
  "peer-reviewed qualitative study"
  "supports neurodivergent community, unmasking/vulnerability and sensory context as parts of friendship ecology"

doubleEmpathy2012 : SourceReference
doubleEmpathy2012 = sourceReference
  "Damian E. M. Milton"
  "On the ontological status of autism: the double empathy problem"
  "Disability & Society 27(6):883-887"
  2012
  "10.1080/09687599.2012.710008"
  "peer-reviewed theoretical article"
  "motivates reciprocal/relational accounts of communicative mismatch rather than locating every mismatch inside one participant"

neuroqueer2021 : SourceReference
neuroqueer2021 = sourceReference
  "Nick Walker; Dora M. Raymaker"
  "Toward a Neuroqueer Future: An Interview with Nick Walker"
  "Autism in Adulthood 3(1):5-10"
  2021
  "10.1089/aut.2020.29014.njw"
  "peer-reviewed interview/theoretical source"
  "provides citable neuroqueer/neurodiversity framing; used as theory/praxis rather than empirical prevalence evidence"

yergeau2018 : SourceReference
yergeau2018 = sourceReference
  "M. Remi Yergeau"
  "Authoring Autism: On Rhetoric and Neurological Queerness"
  "Duke University Press"
  2018
  "ISBN 9780822372182"
  "scholarly monograph / queer-disability theory"
  "motivates neurological queerness and critiques compulsory neuronormative rhetorical assumptions"

neuroqueerIntimacy2026 : SourceReference
neuroqueerIntimacy2026 = sourceReference
  "Monique Huysamen; Chris Hatton; Marianthi Kourti"
  "Embrace Difference, Challenge Normativity: Towards a Neuroqueer-informed Ethic for Supporting Autistic Adults' Intimate Lives"
  "Feminism & Psychology"
  2026
  "10.1177/09593535261422510"
  "peer-reviewed qualitative/neuroqueer study"
  "directly motivates neuroqueering as resistance to entwined neuronormative and heteronormative relationship scripts, including non-escalator and otherwise nonnormative intimate practices"

genderDiversity2025 : SourceReference
genderDiversity2025 = sourceReference
  "Guilhem Bonazzi et al."
  "Gender on the Spectrum: Prevalence of Gender Diversity in Autism Spectrum Disorder - A Systematic Review and Meta-Analysis"
  "Autism in Adulthood"
  2025
  "10.1089/aut.2024.0202"
  "peer-reviewed systematic review/meta-analysis"
  "supports an elevated and heterogeneous prevalence of gender diversity in autistic samples; definitions and ascertainment remain important"

hostileDesign2024 : SourceReference
hostileDesign2024 = sourceReference
  "Michael Kauff; Lena Laemmle; Esther Kroll; Larissa Gehring; Roman Soucek; Frank Asbrock"
  "Should the city be for everyone? The relationship between worldviews, ideological attitudes, and the approval of hostile design"
  "Journal of Community & Applied Social Psychology 34(4):e2867"
  2024
  "10.1002/casp.2867"
  "peer-reviewed correlational political-psychology study"
  "supports association of hostile-design approval with RWA, SDO and dangerous/competitive worldviews; does not establish that every conservative endorses hostile design"

supportiveHousing2023 : SourceReference
supportiveHousing2023 = sourceReference
  "Joseph A. Wagoner"
  "Ideological orientations, intergroup stereotypes, and opposition to permanent supportive housing"
  "Analyses of Social Issues and Public Policy 23(2):282-307"
  2023
  "10.1111/asap.12346"
  "peer-reviewed correlational political-psychology study"
  "supports an ideological/stereotype pathway to opposition to supportive housing, especially via social-dominance orientation; not a universal partisan law"

crenshaw1991 : SourceReference
crenshaw1991 = sourceReference
  "Kimberle Crenshaw"
  "Mapping the Margins: Intersectionality, Identity Politics, and Violence against Women of Color"
  "Stanford Law Review 43(6):1241-1299"
  1991
  "10.2307/1229039"
  "legal/critical theory"
  "grounds intersectionality as structural and relational; statistical interaction alone is not treated as the definition of intersectionality"

oldenburg1989 : SourceReference
oldenburg1989 = sourceReference
  "Ray Oldenburg"
  "The Great Good Place"
  "Paragon House"
  1989
  "book; no DOI asserted"
  "urban sociology / third-place theory"
  "conceptual origin for third places outside home and work; neurodivergent accessibility extensions are DASHI synthesis, not Oldenburg's theorem"

bronfenbrenner1979 : SourceReference
bronfenbrenner1979 = sourceReference
  "Urie Bronfenbrenner"
  "The Ecology of Human Development"
  "Harvard University Press"
  1979
  "ISBN 9780674224575"
  "developmental/social-ecological theory"
  "motivates nested person-environment systems; DASHI affordance cones are a separate mathematical translation"

record SolisConceptProvenance : Set where
  constructor solisConceptProvenance
  field
    label : String
    provenanceClass : String
    suppliedDescription : String
    academicValidationInstalled : Bool
    empiricalAutismLawInstalled : Bool

open SolisConceptProvenance public

solisConversationConcept : SolisConceptProvenance
solisConversationConcept = solisConceptProvenance
  "Solis communicator / system-sensitivity / psybernetic-dissonance concept bundle"
  "user-supplied prior-discussion conceptual material"
  "Autistic Signal[x] as a candidate systemic-integrity check; thresholded system-risk flag; sacred-data/syntax-checker metaphor; optional 3-6-9 and phase-shifted-Nash analogies"
  false
  false

record RegistryBoundary : Set where
  constructor registryBoundary
  field
    empiricalAndTheoreticalRolesSeparated : Bool
    qualitativeFriendshipEvidenceInstalled : Bool
    neuroqueerSourcesInstalled : Bool
    builtEnvironmentSourcesInstalled : Bool
    politicalHostileDesignSourcesInstalled : Bool
    intersectionalSourceInstalled : Bool
    solisUserConceptSeparatedFromAcademicEvidence : Bool

canonicalRegistryBoundary : RegistryBoundary
canonicalRegistryBoundary =
  registryBoundary true true true true true true true
