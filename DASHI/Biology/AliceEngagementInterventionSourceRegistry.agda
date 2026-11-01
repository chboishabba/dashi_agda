module DASHI.Biology.AliceEngagementInterventionSourceRegistry where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-bound bibliography for the OEF / redesign / nudge lane.
-- Metadata is retained as provenance only and confers no theorem authority.
------------------------------------------------------------------------

record EngagementReference : Set where
  constructor engagementReference
  field
    key : String
    title : String
    authors : List String
    doi : String
    venue : String
    year : Nat
    sourceRole : String
    boundary : String
    metadataVerified : Bool
    metadataVerifiedIsTrue : metadataVerified ≡ true

open EngagementReference public

oef2018Authors : List String
oef2018Authors =
  "Petrea Redmond" ∷ "Amanda Heffernan" ∷ "Lindy Abawi" ∷
  "Alice Brown" ∷ "Robyn Henderson" ∷ []

oef2018 : EngagementReference
oef2018 =
  engagementReference
    "oef-2018"
    "An Online Engagement Framework for Higher Education"
    oef2018Authors
    "10.24059/olj.v22i1.1175"
    "Online Learning 22(1), 183-204"
    2018
    "Founding five-dimension OEF: social, cognitive, behavioural, collaborative and emotional engagement; indicators are presented as illustrative rather than exhaustive."
    "The framework is a conceptual/research/practice lens, not an exhaustive world carrier and not a proof that omitted distinctions have positive measured residual mass."
    true refl

conceptual2022Authors : List String
conceptual2022Authors =
  "Alice Brown" ∷ "Jill Lawrence" ∷ "Marita Basson" ∷ "Petrea Redmond" ∷ []

conceptual2022 : EngagementReference
conceptual2022 =
  engagementReference
    "online-engagement-conceptual-framework-2022"
    "A conceptual framework to enhance student online learning and engagement in higher education"
    conceptual2022Authors
    "10.1080/07294360.2020.1860912"
    "Higher Education Research & Development 41(2), 284-299"
    2022
    "Develops a proactive online-engagement framework using course learning analytics, expectation management, communication and nudging strategies."
    "The framework motivates an intervention-policy instance; it does not establish that every coarse engagement state is dynamically or policy-safe."
    true refl

criticalReflection2022Authors : List String
criticalReflection2022Authors =
  "Petrea Redmond" ∷ "Stephanie M. Foote" ∷ "Alice Brown" ∷
  "Deborah Mixson-Brookshire" ∷ "Lindy-Anne Abawi" ∷ "Robyn Henderson" ∷ []

criticalReflection2022 : EngagementReference
criticalReflection2022 =
  engagementReference
    "oef-critical-reflection-2022"
    "Adopting a framework to support the process of critical reflection and understanding of online engagement"
    criticalReflection2022Authors
    "10.1007/s12528-021-09281-3"
    "Journal of Computing in Higher Education 34, 109-131"
    2022
    "Uses an online-engagement framework as a practitioner reflection surface for understanding and redesigning online engagement."
    "Reflection through a framework remains observer-indexed; successful reflection does not identify the framework with the full situated learner state."
    true refl

nudge2023Authors : List String
nudge2023Authors =
  "Alice Brown" ∷ "Jill Lawrence" ∷ "Marita Basson" ∷ "Megan Axelsen" ∷
  "Petrea Redmond" ∷ "Joanna Turner" ∷ "Suzanne Maloney" ∷ "Linda Galligan" ∷ []

nudge2023 : EngagementReference
nudge2023 =
  engagementReference
    "nudge-protocol-2023"
    "The creation of a nudging protocol to support online student engagement in higher education"
    nudge2023Authors
    "10.1177/14697874211039077"
    "Active Learning in Higher Education 24(3), 257-271"
    2023
    "Combines learning analytics and nudge theory into a protocol concerned with who, when and how to nudge."
    "A nudge protocol supplies an empirical quotient-to-policy loop; the DASHI PolicyRelativeSafety theorem is a separate formal obligation."
    true refl

design2025Authors : List String
design2025Authors =
  "Melissa Fanshawe" ∷ "Alice Brown" ∷ "Petrea Redmond" ∷ []

design2025 : EngagementReference
design2025 =
  engagementReference
    "oef-design-experiment-2025"
    "Using an online engagement framework to redesign the learning environment for higher education students: A design experiment approach"
    design2025Authors
    "10.24059/olj.v29i2.4447"
    "Online Learning 29(2)"
    2025
    "Audits and redesigns two online Initial Teacher Education courses using the five OEF dimensions, then evaluates 24 offerings using feedback and analytics."
    "Different measurement fibres (qualitative references, LMS participation, satisfaction, attrition) must not be silently promoted to one universal pedagogical-value measure."
    true refl

che2019Authors : List String
che2019Authors = "Alice Brown" ∷ "Patrick A. Danaher" ∷ []

che2019 : EngagementReference
che2019 =
  engagementReference
    "che-principles-2019"
    "CHE Principles: facilitating authentic and dialogical semi-structured interviews in educational research"
    che2019Authors
    "10.1080/1743727X.2017.1379987"
    "International Journal of Research & Method in Education 42(1), 76-90"
    2019
    "Develops Connectivity, Humanness and Empathy as ethical/methodological principles for authentic dialogical interviewing."
    "CHE motivates relational and non-flattening inquiry practice; it does not by itself prove the DASHI reopening, quotient-safety or governance constructions."
    true refl

canonicalEngagementReferences : List EngagementReference
canonicalEngagementReferences =
  oef2018 ∷ conceptual2022 ∷ criticalReflection2022 ∷
  nudge2023 ∷ design2025 ∷ che2019 ∷ []
