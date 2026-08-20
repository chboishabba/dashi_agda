module DASHI.Education.EarlyYearsEmpowermentConnectednessSourceRegistry where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE REGISTRY: EARLY-YEARS EMPOWERMENT + CONNECTEDNESS
--
-- Bibliographic/public-policy metadata establishes provenance and interpretive
-- calibration only. It does not promote any policy wording, qualitative
-- interpretation or named author into theorem authority for a particular
-- family, child, service or community.
------------------------------------------------------------------------

record EmpowermentConnectednessReference : Set where
  constructor empowermentConnectednessReference
  field
    key : String
    title : String
    authors : List String
    year : Nat
    venue : String
    doi : String
    canonicalURL : String
    sourceRole : String
    authorityBoundary : String
    metadataVerified : Bool
    metadataVerifiedIsTrue : metadataVerified ≡ true

open EmpowermentConnectednessReference public

earlyYearsStrategy2024 : EmpowermentConnectednessReference
earlyYearsStrategy2024 =
  empowermentConnectednessReference
    "australian-early-years-strategy-2024-2034"
    "Early Years Strategy 2024-2034"
    ("Australian Government Department of Social Services" ∷ [])
    2024
    "Australian Government national strategy, published 7 May 2024"
    "no-doi-assigned"
    "https://www.dss.gov.au/early-years-strategy/resource/early-years-strategy-2024-2034"
    "Source for the policy vision that children thrive with empowered and connected families supported by strong communities; explicitly records child-and-family-centred, strengths-based and community-respecting principles."
    "Strategy language does not itself establish that a particular practice empowers a particular family, nor that professional interpretation substitutes for family, child or community evidence."
    true refl

qualityArea6 : EmpowermentConnectednessReference
qualityArea6 =
  empowermentConnectednessReference
    "acecqa-quality-area-6"
    "Quality Area 6: Collaborative partnerships with families and communities"
    ("Australian Children's Education and Care Quality Authority" ∷ [])
    2026
    "Guide to the National Quality Framework / National Quality Standard"
    "no-doi-assigned"
    "https://www.acecqa.gov.au/national-quality-framework/guide-nqf/section-3-national-quality-standard-and-assessment-and-rating/quality-area-6-collaborative-partnerships-families-and-communities"
    "Source for the current regulatory-quality surface around supportive family relationships, shared decision-making, access, participation and community engagement."
    "Quality Area 6 already contains reciprocal, respectful and family-expertise language; it must not be caricatured as purely transactional, and regulatory wording does not prove a downstream empowerment effect."
    true refl

brownKimber2026 : EmpowermentConnectednessReference
brownKimber2026 =
  empowermentConnectednessReference
    "brown-kimber-student-voice-agency-2026"
    "Repositioning Student Voice and Agency: A Call for the Epistemic Expansion of Scholarship of Teaching and Learning Inquiry"
    ("Alice Brown" ∷ "Megan Kimber" ∷ [])
    2026
    "Active Learning in Higher Education"
    "10.1177/14697874261426374"
    "https://doi.org/10.1177/14697874261426374"
    "Alice-linked source for preserving voice and agency as epistemic coordinates rather than treating institutional observation as the whole learner/family system."
    "Higher-education SoTL results are conceptual/provenance calibration here; they do not establish empirical findings for the rural early-childhood pilot."
    true refl

canonicalEmpowermentConnectednessSources : List EmpowermentConnectednessReference
canonicalEmpowermentConnectednessSources =
  earlyYearsStrategy2024
  ∷ qualityArea6
  ∷ brownKimber2026
  ∷ []
