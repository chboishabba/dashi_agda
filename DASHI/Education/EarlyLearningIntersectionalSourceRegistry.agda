module DASHI.Education.EarlyLearningIntersectionalSourceRegistry where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-bound registry for the intersectional / political-economy extension
-- of the early-learning choice formalisation.
--
-- Metadata establishes provenance only.  No empirical source below is promoted
-- into theorem authority for a particular Australian policy proposal.
------------------------------------------------------------------------

record EarlyLearningReference : Set where
  constructor earlyLearningReference
  field
    key : String
    title : String
    authors : List String
    year : Nat
    venue : String
    doi : String
    sourceRole : String
    authorityBoundary : String
    metadataVerified : Bool
    metadataVerifiedIsTrue : metadataVerified ≡ true

open EarlyLearningReference public

heathBrown2021 : EarlyLearningReference
heathBrown2021 =
  earlyLearningReference
    "brown-homeschooling-right-2021"
    "Homeschooling the Right: How Conservative Education Activism Erodes the State"
    ("Heath Brown" ∷ [])
    2021
    "Columbia University Press"
    "10.7312/brow18880"
    "Documents conservative homeschooling as a distinct political-organisational formation and develops a parallel-politics/state-substitution account."
    "Does not imply that every homeschooling family is conservative, religious, anti-state, anti-gender or politically coordinated."
    true refl

tomazini2026 : EarlyLearningReference
tomazini2026 =
  earlyLearningReference
    "tomazini-sacred-families-dangerous-schools-2026"
    "Sacred Families, Dangerous Schools: Transnational Homeschooling Advocacy and Anti-Gender Politics in Brazil"
    ("Carla Tomazini" ∷ [])
    2026
    "Social Politics: International Studies in Gender, State & Society"
    "10.1093/sp/jxag045"
    "Documents transnational conservative homeschooling advocacy, anti-gender framing, internationalisation strategies and links to moral-conservative political networks."
    "Evidence of a transnational advocacy ecology does not prove command, coordination or causal import for any specific Australian actor or proposal."
    true refl

stoeckl2023 : EarlyLearningReference
stoeckl2023 =
  earlyLearningReference
    "stoeckl-traditional-values-family-homeschooling-2023"
    "Traditional values, family, homeschooling: The role of Russia and the Russian Orthodox Church in transnational moral conservative networks and their efforts at reshaping human rights"
    ("Kristina Stoeckl" ∷ [])
    2023
    "International Journal of Constitutional Law 21(1), 224-242"
    "10.1093/icon/moad026"
    "Provides a source-bound account of homeschooling within transnational moral-conservative networks and human-rights reframing."
    "A network-level pattern cannot be promoted to the motive or voting behaviour of a particular family."
    true refl

forsterVerbist2012 : EarlyLearningReference
forsterVerbist2012 =
  earlyLearningReference
    "oecd-money-or-kindergarten-2012"
    "Money or Kindergarten? Distributive Effects of Cash Versus In-Kind Family Transfers for Young Children"
    ("Michael Forster" ∷ "Gerlinde Verbist" ∷ [])
    2012
    "OECD Social, Employment and Migration Working Papers No. 135"
    "10.1787/5k92vxbgpmnt-en"
    "Compares distributive effects of cash and in-kind family transfers for young children across OECD countries."
    "Cross-country distributive findings do not establish that one instrument dominates every Australian design or every family position."
    true refl

garciaHeckmanLeafPrados2016 : EarlyLearningReference
garciaHeckmanLeafPrados2016 =
  earlyLearningReference
    "garcia-heckman-leaf-prados-life-cycle-2016"
    "The Life-cycle Benefits of an Influential Early Childhood Program"
    ("Jorge Luis Garcia" ∷ "James J. Heckman" ∷ "Duncan Ermini Leaf" ∷ "Maria Jose Prados" ∷ [])
    2016
    "NBER Working Paper 22993"
    "10.3386/w22993"
    "Reports a 13.7 percent annual rate of return and 7.3 benefit-cost ratio for a specific intensive early-childhood programme targeting disadvantaged families."
    "The headline return is programme- and model-specific; it is not a universal multiplier for all ECEC, home learning or family-payment proposals."
    true refl

monforteNetherwaySmith2023 : EarlyLearningReference
monforteNetherwaySmith2023 =
  earlyLearningReference
    "world-cafe-coproduction-2023"
    "The world cafe is an unmethod within co-produced research"
    ("Javier Monforte" ∷ "Jake Netherway" ∷ "Brett Smith" ∷ [])
    2023
    "Qualitative Research in Psychology 20(3), 398-419"
    "10.1080/14780887.2023.2239728"
    "Grounds World Cafe as a participatory approach compatible with co-produced research and cross-perspective knowledge generation."
    "Participation in a World Cafe does not by itself prove equal authority, representative inclusion, policy safety or just outcomes."
    true refl

canonicalEarlyLearningIntersectionalSources : List EarlyLearningReference
canonicalEarlyLearningIntersectionalSources =
  heathBrown2021
  ∷ tomazini2026
  ∷ stoeckl2023
  ∷ forsterVerbist2012
  ∷ garciaHeckmanLeafPrados2016
  ∷ monforteNetherwaySmith2023
  ∷ []
