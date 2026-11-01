module DASHI.Education.EarlyLearningComparativeEvidenceSourceRegistry where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- COMPARATIVE EARLY-LEARNING / ALTERNATIVE-EDUCATION EVIDENCE REGISTRY
--
-- These sources are deliberately retained as heterogeneous evidence surfaces.
-- They do not induce a universal ranking of centre care, home care, structured
-- homeschooling, Waldorf education, unschooling or parental autonomy.
------------------------------------------------------------------------

record ComparativeReference : Set where
  constructor comparativeReference
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

open ComparativeReference public

bakerGruberMilligan2008 : ComparativeReference
bakerGruberMilligan2008 =
  comparativeReference
    "quebec-universal-childcare-2008"
    "Universal Child Care, Maternal Labor Supply, and Family Well-Being"
    ("Michael Baker" ∷ "Jonathan Gruber" ∷ "Kevin Milligan" ∷ [])
    2008
    "Journal of Political Economy 116(4), 709-745"
    "10.1086/591908"
    "Quasi-experimental evidence from Quebec: subsidised universal childcare increased maternal labour supply while the authors estimated adverse changes on several contemporaneous child and family well-being measures."
    "The result identifies one policy rollout and does not prove that universal professional ECEC, centre care, or public entitlement is generally harmful. Quality, counterfactual care, family type and rollout conditions remain open coordinates."
    true refl

bakerGruberMilligan2019 : ComparativeReference
bakerGruberMilligan2019 =
  comparativeReference
    "quebec-long-run-2019"
    "The Long-Run Impacts of a Universal Child Care Program"
    ("Michael Baker" ∷ "Jonathan Gruber" ∷ "Kevin Milligan" ∷ [])
    2019
    "American Economic Journal: Economic Policy 11(3), 1-26"
    "10.1257/pol.20170603"
    "Reports persistence of some negative non-cognitive effects to school ages and worse later health, life satisfaction and crime outcomes for cohorts with increased Quebec childcare access; crime effects were concentrated in boys."
    "Long-run cohort effects do not identify a universal causal effect of professional ECEC and must remain separated from programme quality, family counterfactual and subgroup heterogeneity."
    true refl

kottelenbergLehrer2017 : ComparativeReference
kottelenbergLehrer2017 =
  comparativeReference
    "quebec-heterogeneity-2017"
    "Targeted or Universal Coverage? Assessing Heterogeneity in the Effects of Universal Child Care"
    ("Michael J. Kottelenberg" ∷ "Steven F. Lehrer" ∷ [])
    2017
    "Journal of Labor Economics 35(3), 609-653"
    "10.1086/690652"
    "Shows policy-relevant heterogeneity in Quebec developmental effects and evidence of gains for some disadvantaged single-parent households, consistent with differences in counterfactual home-learning environments."
    "Subgroup heterogeneity is evidence against a one-scalar outcome model; it does not establish a deterministic rule that any demographic group should receive or avoid centre-based care."
    true refl

haeckLebihanMerrigan2018 : ComparativeReference
haeckLebihanMerrigan2018 =
  comparativeReference
    "quebec-nineteen-year-followup-2018"
    "Universal Child Care and Long-Term Effects on Child Well-Being: Evidence from Canada"
    ("Catherine Haeck" ∷ "Laetitia Lebihan" ∷ "Philip Merrigan" ∷ [])
    2018
    "Journal of Human Capital 12(1), 38-98"
    "10.1086/696702"
    "Follows treated cohorts for more than nineteen years; reports persistence of many negative preschool estimates, attenuation after school entry, and little evidence of persistence for ages 12-19."
    "Attenuation and outcome-specific persistence prevent promotion of one early measured effect into a universal life-course verdict."
    true refl

bakerGruberMilligan2026 : ComparativeReference
bakerGruberMilligan2026 =
  comparativeReference
    "quebec-maternal-long-run-2026"
    "Investing in Mothers? The Long-Run Impact of a Universal Child Care Program on Maternal Work and Income"
    ("Michael Baker" ∷ "Jonathan Gruber" ∷ "Kevin Milligan" ∷ [])
    2026
    "NBER Working Paper 35514"
    "10.3386/w35514"
    "Reports enduring positive impacts of Quebec childcare access on maternal employment, earnings and occupational upgrading, with estimated fiscal recapture of 75-117 percent of upfront programme costs."
    "This 2026 working-paper estimate updates the fiscal/labour evidence surface but does not cancel the distinct child-outcome evidence or imply that fiscal recapture equals total social welfare."
    true refl

fendelJochimsen2022 : ComparativeReference
fendelJochimsen2022 =
  comparativeReference
    "home-care-allowance-labour-2022"
    "Home care allowance and labor market participation of immigrant and native-born mothers"
    ("Tanja Fendel" ∷ "Beate Jochimsen" ∷ [])
    2022
    "SN Social Sciences 2, 93"
    "10.1007/s43545-022-00393-w"
    "Finds negative maternal labour-participation effects of a German home-care allowance, larger for immigrant mothers; reviews analogous Nordic evidence and stratified uptake."
    "Cash-for-care effects are context-dependent and cannot be promoted into a universal claim that family-care payments necessarily reduce maternal employment."
    true refl

telferRadzat2024 : ComparativeReference
telferRadzat2024 =
  comparativeReference
    "waldorf-charter-california-2024"
    "Exploring alternative education: a comparison on 3 levels-Waldorf charters, non-Waldorf charters, and local public schools, as measured by the California Assessment of Student Performance and Progress"
    ("Katherine Telfer-Radzat" ∷ [])
    2024
    "Frontiers in Education 9"
    "10.3389/feduc.2024.1323535"
    "School-level California analysis finds lower Waldorf-inspired charter attainment in earlier tested grades but higher eighth-grade ELA and mathematics attainment under several controlled comparisons."
    "Observational school-level achievement patterns do not prove Waldorf pedagogy causes the trajectory, nor do they establish superiority on unmeasured developmental outcomes."
    true refl

martinChangGouldMeuse2011 : ComparativeReference
martinChangGouldMeuse2011 =
  comparativeReference
    "structured-unstructured-homeschool-2011"
    "The Impact of Schooling on Academic Achievement: Evidence From Homeschooled and Traditionally Schooled Students"
    ("Sandra Martin-Chang" ∷ "Odette N. Gould" ∷ "Reanne E. Meuse" ∷ [])
    2011
    "Canadian Journal of Behavioural Science 43(3), 195-202"
    "10.1037/a0022697"
    "Small comparative study separating structured from unstructured homeschooling; structured homeschoolers scored higher on standardised academic measures while unstructured homeschoolers scored lowest among the three groups."
    "Small non-random samples and goal-measure mismatch prevent identification of structure as a universal causal treatment or academic tests as the sole value criterion."
    true refl

petrovicRolstad2017 : ComparativeReference
petrovicRolstad2017 =
  comparativeReference
    "unschooling-autonomy-philosophy-2017"
    "Educating for autonomy: Reading Rousseau and Freire toward a philosophy of unschooling"
    ("John E. Petrovic" ∷ "Kellie Rolstad" ∷ [])
    2017
    "Policy Futures in Education 15(7-8), 817-833"
    "10.1177/1478210316681204"
    "Develops a philosophical case for unschooling/autonomy while also arguing for combining freedom with forms of educational structure."
    "Normative/philosophical argument is not empirical evidence that unstructured education improves measured child outcomes."
    true refl

farberGeeHariri2022 : ComparativeReference
farberGeeHariri2022 =
  comparativeReference
    "normative-range-parenting-2022"
    "Normative range parenting and the developing brain: A scoping review and recommendations for future research"
    ("Madeline J. Farber" ∷ "Dylan G. Gee" ∷ "Ahmad R. Hariri" ∷ [])
    2022
    "European Journal of Neuroscience 55(9-10), 2341-2358"
    "10.1111/ejn.15003"
    "Reviews limited and methodologically heterogeneous evidence on normative variation in parental care/control and neurodevelopment; discusses autonomy/overprotection policy debates."
    "The review explicitly finds insufficient consistency for clear neural conclusions; it therefore cannot be cited as causal proof that free-range parenting improves developmental outcomes."
    true refl

druckman2001 : ComparativeReference
druckman2001 =
  comparativeReference
    "source-credibility-framing-2001"
    "On the Limits of Framing Effects: Who Can Frame?"
    ("James N. Druckman" ∷ [])
    2001
    "The Journal of Politics 63(4), 1041-1066"
    "10.1111/0022-3816.00100"
    "Experimental source-cue evidence that frame influence depends on source credibility."
    "Source credibility affects persuasion but does not imply that every expert endorsement transfers wholesale legitimacy to every adjacent policy claim."
    true refl

nicholson2011 : ComparativeReference
nicholson2011 =
  comparativeReference
    "unexpected-source-cues-2011"
    "Dominating Cues and the Limits of Elite Influence"
    ("Stephen P. Nicholson" ∷ [])
    2011
    "The Journal of Politics 73(4), 1165-1177"
    "10.1017/S002238161100082X"
    "Experimental evidence that source cues can become influential when an endorsement supplies unexpected information contrary to the source's perceived beliefs."
    "Unexpected/cross-cutting endorsement is a risk factor for credibility transfer, not proof that any specific quotation actually changes public opinion."
    true refl

canonicalComparativeSources : List ComparativeReference
canonicalComparativeSources =
  bakerGruberMilligan2008
  ∷ bakerGruberMilligan2019
  ∷ kottelenbergLehrer2017
  ∷ haeckLebihanMerrigan2018
  ∷ bakerGruberMilligan2026
  ∷ fendelJochimsen2022
  ∷ telferRadzat2024
  ∷ martinChangGouldMeuse2011
  ∷ petrovicRolstad2017
  ∷ farberGeeHariri2022
  ∷ druckman2001
  ∷ nicholson2011
  ∷ []
