{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayF1MixingSourceAuditExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Attr

------------------------------------------------------------------------
-- F1 mixing source audit — 2026-09-17
--
-- This owner records what the literature actually supplies around the new
-- connected-correlation / joint-density F1 normal form.  It deliberately does
-- NOT infer the needed 4d SU(2) Wilson trajectory theorem from neighbouring
-- cluster-expansion or strong-mixing results.
--
-- Source proposition
--   != DASHI formal reconstruction
--   != same-object application to the literal Wilson family
--   != physical F1 inhabitant.
------------------------------------------------------------------------

balabanCMP116 : Attr.AttributedSource
balabanCMP116 = Attr.mkDOISource
  "Tadeusz Bałaban"
  "Renormalization group approach to lattice gauge field theories. II. Cluster expansions"
  "Communications in Mathematical Physics 116(1), 1-22"
  "1988"
  "10.1007/BF01239022"
  "https://doi.org/10.1007/BF01239022"
  Attr.academicArticleSource
  "primary non-Abelian lattice-gauge RG source: represents the fluctuation-field integral by an exponentiated cluster expansion and proves the expansion terms satisfy the inductive assumptions; this source role does not by itself assert the DASHI uniform two-slice density defect"
  Attr.publicAttribution

balabanCMP119 : Attr.AttributedSource
balabanCMP119 = Attr.mkDOISource
  "Tadeusz Bałaban"
  "Convergent renormalization expansions for lattice gauge theories"
  "Communications in Mathematical Physics 119(2), 243-285"
  "1988"
  "10.1007/BF01217741"
  "https://doi.org/10.1007/BF01217741"
  Attr.academicArticleSource
  "primary lattice-gauge RG source extending the effective-density induction to large-field domains and convergent renormalization expansions; not a recorded theorem equating the literal two-slice Wilson law with a product-density perturbation"
  Attr.publicAttribution

koteckyPreiss1986 : Attr.AttributedSource
koteckyPreiss1986 = Attr.mkDOISource
  "R. Kotecký and D. Preiss"
  "Cluster expansion for abstract polymer models"
  "Communications in Mathematical Physics 103, 491-498"
  "1986"
  "10.1007/BF01211762"
  "https://doi.org/10.1007/BF01211762"
  Attr.academicArticleSource
  "abstract polymer cluster-expansion convergence theorem; supplies a general convergence precedent, not the physical identification or trajectory estimate for the 4d SU(2) Wilson measure"
  Attr.publicAttribution

dobrushinShlosman1987 : Attr.AttributedSource
dobrushinShlosman1987 = Attr.mkDOISource
  "R. L. Dobrushin and S. B. Shlosman"
  "Completely analytical interactions: Constructive description"
  "Journal of Statistical Physics 46, 983-1014"
  "1987"
  "10.1007/BF01011153"
  "https://doi.org/10.1007/BF01011153"
  Attr.academicArticleSource
  "strong/complete-analyticity precedent relating finite-volume analyticity, correlation decay and truncated-correlation conditions; not automatically a theorem for compact non-Abelian Wilson gauge variables"
  Attr.publicAttribution

stroockZegarlinski1992 : Attr.AttributedSource
stroockZegarlinski1992 = Attr.mkDOISource
  "Daniel W. Stroock and Bogusław Zegarlinski"
  "The logarithmic Sobolev inequality for discrete spin systems on a lattice"
  "Communications in Mathematical Physics 149, 175-193"
  "1992"
  "10.1007/BF02096629"
  "https://doi.org/10.1007/BF02096629"
  Attr.academicArticleSource
  "proves an equivalence between a Dobrushin-Shlosman mixing condition and logarithmic Sobolev inequalities for finite-range lattice gases with finite spin space; retained as a structural precedent only"
  Attr.publicAttribution

forsstrom2022 : Attr.AttributedSource
forsstrom2022 = Attr.mkDOISource
  "Malin Palö Forsström"
  "Decay of Correlations in Finite Abelian Lattice Gauge Theories"
  "Communications in Mathematical Physics 393, 1311-1346"
  "2022"
  "10.1007/s00220-022-04391-0"
  "https://doi.org/10.1007/s00220-022-04391-0"
  Attr.academicArticleSource
  "rigorous finite-Abelian Z^4 lattice-gauge comparator proving decay bounds for local-function correlations at sufficiently large inverse coupling; group/model scope is retained and is not transferred to SU(2)"
  Attr.publicAttribution

f1MixingSourceAtlas : Attr.AttributedSourceAtlas
f1MixingSourceAtlas = Attr.mkSourceAtlas
  "Yang-Mills F1 cluster/mixing source audit"
  "DASHI.Physics.YangMills.YMClayF1MixingSourceAuditExact"
  (balabanCMP116 ∷ balabanCMP119 ∷ koteckyPreiss1986 ∷
   dobrushinShlosman1987 ∷ stroockZegarlinski1992 ∷ forsstrom2022 ∷ [])
  "source-bounded precedents for cluster expansion, complete analyticity, strong mixing, and lattice-gauge correlation decay; explicitly excludes inference of the open literal 4d SU(2) Wilson trajectory mixing theorem"

------------------------------------------------------------------------
-- Exact authority firewalls found by the web/source audit.
------------------------------------------------------------------------

balabanCMP116HasExponentiatedClusterExpansionRole : Bool
balabanCMP116HasExponentiatedClusterExpansionRole = true

balabanCMP116HasExponentiatedClusterExpansionRoleIsTrue :
  balabanCMP116HasExponentiatedClusterExpansionRole ≡ true
balabanCMP116HasExponentiatedClusterExpansionRoleIsTrue = refl

balabanCMP116DirectlyPaysUniformTwoSliceDensity : Bool
balabanCMP116DirectlyPaysUniformTwoSliceDensity = false

balabanCMP116DirectlyPaysUniformTwoSliceDensityIsFalse :
  balabanCMP116DirectlyPaysUniformTwoSliceDensity ≡ false
balabanCMP116DirectlyPaysUniformTwoSliceDensityIsFalse = refl

abstractKPConvergencePaysPhysicalWilsonMixing : Bool
abstractKPConvergencePaysPhysicalWilsonMixing = false

abstractKPConvergencePaysPhysicalWilsonMixingIsFalse :
  abstractKPConvergencePaysPhysicalWilsonMixing ≡ false
abstractKPConvergencePaysPhysicalWilsonMixingIsFalse = refl

dobrushinShlosmanStrongMixingAutomaticallyAppliesToSU2Wilson : Bool
dobrushinShlosmanStrongMixingAutomaticallyAppliesToSU2Wilson = false

dobrushinShlosmanStrongMixingAutomaticallyAppliesToSU2WilsonIsFalse :
  dobrushinShlosmanStrongMixingAutomaticallyAppliesToSU2Wilson ≡ false
dobrushinShlosmanStrongMixingAutomaticallyAppliesToSU2WilsonIsFalse = refl

finiteAbelianCorrelationDecayPaysSU2ContinuumF1 : Bool
finiteAbelianCorrelationDecayPaysSU2ContinuumF1 = false

finiteAbelianCorrelationDecayPaysSU2ContinuumF1IsFalse :
  finiteAbelianCorrelationDecayPaysSU2ContinuumF1 ≡ false
finiteAbelianCorrelationDecayPaysSU2ContinuumF1IsFalse = refl

clusterExpansionCanBeUpstreamOfMixingProof : Bool
clusterExpansionCanBeUpstreamOfMixingProof = true

clusterExpansionCanBeUpstreamOfMixingProofIsTrue :
  clusterExpansionCanBeUpstreamOfMixingProof ≡ true
clusterExpansionCanBeUpstreamOfMixingProofIsTrue = refl

interactingSU2TrajectoryMixingStillOpen : Bool
interactingSU2TrajectoryMixingStillOpen = true

interactingSU2TrajectoryMixingStillOpenIsTrue :
  interactingSU2TrajectoryMixingStillOpen ≡ true
interactingSU2TrajectoryMixingStillOpenIsTrue = refl

-- The precise theorem target after this source audit: either establish a
-- same-object uniform two-slice density/mixing estimate for the literal Wilson
-- family, or provide a complete observable-basis/operator-norm extension that
-- upgrades existing pairwise correlation estimates to the vacuum-orthogonal
-- transfer norm.  The literature atlas above is input/provenance, not payment.

data MixingSourceAuditPresent : Set where
  mixingSourceAuditPresent : MixingSourceAuditPresent

mixingSourceAuditWitness : MixingSourceAuditPresent
mixingSourceAuditWitness = mixingSourceAuditPresent
