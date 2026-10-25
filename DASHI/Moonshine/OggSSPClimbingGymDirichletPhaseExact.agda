module DASHI.Moonshine.OggSSPClimbingGymDirichletPhaseExact where

------------------------------------------------------------------------
-- MULTIPLICATIVE DIRICHLET-PHASE / HELD-OUT MAX-CUT
--
-- Executable producer:
--   scripts/monster_climbing_gym_dirichlet_phase.py
--
-- The finite observable here is p^(i gamma) = exp(i gamma log p), not the
-- additive prime winding exp(i omega p).  The producer exposes the twenty
-- per-prime means and the complete pair kernel
--
--   K(p,q) = mean_gamma (p/q)^(i gamma),
--
-- then reruns every C(20,5)=15504 balanced Ogg/control assignment.
--
-- A second diagnostic subtracts only the leading fixed-X Landau prime term.
-- This is source-shaped normalization, not a finite explicit-formula theorem.
-- The discovery residual becomes more tail-like, but the same locked statistic
-- fails to replicate on the disjoint zeros 850..1698 window after the correct
-- cumulative-height differencing.  That negative result is terminal evidence
-- against promoting the exploratory discovery tail to Monster specificity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPClimbingGymPhaseControlExact as Phase

------------------------------------------------------------------------
-- 1. Exact finite coordinates of the executable experiment.
------------------------------------------------------------------------

oggPrimeCount : Nat
oggPrimeCount = 15

nonOggControlCount : Nat
nonOggControlCount = 5

combinedPrimeCount : Nat
combinedPrimeCount = 20

balancedAssignmentCount : Nat
balancedAssignmentCount = 15504

discoveryZeroCount : Nat
discoveryZeroCount = 849

heldOutZeroCount : Nat
heldOutZeroCount = 849

discoveryRawEnergyLowerOrEqual : Nat
discoveryRawEnergyLowerOrEqual = 3459

discoveryRawCoherenceUpperOrEqual : Nat
discoveryRawCoherenceUpperOrEqual = 541

discoveryLandauResidualEnergyLowerOrEqual : Nat
discoveryLandauResidualEnergyLowerOrEqual = 2294

discoveryLandauResidualCoherenceUpperOrEqual : Nat
discoveryLandauResidualCoherenceUpperOrEqual = 248

heldOutRawEnergyLowerOrEqual : Nat
heldOutRawEnergyLowerOrEqual = 11261

heldOutRawCoherenceUpperOrEqual : Nat
heldOutRawCoherenceUpperOrEqual = 1067

heldOutLandauResidualEnergyLowerOrEqual : Nat
heldOutLandauResidualEnergyLowerOrEqual = 10819

heldOutLandauResidualCoherenceUpperOrEqual : Nat
heldOutLandauResidualCoherenceUpperOrEqual = 7367

producerPath : String
producerPath = "scripts/monster_climbing_gym_dirichlet_phase.py"

discoveryCachePath : String
discoveryCachePath = "scripts/data/monster_climbing_gym_first_849_zeros.json"

heldOutCachePath : String
heldOutCachePath = "scripts/data/monster_climbing_gym_zeros_850_1698.json"

multiplicativeObservableLabel : String
multiplicativeObservableLabel = "p^(i*gamma)=exp(i*gamma*log p)"

pairKernelLabel : String
pairKernelLabel = "K(p,q)=mean_gamma (p/q)^(i*gamma)"

landauPrimeMeanDiagnosticLabel : String
landauPrimeMeanDiagnosticLabel =
  "-(DeltaT/(2*pi*N))*log(p)/sqrt(p), prime-only leading fixed-X Landau term"

------------------------------------------------------------------------
-- 2. Surrounding prior art, with claim-relative attribution.
------------------------------------------------------------------------

landau1911Source : Source.AttributedSource
landau1911Source =
  Source.mkNoDOISource
    "Edmund Landau"
    "Über die Nullstellen der Zetafunktion"
    "Mathematische Annalen 71, 548-564"
    "1911"
    "https://eudml.org/doc/158549"
    Source.academicArticleSource
    "classical fixed-X sum over nontrivial zeta zeros with a von-Mangoldt prime-power main term; does not contain the DASHI Ogg contrast or held-out experiment"
    Source.publicAttribution

gonek1993Source : Source.AttributedSource
gonek1993Source =
  Source.mkNoDOISource
    "Steven M. Gonek"
    "An explicit formula of Landau and its applications to the theory of the zeta-function"
    "Contemporary Mathematics 143, 395-413"
    "1993"
    "bibliographic source; AMS Contemporary Mathematics 143"
    Source.academicChapterSource
    "uniform Landau-Gonek explicit-formula context; does not supply an Ogg/Monster interpretation"
    Source.publicAttribution

durkanHughesPearceCrump2026Source : Source.AttributedSource
durkanHughesPearceCrump2026Source =
  Source.mkNoDOISource
    "Benjamin Durkan; Christopher Hughes; Andrew Pearce-Crump"
    "Generalisations of the Landau--Gonek Theorem and applications to mean values of zeta"
    "arXiv:2601.18025"
    "2026"
    "https://arxiv.org/abs/2601.18025"
    (Source.namedSourceKind "research preprint")
    "2026 surrounding SOTA on zero sums X^rho and their sensitivity to arithmetic X; no Ogg-specific claim is imported"
    Source.publicAttribution

odlyzkoZeroTableSource : Source.AttributedSource
odlyzkoZeroTableSource =
  Source.mkNoDOISource
    "Andrew M. Odlyzko"
    "Tables of zeros of the Riemann zeta function"
    "official University of Minnesota zero tables"
    "public table; accessed 2026"
    "https://www-users.cse.umn.edu/~odlyzko/zeta_tables/"
    (Source.namedSourceKind "numerical reference dataset")
    "independent numerical reference: zeros1 contains the first 100000 ordinates with stated accuracy within 3e-9; used here only to anchor the held-out cache provenance"
    Source.publicAttribution

randomizationInference2024Source : Source.AttributedSource
randomizationInference2024Source =
  Source.mkNoDOISource
    "David M. Ritzwoller; Joseph P. Romano; Azeem M. Shaikh"
    "Randomization Inference: Theory and Applications"
    "arXiv:2406.09521"
    "2024"
    "https://arxiv.org/abs/2406.09521"
    (Source.namedSourceKind "research review/preprint")
    "randomization tests have exact finite-sample Type-I control under the randomization/group-invariance hypothesis; therefore exhaustive relabelling rank alone is not silently promoted to an exact p-value here"
    Source.publicAttribution

dirichletPhaseSourceAtlas : Source.AttributedSourceAtlas
dirichletPhaseSourceAtlas =
  Source.mkSourceAtlas
    "Monster climbing-gym multiplicative-phase source atlas"
    "DASHI.Moonshine.OggSSPClimbingGymDirichletPhaseExact"
    (landau1911Source
      ∷ gonek1993Source
      ∷ durkanHughesPearceCrump2026Source
      ∷ odlyzkoZeroTableSource
      ∷ randomizationInference2024Source
      ∷ [])
    "claim-relative provenance for explicit-formula prior art, held-out zero anchors, and the randomization-inference promotion boundary"

------------------------------------------------------------------------
-- 3. Terminal empirical/promotion boundary.
------------------------------------------------------------------------

record DirichletPhaseBoundary : Set where
  constructor dirichlet-phase-boundary
  field
    multiplicativePhaseDistinctFromAdditivePrimeWinding : Bool
    twentyPrimeMomentAtlasExecutable : Bool
    fullTwentyByTwentyPairKernelExecutable : Bool
    allBalancedPartitionsReplayed : Bool
    landauGonekPriorArtAttributed : Bool
    landauPrimeMainUsedAsDiagnostic : Bool
    landauMainTermClaimedExactFiniteFormula : Bool
    odlyzkoHeldOutAnchorsAcquired : Bool
    heldOutWindowDisjoint : Bool
    heldOutStatisticLockedBeforeEvaluation : Bool
    discoveryResidualTailObserved : Bool
    heldOutRawTailReplicatesDiscovery : Bool
    heldOutResidualTailReplicatesDiscovery : Bool
    randomizationHypothesisEstablished : Bool
    exhaustiveRankPromotedToExactPValue : Bool
    heldOutReplicatedMonsterSpecificAnomaly : Bool
    monsterMechanismPromoted : Bool
    moonshineTheoremPromoted : Bool
    riemannHypothesisEvidencePromoted : Bool

open DirichletPhaseBoundary public

canonicalDirichletPhaseBoundary : DirichletPhaseBoundary
canonicalDirichletPhaseBoundary =
  dirichlet-phase-boundary
    true   -- p^(it) is kept distinct from exp(i omega p)
    true   -- executable emits twenty per-prime means/contributions
    true   -- executable emits the complete complex K(p,q) matrix
    true   -- all 15504 balanced assignments are enumerated
    true   -- Landau/Gonek + 2026 extension sources are explicitly attributed
    true   -- only the leading prime main term is subtracted diagnostically
    false  -- no exact finite explicit formula is manufactured
    true   -- zero #850 and #1698 are independently anchored to Odlyzko zeros1
    true   -- zeros 850..1698 do not overlap zeros 1..849
    true   -- the same coherence statistic/residual normalization is reused
    true   -- discovery residual coherence is 248/15504 upper-tail
    false  -- held-out raw coherence is 1067/15504, not the discovery tail
    false  -- held-out residual is 7367/15504 (~47.5%), plainly non-replicating
    false  -- no exchangeability/group-invariance null theorem is claimed
    false  -- exhaustive combinatorial percentile is not silently a p-value
    false  -- held-out result blocks Monster-specific anomaly promotion
    false  -- no physical/representation mechanism follows from this statistic
    false  -- no Moonshine theorem follows from this finite diagnostic
    false  -- no RH evidence is promoted

------------------------------------------------------------------------
-- 4. Regression against the older first-849 phase-control owner.
------------------------------------------------------------------------

discoveryRawEnergyCountAgreesWithPhaseOwner :
  discoveryRawEnergyLowerOrEqual ≡ Phase.energyLowerOrEqualCount
discoveryRawEnergyCountAgreesWithPhaseOwner = refl

discoveryRawCoherenceCountAgreesWithPhaseOwner :
  discoveryRawCoherenceUpperOrEqual ≡ Phase.coherenceUpperOrEqualCount
discoveryRawCoherenceCountAgreesWithPhaseOwner = refl

dirichletPhaseSourceAtlasNonPromoting :
  Source.atlasCreatesAuthority dirichletPhaseSourceAtlas ≡ false
dirichletPhaseSourceAtlasNonPromoting = refl
