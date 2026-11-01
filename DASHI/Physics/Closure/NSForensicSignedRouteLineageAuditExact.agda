module DASHI.Physics.Closure.NSForensicSignedRouteLineageAuditExact where

------------------------------------------------------------------------
-- NS SIGNED-ROUTE FORENSIC LINEAGE: EARLIEST -> FORWARD
--
-- PURPOSE
-- ------
-- One provenance/path-tracing ledger for the signed/resolvent Navier--Stokes
-- route.  Dates below are repository first-appearance dates recovered from Git
-- history, with UTC and Australia/Brisbane coordinates retained together.
--
-- CURRENT HISTORICAL RESULT
-- -------------------------
-- The earliest RECOVERED point at which all principal coordinates of the later
-- final problem are simultaneously present is 2026-07-26:
--
--   exact signed physical coefficient
--     + cancellation-aware signed-gap route
--     + cutoff-uniform quantitative target
--     + dissipation comparator
--     + arbitrary-data/global consumer.
--
-- This is a PROBLEM-SPECIFICATION claim, not a solved-theorem claim.
--
-- The forward audit then shows a repeated pattern:
--
--   abstract / majorant formulation
--     -> signed same-object correction
--     -> physical specialization
--     -> removal of caller-selectable transport/proxy coordinates
--     -> literal Package-A / R406 / critical-barrier consumer.
--
-- By R355 the repository explicitly says most of the apparent frontier was
-- repository plumbing rather than new analysis.  By R373 the old nonnegative
-- coherent-Gram majorant is explicitly bypassed by a signed-through-time route.
-- R375/R377/R379 then make the signed family literally physical and remove
-- caller-selectable Gram/transport data.  R410/R414/R422 bind the target to the
-- actual R406/R290 carrier, and R423 names the remaining same-object producer.
--
-- FORENSIC FIREWALL
-- -----------------
-- Chronology establishes source existence/provenance only.  It does NOT by
-- itself establish correctness, third-party access, copying, training use,
-- reward hacking, or exact same-object identity.  Exact identity is recorded
-- only where the formal owner itself supplies the same-carrier/equality weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

-- Historical owners.
import DASHI.Physics.Closure.NSWall1CanonicalResolventGap as JulyResolvent
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as JulySigned
import DASHI.Physics.Closure.NSTriadKNSignedUniformGapProgram as JulyGap
import DASHI.Physics.Closure.NSTriadKNSignedGapAprioriComposition as JulyApriori
import DASHI.Physics.Closure.NSTriadKNExactCoefficientToPhysicalWeight as JulyPhysical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadFrontierProgram as JulyStage3
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalSignedShellCellRound26Exact as AugShell
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorBonyWeldRound123Exact as R123
import DASHI.Physics.Closure.NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact as R228
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNHeatWeightedCommutatorSchurRound301Exact as R301
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedSpacetimeToResolventRound351Exact as R351
import DASHI.Physics.Closure.NSTriadKNResolventPackageAFrontierCorrectionRound355Exact as R355
import DASHI.Physics.Closure.NSTriadKNSignedGramBypassesCoherentMajorantRound373Exact as R373
import DASHI.Physics.Closure.NSTriadKNPhysicalSignedGramFamilyRound375Exact as R375
import DASHI.Physics.Closure.NSTriadKNPhysicalSignedGramToPackageARound377Exact as R377
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalGramToPackageARound379Exact as R379
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNSignedTTStarCriticalCancellationTargetRound410Exact as R410
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact as R423

-- Later exact descendants / current convergence.
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairCompanionRound496Exact as R496
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNNestedSlotBonyClassNormBidiRound584Exact as R584
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact as Weld541x573
import DASHI.Physics.Closure.NSTriadKNNestedFactoredFullToDirectFibreBidiExact as NestedFibre
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedExactClassNormPaymentBidiExact as Exact584Payment

data Repository : Set where
  dashiCFD dashiAgda : Repository

data Role : Set where
  structuralAncestor signedCoherence empiricalBarrier empiricalSignedResidual : Role
  signedMajorantBoundary resolventBaseline architectureAssembly : Role
  finalProblemSpecification physicalInstantiation signedCarrierMaturation : Role
  sameObjectCorrection packageAConvergence liveR406Convergence : Role
  canonicalSignedTarget directResolventConvergence nestedConvergence analyticFrontier : Role

data Relation : Set where
  broadAncestor empiricalPrecursor representationBoundary architectureEdge : Relation
  problemSpecification physicalSpecialization formalRefinement exactSameObject : Relation
  exactSpecialization canonicalConsumer survivingBoundary : Relation

record Receipt : Set where
  constructor receipt
  field
    repository : Repository
    artefact : String
    path : String
    commit : String
    utc : String
    brisbane : String
    role : Role
    note : String
open Receipt public

record Edge : Set where
  constructor edge
  field
    from to : String
    relation : Relation
    rationale : String
    exactCarrier : Bool
open Edge public

mk : Repository → String → String → String → String → String → Role → String → Receipt
mk repo name p sha u b r n = receipt repo name p sha u b r n

------------------------------------------------------------------------
-- EARLY SIGN / SUPPORT / EMPIRICAL BARRIER
------------------------------------------------------------------------

jan24 = mk dashiCFD
  "signed/ternary CFD structural carrier"
  "COMPACTIFIED_CONTEXT.md; dashi_les_vorticity_codec_v2.py; dashi_signed_branchedflow_codec.npz"
  "1cb1bb612c4061676a06e615f69bf282462c25cc"
  "2026-01-24T09:06:14Z" "2026-01-24T19:06:14+10:00" structuralAncestor
  "signed anomaly -> ternary state -> support -> residual; structural ancestor only"

jan27 = mk dashiCFD
  "Signed Filament Annihilation"
  "docs/signed_filament_annihilation.md"
  "7938f8282541b142e93cb2a7dadf32d83ca553b3"
  "2026-01-27T14:33:22Z" "2026-01-28T00:33:22+10:00" signedCoherence
  "F_k = sigma_k*s_k; support/sign factorized; annihilation/coarse-graining may not create support"

jun03 = mk dashiCFD
  "theta flux/dissipation sweep"
  "scripts/ns_theta_full_sweep.py"
  "125e52e04bed4042890d95db5d5371104ba1aafe"
  "2026-06-03T14:15:39Z" "2026-06-04T00:15:39+10:00" empiricalBarrier
  "empirical |Flux|/Diss high-frequency barrier; early absolute value is historical representation loss"

jun04 = mk dashiCFD
  "signed ternary cross-shell flip/net-residue audit"
  "scripts/ns_signed_ternary_flip_audit.py; scripts/ns_material_parent_summary.py; scripts/ns_ternary_cross_shell_matrix.py"
  "1c9ca183515e3a26988ae21785de9a45481e37d2"
  "2026-06-04T04:13:12Z" "2026-06-04T14:13:12+10:00" empiricalSignedResidual
  "signed +/- imbalance formed before magnitude diagnostics"

------------------------------------------------------------------------
-- JULY: ARCHITECTURE ASSEMBLY -> EARLIEST RECOVERED FINAL-PROBLEM SPEC
------------------------------------------------------------------------

jul20Resolvent = mk dashiAgda
  "canonical finite resolvent / strict gap baseline"
  "DASHI/Physics/Closure/NSWall1CanonicalResolventGap.agda"
  "d10569457f09993174e1b921935dadb1eebced05"
  "2026-07-20T01:43:20Z" "2026-07-20T11:43:20+10:00" resolventBaseline
  "resolvent/gap coordinate exists; finite baseline explicitly not physical low block absent representation"

jul20MajorantBoundary = mk dashiAgda
  "signed response separated from pair-majorant kernel"
  "DASHI/Physics/Closure/NSCompactGammaOffPacketPairIncidenceKernelBridge.agda"
  "723bf33bd9bf1947eb5bbda6dd3df700b5b05e39"
  "2026-07-20T01:57:40Z" "2026-07-20T11:57:40+10:00" signedMajorantBoundary
  "signed near response <= nonnegative majorant action; pair majorant cannot reproduce signed response entrywise"

jul20PR145 = mk dashiAgda
  "PR #145 Schur/resolvent/gap packet" "pull/145"
  "8905dc5c4c3389f18698f1669040dcf5923af0c6"
  "2026-07-20T03:02:06Z" "2026-07-20T13:02:06+10:00" architectureAssembly
  "finite Schur + low resolvent + strict gap; representation remains guarded"

jul20PR140 = mk dashiAgda
  "PR #140 compact-Gamma signed-response/Schur/tail architecture" "pull/140"
  "e64a38ab617cf88035555a07a223afe46480df0e"
  "2026-07-20T06:17:05Z" "2026-07-20T16:17:05+10:00" architectureAssembly
  "signed near response + pair-incidence majorant + Schur target + far tail + D-log-E consumer"

jul20PR227 = mk dashiAgda
  "PR #227 cross-pollinated analytic closure stack" "pull/227"
  "c2b313a0878b0281781dd7a1bf3ae851d24af8d9"
  "2026-07-20T09:42:15Z" "2026-07-20T19:42:15+10:00" architectureAssembly
  "differentiated triads + full-shell pair incidence + tail + Galerkin + invariant region + BKM"

jul20PR255 = mk dashiAgda
  "PR #255 concrete far-tail commutator decay" "pull/255"
  "bc9a627985cf4140ee10260f6399050aacf5cba4"
  "2026-07-20T15:09:40Z" "2026-07-21T01:09:40+10:00" architectureAssembly
  "far-low commutator gain + far-high Sobolev tail + cutoff-uniform epsilon(R) endpoint"

jul25PR336 = mk dashiAgda
  "PR #336 exact signed multiplier-difference commutator frontier" "pull/336"
  "68ab8ffbcf5c0aa791720a454dbeb1631ea933b2"
  "2026-07-25T07:09:05Z" "2026-07-25T17:09:05+10:00" signedMajorantBoundary
  "K_raw, signed K_diff and K_absdiff separated; exact commutator identity before norm; absolute Schur route empirically poor"

jul26Coefficient = mk dashiAgda
  "exact signed velocity-form Galerkin coefficient"
  "DASHI/Physics/Closure/NSTriadKNExactSignedGalerkinCoefficient.agda"
  "466c9cdea3336fb3b0c727ee21900d008d90a00d"
  "2026-07-26T02:44:07Z" "2026-07-26T12:44:07+10:00" finalProblemSpecification
  "literal -i P_k[(u_p.q)u_q]; no positive part, abs, phase ansatz or hidden half"

jul26Physical = mk dashiAgda
  "exact signed coefficient -> retained physical triads"
  "DASHI/Physics/Closure/NSTriadKNExactCoefficientToPhysicalWeight.agda"
  "a4f38a003e74cfb31d8dc452a0e1eb7c6fc565ca"
  "2026-07-26T02:46:25Z" "2026-07-26T12:46:25+10:00" finalProblemSpecification
  "raw coefficient remains signed; Nat kernel explicitly only coefficientMajorant(raw coefficient)"

jul26Stage3 = mk dashiAgda
  "signed physical Stage-3 frontier aggregate"
  "DASHI/Physics/Closure/NSTriadKNPhysicalTriadFrontierProgram.agda"
  "5e1ae9dc413a9447bfa515a784bdeb08dab53f2e"
  "2026-07-26T02:51:51Z" "2026-07-26T12:51:51+10:00" finalProblemSpecification
  "signed coefficient + positive-part no-go + physical fibres + class envelopes + finite/uniform no-go + global cutset"

jul26Gap = mk dashiAgda
  "signed cutoff-uniform gap program"
  "DASHI/Physics/Closure/NSTriadKNSignedUniformGapProgram.agda"
  "e8d8781781f825f3b27fbf578887d6e619bf5953"
  "2026-07-26T03:25:40Z" "2026-07-26T13:25:40+10:00" finalProblemSpecification
  "Route B preserves signed blocks; permutation/reality/complete-triad cancellation + uniform numerical-range target"

jul26Global = mk dashiAgda
  "signed gap -> arbitrary-data uniform a-priori consumer"
  "DASHI/Physics/Closure/NSTriadKNSignedGapAprioriComposition.agda"
  "a872ad2a4249e2d6f1056595df980000fe7472aa"
  "2026-07-26T04:17:22Z" "2026-07-26T14:17:22+10:00" finalProblemSpecification
  "signed Nonlinear<=Dissipation + exact energy identity -> cutoff-independent arbitrary-data control"

------------------------------------------------------------------------
-- AUGUST: PHYSICAL-CARRIER MATURATION AND RESOLVENT/SPACETIME RE-EXPRESSION
------------------------------------------------------------------------

aug08Shell = mk dashiAgda
  "literal physical signed shell ledger"
  "DASHI/Physics/Closure/NSTriadKNLuoPhysicalSignedShellCellRound26Exact.agda"
  "19aa8cb1d7b373fdf74ac0674832477a94d98f5a"
  "2026-08-08T06:50:21Z" "2026-08-08T16:50:21+10:00" physicalInstantiation
  "HH+LH+HL+CC+Com forced by literal physical output fibre and genuine shell balance"

aug27R123 = mk dashiAgda
  "R123 physical quartic -> signed pure-commutator Bony folds"
  "DASHI/Physics/Closure/NSTriadKNExternalPureCommutatorBonyWeldRound123Exact.agda"
  "1ccc381d7d2b71e6add0110d1575a8d35242496c"
  "2026-08-27T14:06:10Z" "2026-08-28T00:06:10+10:00" signedCarrierMaturation
  "2*full physical quartic = four signed Bony commutator folds; no cellwise abs/cardinality tax"

aug29R228 = mk dashiAgda
  "R228 mixed-helicity spacetime frontier"
  "DASHI/Physics/Closure/NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact.agda"
  "2b18f2f747863c67a9274463891774a4170d8fa0"
  "2026-08-29T13:01:57Z" "2026-08-29T23:01:57+10:00" signedCarrierMaturation
  "remaining Package-A theorem isolated as cutoff-uniform physical mixed-helicity spacetime estimate"

aug30R290 = mk dashiAgda
  "R290 resolvent-weighted temporal Gram flux"
  "DASHI/Physics/Closure/NSTriadKNWeightedGramFluxCompilerRound290Exact.agda"
  "9bc61ac8e9b046c7bcb781fb5badba5654d1acf0"
  "2026-08-30T11:08:41Z" "2026-08-30T21:08:41+10:00" signedCarrierMaturation
  "viscous pair resolvent w*lambda=1 rewrites Gram debt as endpoint flux + weighted nonlinear remainder"

aug30R294 = mk dashiAgda
  "R294 swap-invariant weighted commutator"
  "DASHI/Physics/Closure/NSTriadKNResolventWeightedMixedCommutatorRound294Exact.agda"
  "64e2a4d2b067a05c0a8cf979ea3ed74f960c56dc"
  "2026-08-30T11:19:48Z" "2026-08-30T21:19:48+10:00" sameObjectCorrection
  "generic swap-invariant weight preserves mixed-commutator cancellation before absolute values"

aug31R301 = mk dashiAgda
  "R301 same-object heat-weighted R294 spacetime frontier"
  "DASHI/Physics/Closure/NSTriadKNHeatWeightedCommutatorSchurRound301Exact.agda"
  "489f48fac67b7effe1ffd6200c7f614ff4d60a0d"
  "2026-08-31T10:04:17Z" "2026-08-31T20:04:17+10:00" sameObjectCorrection
  "requires literal R294 carrier; row/column + spacetime estimates are named payment"

aug31R351 = mk dashiAgda
  "R351 spacetime payment -> existing resolvent absorption consumer"
  "DASHI/Physics/Closure/NSTriadKNHeatWeightedNestedSpacetimeToResolventRound351Exact.agda"
  "523909ea07409de82e225153572bfbc8f91b7e35"
  "2026-08-31T14:58:10Z" "2026-09-01T00:58:10+10:00" sameObjectCorrection
  "R301 payment directly inhabits old R300 resolvent absorption leaf by monotonicity"

------------------------------------------------------------------------
-- AUG31/SEP1: REPOSITORY ITSELF IDENTIFIES PLUMBING AND REMOVES MAJORANT ROUTE
------------------------------------------------------------------------

aug31R355 = mk dashiAgda
  "R355 corrected resolvent frontier -> literal physical Package A"
  "DASHI/Physics/Closure/NSTriadKNResolventPackageAFrontierCorrectionRound355Exact.agda"
  "3cd98fa8e575c3cd151822e6cbda120abdc458c0"
  "2026-08-31T15:09:44Z" "2026-09-01T01:09:44+10:00" packageAConvergence
  "explicitly states most apparent frontier was repository plumbing; R351->R352->R353->R354 reaches literal R240 Package A"

aug31R373 = mk dashiAgda
  "R373 signed Gram bypasses coherent majorant frontier"
  "DASHI/Physics/Closure/NSTriadKNSignedGramBypassesCoherentMajorantRound373Exact.agda"
  "0001e2dce57b9c988532c24dc33af30d3567ecba"
  "2026-08-31T15:54:53Z" "2026-09-01T01:54:53+10:00" packageAConvergence
  "newer R303/R353 route retains Gram SIGNED through time; old nonnegative R222 majorant no longer prerequisite"

aug31R375 = mk dashiAgda
  "R375 make signed-Gram companion and integral literally physical"
  "DASHI/Physics/Closure/NSTriadKNPhysicalSignedGramFamilyRound375Exact.agda"
  "6fe15ef99abe96740fa4995900f165f1e2c226a9"
  "2026-08-31T16:02:08Z" "2026-09-01T02:02:08+10:00" packageAConvergence
  "R353 companion = R228 physical companion and integration = physical integrateTo; R354 identity becomes refl"

aug31R377 = mk dashiAgda
  "R377 physical signed-Gram family is the Package-A input"
  "DASHI/Physics/Closure/NSTriadKNPhysicalSignedGramToPackageARound377Exact.agda"
  "c08fd80ee8745649d9047e6f8deeb318eb622353"
  "2026-08-31T16:05:50Z" "2026-09-01T02:05:50+10:00" packageAConvergence
  "routine R354 transport obligations removed; only substantive signed-payment + physical integration data remain"

aug31R379 = mk dashiAgda
  "R379 exact global Gram debt feeds physical signed Package A"
  "DASHI/Physics/Closure/NSTriadKNPhysicalGlobalGramToPackageARound379Exact.agda"
  "3b9484614be1b61e67ed43b10ca3eb74f8d177e7"
  "2026-08-31T16:10:34Z" "2026-09-01T02:10:34+10:00" packageAConvergence
  "gramDebt no longer caller-selectable; fixed to literal R378 global debt; companion = cellMass + globalGramDebt"

------------------------------------------------------------------------
-- SEP1-SEP2: LIVE R406 / CRITICAL-BARRIER SAME-OBJECT CONVERGENCE
------------------------------------------------------------------------

sep01R406 = mk dashiAgda
  "R406 live R378 flux on fixed canonical output list"
  "DASHI/Physics/Closure/NSTriadKNFixedOutputLiveGlobalFluxRound406Exact.agda"
  "341747bff0c977aadc89f8f55b05225b1c9ce15c"
  "2026-09-01T05:21:27Z" "2026-09-01T15:21:27+10:00" liveR406Convergence
  "literal live weighted remainder/flux carrier fixed on canonical physical output list"

sep01R410 = mk dashiAgda
  "R410 signed critical target bound to actual R405/R406 modules"
  "DASHI/Physics/Closure/NSTriadKNSignedTTStarCriticalCancellationTargetRound410Exact.agda"
  "b79e3a5f33d3df3ce52e9777596ee823a8b39863"
  "2026-09-01T06:24:21Z" "2026-09-01T16:24:21+10:00" canonicalSignedTarget
  "target must pay exact R406/R290 signed off-diagonal remainder; no Wiener-positive proxy or cutoff-dependent replacement"

sep01R414 = mk dashiAgda
  "R414 one cancellation pays R406 remainder and critical barrier"
  "DASHI/Physics/Closure/NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact.agda"
  "8bff9ff11443bfce551e44aeddea10c6484b6d82"
  "2026-09-01T06:35:08Z" "2026-09-01T16:35:08+10:00" canonicalSignedTarget
  "Round104 remainder is definitionally the R406 remainder integral; second independent remainder estimate removed"

sep01R422 = mk dashiAgda
  "R422 actual R290 pair derivatives -> exact R406 flux derivative"
  "DASHI/Physics/Closure/NSTriadKNR418FinitePairFamilyToR409Round422Exact.agda"
  "aa47f839f6d90d318c25b66aeba2809ff789e6b5"
  "2026-09-01T08:32:41Z" "2026-09-01T18:32:41+10:00" liveR406Convergence
  "same R291/R290 pair curves aggregated and transported only at final boundary to literal R406 flux/tangent"

sep02R423 = mk dashiAgda
  "R423 quadratic companion signed heat -> critical barrier same-object target"
  "DASHI/Physics/Closure/NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact.agda"
  "a49e8d5db9334e60f0a12ade71442dd2d96f1e18"
  "2026-09-02T03:43:19Z" "2026-09-02T13:43:19+10:00" canonicalSignedTarget
  "quadratic companion forcing cross must equal signed heat cross; pays literal R406 remainder and same critical barrier; no alternate companion/positive Wiener envelope/second remainder"

------------------------------------------------------------------------
-- LATER CANONICAL DIRECT/NESTED RE-EXPRESSIONS
------------------------------------------------------------------------

sep07R496 = mk dashiAgda
  "R496 direct nonseparable resolvent pair companion"
  "DASHI/Physics/Closure/NSTriadKNDirectResolventPairCompanionRound496Exact.agda"
  "9be2933f265e95ccc9f2dca5204b21bc528fc393"
  "2026-09-07T18:53:49Z" "2026-09-08T04:53:49+10:00" directResolventConvergence
  "literal weighted remainder represented by canonical direct Cauchy-resolvent pair companion"

sep07R503 = mk dashiAgda
  "R503 signed direct-resolvent terminal consumer"
  "DASHI/Physics/Closure/NSTriadKNDirectResolventSignedCrossToR415Round503Exact.agda"
  "984eaa83d988b0292ead61cfef8e9db463cbb425"
  "2026-09-07T19:02:43Z" "2026-09-08T05:02:43+10:00" directResolventConvergence
  "preserves sign and asks cutoff-uniform one-sided direct-companion bound"

sep09R541 = mk dashiAgda
  "R541 spectator Cauchy resolvent as R294 weight"
  "DASHI/Physics/Closure/NSTriadKNSpectatorResolventR294WeightRound541Exact.agda"
  "350a5e27443ee05db7fbbf8359165ef5a10e672d"
  "2026-09-09T04:56:22Z" "2026-09-09T14:56:22+10:00" nestedConvergence
  "literal spectator pair kernel is exact R294 swap-invariant weight"

sep09R573 = mk dashiAgda
  "R573 weighted nested four-sign commutator"
  "DASHI/Physics/Closure/NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact.agda"
  "8c4c2411d3cc292cef93dd6fb307a18b402ff564"
  "2026-09-09T09:17:38Z" "2026-09-09T19:17:38+10:00" nestedConvergence
  "weighted outer carrier equals nested four-sign inner representation before norms"

sep09R584 = mk dashiAgda
  "R584 live nested-slot Bony class-norm carrier"
  "DASHI/Physics/Closure/NSTriadKNNestedSlotBonyClassNormBidiRound584Exact.agda"
  "b42b6510c4025d835192d1d84d188ed87426abc9"
  "2026-09-09T14:49:15Z" "2026-09-10T00:49:15+10:00" analyticFrontier
  "class norms placed on actual R573 slot-transformed cells"

sep10Weld = mk dashiAgda
  "explicit R541 x R573 spectator-resolvent nested weld"
  "DASHI/Physics/Closure/NSTriadKNSpectatorResolventNestedCommutatorBidiExact.agda"
  "b06ec702a45c595449c044a19ad14d5b37327ace"
  "2026-09-10T05:01:10Z" "2026-09-10T15:01:10+10:00" nestedConvergence
  "literal R541 spectator weight instantiated into R573 before norm/abs/Schur/Laplace"

------------------------------------------------------------------------
-- CHRONOLOGY
------------------------------------------------------------------------

chronology : List Receipt
chronology =
  jan24 ∷ jan27 ∷ jun03 ∷ jun04 ∷
  jul20Resolvent ∷ jul20MajorantBoundary ∷ jul20PR145 ∷ jul20PR140 ∷
  jul20PR227 ∷ jul20PR255 ∷ jul25PR336 ∷ jul26Coefficient ∷ jul26Physical ∷
  jul26Stage3 ∷ jul26Gap ∷ jul26Global ∷ aug08Shell ∷ aug27R123 ∷ aug29R228 ∷
  aug30R290 ∷ aug30R294 ∷ aug31R301 ∷ aug31R351 ∷ aug31R355 ∷ aug31R373 ∷
  aug31R375 ∷ aug31R377 ∷ aug31R379 ∷ sep01R406 ∷ sep01R410 ∷ sep01R414 ∷
  sep01R422 ∷ sep02R423 ∷ sep07R496 ∷ sep07R503 ∷ sep09R541 ∷ sep09R573 ∷
  sep09R584 ∷ sep10Weld ∷ []

------------------------------------------------------------------------
-- FORWARD SNOWBALL
------------------------------------------------------------------------

janToJune = edge "Jan signed/support semantics" "June signed-transfer/barrier experiments"
  empiricalPrecursor "sign/support/coherence becomes explicit empirical signed residue plus barrier search" false

juneToJuly = edge "June signed transfer + theta barrier" "Jul20 signed-response/majorant separation"
  representationBoundary "formal lane records that nonnegative majorant is not the signed response" false

julyArchitecture = edge "Jul20 resolvent/Schur/tail/Galerkin architecture" "Jul26 assembled signed physical problem"
  architectureEdge "global closure machinery meets exact signed coefficient and cutoff-uniform signed-gap target" false

julyFinalProblem = edge "Jul26 exact signed physical operator" "Jul26 signed gap -> arbitrary-data consumer"
  problemSpecification "all principal coordinates of later terminal problem simultaneously present; quantitative signed estimate still open" false

julyToPhysical = edge "Jul26 signed physical frontier" "Aug08 literal physical signed shell ledger"
  physicalSpecialization "abstract signed frontier lands on genuine energy balance and physical fibres" true

physicalToCommutator = edge "Aug08 signed shell" "Aug27 R123 signed commutator Bony carrier"
  formalRefinement "full physical quartic sum rewritten into signed commutator classes before absolute values" false

commutatorToSpacetime = edge "R123 signed carrier" "R228 cutoff-uniform mixed-helicity spacetime leaf"
  formalRefinement "finite signed cancellation collapses Package A to one physical spacetime theorem" false

spacetimeToResolvent = edge "R228 spacetime leaf" "R290/R294 resolvent-weighted signed commutator"
  formalRefinement "pair damping/resolvent re-expresses Gram debt while retaining cancellation" false

sameObjectSpacetime = edge "R294 literal weighted commutator" "R301 same-object heat/spacetime payment"
  exactSameObject "R301 explicitly requires the actual R294 carrier and rejects proxy carriers" true

spacetimeToOldConsumer = edge "R301 signed spacetime payment" "R351 existing R300 resolvent consumer"
  canonicalConsumer "payment inhabits already-owned consumer via monotonicity; no new consumer architecture" true

plumbingCorrection = edge "R351/R352/R353/R354 chain" "R355 literal R240 Package A"
  canonicalConsumer "repository explicitly identifies most apparent frontier as plumbing; physical producers + same-object receipts feed existing compilers" true

majorantBypass = edge "old R222 nonnegative coherent majorant" "R373 signed-through-time R303/R353 route"
  representationBoundary "signed integrated debt suffices; positive coherent majorant no longer prerequisite" false

physicalSignedFamily = edge "R353 generic signed family" "R375/R377 literal physical Package A input"
  exactSpecialization "companion/integration made definitionally physical; routine transport receipts removed" true

literalGlobalDebt = edge "R377 signed Package-A core" "R379 literal R378 global Gram debt"
  exactSpecialization "gramDebt and companion ledger cease to be caller-selectable" true

liveR406 = edge "R379 physical signed Package A" "R406 live canonical flux/remainder"
  formalRefinement "same signed/Gram/resolvent debt becomes fixed live R406 carrier" false

r406ToCritical = edge "R406 literal remainder" "R410/R414 Round104 critical barrier"
  exactSameObject "Round104 integrable remainder is definitionally the R406 remainder integral; no second estimate" true

r290ToR406Derivative = edge "R290 same-pair derivatives" "R422 exact R406 flux derivative"
  exactSameObject "finite family of same R291/R290 pairs transported only at final boundary to literal R406" true

r423Canonical = edge "quadratic companion forcing" "R423 signed heat / R406 / critical-barrier target"
  exactSameObject "producer must equal same signed heat cross that pays R406 and the critical barrier" true

r423ToDirect = edge "R423 signed companion target" "R496/R503 direct resolvent consumer"
  formalRefinement "later tranche re-expresses same cutoff-uniform signed-resolvent obligation on direct companion carrier" false

directToNested = edge "R503 direct signed consumer" "R541 x R573 nested spectator weld"
  exactSpecialization "literal Cauchy spectator weight and nested four-sign cancellation are composed on same route" true

snowball : List Edge
snowball =
  janToJune ∷ juneToJuly ∷ julyArchitecture ∷ julyFinalProblem ∷ julyToPhysical ∷
  physicalToCommutator ∷ commutatorToSpacetime ∷ spacetimeToResolvent ∷
  sameObjectSpacetime ∷ spacetimeToOldConsumer ∷ plumbingCorrection ∷ majorantBypass ∷
  physicalSignedFamily ∷ literalGlobalDebt ∷ liveR406 ∷ r406ToCritical ∷
  r290ToR406Derivative ∷ r423Canonical ∷ r423ToDirect ∷ directToNested ∷ []

------------------------------------------------------------------------
-- ATTRIBUTION ATLAS
------------------------------------------------------------------------

src : String → String → String → Source.AttributedSource
src title context relationship = Source.mkNoDOISource
  "Johl Brown" title context "2026" "https://github.com/chboishabba"
  (Source.namedSourceKind "GitHub repository source/commit/PR") relationship Source.publicAttribution

forensicSourceAtlas : Source.AttributedSourceAtlas
forensicSourceAtlas = Source.mkSourceAtlas
  "NS signed-route earliest-forward forensic source atlas"
  "DASHI.Physics.Closure.NSForensicSignedRouteLineageAuditExact"
  (src "dashiCFD Jan origins" "Jan24/Jan27 commits" "structural signed/support provenance" ∷
   src "dashiCFD June NS experiments" "Jun03/Jun04 commits" "empirical signed/barrier precursors" ∷
   src "July assembled NS architecture" "Jul20-Jul26 commits/PRs" "earliest recovered final-problem specification" ∷
   src "August physical/resolvent route" "Aug08-Aug31 commits" "physical carrier maturation and same-object corrections" ∷
   src "Sep1-Sep2 Package-A/R406 convergence" "R355-R423 commits" "literal physical signed consumer convergence" ∷
   src "later direct/nested route" "R496-R584 and weld commits" "later canonical re-expression/specialization" ∷ [])
  "chronology and formalisation relationships only; citation imports neither proof nor external influence"

------------------------------------------------------------------------
-- FORENSIC WRONGTYPE FIREWALLS
------------------------------------------------------------------------

data SourceExistenceImpliesCorrectness : Set where
data ChronologyImpliesThirdPartyAccess : Set where
data PublicRepoImpliesTrainingUse : Set where
data ChronologyImpliesCopying : Set where
data ChronologyImpliesRewardHacking : Set where
data PrecursorImpliesSameObject : Set where
data ProblemSpecificationImpliesSolved : Set where
data SameProblemShapeImpliesSameCarrier : Set where

noCorrectness : SourceExistenceImpliesCorrectness → ⊥
noCorrectness ()
noThirdPartyAccess : ChronologyImpliesThirdPartyAccess → ⊥
noThirdPartyAccess ()
noTrainingInference : PublicRepoImpliesTrainingUse → ⊥
noTrainingInference ()
noCopyingInference : ChronologyImpliesCopying → ⊥
noCopyingInference ()
noRewardHackingInference : ChronologyImpliesRewardHacking → ⊥
noRewardHackingInference ()
noPrecursorIdentity : PrecursorImpliesSameObject → ⊥
noPrecursorIdentity ()
problemSpecifiedDoesNotMeanSolved : ProblemSpecificationImpliesSolved → ⊥
problemSpecifiedDoesNotMeanSolved ()
sameShapeDoesNotMeanSameCarrier : SameProblemShapeImpliesSameCarrier → ⊥
sameShapeDoesNotMeanSameCarrier ()

------------------------------------------------------------------------
-- AUDIT FINDINGS
------------------------------------------------------------------------

earliestRecoveredFinalProblemSpecificationIsJuly26 : Bool
earliestRecoveredFinalProblemSpecificationIsJuly26 = true

july26ClaimedSolved : Bool
july26ClaimedSolved = false

r355RepositoryPlumbingCorrectionRecorded : Bool
r355RepositoryPlumbingCorrectionRecorded = true

r373SignedRouteBypassesNonnegativeMajorant : Bool
r373SignedRouteBypassesNonnegativeMajorant = R373.round373R222NonnegativeCoherentMajorantRequiredBySignedRoute

r375R353IsDefinitionallyPhysical : Bool
r375R353IsDefinitionallyPhysical = R375.round375R353CompanionIsDefinitionallyPhysical

r377OnlySubstantiveSignedPhysicalInputsRemain : Bool
r377OnlySubstantiveSignedPhysicalInputsRemain = R377.round377OnlySignedPaymentAndPhysicalIntegrationDataRemain

r379LiteralGlobalDebtUsed : Bool
r379LiteralGlobalDebtUsed = R379.round379ExactR378GlobalGramDebtUsed

r410TargetIsLiteralR406 : Bool
r410TargetIsLiteralR406 = R410.round410TargetIsLiteralR406Remainder

r414SecondRemainderNeeded : Bool
r414SecondRemainderNeeded = R414.round414SecondIndependentRemainderEstimateNeeded

r422FinalTargetIsLiteralR406 : Bool
r422FinalTargetIsLiteralR406 = R422.round422FinalTargetIsLiteralR406Flux

r423PositiveWienerEnvelopeRequired : Bool
r423PositiveWienerEnvelopeRequired = R423.round423PositiveWienerEnvelopeRequired

r423RemainingProducerIsCutoffUniformSignedCompanionBudget : Bool
r423RemainingProducerIsCutoffUniformSignedCompanionBudget = R423.round423RemainingNovelProducerIsCutoffUniformSignedCompanionBudget

r541xR573ExplicitCompositionRecorded : Bool
r541xR573ExplicitCompositionRecorded = Weld541x573.roundSpectatorNestedR541WeightInstantiatedIntoR573

nestedRouteLandsOnCanonicalDirectCarrier : Bool
nestedRouteLandsOnCanonicalDirectCarrier = NestedFibre.nestedFactoredFullToCanonicalR497CarrierClosed

currentUsefulUniformEnvelopeClosed : Bool
currentUsefulUniformEnvelopeClosed = Exact584Payment.uniformUpperOnExactClassNormEnvelopeClosed

currentR503BudgetClosed : Bool
currentR503BudgetClosed = R503.round503DirectOffDiagonalBudgetClosed

clayPromotion : Bool
clayPromotion = false

-- Expected polarities of the forensic conclusions.
earliestRecoveredFinalProblemSpecificationIsJuly26IsTrue :
  earliestRecoveredFinalProblemSpecificationIsJuly26 ≡ true
earliestRecoveredFinalProblemSpecificationIsJuly26IsTrue = refl

july26ClaimedSolvedIsFalse : july26ClaimedSolved ≡ false
july26ClaimedSolvedIsFalse = refl

r373SignedRouteBypassesNonnegativeMajorantIsFalse :
  r373SignedRouteBypassesNonnegativeMajorant ≡ false
r373SignedRouteBypassesNonnegativeMajorantIsFalse =
  R373.round373R222NonnegativeCoherentMajorantRequiredBySignedRouteIsFalse

r375R353IsDefinitionallyPhysicalIsTrue : r375R353IsDefinitionallyPhysical ≡ true
r375R353IsDefinitionallyPhysicalIsTrue = refl

r377OnlySubstantiveSignedPhysicalInputsRemainIsTrue :
  r377OnlySubstantiveSignedPhysicalInputsRemain ≡ true
r377OnlySubstantiveSignedPhysicalInputsRemainIsTrue = refl

r379LiteralGlobalDebtUsedIsTrue : r379LiteralGlobalDebtUsed ≡ true
r379LiteralGlobalDebtUsedIsTrue = refl

r410TargetIsLiteralR406IsTrue : r410TargetIsLiteralR406 ≡ true
r410TargetIsLiteralR406IsTrue = refl

r414SecondRemainderNeededIsFalse : r414SecondRemainderNeeded ≡ false
r414SecondRemainderNeededIsFalse = R414.round414SecondIndependentRemainderEstimateNeededIsFalse

r422FinalTargetIsLiteralR406IsTrue : r422FinalTargetIsLiteralR406 ≡ true
r422FinalTargetIsLiteralR406IsTrue = R422.round422FinalTargetIsLiteralR406FluxIsTrue

r423PositiveWienerEnvelopeRequiredIsFalse : r423PositiveWienerEnvelopeRequired ≡ false
r423PositiveWienerEnvelopeRequiredIsFalse = R423.round423PositiveWienerEnvelopeRequiredIsFalse
