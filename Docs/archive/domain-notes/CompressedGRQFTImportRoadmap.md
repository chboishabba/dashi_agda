# Compressed GR/QFT Import Roadmap

## Status

The current GR/QFT roadmap has a new import-compression lane.  The lane records
three external formal candidates as leverage points, but it does not promote
any local DASHI physics receipt from citation alone:

- `DCHoTT-Agda` / Wellen-Cherubini differential cohesion in Agda: candidate
  infrastructure for manifolds, formal disks, frame bundles, Cartan geometry,
  and torsion-free G-structure style metric-adapter work.
- Haag-Kastler stacks / locally covariant AQFT: candidate infrastructure for a
  local-algebra net receipt that avoids choosing one global Fock
  representation as the primitive QFT carrier.
- Schreiber's modal/cohesive HoTT physics programme: candidate ambient grammar
  for comparing carrier transport, metric adapters, gauge fields, and AQFT
  locality in one cohesive vocabulary.

The corresponding Agda surface is
`DASHI.Physics.Closure.ExternalFormalImportRoadmapReceipt`.  Its canonical
receipt records the timeline compression as real, but keeps
`theoremImportedIntoDASHI` false.  The DCHoTT dependency is now cloned locally
and the flat import shim typechecks.  The next bridge surface,
`DASHI.Geometry.LeviCivitaBridge`, also typechecks against the actual exported
`G-structures` socket.  This is a bridge socket, not theorem promotion: B0
geometric emergence, torsion-free specialisation, and Levi-Civita uniqueness
remain open.  `DASHI.Geometry.DCHoTTBridgeObligationIndex` now decomposes B0
into four open audit targets: carrier-to-formal-D-space, wave-coherence to
flat formal disk, refinement stability to G-structure, and G-structure to
Levi-Civita specialisation.  `DASHI.Geometry.ProObjectSemantics` now constructs
the DASHI-side B0.1 compatible-family/pro-object semantics: compatible limit
points, depth projections, refinement coherence, depthwise ball/agreement
laws, and the depth-zero formal-disk relation.  This still does not construct
transport-smooth sheaves, formal-disk-to-DCHoTT equivalence, a DCHoTT
manifold, G-structure, torsion-free specialization, or Levi-Civita adapter.
The Haag-Kastler stack surface is also now recorded as a
self-contained DASHI receipt at `DASHI.Physics.Closure.AQFTNetReceipt`; this
is a governance/intake surface, not a concrete QFT carrier.  The first
free-field witness and boundary surfaces are also now explicit:
`DASHI.Physics.Closure.KleinGordonAQFTReceipt` records the cited
Klein-Gordon stack witness, while
`DASHI.Physics.Closure.InteractingQFTBoundaryReceipt` records constructive
interacting nets as the first open QFT obligation.  `DASHI.Physics.QFT.AQFTTypedNetSurface`
adds the typed local-algebra interface that those receipts should refine
toward; it is still abstract and does not construct a C*-algebra, GNS state,
Born-rule adapter, or interacting theory.

Terminal hard-problem claims are now read through a three-gate formalism. Gate
1 is official/external authority: Clay still records Yang-Mills mass gap as
unsolved as of `2026-05-18`; Odusanya/`yangmills.dev` is a separate claimed
proof series under review; and any Zenodo dissolution/recontextualisation
record is an alternative interpretation/intake artifact, not the same claim.
Gate 2 is DASHI receipt authority: ST3 depth-recursion monotonicity is recorded
only as a local finite-carrier spectral-gap receipt. Gate 3 is continuum/terminal external authority:
Clay promotion, full GRQFT/TOE closure, cosmological constant, `G_DHR = G_SM`,
and absolute mass-scale closure remain open until their exact authority and
bridge receipts are inhabited.

The latest accounting separates DASHI local finite-carrier spectral-gap receipt
status from external authority. ST3 depth-recursion monotonicity is now recorded
only as local finite-carrier receipt evidence for DASHI. It is not a Clay promotion: journal, community, and
Clay review remain pending, and the strong terminal theorem plus Clay continuum
Yang-Mills claim remain false.
The four named strong-terminal obligations are B0.1 `Im` reflection/path
reflection, B0.3 `WeakBG` G-structure/Wellen binding, the
MassGap -> EnergyPositivity -> Bisognano-Wichmann -> TimeSlice bridge, and
DR/Doplicher-Roberts reconstruction under the DHR hypotheses. The six-postulate
minimal closure package additionally records `cStarCompletion` and external
mass-gap authority as guarded requirements. The DASHI depth-recursion
contraction route should now be described as internal monotonicity closure, not
as Clay authority or terminal promotion.

The current proof-landscape intake should be read as four active lineages, not
as four accepted proofs. Odusanya/Balaban RG is a claimed/preprint external
route whose lattice gap, Balaban induction, OS reconstruction,
compact-simple-group extension, and machine-verification stages remain under
review. Agawa holonomy non-local RG is a separate preprint/intake route. The
working Agawa-to-DASHI vocabulary map is provisional: holonomy or Wilson-loop
variables map to the B0.2 holonomy/flat-formal-disk surface; non-local blocks
and coarse-graining data map to depth/refinement and AQFT region restriction;
holonomy-defect or curvature observables map to the real operator-norm defect
surface; and scaling or continuum-limit variables remain Gate 3 data, not
finite-depth promotion. The dissolution/recontextualisation campaign remains
an alternative interpretation/intake surface. The DASHI mass-gap route is now
internally closed by ST3 depth-recursion monotonicity, while journal,
community, and Clay acceptance remain external authority obligations. Candidate
disproof or obstruction intake must stay visible:
Gribov-copy obstruction, IR slavery, and massless-gluon/scaling objections are
not answered by citation alone and must be discharged by the relevant typed
bridge or accepted external theorem before any continuum claim promotes.

The latest Agawa completion intake is now represented more sharply in the
terminal roll-up: its stable-IR-fixed-point claim and its finite
Gribov-ambiguity/Morse-theory claim are encoded as claimed formalism, with the
DASHI G4 prime-lane independence axiom supplying the intended geometric
completeness bridge. This narrows the shape of the mass-gap authority gate, but
it does not change the promotion status: `continuumClayMassGapPromoted` remains
false until accepted external authority reviews the internal ST3 receipt.

The DHR and time-slice gates are also deliberately separated. The
Doplicher-Roberts theorem is now treated as a clean categorical authority once
the five hypotheses are typed, but it reconstructs `G_DHR`; it does not compute
the prime-lane `laneDimension` function. The Moonshine tranche now supplies a
validated Agda receipt surface for a conditional authority-cited
`laneDimension` bridge: Ogg's theorem selects exactly the 15 supersingular
primes through the genus-zero property; the no-ghost theorem supplies orbifold
compatibility; Dong-Li-Mason supplies the Moonshine VOA weight-1 Lie-algebra
table authority; and the local proof bridge is `DASHIPrimeLaneEquiv`. This is
not a new theorem accepted by the mathematical or physics community; until the
bridge is inhabited, it is not an unconditional `G_DHR = G_SM` or Standard
Model derivation. The `p = 7`
high-energy `SU(2)_R` bridge is tracked separately from the low-energy Standard
Model group. The
Bisognano-Wichmann theorem for nets feeds the time-slice theorem only modulo
net, vacuum, covariance, and energy-positivity hypotheses; it is not an
unconditional AQFT promotion.

The adapter/stress-energy layer is now receipt-surface complete for the current
gate accounting: no-natural-state-selection, no-preferred-vacuum, and Wald
coefficient selection are recorded as complete receipt surfaces. The final
Adapter4 inventory is `{G_Newton, v_Higgs, f_a, compact universe}`. This is a
reduction of the open empirical inventory, not a strong terminal theorem:
`weakTerminalClaimPromoted` remains modulo the minimal postulates/open gates and
`terminalClaimPromoted` remains false.

Assuming the six safe postulates are accepted and the weak terminal claim is
inhabited, the next roadmap tranche is ordered by leverage. First comes the
conditional `laneDimension` receipt/bridge package. The formal-group-only
calculation must be corrected in all downstream prose: the height-2 formal
group and its Dieudonne module alone give an `SU(2)` compact-real-form shape,
not the desired
`U(1), SU(2), SU(3), SU(2)_R` table. The Serre-Tate and conductor/Hecke routes
have failed to give a clean formula or remain finite computation targets. The
current Moonshine proof route is conditional: Ogg genus-zero gives the 15
prime lane set, no-ghost gives orbifold compatibility, Dong-Li-Mason gives the
weight-1 Lie-algebra table, and `DASHIPrimeLaneEquiv` must identify that
external table with the DASHI prime-lane dimension function. Under that bridge
`laneDimension` may be recorded only as a DASHI-local validated receipt claim;
without it, no unconditional formula is proved.

Second comes matter-prime-lane accounting. After gauge lanes `{2,3,5,7}`, the
listed remaining supersingular primes are `{11,13,17,19,23,29,31,41,47,59,71}`;
that is eleven lanes, not twelve. The matter-generation grouping is therefore
an open accounting issue. The roadmap must not claim three full four-prime
matter generations until a later receipt explains the missing lane, duplicated
role, or revised grouping convention. Third comes the hierarchy/final Adapter4
decision: SUSY may be recorded as Higgs-scale stabilization only, the relaxion
route currently has no successful DASHI receipt, and accepting `v_Higgs` as
irreducible is a governance decision that leaves the final Adapter4 inventory
at `{G_Newton, v_Higgs, f_a, compact universe}`.

Fourth, the terminal flip remains exactly conjunctive:
`continuumMassGapProved and laneDimensionTheorem and FinalAdapter4Accepted`.
The mass-gap component now has DASHI-internal ST3 depth-recursion monotonicity
closure, but still requires external journal/community/Clay acceptance before
Clay promotion; the Moonshine lane bridge does not change Clay governance or
`terminalClaimPromoted = false`. Fifth, the paper architecture should be
split into seven stages: Paper 1 is submittable now as the typed receipt system
and honest-frontier architecture; Paper 2 is gated by B0.1-B0.3 geometry;
Paper 3 by AQFT quotient, time-slice, DHR category construction, and
Reeh-Schlieder accounting; Paper 4 by the conditional `laneDimension`
receipt/bridge package, Serre-Tate-DHR bridge, and Pati-Salam refinement;
Paper 5 by matter lanes and Yukawa textures; Paper 6 by external acceptance of
the internally receipted
mass-gap closure; and Paper 7 by the terminal composition with the final
Adapter4 inventory.

For publishability, this compresses further into an honest three-zone map.
Paper 1 is the now-publishable receipt/governance and honest-frontier paper.
Papers 2-3 are an execution sprint after the remaining flag split plus AQFT/DHR
citation, quotient, and time-slice cleanup: Paper 2 should isolate the B0
geometry bridge, and Paper 3 should package the AQFT carrier quotient, Cauchy
evolution/time-slice target, DHR citation/sector surface, and the
Reeh-Schlieder closure already supplied by existing receipts and dependencies.
Papers 4-5 and 7 are not sprint write-ups; Paper 4 is bridge-gated on
`DASHIPrimeLaneEquiv`/Serre-Tate-DHR/Pati-Salam, while Paper 6 is internally
receipted but externally Clay-pending. The weak terminal claim remains gated by
the safe postulates/open receipts, and `terminalClaimPromoted` remains false.

The latest Papers 2-7 obligation map should be maintained as named discharge
targets rather than a stronger publication claim. Paper 2 carries P2-A and
P2-B as immediate `DASHIPrimeLaneEquiv` closure items: inhabiting that bridge
may close those two local obligations, but it does not by itself derive the
Standard Model, promote terminal closure, or alter Clay governance. Paper 3
carries M3-A, M3-B, and M3-C for the matter/AQFT-facing package: the map must
name the carrier or quotient target, the external authority/citation boundary,
and the Reeh-Schlieder dependency-accounting receipt. Paper 4 carries G4-A and
G4-B for gauge and lane dimension: the Moonshine bridge is separate from any
Pati-Salam refinement or low-energy Standard Model comparison. Paper 5 carries
GR5-A and GR5-B for geometry/stress-energy: B0/GR geometry and Wald
stress-energy authority stay distinct. Paper 6 carries G6-A and G6-B for
mass-gap governance: DASHI local finite-carrier ST3 receipt evidence and external
journal/community/Clay acceptance are separate gates. Paper 7 is
implementation/governance only, covering terminal composition staging, final
Adapter4 inventory, and publication controls while keeping
`terminalClaimPromoted = false` and `continuumClayMassGapPromoted = false`.

## Professor-Facing Roadmap Wording

The complete-unification-paper roadmap should be stated as a compressed
construction programme, not as a completed theorem:

> DASHI currently stages a finite-depth/refinement carrier programme whose next
> mathematical target is a condensed/profinite-style comparison category:
> B0 should identify the inverse-limit carrier with an appropriate formal-disk
> geometry, AQFT should then build local algebras over restricted carrier
> regions with time-slice control, and the final GR/QFT composition should be
> admitted only after the metric/signature, Born-state, vacuum-selection, and
> coupling-calibration adapter no-go obligations are proved or externally
> discharged.

The caveats are part of the statement.  B0.1 now has a constructed DASHI-side
compatible-family/pro-object semantics receipt in `ProObjectSemantics.agda`,
but B0.1 still does not prove transport-smooth sheaves, formal-disk-to-DCHoTT
equivalence, or a DCHoTT manifold.  B0.2/B0.3 remain target sockets.  The AQFT
time-slice surface is a target for Cauchy evolution, not a constructed local
algebra net.  The adapter irreducibility index records theorem obligations,
not no-go theorems already proved.  The terminal GRQFT claim remains
non-promoted until the B0 bridge, AQFT carrier algebra, adapter no-go
obligations, stress-energy interface, and empirical/authority receipts are all
inhabited.

The remaining formalism implementation lanes have now landed as target surfaces,
still deliberately narrower than a completion claim.
`TransportSmoothFormalDiskSurface.agda` records the B0.1 analytic surface for
transport-smooth functions, clopen-ball sites, sheaf-style locality/gluing, the
first-order approximation target, formal-disk comparison, and tangent/graded
piece binding. `FlatFormalDiskHolonomySurface.agda` records the B0.2 normed
fibre, operator-norm defect, summability, finite-area loop, nonabelian-Stokes,
holonomy, path-independence, and flat-connection targets.
`GStructureLeviCivitaBindingSurface.agda` records the B0.3 frame/metric tower,
SO(3,1) reduction, first-prolongation-zero, and Wellen/Levi-Civita sockets.
`AQFTCarrierAlgebraQuotientSurface.agda` now records the quotient operations,
transport equivalence, colimit universality, isotony/G6/descent, and
Cauchy/time-slice intermediate targets. `MatterRepresentationReceiptSurface.agda`,
`StressEnergyBridgeReceiptSurface.agda`, and
`TerminalCompletenessGrammarSurface.agda` record matter, stress-energy/Wald, and
terminal grammar sockets. The terminal grammar is allowed to expose finite,
constructor-backed classification evidence and derivation-tree availability for
the current statement list. Its current finite classifier totality/soundness and
finite derivation-availability receipt are now inhabited, but terminal TOE
remains a blocked completeness target rather than an inhabited derivation. These
surfaces do not claim B0, AQFT time-slice, stress-energy, GRQFT, Standard Model,
or TOE completion; the terminal promotion gate remains false until the exact
authority receipts are inhabited.

The missing-primitive intake pass narrows several blockers without closing the
bridge. `RealAnalysisAxioms.agda` is a postulated authority interface for the
real/operator-norm/Banach/geometric-series facts needed by B0.2; it is not a
local analytic proof. The bundled DCHoTT `Im` and `FormalDisk` modules are now
visible through the shim, but the DASHI formal disk only has a comparison socket
until maps, roundtrips, and equivalence are constructed. The SO(3,1)
first-prolongation-zero calculation is now local abstract-index evidence, but
the Wellen theorem import and DCHoTT G-structure binding remain open. AQFT
quotient work uses a non-cubical setoid quotient surface rather than global
cubical flags; C*-completion, GNS, and full AQFT promotion remain blocked. DHR
now has localised-endomorphism, transportability, intertwiner,
statistics-operator, and Doplicher-Roberts authority sockets, but the
`laneDimension` computation still controls any `G_DHR = G_SM` claim. The
state/vacuum/Wald surfaces expose primitive witnesses and ambiguity parameters
only; no Born-rule, vacuum, stress-energy, GRQFT, or TOE promotion follows.
After the second audit, the active frontier is sharper: B0.2 can cite an
authority-backed holonomy theorem socket but not a local proof; B0.1 has a
one-way DASHI-to-DCHoTT depth-zero formal-disk map but not an equivalence;
B0.3 has local SO(3,1) first-prolongation-zero evidence and is blocked next on
the actual DCHoTT G-structure/Wellen binding; AQFT has setoid quotient
extensionality for the transport relation but not C*-completion or a concrete
time-slice algebra; DHR primitives are typed and the Standard Model comparison
is concentrated in `laneDimension`; adapter/stress-energy blockers are now
authority-token or Wald-coefficient selection boundaries.
The Tier B / Paper 2 carrier-geometry sprint accounting keeps B0.1-B0.3 as
promote-after-sprint targets, not promoted receipts.  The local Agda flag
architecture must stay split: `--cohesion` and `--cubical` are incompatible in
the current local setup, so cohesive carrier/DCHoTT modules and cubical
quotient/path modules must compile separately and meet only through a
proof-erasing interface of postulates/types.  `WeakBGCorrespondence` also
needs a precise Wellen DCHoTT thesis theorem and page citation before it can
serve as an authority citation.
The Worker 6 gate pass makes those boundaries explicit in the typed surfaces:
no-natural-state-selection and no-preferred-vacuum are receipt surfaces tying
the theorem target to primitive witnesses and constructorless authority tokens,
not no-go theorems; Wald `c1/c2/c3` are adapter parameters for local curvature
ambiguity, not selected physical coefficients; and the terminal weak claim is
an open-status grammar gated by B0, AQFT, DHR, `laneDimension`,
stress-energy/Wald authority, and adapter no-go authority.
Under the latest accounting, that weak terminal grammar is promoted only modulo
the six-postulate minimal closure package; it does not discharge the four named
strong-terminal obligations, the C*-completion authority, or the uniform
mass-gap quantifier exchange.
The current sequestering v2 wording is narrower: it may reduce the local Wald
`c1` contribution, but no Lambda receipt can promote without the
compact-universe premise, shift-symmetry authority, and explicit `c2/c3`
inputs. Yukawa-sector ratio-form material is likewise bounded: it may promote
only under MatterPrimeLane/Froggatt-Nielsen/Frobenius hypotheses, while the
Higgs vev remains an irreducible adapter input.

The next professor-facing layer is now split into five target-only surfaces.
`DCHoTTBridgeObligationIndex.agda` records the tangent-category structure
needed before the pro-object can be compared to the DCHoTT tangent exponential.
`CharacteristicClassReceiptSurface.agda` records AHSS obstruction, Chern-Weil,
Pontryagin, and Euler targets downstream of B0 and Levi-Civita.
`ModularTheoryReceiptSurface.agda` records GNS/von-Neumann, Tomita-Takesaki,
KMS, Unruh/Rindler, and Bisognano-Wichmann targets.  `DHRGaugeReceiptSurface.agda`
records Haag duality, controlled gauge duality failure, DHR selection,
Tannaka reconstruction, Standard Model matching, and prime-lane condensation
targets.  `OPEConformalBootstrapReceiptSurface.agda` records OPE,
dilatation/scaling, conformal bootstrap, and mass-gap-as-spectral-output
targets.  These are roadmap receipts only; they do not promote characteristic
classes, modular theory, DHR reconstruction, Standard Model matching, bootstrap
closure, mass gap, GRQFT, or TOE claims.

`DASHI.Physics.Closure.KTheoryNovikovReceiptSurface` adds the professor-facing
K-theory/Novikov layer as typed target surfaces only: Novikov/assembly-map
input, K-theory charge classification through a future DHR adapter, a six-term
exact-sequence bulk-boundary receipt target, and a dependency graph linking B0,
AQFT, DHR, K-theory, mass-gap, and Lambda obligations.  These surfaces do not
construct an assembly map, classify charges, prove a bulk-boundary exact
sequence, solve mass gap, calibrate Lambda, or promote GRQFT.

The arithmetic/representation-theory extension is now split into five more
target-only surfaces. `MoonshinePrimeLaneReceiptSurface.agda` records the
Chen-prime observation over the 15 tracked Monster/supersingular lanes plus the
genus-zero/Hauptmodul and McKay-Thompson amplitude sockets.
`VOAMoonshineBridgeReceiptSurface.agda` records VOA, Moonshine VOA,
chiral-CFT-net, holomorphic-factorisation, K3-compactification, and 4D
effective-theory targets. `WittenIndexSUSYBoundarySurface.agda` records
spin-structure, SUSY, Witten-index, observed-SM/SUSY-status, and
cosmological-constant implication targets. `GNSFellRepresentationSurface.agda`
records GNS universality, state-observable duality, folia, superselection
representation classes, Fell topology, and KMS-family proximity targets.
`PrimeLaneGaugeAssignmentReceiptSurface.agda` records the 15-lane product,
Chen pairing/cluster, DHR-computation-vs-adapter, residual `H`, exact Standard
Model match, and nontrivial residual branches.  These surfaces are governance
and proof-target sockets only; they do not promote a Chen/Moonshine theorem,
VOA-to-AQFT bridge, K3 oxidation, SUSY result, GNS/Fell theorem, prime-lane
gauge assignment, Standard Model match, GRQFT receipt, or TOE claim.

K3 geometry, Seiberg-Witten/S-duality/Langlands, arithmetic cohomology, and
supersingular-K3/Frobenius/primes-to-gauge comparisons are likewise roadmap
targets unless and until separate DASHI Agda receipts formalize the exact
objects, maps, hypotheses, and imported theorem boundaries.  Any seven-step or
similar explanatory chain in this area must be read as an external/reference
programme, not as steps already internally proved by DASHI.  In particular,
supersingular primes and Frobenius traces may guide gauge-lane hypotheses only
as target sockets; they do not by themselves construct a Standard Model group,
hypercharge embedding, anomaly cancellation, Langlands correspondence, S-dual
QFT, GRQFT receipt, or TOE closure.

`DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface` and
`DASHI.Physics.Closure.TerminalOpenProblemStatusSurface` record the updated
terminal hard-problem status. The official Clay status is still unsolved as of
`2026-05-18`, so Clay/external Yang-Mills promotion remains open. DASHI now
records a separate internal ST3 depth-recursion/Banach receipt for the
continuum mass-gap dependency; this is not Clay authority.
Odusanya/`yangmills.dev` is tracked as a separate external 2026
Balaban-RG/machine-verification claimed proof series under review, with no
Clay acceptance. Any Zenodo
dissolution/recontextualisation record is an alternative intake artifact, not
a substitute for the Odusanya series, Clay acceptance, or a local proof. The
Balaban/Odusanya route is broken into typed intake stages: lattice
transfer-matrix gap, Balaban master induction, Osterwalder-Schrader
reconstruction, compact-simple-group extension, and machine-verification
authority. A finite-depth DASHI mass-gap receipt may promote only as a bounded
local statement when its typed witness is inhabited; it does not solve the
continuum Clay problem. The cosmological constant remains an open
Adapter2-times-Adapter4 calibration problem; SUSY cancellation, landscape
selection, and sequestering are strategy targets only. Sequestering v2 may
lower the local `c1` term, but still requires compact-universe,
shift-symmetry, and `c2/c3` inputs before a Lambda receipt can promote.
`G_DHR = G_SM` remains an open localized-transportable-endomorphism,
statistics-operator, Doplicher-Roberts reconstruction, and prime-lane
automorphism computation. Born/coupling no-go arguments are proof strategies
until formalized as adapter irreducibility theorems; the current surfaces name
the Gleason/Busch no-state-selection boundary and the beta-function
matter-representation boundary. Strong CP/Peccei-Quinn is an Adapter4
sub-problem target with theta-vacuum, axion-window, and K-theory
instanton-character sockets, not a solved calibration receipt.
Yukawa ratio-form statements may be promoted only under
MatterPrimeLane/Froggatt-Nielsen/Frobenius hypotheses; the Higgs vev and
absolute mass scale remain irreducible adapter inputs.

## DCHoTT Intake State

The local clone is:

- path: `DCHoTT-Agda`
- remote: `https://github.com/felixwellen/DCHoTT-Agda.git`
- commit: `ca8c755af0b26f8f50c5a60d3b7f9384a26f5d0e`
- local Agda: `2.6.4.3`
- stdlib lib file: `/usr/share/agda/lib/standard-library.agda-lib`
  (`standard-library-2.0`)
- license file: not present in the cloned repository root; license remains an
  intake item before vendoring or redistribution claims

The clone uses a flat module layout.  Imports are therefore:

```agda
open import Manifolds
open import FormalDiskBundle
open import G-structure
```

not `DCHoTT.Manifolds` or other namespaced forms.  The project library file
adds `DCHoTT-Agda` to `include:` so `DASHI.Geometry.DCHoTTImportShim`
can typecheck these imports.

The immediate exported bridge sockets are now identified:

| DCHoTT module | Exported socket | DASHI use |
| --- | --- | --- |
| `HomogeneousType` | `homogeneous-structure-on_` | model homogeneous carrier for manifold targets |
| `Manifolds` | `_-manifold`, `homogeneous-space-as-manifold` | manifold socket and homogeneous example |
| `FormalDiskBundle` | `formal-disk-bundle`, `T∞`, `T∞-as-dependent-type` | infinitesimal/formal-disk carrier bridge |
| `G-structure` | `groups-over-automorphismgroup-of_`, `G-structures`, `G-str→` | G-structure lift/pullback surface |

`G-structure.agda` contains a comment saying the code will work toward
torsion-free G-structures, but this clone does not expose a
`TorsionFreeGStructure` identifier.  The Phase 2 bridge must therefore target
the currently exported `G-structures` surface first, then add or import the
torsion-free/Levi-Civita specialization separately.

Flag accounting is part of the bridge boundary.  The current local setup does
not admit one module that is both `--cohesion` and `--cubical`; carrier geometry
and cubical quotient work must remain separately compiled, with any connection
expressed through erased postulated/type interfaces rather than direct
mixed-flag imports.

`DASHI.Geometry.LeviCivitaBridge` is now that first surface.  It imports the
real DCHoTT `G-structures` socket, links the existing DASHI flat
`GRConcreteLeviCivita` prerequisite and downstream
`DiscreteEinsteinTensorCandidate` diagnostic, and records B0 as the first open
obligation.  It intentionally does not construct an Einstein tensor, GR
promotion, G6/W7 promotion, or a GRQFT closure receipt.

## Local Overlap Audit

The repo is not empty on these themes.  The audit distinguishes local overlap
from imported external formal infrastructure:

| Surface | In repo? | Current reading |
| --- | --- | --- |
| Flat Levi-Civita prerequisite | yes | `GRConcreteLeviCivita.agda` closes only the selected flat Minkowski finite-r prerequisite. |
| Non-flat Levi-Civita / metric adapter | no | The non-flat route is still blocked on scalar algebra, Christoffel-from-metric, Ricci, and Einstein-tensor laws. |
| GR/QFT consumer obligation | yes | `GRQFTConsumerNextObligation.agda` names downstream fields and keeps the promotion token constructorless. |
| AQFT net receipt | yes | `AQFTNetReceipt.agda` records the point/descent/isotony/causality/time-slice contract from arXiv:2404.14510v2, while keeping GNS/vacuum, Born rule, representation choice, and interacting QFT open. |
| Klein-Gordon free-field witness | yes | `KleinGordonAQFTReceipt.agda` records Theorem 4.41 as a cited witness surface, while keeping the concrete algebra-net reconstruction, vacuum selection, and Born rule open. |
| Interacting-QFT boundary | yes | `InteractingQFTBoundaryReceipt.agda` names constructive interacting local algebra nets, renormalisation, and coupling calibration as open obligations. |
| Adapter-boundary matrix | yes | `Docs/PhysicsLaneMaturityMatrix.md` already records metric, representation, GNS/vacuum, Born-rule, and calibration boundaries. |
| DCHoTT dependency / import shim | yes | `DCHoTT-Agda` is cloned locally and `DASHI.Geometry.DCHoTTImportShim` typechecks against its flat modules. |
| DCHoTT Levi-Civita bridge socket | yes | `DASHI.Geometry.LeviCivitaBridge` typechecks against `G-structures` and records B0 as first open obligation. |
| DCHoTT B0 obligation index | yes | `DASHI.Geometry.DCHoTTBridgeObligationIndex` splits B0 into four open sub-obligations, records B0.1/B0.2/B0.3 target surfaces, and constructs no B0 promotion receipt. |
| B0.1 DASHI-side pro-object semantics | yes | `DASHI.Geometry.ProObjectSemantics` constructs compatible pro-object points, projections, refinement coherence, depthwise agreement/ball laws, and the depth-zero formal-disk relation without proving DCHoTT smoothness or formal-disk equivalence. |
| AQFT typed net surface | yes | `DASHI.Physics.QFT.AQFTTypedNetSurface` introduces typed region/local-algebra sockets for isotony, causality, time-slice, and descent while keeping concrete C*-algebras, GNS, Born, vacuum, and interacting QFT open. |
| K-theory / Novikov target surface | yes | `KTheoryNovikovReceiptSurface.agda` records Novikov assembly, K-theory charge classification, six-term bulk-boundary, and B0/AQFT/DHR/K-theory/mass-gap/Lambda dependency targets without promotion. |
| Terminal open-problem status surface | yes | `TerminalOpenProblemStatusSurface.agda` records the three-gate status and the current proof landscape: Odusanya/Balaban RG as claimed/preprint intake, Agawa holonomy non-local RG as separate preprint/intake with only a provisional DASHI variable map, dissolution/recontextualisation as alternative finite/discrete-lattice campaign intake, and the DASHI-internal ST3/Banach finite-carrier receipt. Clay Yang-Mills remains officially unsolved as of `2026-05-18`; Gribov-copy, IR-slavery, and massless-gluon/scaling objections remain candidate obstruction checks; DASHI local finite-depth/finite-carrier spectral-gap receipt does not close continuum/Clay authority; Lambda strategies, `G_DHR = G_SM`, Higgs-vev scale, and strong CP/PQ remain open. |
| DCHoTT imported theorem | no | The shim sees manifold/formal-disk/G-structure surfaces but imports no torsion-free Levi-Civita or B0 theorem. |

So the corrected state is: DASHI already has substantial native bridge targets
for the import work, DCHoTT flat import resolution and the first
`G-structures` bridge socket are now live, B0 has a four-part obligation index,
and the AQFT stack contract, typed local-algebra surface, Klein-Gordon
free-field witness, and interacting-QFT boundary are locally receipted.  No
DCHoTT theorem, concrete AQFT algebra net, interacting QFT
construction, or cohesive theorem has been consumed yet.  The next action is
replacing the B0 postulate and refining the AQFT receipts into typed carriers,
not a from-scratch conceptual design pass.

## Roadmap Compression

| Stage | Previous stance | Compressed stance | Promotion boundary |
| --- | --- | --- | --- |
| Stage 2 metric adapter | build Levi-Civita/metric-adapter machinery locally | import or bridge to DCHoTT torsion-free G-structure and frame-bundle infrastructure | only after exact dependency intake and Agda bridge typecheck |
| Stage 3 QFT carrier | start from Fock/CCR/CAR carrier and hit representation issues early | refine the AQFT net/descent receipt into typed local-algebra carriers; defer GNS/vacuum/Born choices to adapters | AQFT net does not solve interacting QFT or Born/vacuum selection |
| Stages 4-6 GRQFT | compose from locally built geometry/QFT pieces | use cohesive/modal HoTT as the comparison language for geometry, gauge, and locality | Clay Yang-Mills remains officially unsolved; Odusanya/`yangmills.dev` and Zenodo records are external/alternative intake only; finite-depth mass-gap receipts do not solve continuum mass gap; no cosmological-constant, DHR=SM, Higgs-vev, coupling/Born no-go, strong-CP, or TOE promotion follows |

## Execution Plan

1. Complete dependency intake for `DCHoTT-Agda`.
   The clone and flat import shim are present.  Remaining intake is license
   clarification and compatibility notes beyond the minimal shim.

2. Replace the B0 bridge postulate with a proof or imported theorem.
   `DASHI.Geometry.DCHoTTImportShim` proves the flat imports resolve, and
   `DASHI.Geometry.LeviCivitaBridge` proves the actual `G-structures` socket
   can be targeted.  `DASHI.Geometry.DCHoTTBridgeObligationIndex` fixes the
   proof checklist so this does not remain one opaque postulate and now records
   the B0.1 compatible family, B0.2 flat-disk, and B0.3 frame/metric/G-structure
   target surfaces. `DASHI.Geometry.ProObjectSemantics` constructs the
   DASHI-side B0.1 compatible-family semantics; the next deliverable is the
   B0.1 analytic surface/specification deepening, the
   transport-smooth/formal-disk-to-DCHoTT adapter, B0.2 holonomy /
   flat-formal-disk target work, then the proof-grade B0.3 bridge from DASHI
   wave-coherent/refinement-stable transport into the DCHoTT G-structure socket,
   followed by the torsion-free/Levi-Civita specialisation.

3. Write the DASHI-to-DCHoTT translation layer.
   Map DASHI carrier, transport receipt, curvature receipt, admissibility, and
   promotion gates into the DCHoTT/cohesive vocabulary.  Only after this bridge
   typechecks can `LeviCivitaAdapterReceipt` cite an imported theorem.

4. Refine the `AQFTNetReceipt` surface.
   The current receipt names point/descent, isotony, causality, time-slice, and
   Klein-Gordon witness surfaces.  `KleinGordonAQFTReceipt` and
   `InteractingQFTBoundaryReceipt` now separate the free-field witness from the
   interacting-field boundary.  `DASHI.Physics.QFT.AQFTTypedNetSurface` now
   supplies the typed open-region/local-algebra/morphism/descent interface; the
   next deliverable is wiring the governance receipts to this surface and
   deepening the carrier/quotient/directed-colimit/time-slice specifications
   while keeping GNS state, vacuum selection, Born rule, renormalisation, and
   empirical representation choices as explicit adapters.

5. Connect both bridges to existing GR/QFT consumer obligations.
   The target is better staging for `GRQFTConsumerNextObligation`, not a
   constructed `GRQFTClosurePromotionReceipt`.  Matter/stress-energy work should
   remain grammar and compatibility scaffolding until a W4 authority-backed
   source receipt, stress-energy conservation/compatibility law, and shared
   carrier restriction are supplied.

6. Stage the K-theory / Novikov layer after AQFT and DHR.
   Use `KTheoryNovikovReceiptSurface.agda` as the target index for assembly-map,
   charge-classification, and six-term bulk-boundary work.  The first real
   deliverables remain concrete AQFT carrier algebra, DHR sector adapter, and
   K-theory operations; the current receipt is a dependency graph only.

7. Track terminal hard-problem intake without promotion.
   `TerminalOpenProblemStatusSurface.agda` should be the single status surface
   for Odusanya/Balaban RG review state, Agawa holonomy non-local RG intake and
   variable mapping, dissolution/recontextualisation intake, DASHI per-depth
   pro-object and ST3/Banach mass-gap receipts, candidate disproof/obstruction intake,
   cosmological-constant strategy targets, `G_DHR = G_SM`, Born/coupling no-go
   proof strategies, and strong CP/PQ. The next real deliverables are accepted
   authority for any external theorem, local Agda formalization, uniform
   lower-bound and continuum bridge receipts, and explicit obstruction
   discharges; citation alone does not alter `terminalClaimPromoted = false`.

8. Track the post-weak-terminal tranche plan without promotion.
   The next admissible mathematical implementation sequence is
   conditional `laneDimension` receipt/bridge package, matter lane accounting,
   final Adapter4 hierarchy decision, terminal flip condition, then the
   seven-paper publication split. `laneDimension` now has a validated Agda
   receipt surface for a conditional Moonshine authority bridge: Ogg
   genus-zero supplies the 15 primes, no-ghost supplies orbifold compatibility,
   Dong-Li-Mason supplies the weight-1 Lie-algebra table authority, and
   `DASHIPrimeLaneEquiv` must identify that table with DASHI lane dimensions.
   Keep the formal-group-only `SU(2)` correction visible, keep the eleven-lane
   matter caveat visible, record ST3 depth-recursion monotonicity as
   a DASHI local finite-carrier spectral-gap receipt, and keep Clay/terminal promotion false
   until external authority accepts it.

## Stop Rule

Do not replace an open obligation with a citation.  Imported formal work can
compress a lane only when the dependency is present, the bridge typechecks, and
the local receipt records the imported theorem boundary.  Until then, the
compressed roadmap is a high-leverage work plan, not a physics closure result.
