# Archive Topic Integration Plan

Status: paper-writing coordination plan; docs-only; non-promoting.

This plan records the archive and NotebookLM topics that should affect Paper 1
assembly. It is a routing document, not a theorem, receipt, authority token, or
claim surface. Repo-local Agda modules and current gate docs remain the source
of truth for paper claims.

## Thesis

Paper 1 is a physics-unification paper. Typed claim governance, obstruction
semantics, and fail-closed promotion are the enforcement architecture that
makes the unification program publishable without laundering diagnostics,
request surfaces, or future-work routes into completed physics.

The correct empirical wording is:

> DASHI has an inhabited bounded W3 `t43` below-Z Drell-Yan comparison-law
> receipt, promoted only for that local comparison surface. It does not pass
> the stricter falsification-lane threshold or the later strict log-covariance
> protocol; those diagnostics identify the next shape-law obstruction.

## Topic Location Map

| Topic | Paper destination | Repo/source anchors | Claim boundary |
|---|---|---|---|
| Physics-unification thesis | `sections/01_intro_conclusion.md`, `sections/08_constructive_toe_framing.md`, `Paper1_Manuscript.md` | `README.md`, `Docs/CurrentGateStatus.md`, this folder's `README.md` and `ClaimLedger.md` | Main thesis. Do not reduce Paper 1 to a governance-only paper. |
| Typed governance / obstruction semantics | `sections/02_governance_method.md`, `sections/11_physics_language_containment.md` | `ClaimLedger.md`, `Docs/CurrentGateStatus.md` | Enforcement architecture and claim-control layer, not the whole paper thesis. |
| Drell-Yan W3 bounded `t43` receipt | `sections/05_empirical_appendix.md`, manuscript empirical section | `DASHI/Physics/Closure/HEPDataW3ComparisonLawReceipt.agda`, `DASHI/Physics/Closure/DrellYanAdjacentRatioEmpiricalLaneReceipt.agda` | Positive bounded W3 comparison-law lane: `chi2/dof = 2.1565191176`, threshold `4.0`, `t43` only. |
| Strict Drell-Yan diagnostics | `sections/05_empirical_appendix.md`, exact gaps table | `DASHI/Physics/Closure/DrellYanStrictLogLinearSubspaceReceipt.agda`, `scripts/data/outputs/t43_strict_log_*_20260515.json` | Negative strict diagnostic, not an override of the bounded W3 receipt. |
| W5 CT18 observable mismatch | Empirical gaps subsection | `Docs/CurrentGateStatus.md`, W4/W5 DY docs and scripts | Explicitly different observable/regime; not W5 closure. |
| 15 SSP / JMD / Monster provenance | `sections/07_provenance_lit.md`, short carrier-background paragraph | `SourceLedger.md`, archive review, JMD/outreach docs | Attribute 15 SSP coordinate input to JMD. No Monster/moonshine closure claim. |
| Base369 / trit / p-adic carrier intuition | Background or appendix | Archive review; repo trit/base modules where cited | Expository substrate only unless tied to exact Agda surfaces. |
| Hensel lifting / p-adic convergence | Background / mathematical constructions | p-adic/UFT archive topics; current ultrametric docs | Explain refinement without polarity flip; no convergence theorem unless repo-backed. |
| UFT-C / lattice logic / SWAR | Compression/semantic geometry appendix | NotebookLM and worklog sources; `SourceLedger.md` | Implementation/reference machinery, not a performance or proof claim. |
| Markov-compatible projection | Appendix or short discussion subsection | Archive Markov compatibility hits | DASHI may be Markov after quotienting history into a typed joined state; not a classical upstream Markov chain. |
| Orbit-shell / Lorentz-signature family | Future-work appendix | Math outreach docs, archive orbit-shell/B4/signature material | Future route only; useful to show non-vacuous unification path. |
| G2/G3/G6/E8 formal core | `sections/03_formal_core.md`, manuscript construction section | `Docs/CurrentGateStatus.md`, relevant Agda modules | Positive only where inhabited; preserve typed blockers. |
| Cross-domain variational spine | `sections/15_cross_domain_variational_spine.md`, discussion/outlook | `DASHI/Physics/Closure/CrossDomainVariationalSpine.agda`, `ClaimLedger.md` | Shared typed schema/theorem-target boundary only. |
| Wave/unitary lift | Future-work appendix | Archive wave/unitary hits | High overclaim risk; not new quantum mechanics. |
| Energy vacua / Standard Model emergence | Future-work only | Archive/NotebookLM | Too broad for Paper 1 positive claims. |
| DNA/brain/sofic/perception | Future appendix or exclude | `BrainConnectomeFMRIObservationQuotient.agda`, `DevelopmentalGenomicInverseBridge.agda` | Non-promoting theorem targets only. |
| Trading/legal/social/cultural material | Exclude from Paper 1 body | Archive/NotebookLM | Dilutes the physics-unification paper. |

## Source Handles

- Robust-context thread: `SOTA Paper Publishing Tools`,
  online UUID `6a05676e-f358-83ec-a178-3dcc5f537a9a`, canonical archive ID
  `edac27557dd34bf9ab9f4563525aecc742c976a1`.
- Robust-context thread: `As you can see in the pumls there are many blockers`,
  online UUID `8daefbbb-e5e4-4c27-92c2-9cf7e9de0aa3`, canonical archive ID
  `9fd02df16462bcb491ed4c155b1a4e73ba0fb173`.
- NotebookLM IDs already recorded in `SourceLedger.md`.

## Integration Rules

- Update `ClaimLedger.md` whenever a manuscript sentence needs positive
  wording, blocked wording, or future-work routing.
- Do not use archive, NotebookLM, or worklog text as semantic authority.
- Keep the bounded W3 receipt and strict-log diagnostics as separate surfaces.
- Treat older NotebookLM or archive statements that frame Paper 1 as only a
  formal-methods collider paper as risk warnings, not as the current thesis.
- If a topic is not anchored in repo-local theorem, receipt, audit, diagnostic,
  or blocker surfaces, route it to appendix, future work, or exclusion.
