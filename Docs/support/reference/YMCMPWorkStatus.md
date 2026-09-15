# Yang–Mills CMP Work Status

Status: navigation / archaeology companion to `YMRHPRRoundArchaeologyAudit.md`. **Not theorem authority and not a Clay-completion claim.**

Purpose: stop repeated proof-search from treating `CMP109`, `CMP116`, `CMP119`, or `CMP122` as one undifferentiated open task. The paper-level source authority, most carrier dictionaries, and downstream compiler plumbing have already been developed across many PRs. Future Pareto search should reopen a CMP-labelled object only when a current consumer exposes a specific unpaid same-object physical/source instantiation.

## Executive rule

**DO NOT reopen “formalise CMP109/116/119/122” as a generic task.**

Use this classification instead:

| Source family | Repository status for current search | What is already owned | What may still be legitimately open |
|---|---|---|---|
| CMP109 | SOURCE/COMPILER LARGELY OWNED | regular small-field effective-action lane, differentiated coordinate machinery, Eq.(5.1)-facing continuation interfaces, downstream BC/response compilers | a *specific literal physical differential/source identification* required by a live consumer; not CMP109 as a whole |
| CMP116 | SOURCE/COMPILER LARGELY OWNED | localization/cluster-expansion continuation, marked-source/localization machinery, common continuation interfaces, Row-C donor machinery | a *specific carrier realization, uniform analytic radius, marked-row or quantitative physical estimate* if still demanded by the current consumer |
| CMP119 | SOURCE OBJECT/DICTIONARY LARGELY OWNED | complete-density dictionary, raw source state, finite-beta construction, `rho_k/U_k/E_k/R_k/B_k/A_k/vacuum` vocabulary, Eq.(2.23), function-valued regular `E_k`, selected regular-E projection, source-localization interface | exact same-object realization of a selected physical carrier if not already attached; do not reconstruct the complete-density theory merely because a later wrapper is conditional |
| CMP122 | PUBLISHED THEOREM BOUNDARY OWNED | Theorem-1/UV-stability authority, finite-history coupling hypothesis, active-scale source theorem carrier, raw-CMP119 active specialization | theorem-bearing exact instantiation on a selected source family if a current consumer lacks it; continuum/OS/mass-gap consequences remain separate and are **not** supplied by CMP122 |

## PR chronology that established this

### #543 — source-faithful complete-density reuse

`YM Gate I + source-faithful complete-density RG reuse`

This is the major route correction from “rebuild RG1a/RG1b” to “reuse Bałaban's published complete-density theorem”. It introduced/used the CMP119/CMP122 -> existing `CombinedRGAdmissibility` path and explicitly stated that the frontier is literal source-carrier identification rather than another generic cluster/RG theorem.

### #568 — published four-dimensional UV boundary

`YM Round58: canonical G2, compact-group one-loop, and published 4D UV boundary`

This tranche separated:

- raw CMP119 scale-indexed objects and Eq.(2.23);
- finite-beta-history construction;
- CMP122 Theorem-1 active-scale specialization;
- published four-dimensional finite-cutoff UV stability;
- later continuum Schwinger/OS/nontriviality/clustering obligations.

Important conclusion: **published CMP122 UV stability is not a missing DASHI theorem and is not the Clay mass-gap theorem.**

### #821 — broad raw-source wall (historical, later superseded as preferred prerequisite)

`YM: isolate literal CMP119 raw-source family as first preferred source wall`

This correctly enforced same-object source discipline and separated complete action `A_k` from the regular small-field `E_k`, but its broad “raw objects first” route was later made unnecessarily strong for the BC1 consumer.

### #846 — consumer-indexed regular-E recut

`YM: recut preferred source frontier to regular-E and marked-history seams`

This explicitly superseded full CMP119 raw-state reconstruction as the preferred BC1 prerequisite. It records that:

- BC1 only needs the source regular-E coordinate `(k,rho_k) -> E_k`;
- stronger full CMP119 residual-family construction is only an alternate producer;
- CMP109/CMP116 continuation is compiler-owned once the regular-E realization is supplied;
- BC1 potential same-objectness is compiler-owned once that realization is supplied.

## Internal-round compression after #846

The roundup's internal-round crosswalk should be read as a sequence of **reductions**, not as a list of new CMP theorems that still need proving:

```text
R214   source-fixed rho_k -> A_k semantics (important for generated-action/unification provenance)
R215   BC1 route reversal: use literal regular E_k, not whole A_k
R216-217 broad raw-source split (historical preferred wall)
R218   published source flow
R219   beta-driven complete-density/residual-family construction
R221   regular-E source projection
R225   preferred regular-E route; full residual family demoted to stronger alternate producer
R234   source-fixed regular-E semantics
R235   localization-radius split
R236   recomputed source frontier
R237   selected-scale semantics
R240   consumer priority router
R241   regular-E projection becomes compiler consequence
R242   `RegularTerm = Background -> Real` at source construction
R243   extraction/evaluation become projection/application
R244   published CMP119 localization authority separated from repository carrier realization
R245   function-valued E + localization -> CMP109/116 continuation compiler
R246   consumer-indexed active-scale Section-2 regular-E form
R247   active continuation / focused validation; full quantitative bounds no longer primitive for BC1 continuation
```

The direction of travel is therefore:

```text
broad CMP reconstruction
  -> source-native complete density
  -> selected regular E
  -> function-valued regular E
  -> active-scale regular-E/localization form
  -> compiler-owned CMP109/116 -> BC1
```

not the reverse.

## What “conditional” means here

A `ProofLevel = conditional` on a late CMP wrapper does **not** imply “CMP theorem missing”. Before doing new CMP work, classify the condition:

1. **published source theorem authority missing?** Usually no for CMP109/116/119/122 core source statements already imported.
2. **generic compiler missing?** Frequently already closed in later rounds.
3. **same-object carrier realization missing?** Potentially yes.
4. **literal physical estimate missing?** Potentially yes.
5. **continuum/OS/mass-gap consequence missing?** These are separate programmes and must not be charged to CMP122.

Only (3) or (4), when demanded by the current consumer, should normally survive the Pareto filter.

## Current do-not-reopen list

Unless a current exact consumer demonstrates otherwise, do not spend proof-search budget on:

- re-proving CMP119 complete-density RG theory generically;
- re-proving CMP122 four-dimensional UV stability generically;
- re-deriving the finite-beta running-coupling identity already made definitional in the source-native construction;
- rebuilding an abstract `RegularTerm` semantics instead of using the function-valued `E_k` representation;
- rebuilding CMP109/CMP116 continuation plumbing already compiled from regular-E/localization;
- treating the complete action `A_k` as the object differentiated by CMP109 Eq.(5.1);
- treating CMP122 UV stability as continuum Schwinger construction, OS reconstruction, nontriviality, clustering, or physical mass gap.

## Live-search rule

When YM Pareto search lands on a CMP-labelled conditional, first search this status file and the roundup. Then ask:

```text
Which exact current consumer?
Which exact selected source object?
Which same-object equality/physical estimate is absent?
Was that equality already paid under an earlier/later round alias?
```

Only search the wider PR history if the roundup/status files do not answer those questions.

## Primary source coordinates retained

- CMP109 — Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories I*, DOI `10.1007/BF01215223`.
- CMP116 — Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, DOI `10.1007/BF01239022`.
- CMP119 — Bałaban, *Convergent Renormalization Expansions for Lattice Gauge Theories*, DOI `10.1007/BF01217741`.
- CMP122 I — Bałaban, *Large Field Renormalization I: The Basic Step of the R-Operation*, DOI `10.1007/BF01257412`.
- CMP122 II — Bałaban, *Large Field Renormalization II: Localization, Exponentiation, and Bounds for the R Operation*, DOI `10.1007/BF01238433`.

Person QID / exact paper-specific Dewey remain unresolved unless an authoritative identity/catalogue source is acquired. Do not guess them.
