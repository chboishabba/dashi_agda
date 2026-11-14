# Local-agent symbol snowball — Agda Golden first, Lean downstream

Date: 31 October 2026. Authority: the EXISTING tools/agda_preflight repository-intelligence product and its dashi-repo command. The current exact proof/analytic register has **39 obligations** in [the original roadmap](2026-10-31-openai-math-exact-lemma-maxcut-ledger.md). Machine-readable search [175 terms across 13 ranked lanes](2026-10-31-local-symbol-snowball-terms.json). The driver is [scripts/run_openai_math_symbol_snowball.py](../../../scripts/run_openai_math_symbol_snowball.py). This does not introduce a second repository index or database.

## Workstation commands

Run in the actual dashi_agda checkout, with sibling dashi_lean4:

~~~bash
python -m pip install -e './tools/agda_preflight[test,mcp]'
dashi-repo index --root .
dashi-repo status --root .

# Safe non-mutating preview, P0/P1/P2 high priority
python scripts/run_openai_math_symbol_snowball.py \
  --agda-root . --lean-root ../dashi_lean4 \
  --mode plan --group P0 --group P1 --group P2 --max-terms 40 --related

# Query canonical repository semantic index plus cross-language rg
python scripts/run_openai_math_symbol_snowball.py \
  --agda-root . --lean-root ../dashi_lean4 --mode both \
  --max-terms 175 --max-lines 12 --related \
  --out /tmp/dashi-symbol-snowball.tsv

# Exact mathematical research frontier without losing first-task focus
python scripts/run_openai_math_symbol_snowball.py \
  --agda-root . --lean-root ../dashi_lean4 --mode both \
  --group R03 --group R04 --group R05 --group R06 \
  --max-terms 80 --out /tmp/dashi-analytic-source-candidates.tsv

# Follow-up original owner proof and source history
dashi-repo discover 'finite supported Tseitin count' --root .
dashi-repo related \
  DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinUniqueExtensionExact.uniqueUsedCoordinates \
  --root .
dashi-repo archaeology 'global Tseitin canonical assignment' --root .
dashi-repo prove discover 'finite CNF model count' --root .
~~~

The default mode plan only prints commands. The both mode executes queries against the native canonical dashi-repo Agda SQLite semantic index at .dashi/repository.sqlite3 and an optional plain-text rg fallback on local Lean files. TSV files are disposable HUMAN/AGENT receipts, not persistent subsystem databases or proofs. The driver never creates a parallel index, claims a mathematical absence result, or edits files. The dashi-repo discover/related/archaeology/proof-route commands own the real semantic and history logic; avoid implementing another.

## Highest-alpha search lanes

| Lane | First original declarations or structural patterns to reuse |
|---|---|
| P0 | Kernel elaboration, binder/index/import problems, Agda-safe trust, actual Lean pins |
| P1 | ProgramAssignmentRealizes, uniqueUsedCoordinates, uniqueAuxiliaryGateValues, Fin.opposite and earliest gate-index owner |
| P2 | Finite Fubini sum, accepted input fibres, originalGlobalCNFCountExact, optGlobalCNFCountExact |
| P3 | Literal polarity, SAT.Literal, List.toFinset, exact per-assignment truth and finite model counts |
| P4 | encodeCNF, encodeNat, frame, runtimeBound, visitedSpace, frontend bit-operation costs |
| P5 | OpenAI 378 exact_count_and_sat, TSavo external proof ownership, source pin and axioms |
| R00 | Native #1438 grid 27 vertices / 54 edges / two checkerboard colourings |
| R02 | DISTINCT #1414 27 ternary functions / 11 orbits / 7+4 parity, Ibrahim Monster 3B |
| R03 | Genuine twin-prime late pair count jumps (finite sieve/CRT alone not enough) |
| R04 | Genuine RH A1/A2/B strict scalar and signed-fifth correlation estimates |
| R05 | Pickover real enormous-factorial phase enclosure, not only Eisenstein radix |
| R06 | YM continuum physical measure/OS reconstruction and physical mass gap |
| R07 | DA51, QID concept identity, provenance, TOE and no ESD edits |

## Agent protocol: O / R / C / S / L / P / G / F

**O — organization and authorship:** establish exact original Golden Agda owner, earliest known PR/commit and historical mathematical author; preserve Ibrahim Monster 3B attribution. Protected ESD surfaces are import-only. Search actual source, not only PR titles.

**R — requirement/preconditions:** restate the exact quantified statement and types. The P2 finite counting carrier is CNF.Bits (inputs+gates), NOT unrestricted Cook.Assignment Nat-to-Bool tails. The 27 native graph vertices are not the distinct 27 ternary endomorphisms.

**C — code:** reuse existing DAG evaluator, original ProgramAssignmentRealizes, canonical UniqueExtension owner, Fin and List/Finset lemmas, and existing dashi-repo search. If the original owner already has the theorem, import/adapt it rather than writing a new theorem with a similar name.

**S — status/invariants:** classify each match as catalogue, similar signature, source-written, Agda kernel accepted, Lean kernel accepted, executed Python, or missing mathematical certificate. A symbol match is never proof equality. Numeric 3/9/27/369/7+4 and a QID label require a typed same-object adapter.

**L — linked theorem:** require both source Boolean SAT directions, exact model count, matching indices, literal polarity and conditions when moving Agda original circuit to Lean canonical SAT.CNF.

**P — performance:** retain source list clause count at most 3g+1 and the conditional encoding length at most 72(v+1)^2, v=inputs+gates. These do NOT prove preprocessing time or every-prefix machine space; find and pay those actual cost lemmas. The new ordered normalization compares at most 6m+m(m-1)/2 bounded-width items, not yet primitive machine bits.

**G — gate/verification:** use actual Agda and Lean compiler receipts. dashi-repo preflight, rg, Python, PR metadata and CI labels are not acceptance. Current Agda and staged Lean P1–P4 remain source-written pending local kernel builds. Keep Lean 4.28 pin separate from later upstream OAI378 Lean 4.34.1.

**F — frontier:** list the precise remaining lemma, search its highest-value imported donor, then implement it. For RH/twin/Pickover/YM, genuine analytic or physical certificates remain the targets; further representation alone does not discharge them.

## Suggested direct local proof checks (user-run, no CI)

~~~bash
dashi-repo diagnose DASHI/Research/OpenAIMath/Everything.agda --root .
dashi-repo next DASHI/Research/OpenAIMath/Everything.agda --require-fix --root .
agda -i . DASHI/Research/OpenAIMath/Everything.agda
agda -i . DASHI/Research/OpenAIMath/OpenAIMathSharedTseitinOptimizedCNFExact.agda

cd ../dashi_lean4
lake env lean Integration/OpenAIMath/ListFinsetCNFTransport.lean
python scripts/check_openai378_frontend_exact.py
python scripts/check_openai378_27grid_maxcut_bridge.py
~~~

Supply the Agda standard library include path as configured in the actual checkout; do not guess. The upstream378 bridge must be built against an explicitly pinned newer upstream environment, not accidentally imported into the Lean 4.28 authority spine.

**Agent output contract:** obligation ID | query and native semantic candidate | exact signature and dependencies | original mathematical/source owner | matched preconditions and negative control | reused theorem or new adapter | source hash | executed local verification | Agda/Lean kernel status (or NOT RUN) | exact remaining math/bit-time/visited-space obligation.

For claims of no existing owner, use fail-closed native discovery with a complete fresh Agda inventory and complete history harvest; textual rg NO_MATCH is never an absence certificate. Continue per Pareto/max-cut after each repaired compiler error, but never promote a matching numeral into a same-object theorem.
