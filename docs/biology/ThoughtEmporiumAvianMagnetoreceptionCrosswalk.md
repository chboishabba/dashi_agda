# Magnetoreception: Thought Emporium (2020) × avian mechanism owners (2019–2026)

## Source attribution and version

- **Provided transcript:** The Thought Emporium, **“Genetic Modification To Sense Magnetic Fields – Whose Gene #11”**, livestream of **17 June 2020**, presenter/creator credited as **The Thought Emporium**. The user-supplied plain-text transcript comprises **2,853 lines**; its locally inspected SHA-256 is `59388d04a5e7baa3465f84bcf25d71830e9e5d61c3ebc011d7c8ca05fda758c8`. This digest identifies the **uploaded transcript**, not an independently authenticated YouTube archive or the video's master audio.
- The original stream explicitly frames the biological intervention as **hypothetical**, and ends by proposing to finish the design in another stream. **No tested animal or human genetic gain of function is shown.**
- **New 2026-11-03 GitHub verification:** The original attributed [The Thought Emporium / Justin Atkin repository](https://github.com/thethoughtemporium/Whose-gene-is-it-anyway) explicitly describes the saved plasmid collection as `CC BY-SA 4.0`. Its [`magnetoreception` folder](https://github.com/thethoughtemporium/Whose-gene-is-it-anyway/tree/master/magnetoreception) contains the file `paav syn with pigeonized human cacna1d.gb` (**18,278 bytes**, GitHub blob SHA `0578ad167666789fbfd3faa849a455c25097b90c`), added by [commit `f83aaf2b3ada085d02d8a25cfdc4ae32c80fe09d`](https://github.com/thethoughtemporium/Whose-gene-is-it-anyway/commit/f83aaf2b3ada085d02d8a25cfdc4ae32c80fe09d), author timestamp **2020-07-04T03:23:52Z**. This confirms a **later digitally archived design**, **17 days after the 2020-06-17 original stream**. It does **not** establish the precise subsequent broadcast in which it was completed, GenBank syntax validation, independent assembly correctness, physical plasmid synthesis, in-vivo function or sensory enhancement. Do not import/copy the sequence into DASHI.

- **Simon Nimpf, Gregory Charles Nordmann, Daniel Kagerbauer, E. Pascal Malkemper, Lukas Landler, Artemis Papadaki-Anastasopoulou, Lyubov Ushakova, Andrea Wenninger-Weinzierl, Maria Novatchkova, Peter Vincent, Thomas Lendl, Martin Colombini, Matthew J. Mason and David A. Keays (2019)**, “A Putative Mechanism for Magnetoreception by Electromagnetic Induction in the Pigeon Inner Ear,” *Current Biology* 29:4052–4059.e4. DOI [10.1016/j.cub.2019.09.048](https://doi.org/10.1016/j.cub.2019.09.048). Credit the experimental neuron-marker/vestibular induction results and channel-isoform observations to these authors.
- **Xu, Jarocha, Zollitsch and colleagues (2021)**, “Magnetic sensitivity of cryptochrome 4 from a migratory songbird,” *Nature* 594:535–540. DOI [10.1038/s41586-021-03618-9](https://doi.org/10.1038/s41586-021-03618-9). Credit the **in-vitro** photochemistry of European-robin CRY4, with comparison to nonmigratory species, to this study.
- **Gregory C. Nordmann, Spencer D. Balay, Thamari N. Kapuruge, Marco Numi, Christoph Leeb, Simon Nimpf, E. Pascal Malkemper, Lukas Landler and David A. Keays (online 20 November 2025; journal issue 12 March 2026)**, “A global screen for magnetically induced neuronal activity in the pigeon brain,” *Science* 391:1155–1160. DOI [10.1126/science.aea6425](https://doi.org/10.1126/science.aea6425). This is **post-stream** and reports activation in medial vestibular nuclei and caudal mesopallium plus candidate type-II vestibular hair-cell machinery. It supports a proposed pathway, not human editing or a sole receptor.
- **Clivia Lisowski and colleagues (2026)**, “Homing pigeon navigation relies on superparamagnetic macrophages under overcast conditions,” *Science* 392:985–991. DOI [10.1126/science.ady2486](https://doi.org/10.1126/science.ady2486). The existing DASHI `AvianMagnetoreceptionSourceRegistry` and `AvianHepaticMacrophageMagnetoreception` own this evidence. The source reports iron-bearing hepatic macrophages and a **context-conditional macrophage depletion behavioural effect**; complete autonomic afference and central representation remain unproved.
- **Connie X. Wang and colleagues (2019)**, “Transduction of the geomagnetic field as evidenced from alpha-band activity in the human brain,” *eNeuro* 6:ENEURO.0483-18.2019. DOI [10.1523/ENEURO.0483-18.2019](https://doi.org/10.1523/ENEURO.0483-18.2019). EEG magnetic response is an **electrophysiological observation**, not conscious human magnetic perception or a validated gene-editing target.
- **Caution regarding MagR/magnetite:** the video proposes broad dismissal of particular candidates. That should remain the **video author's 2020 interpretation**, not a universal experimental theorem. The later mechanism-plural literature, especially the 2026 hepatic macrophage finding, makes blanket “birds do not use magnetic material” claims unsound.

## Original GenBank document ingestion (next exact work)

See [the source-inspected GenBank → DASHI integration plan](ThoughtEmporiumMagnetoreceptionGenBankIngestPlan.md) for the original 11,214-base circular archive, its 22 annotation features, lossless location AST, Golden codec and protein-context owner reuse, ontology/PNF join, and exact acceptance gates GB01–GB08. The external GenBank file exists and was metadata-inspected. **The reusable parser, candidate-only ontology worklist, source inventory and Golden location core are now source-written on PR #1461; exact original-file Python replay, full semantic record roundtrip and Agda kernel acceptance remain OPEN.** The source author and GitHub commit remain credited. Importantly, the original feature labelled `cacna1d human plus pigeon` is a `misc_feature`, not one of its two `CDS` features, so it cannot be silently promoted into a validated protein identity.

## Transcript-to-evidence crosswalk

| Transcript window | Stream claim or discussion | Science/evidence ceiling |
|---|---|---|
| ~4:34–14:30 | Bird navigation, magnetite, MagR, retinal CRY1a/CRY4 and magnetic protein candidates | Mechanism debate; no blanket exclusion. Molecular MagR/composite claims are not a demonstrated receptor-to-brain route |
| ~14:30–16:19 | Neuronal response concerns and failed/contested magnetogenetic claims | Critical context; does not prove absence of all retinal magnetic sensing |
| ~16:19–23:53 | Proposed semicircular-canal induction in pigeons | Nimpf et al. 2019 supports neural activation, a physical induction model and a candidate `CaV1.3` isoform; mechanism remains putative |
| ~23:53–30:41 | Differences in channel processing and conjecture that human sensation could be changed | Cross-species and channel-to-phenotype sufficiency **unproved** |
| ~30:41–45:16 | Viral/CRISPR editing and promoter ideas | Speculative technical discussion **not replicated as an implementation** in DASHI; no successful magnetic sense intervention |
| ~1:13–1:19 onward | Splice and reference-sequence ambiguities in the stream | Shows unresolved source-species/isoform matching; does not supply verified human homology or safe edit |
| ~2:52–2:54 | Creator says the design will be finished later | The **present stream did not complete or validate a working genetic modification** |
| GitHub commit 2020-07-04 | Author-published GenBank file in `magnetoreception` folder | Digital file publication is **real and later than the stream**; verified file presence and commit metadata do not pay biological validation |

**Time- and provenance-sensitive correction:** the 2020 stream could not have discussed Xu 2021, Nordmann 2025/2026, or Lisowski 2026 as published evidence. They are **later independent literature** added by DASHI, not claims attributed to the original video.

## Mechanism cross-pollination, not collapse

The existing canonical `DASHI.Biology.MagnetoreceptionSurface` already declares `radicalPairRetinalChannel`, `vestibularCandidateChannel`, `hepaticMacrophageChannel`, `trigeminalCandidateChannel` and a mechanism-unresolved channel. The new source-linked adapter `AvianMagnetoreceptionThoughtEmporiumEvidenceExact` reuses that owner, plus:

- `AvianCryptochromeMagnetoreceptionInhabitant` and `AvianRFOverlayMechanismAdapter`: retinal cryptochrome/radical-pair and RF perturbation remain **one** candidate branch. RF perturbation alone does not prove that receptor's unique mechanism.
- `AvianHepaticMacrophageMagnetoreception` and `AvianMagnetoreceptionSourceRegistry`: existing **Lisowski 2026** source and context-specific behavioural intervention remain under their original theorem/data owner. No competing redefinition is introduced.
- `AvianMagnetoreceptionThoughtEmporiumEvidenceExact.vestibularCandidateSurface`: a symbolic `Generic.MagnetoreceptionSurface` with `vestibularCandidateChannel` and `vestibularCandidateRoute`; evidence grades are **correlational** for candidate receptor/afference and **structural** for proposed navigation use. The dummy token maps do not simulate, derive or calibrate real pigeon sensory transduction.
- `DASHI.Core.AttributedSourceCore` and `ScientificMechanismEvidenceBidiExact`: original article/source ownership, paper observation versus video speculation, and independent reverse-evidence obligations.

**Physics compatibility boundary:** a stationary loop with **unchanging flux** does not, by Faraday induction alone, develop the induced EMF that a time-varying magnetic flux would produce. The transcript's loop analogy must be accompanied by explicit motion, rotation or varying flux. The Golden core records *constructor-level* difference between those premises, not a derivation of biological voltage or neuron spikes.

## Golden finite core

`DASHI.Biology.AvianMagnetoreceptionStreamFiniteCore` is a self-contained Agda `{-# OPTIONS --safe #-}` module importing only Agda builtin equality. It states disjoint-constructor proofs for:

- static-loop constant flux versus changing-flux premise;
- author's video discussion/putative mechanism/observation versus independently demonstrated human enhancement;
- in-vitro molecular assay versus homing behaviour;
- neural marker or human EEG versus conscious perception/human genetic enhancement;
- pigeon/robin versus human genetic-functional transport;
- single vestibular mechanism versus unproved universal exclusivity.

**These are typed proof-obligation guards; no fact about a species is established by defining distinct constructors.** Other modules remain legacy non-Golden dependencies and require exact-head Agda checks.

## Exact max-cut

1. **M01 — Transcript, digital artifact and source identity:** SHA-256 of the supplied text is pinned. The original GitHub author-published GenBank artifact's **path, blob SHA, byte size, commit SHA and 2020-07-04 commit timestamp** are now pinned, with independent correctness/biology not inferred. Precise YouTube watch URL/transcript alignment, identity and date of the *follow-up* design stream, independently authenticated `gb` validation and original paper source-data receipts remain open.
2. **M02 — Retinal experimental weld:** connect Xu et al. in-vitro CRY4 sensitivity to an *in vivo* retinal transducer, central activity and controlled compass behaviour; no conflation with pigeon channel or universal human ability.
3. **M03 — Vestibular mechanism weld:** integrate Nimpf 2019 and Nordmann 2025/2026 source observations with matching vestibular cell identity, induced field, afferent signal and behavioural necessity. The present science is stronger than 2020's conjecture but does not prove complete causation.
4. **M04 — Hepatic cross-channel discrimination:** retain Lisowski 2026 overcast/sun intervention as independent evidence, without converting macrophage magnetism to a fully reconstructed neural signal or using it to refute CRY4/vestibular candidates.
5. **M05 — Human evidence boundary:** Wang 2019 alpha EEG response does not establish a conscious magnetic compass or warrant human gene modification; the livestream's human transfer hypothesis remains unvalidated.
6. **M06 — Physical same-object:** quantify magnetic-flux rate, geometry, conductive tissue properties and physiological response from independently source-grounded data **only if available**; a loop analogy plus a proposed calcium-channel isoform is insufficient.
7. **M07 — Cross-species/isoform evidence:** provenance-bound orthology, splice-isoform and tissue expression must be established by official source records before any human causal functional assertion. No human gene modification recipe or implementation is part of this tranche.
8. **M08 — Kernel and test acceptance:** run Agda on the standalone Golden core, source adapter and canonical import roots, and run the focused Python static/negative regressions. Record checker/toolchain and exact head. **Source-written code and static source inspection are not Agda kernel acceptance.**

## Attribution / scope

The Thought Emporium is credited for its creator-led exploration and its speculative conceptual proposal. Nimpf, Nordmann, Xu, Lisowski, Wang and colleagues are credited for their independent scientific studies, and earlier DASHI magnetoreception and physics owners retain original proof ownership. This contribution is a **non-operational evidence formalisation**; it supplies no editable vector, gene sequence, CRISPR guide, tissue-delivery method, animal intervention or biochemical construction details.
