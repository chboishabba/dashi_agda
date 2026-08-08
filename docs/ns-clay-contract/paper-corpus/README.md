# Navier–Stokes claimed-paper corpus

[Back to the Clay-contract overview](../README.md)

This directory treats every located paper as mathematical input rather than social proof. Peer-reviewed papers, arXiv preprints, repository deposits, independent publications and web essays can all contribute local lemmas or falsifiable claims. None is promoted merely because it states “global regularity” or “Problem B solved.”

The workflow is:

1. preserve the source’s own theorem statement and notation;
2. isolate the first load-bearing implication;
3. translate it into a typed precondition/postcondition contract;
4. search for finite rational, Fourier or quantifier countermodels;
5. retain valid local lemmas even when the terminal argument fails;
6. map surviving producers onto the canonical highest-alpha ladder;
7. permit terminal composition only after cutoff-uniform physical estimates are independently checked.

## Documents

- [Audit matrix](audit-matrix.md)
- [Highest-alpha lemma ladder](highest-alpha-lemma-ladder.md)

## Formal modules

- `NSTriadKNLuoClaimedSolutionCorpusRound24Exact.agda`
- `NSTriadKNLuoAbuGhuwalehAdditiveFloorNoGoExact.agda`
- `NSTriadKNLuoCamlinTemporalLiftNoGoExact.agda`
- `NSTriadKNLuoClaimRouteCrosswalkRound24Exact.agda`
- `NSTriadKNLuoHighestAlphaClayLemmaLadderRound24Exact.agda`
- `DASHI/Papers/NavierStokes/ClaimCorpusHighestAlphaRound24.agda`

## Current authority boundary

The corpus search is intentionally not declared exhaustive. The two exact no-go modules disprove particular implications as written; they do not prove that every lemma in the corresponding manuscript is false. Papers with open load-bearing producers remain in the corpus until those producers are proved, repaired or falsified.
