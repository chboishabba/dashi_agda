# Crypto Blue-Team State Contracts — Round 12

This note indexes the theorem-bearing Round-12 crypto surface. It is not a security claim for any deployed primitive.

## Core rule

A protocol observation is useful to an attacker only insofar as it refines the hidden-state fibre relevant to the protected output. `ChosenCiphertextObservationRefinementExact` proves two complementary facts: adding an observation is monotone candidate refinement, while an observation that factors only through an already-public projection cannot distinguish two hidden states in the same public fibre. A genuinely new split therefore requires a hidden-dependent outcome/oracle or genuinely new public state.

`PublicSecretFactorisationAttackExact` sharpens this from full-state recovery to protected-label recovery. If one public fibre contains two fine states with different secret labels, deterministic exact public recovery is impossible on that fibre. Conversely, an explicit public factorisation through an intermediate quotient gives exact secret-label recovery without reconstructing the complete fine state.

## Ten-candidate state matrix

The educational comparison remains: one-time pad; AES-GCM; ChaCha20-Poly1305; RSA-OAEP; Diffie-Hellman; X25519; ElGamal; HPKE; ML-KEM; QKD plus symmetric follow-on protection.

`TopTenCryptoBlueTeamProfilesExact` gives each candidate a primitive kind and falsification surfaces. `TopTenCryptoStateContractMatrixExact` separately gives preconditions, postconditions and invariants. `TopTenCryptoObservationSurfacesExact` separates public-only, hidden-dependent and physical-channel observations. `TopTenCryptoDependencyGraphExact` expresses component-security cuts.

The principal exact cross-candidate results are:

- OTP / stream-XOR family: same keystream reuse exposes the plaintext XOR relation exactly (`XorReuseLeakExact`). This is a conditional algebraic theorem, not an assertion that conforming AEAD executions reuse nonces.
- AES-GCM / ChaCha20-Poly1305: nonce uniqueness is an explicit state invariant; authentication outcomes are modelled as potentially hidden-dependent surfaces whose ability to split a secret fibre still requires an `ObservationSplitWitness`.
- RSA-OAEP / randomized PKE: `PublicCandidateTestingExact` separates public re-encryption verification of a supplied message+coins witness from construction of that witness; validity-oracle visibility is a separate dependency.
- Diffie-Hellman / X25519: deterministic public forward-map candidate testing is separated from preimage search and discrete-log assumptions. X25519 follows RFC 7748 semantics: the state matrix tracks all-zero shared-secret handling and context binding rather than importing generic Weierstrass point-validation rules.
- ElGamal: discrete-log hardness, fresh ephemeral randomness and public element handling are separate obligations; randomized re-encryption candidate testing does not construct the candidate.
- HPKE: KEM, KDF, AEAD and context binding are separate proof-bearing obligations; a supplied break of any component contradicts a complete HPKE contract.
- ML-KEM: the existing noisy residual test, passive-transcript invariance, secret-labelled fibre analysis, public-factorisation attack witness and implicit-rejection observation surface are composed rather than duplicated.
- QKD + symmetric protection: authenticated classical-channel readiness is a typed precondition; parameter testing and the follow-on symmetric primitive remain independent obligations.

## Primary references carried in Agda

- Claude E. Shannon, “Communication Theory of Secrecy Systems”, *Bell System Technical Journal* 28(4), 1949. DOI `10.1002/j.1538-7305.1949.tb00928.x`.
- NIST, *Advanced Encryption Standard (AES)*, FIPS 197-upd1, 2023. DOI `10.6028/NIST.FIPS.197-upd1`.
- Morris Dworkin, *Recommendation for Block Cipher Modes of Operation: GCM and GMAC*, NIST SP 800-38D. DOI `10.6028/NIST.SP.800-38D`.
- Yoav Nir and Adam Langley, RFC 8439, *ChaCha20 and Poly1305 for IETF Protocols*. DOI `10.17487/RFC8439`.
- Kathleen Moriarty, Burt Kaliski, Jakob Jonsson, Andreas Rusch, RFC 8017, *PKCS #1: RSA Cryptography Specifications Version 2.2*. DOI `10.17487/RFC8017`.
- Whitfield Diffie and Martin E. Hellman, “New Directions in Cryptography”, *IEEE Transactions on Information Theory* 22(6), 1976. DOI `10.1109/TIT.1976.1055638`.
- Adam Langley, Mike Hamburg, Sean Turner, RFC 7748, *Elliptic Curves for Security*. DOI `10.17487/RFC7748`.
- Taher ElGamal, “A Public Key Cryptosystem and a Signature Scheme Based on Discrete Logarithms”, *IEEE Transactions on Information Theory* 31(4), 1985. DOI `10.1109/TIT.1985.1057074`.
- Richard Barnes, Karthikeyan Bhargavan, Benjamin Lipp, Christopher A. Wood, RFC 9180, *Hybrid Public Key Encryption*. DOI `10.17487/RFC9180`.
- NIST et al., *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203, 2024. DOI `10.6028/NIST.FIPS.203`.
- Artur K. Ekert, “Quantum cryptography based on Bell’s theorem”, *Physical Review Letters* 67, 1991. DOI `10.1103/PhysRevLett.67.661`.
- Gorjan Alagic et al., *Recommendations for Key-Encapsulation Mechanisms*, NIST SP 800-227, 2025. DOI `10.6028/NIST.SP.800-227`.

## Validation boundary

`check_crypto_topten_blue_team_round12.sh` scans the new theorem surface fail-closed and cascades the Round-11 checker. When `agda` is available it typechecks the cumulative aggregate; this environment does not provide Agda, so no kernel-clean claim is made here. No GitHub Actions or CodeRabbit run is required for this tranche.
