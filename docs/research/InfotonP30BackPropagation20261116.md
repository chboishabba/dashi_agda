# Infoton P30 — backpropagation from published constraints (2026-11-16)

**Origin/research integration:** Johl Brown / DASHI. **Public original concept:** January N. Walker, *NISTIR 6025 Information Physics Mapping*, slides 28–31, PDF linked at https://infoton.ai/infoton-p30 . **Status: independent reconstruction of two candidate encoders, not January Walker's original implementation or a physical efficiency demonstration.**

Tested source and receipts: \`scripts/p30_backprop_candidates.py\`, \`scripts/test_p30_backprop_candidates.py\`. Local **16/16 tests passed**; both code blob SHAs match committed source after the test run. Run \`python3 -m unittest discover -s scripts -p 'test_p30_backprop_candidates.py' -v\`.

## Reported facts (direct from slide 29 screenshot)

- 163 characters; 489 encoding operations; 167 positions. The visible natural-language quote, after explicitly **ASCII-normalizing punctuation**, is exactly 163 bytes. Identity of the demo's original byte string is unknown.
- Storage: UTF-8 baseline 163 bytes, P30 CHAR round-trip 167 bytes, P30 PACKED round-trip 171 bytes, P30 DIRECT packed **write-only** 116 bytes, Huffman payload-only 103 bytes, Huffman round-trip total 533 bytes.
- A separate *BIOS-native* operation panel reports 163 ingress encodes and zero read re-verifications. These are **different accounting conventions**, not a verified common physical-instruction count. \`489=3×163\` is exact arithmetic and cannot establish energy/erasure count.

## Source geometry → two falsifiable reconstructions

The source states Euler \`phi(30)=8\` and visualises coprime rays around modulus 30. Its unit group is
\`U(30)={1,7,11,13,17,19,23,29}\`, multiplicatively isomorphic to \`C2×C4\`; it is not the cyclic group C8, and 30 is a *primorial*, not a prime.

**Our inferred**, not disclosed, representation uses eight unit rays and 32 radial depths:
\`8×32=256\` positions, so one byte can be represented as \`(unit,depth)\` with \`unit=U30[rank%8]\`, \`depth=rank//8\`. The exact radial-depth and mapping design is *not* asserted to be the original P30.

Two demonstrably different reversible maps pass all reported counts:
- Natural rank: \`rank=b\`.
- Reflected Gray-code permutation: \`rank=b^(b>>1)\` (plus inverse).

We add an **inferred** four-position/four-byte length header to obtain exactly \`163+4=167\` CHAR positions/bytes. Adding a further **inferred** four-byte CRC32 yields \`163+4+4=171\` PACKED round-trip bytes. This is *a possible fit*, **not** source evidence that Walker uses those headers, CRC32, or Gray coding. Those 489 'three-stage' encoder accounting labels are likewise not measurements of CPU instructions or irreversible physical bit erasures. Both mappings give different codewords and the same published counts: **the original mapping is non-identifiable from these summary counts alone** (indeed, many 256-state permutations have identical sizes).

Tests exhaustively confirm both encoders' round-trips for **all 256 byte values**, zero/random/UTF-8 corpora, and all 163×8=1304 payload one-bit flips under our *illustrative* CRC variant. CRC needs a read verification and does not correct errors; the bare 256-state wheel is perfectly filled, leaving **zero invalid 8-bit position codes** with which to certify corruption. Valid-ray substitution remains a valid state with wrong data in the no-CRC variant. The original P30 verifier is still unknown; this is not a result about an unpublished verifier.

## Capacity / compression / thermodynamic discriminators

- With 256 messages encoded into 256 equipotent codes, an unmodified no-redundancy position mapping is a **bijection**, not universal lossless compression and not an error-correcting code. Any advantage must arise through actual workload-specific compression, a different physical substrate/circuit, a stronger coding contract, a shared dictionary, or another original mechanism. The number-theoretic ray labels alone do not lower Shannon information content.
- A universal lossless mapping from *all* 163-byte strings to 116 bytes is impossible by counting. **For the one displayed natural-language message**, 116 bytes may be entirely possible by compression or shared-model coding. Its measured zero-order Shannon-entropy ideal payload size under our ASCII normalization is approximately **90.392 bytes** (model cost not included). Therefore the reported DIRECT **write-only** 116-byte claim is *not disproved*; it simply lacks its original decoder/framing/equivalence evidence.
- The exact 3× or 1× "operations" tallies are not matched to the 12,264 Hsiao ECC verification tallies in logical or physical scope. Nor is any counted operation automatically an erasure worth \`k_B T ln 2\`; the rack/WUE extrapolations retain their original metrology blockers.

## What one original P30 trace would resolve

A known input string and (1) its full **list of encoded units+depths/positions**, (2) its serialized bytes including header, (3) the actual decode/round-trip procedure, and (4) a substitution/flip detection transcript would immediately distinguish or falsify these candidate maps. A handful of selected inputs [0,1,7,8,15,16,31,32,127,128,255] would establish mapping discontinuities and the role of depth. One original **116-byte DIRECT output and a decode demonstration** would determine whether that mode is merely write-only, dictionary-assisted, compressed, or round-trippable. No proprietary-source access is required to test *black-box observational equivalence* if the original executable provides those inputs/outputs.

## Repo prior art / fail-closed gates

Reuses \`DASHI.Codec.BalancedTritBitFibre\`, \`DASHI.Programmes.FRACDASHExact\`, \`DASHI.ComputerScience.InfotonP30FiniteAuditExact\`, the genuine \`scripts/infoton_p30_ecc_maxcut.py\` SECDED reference and \`DASHI.Quantum.InfotonOriginalPhysicalAdapterWeldExact\`. Do not replace their typed physical and assurance boundaries with an inferred 8-ray drawing. Original Infoton gates **8/19 adjudicated; 11 OPEN**. This completes an **independent inverse-design executable and non-identifiability subgate**, not B1 original-code acquisition, B2 P30 ECC validation, B3 comparable benchmark, or C1 physical rack measurement.
