# Bałaban source text extracts

These are durable working text/OCR extracts used by the literal finite-lattice
operator investigation.  They preserve searchable equation context across a
reboot; they are not a replacement for the source PDFs or an authority for a
mathematical claim.  Check formulas, page numbers, signs, and notation against
the original paper before using an extract in a proof dossier.

## CMP 99 disambiguation

There are two distinct Bałaban papers in volume 99 of *Communications in
Mathematical Physics*.  Bare references to `CMP 99` are therefore forbidden at
source-critical seams.

1. Tadeusz Bałaban, *Spaces of Regular Gauge Field Configurations on a Lattice
   and Gauge Fixing Conditions*, CMP **99(1)** (1985), 75--102.
   DOI `10.1007/BF01466594`.
   This is the regular-configuration / gauge-fixing paper.

2. Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background
   Field*, CMP **99(3)** (1985), 389--434.
   DOI `10.1007/BF01240355`.
   This is the background-propagator paper.  The GAP-1 marked random-walk /
   domain-sequence comparison, including Theorem 3.14 and equation (3.154), is
   attributed to THIS paper.

The durable file `cmp99-background-propagators.txt` is an extract of paper 2,
not paper 1.

## Propagator / RG lineage relevant to GAP-1

- Tadeusz Bałaban, *Propagators and Renormalization Transformations for Lattice
  Gauge Theories. I*, CMP 95 (1984), 17--40. DOI `10.1007/BF01215753`.
- Tadeusz Bałaban, *Propagators and Renormalization Transformations for Lattice
  Gauge Theories. II*, CMP 96 (1984), 223--250. DOI `10.1007/BF01240221`.
- Tadeusz Bałaban, *Spaces of Regular Gauge Field Configurations on a Lattice
  and Gauge Fixing Conditions*, CMP 99(1) (1985), 75--102.
  DOI `10.1007/BF01466594`.
- Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background
  Field*, CMP 99(3) (1985), 389--434. DOI `10.1007/BF01240355`.
- Tadeusz Bałaban, *Renormalization Group Approach to Lattice Gauge Field
  Theories. I. Generation of Effective Actions in a Small Field Approximation
  and a Coupling Constant Renormalization in Four Dimensions*, CMP 109 (1987),
  249--301. DOI `10.1007/BF01215223`.
- Tadeusz Bałaban, *Renormalization Group Approach to Lattice Gauge Field
  Theories. II. Cluster Expansions*, CMP 116(1) (1988), 1--22.
  DOI `10.1007/BF01239022`.

Thus the source chain used by the current differentiated marked-localisation
route is more precisely

```text
CMP95/96 propagator construction
  -> CMP99(1) regular chart / gauge fixing
  -> CMP99(3) background propagator + marked domain comparison
  -> CMP109 twice-differentiated activity / polarization
  -> CMP116 localization/tree resummation.
```

Included packet:

- CMP 95: propagators and renormalization transformations I.
- CMP 98: averaging operations.
- CMP 99(3): background-field propagators, DOI `10.1007/BF01240355`.
- CMP 102: three-dimensional ultraviolet-stability comparison paper.
- CMP 109 and 116: effective actions parts I and II.
- CMP 119 and 122: lattice-gauge renormalization-group papers I and II.

`cmp102-uv-stability-3d.txt` is the 3D comparison paper, not the separate
CMP 102 variational-background-fields paper.  The latter has not been added
because no durable text extraction was present in `/tmp`.

The operator-realization lane currently uses CMP 98 equation (124), CMP 98
equation (127), CMP 99(3) background-propagator equations (3.156)--(3.159), and
CMP 109 equations (2.10)--(2.13), subject to direct PDF verification.

SHA-256 checksums of the saved extracts:

```text
a1521a6ed362edece65230c44d03c21b2097432d1283dfd185edc2a31e163995  cmp102-uv-stability-3d.txt
73d107bbd631db8f48e702a2646dbe09db195cd40e59da5b58b14c6dd3638012  cmp109-effective-actions-part-i.txt
d6b229f61d6f2e1cafe2ced98d39bf399f5d6acdbdb6133925d33ebc8a196799  cmp116-effective-actions-part-ii.txt
37ec016101b53fb1ece79a1eb20e0ecd84ee2664460176a583321ca8e9da2bcb  cmp119-rg-lattice-gauge-i.txt
bf0fc9371b5acb8fddb9bfcd3a89b3500ac3e784a575e67ca4d0d54c2a8ea724  cmp122-rg-lattice-gauge-ii.txt
ebfc00c22feb63a6870f30a85fdcdb60e5d89587d4df140bcc5311f47e589c5  cmp95-propagators-i.txt
7beb694c38f0a7e370b74f3c49fb38d37e529df7b7be7b585b8b74c0e5e4fd96  cmp98-averaging-operations.txt
bb4497fe0c7bde556b0ca029b6f6bfdd46c45bbf2bb3ee713920c23ae946e471  cmp99-background-propagators.txt
```
