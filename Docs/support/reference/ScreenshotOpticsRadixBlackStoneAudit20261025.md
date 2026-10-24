# 2026-10-25 social-media screenshots: optics, base-12 circle, Black Stone

## Scope and status

Four user-supplied screenshot roots, treated separately. This is a source-ledger
and limited **finite mathematical formalisation**, not a calibrated flight test,
a new proof of pi, an archaeological assay, or proof/disproof of a religious
belief. Authoritative canonical ownership remains:

- Maths: `DASHI.Foundations.BaseTwelveCircleRepresentationBoundaryExact`,
  cross-linking `DASHI.Foundations.Base369CirclePhase`,
  `DASHI.Geometry.Base369SectorUnrollingFinite`,
  `DASHI.Foundations.NumberRoleBoundary`, and
  `DASHI.Foundations.P13UnitGroupC12Witness`.
- Optics: existing `DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact`,
  `DASHI.Physics.Optics.DiffuserNoiseStableRecoveryExact`, and
  `DASHI.Physics.Optics.OpticalPhenomenaKernelBridge`. The atlas imports a
  **specific already-owned clipping non-recovery proof**, not a GOES model.
- Provenance: `DASHI.Core.AttributedSourceCore`; new
  `DASHI.Culture.ScreenshotOpticsRadixBlackStoneAttributionExact` is a
  non-promoting source and evidence-role adapter.

No Agda/kernel verification is claimed merely from writing these files.
All domain-specific physical, historical, or theological assertions remain
explicitly attributed or held.

## Source roots, attribution, and dependency boundaries

| Screenshot | What is visible | Correct attribution / status |
|---|---|---|
| `1000018617.png` | In-cockpit display; **comment** from `evgenekb_` says GOES-451M has higher resolution and clean high-magnification output. | The commenter is the author of **the comment**, not demonstrably the creator of the display/video. No original instrument log, test sequence, lens/sensor spec, independent baseline or date calibration is visible. |
| `1000018618.png` | `basetwelvegeometry` circle/polygon; equal-length annotations resembling `0.5 sqrt(2)`; caption proposes a base-12 Cartesian geometry and "discrete pi". | Original source of *the particular claim* is the attributed account/comment; it is not yet evidence of a new circle theorem. "12 June" is visible with no verified year. |
| `1000018619.png` | Graph-paper approximate polygon; `sphinyzw` objects that notation does not alter the object; `basetwelvegeometry` responds that twelfths lack repeating decimals. | Preserve **both** authors distinctly: sceptical comment and author's reply. The absence-of-repeats claim is false without denominator conditions. |
| `1000018620.png` | Close-up of purported Black Stone in a silver surround; cropped theological comment cites a statement of Umar. | Commenter's handle absent; object/location/date cannot be authenticated solely from crop. Separate literal hadith text from the contemporary commenter's explanation. |

Separate outside sources, NOT independent confirmations of all screenshot details:

1. Piotr Butowski, *Enhanced Version Of Russia's Ka-52 Attack Helicopter Appears*, The War Zone, 21 Jul 2023, https://www.twz.com/enhanced-version-of-russias-ka-52-attack-helicopter-appears — secondary identification of GOES-451M in Ka-52M modernisation, not empirical substantiation of all superlatives or the screenshot's exact model.
2. Al-Bukhari, *Sahih al-Bukhari*, Book of Hajj, **1597**, https://sunnah.com/bukhari:1597 — the earlier **literary collection root** for a narration from 'Abis ibn Rabi'a about Umar and the Black Stone. Other websites that reprint the same text are derivative witnesses, not automatically independent events. See also 1605 for a related recension: https://sunnah.com/bukhari:1605.
3. Kerim Kocak, *Features of the Hajar al-Aswad, Black Stone of Makkah, Saudi Arabia*, *Konya Journal of Engineering Sciences* 11(3), 2023, https://dergipark.org.tr/en/pub/konjes/article/1244222 — published discussion of purported fragments/materials; provenance and whether any examined sample is the **same original object** remain separate burdens.
4. Smarthistory, *The Kaaba*, https://smarthistory.org/the-kaaba — art-historical account of traditions and reconstruction, explicitly warns that some events are documented in later literary traditions rather than confirmed by physical investigation.
5. Kenneth H. Rosen, *Elementary Number Theory and Its Applications*, theorem 10.5, https://users.fmf.uni-lj.si/lavric/Rosen%20-%20Elementary%20number%20theory%20and%20its%20applications.pdf — standard terminating radix-expansion criterion. This theorem is not attributed to the screenshot author.

## A. Optics: precise separation of plausible mechanism and claims

The GOES-451M name itself occurs in 2023 reporting on the Ka-52M.
A gyro-stabilised multi-channel imaging instrument can improve image quality
relative to a baseline by reducing angular line-of-sight jitter and/or by
changing sensor, optics and signal processing. That *plausibility* does not
supply the actual test results.

Use a deliberately **generic** stochastic imaging model, not a weapon-system
performance reconstruction:

\[
 y = Q\!\left(\operatorname{clip}\left(g\,[\mathcal H_\theta x
      + \eta_{\mathrm{shot}}+\eta_{\mathrm{read}}],\,W\right)\right)
\]

where \(\mathcal H_\theta\) includes calibrated PSF, geometry, spectral
response and motion; \(Q\) is quantisation, \(W\) a saturation limit. Stabilisation
can alter \(\theta\) and hence the PSF. A screen recording is a further
postprocessing/display/codec/filming observation map \(D(y)\). Visible clarity
of \(D(y)\) is **not an injectivity, SNR, angular resolution or ground-truth
recognition certificate**.

Existing formal theorem (owned by
`DiffuserImagingObserverDynamicRangeExact`):

\[
  Q(a)=Q(b)\implies F(Q(a))=F(Q(b))
\]

for every deterministic postprocessor \(F\). Its concrete witness is the
capacity-one clipping collision of the inputs 1 and 2. This does not assert
that all sensor readings collide, that denoising never works, or that extra
independent measurements cannot restore a distinction. The atlas reuses this
precise lemma.

**Outstanding physical receipts:** authenticated device/model attribution,
conditions and aligned raw/baseline captures; measured PSF/MTF, sensor noise
and pixel sampling; uncertainties and blinded image-quality tests. The reel's
numerical recognition-at-distance and "completely free of noise" claims
remain **unverified social-media assertions**; no operational targeting
performance calculation is attempted here.

## B. Exact circle/radix claims

Numeral bases are encodings of values. In base twelve:

\[
(0.6)_{12}=6/12=1/2=(0.5)_{10},\quad
(0.4)_{12}=4/12=1/3,\quad (0.1)_{12}=1/12.
\]

The two exactly checked first identities live in the Agda ratio-code module as
cross-products (\(5\cdot12=6\cdot10\);
\(4\cdot3=1\cdot12\)). General real-number representation does *not* follow
from this finite demonstration.

**Correct termination criterion.** A reduced rational \(m/n\) terminates in
integer base \(b\ge2\) exactly when each prime factor of \(n\) divides \(b\).
Base 12 = \(2^2\cdot3\), so thirds terminate; fifths in general repeat. Base
10 = \(2\cdot5\), so fifths terminate and thirds repeat. Irrational numbers,
including \(\sqrt2\) and \(\pi\), cannot have a terminating expansion in
*any* integer base. The full theorem and irrationality statements are
established mathematics cited here, but not re-proved in these Agda modules.

If the screenshot's annotation is precisely \(s=\frac12\sqrt2\) and there
are **12 equal sides**, the polygon's perimeter has exact squared length

\[
 P=12s=6\sqrt2,\qquad P^2=72.
\]

`twelveSidePerimeterSquaredIs72` checks the **rational squared-length
arithmetic**, conditional on those side-count and length premises. A finite
polygon's perimeter is not the circumference of a circle. The screenshot does
not establish regularity, circumscription/inscription geometry, a radius, or
an equality with \(2\pi r\).


**Ambiguous decimal point in the reel.** Writing `0.5` does not specify
one-half if *the numerals themselves are base twelve*: `(0.5)_{12}=5/12`,
whereas `(0.5)_{10}=1/2=(0.6)_{12}`. Accordingly, if the visible
`0.5 sqrt(2)` is truly written in dozenal, the squared side length is
`25/72` and twelve equal sides imply **P² = 50**, not 72:

\[
s_{\mathrm{dozenal}}=\frac5{12}\sqrt2,\quad
P=12s=5\sqrt2,\quad P^2=50.
\]

The separate exact Agda theorem
`twelveDozenalDotFivePerimeterSquaredIs50` checks this interpretation.
The same rendered token `12` itself means *fourteen* if parsed in base
twelve (`(12)_{12}=14` decimal); actual side count must be obtained by
counting, not by reading an unspecified numeral. Both perimeter theorems
are conditional on **twelve counted sides**, not on what the author
meant by an ambiguous printed numeral.

For a genuine regular inscribed dodecagon of radius \(r\), a *separate*
standard analytic calculation gives

\[
 P_{\rm in}=24r\sin(\pi/12),\qquad
 P_{\rm out}=24r\tan(\pi/12).
\]

These yield strict lower and upper approximations to \(2\pi r\), not a
replacement of pi. No Agda real-trigonometric proof is claimed in this tranche.

**Non-identifications:** positional base 12, twelve angular sectors \(C_{12}\),
the existing \(p=13\) unit-group witness with order 12, and a dodecagon are
not the same mathematical object merely because they share the integer 12.
An explicit operation-preserving map/intertwiner is required to move from
one carrier to another. This follows the repository's existing role boundary.

## C. Black Stone: text, ritual, material, and belief

Hadith 1597 reports Umar ibn al-Khattab kissing the Black Stone because he
had seen Muhammad do so, while declaring the stone itself could neither
harm nor benefit. **Umar is a companion and later caliph, not a prophet in
Islam**; the screenshot's "my prophet Omar" is a factual category error.
This passage is a strong textual basis for a non-idolatrous explanation of
the ritual *within its tradition*, not laboratory evidence about the material
or divine claims. It is incorrect to describe the Black Stone **alone** as
the qiblah: the directional focus of Islamic ritual prayer is the Kaaba.

Separate four propositions:

1. *Textual*: a named hadith compilation contains a report ascribed to Umar
   with this content — verified against 1597.
2. *Interpretive*: kissing the stone can be explained as following the
   prophetic precedent — a customary theological explanation, attributed.
3. *Material*: the object's geological composition/history — requires
   identified samples and chain of custody; no direct original-stone sample
   is established by the screenshot.
4. *Metaphysical*: the stone's claimed heavenly origin or divinely assigned
   status — theological assertions, not empirically certified by the photo
   or material analysis.

The atlas keeps `classicalTextWitness` and `scientificPhysicalAssay`
different constructors and proves they cannot be silently identified. This
is a type distinction about *evidence roles*, not a proof that any religion
is true or false.

## Pareto / max-cut completion and debts

**Delivered source-written:**

- finite exact base-10/base-12 fraction equality, proof that identical
  printed dot-five notation has different values across radices, and
  both conditional 12-sided perimeter-squared readings (72 and 50);
- explicit separation of radix/C12/P13 roles;
- seven-entry attributed source atlas, distinguishable evidence roles and
  reuse of the existing clipping postprocessing theorem;
- falsifiable observation and historicity requirements, with source roots
  separated from repeated retellings.

**Held:** complete irrationality/real-circle theory port; direct GOES-451M
measurements/controlled comparison; authenticated screenshot source video;
physical same-object geology; external historical triangulation. None can be
paid by adding a Boolean `true`, an uninhabited certificate type, or a
borrowed unrelated proof.

**Source-writing is not kernel verification.** Run, in the repository's
established Agda environment:

```sh
agda -i . DASHI/Foundations/BaseTwelveCircleRepresentationBoundaryExact.agda
agda -i . DASHI/Culture/ScreenshotOpticsRadixBlackStoneAttributionExact.agda
```

These commands have not been executed in the present environment (no `agda`
executable was available). Do not promote the branch to kernel-verified from
static inspection.
