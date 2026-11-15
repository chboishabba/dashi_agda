# Woogaroo / Springview — first-party 2025 audit of earlier action EPBC 2014/7306
**As at 10 November 2026 · original-source audit cut · NOT a legal finding about EPBC 2019/8575.**

## Newly acquired original-government finding

The National EPA publishes a summary of its **2025 compliance audit** for **EPBC 2014/7306, Springview Village One, Springfield, Ipswich City, Queensland**, naming **Stockland Development Pty Limited** as approval holder. Exact displayed audit scope: conditions **1, 2, 3, 4, 5, 6, 7A, 7B, 7C, 8, 9** (11 provisions); results **seven compliant; four not applicable**. The summary reports **no noncompliance among its assessed categories**. It does **not** say which four conditions were inapplicable, certify all conditions outside the scope, identify the authorised 7.6-ha overlap, or provide actual land clearing geometry.

Original government page: https://www.nationalepa.gov.au/epbc/compliance/audits (section “2025”, row “EPBC 2014/7306&”; sourced 10 Nov 2026). This is genuine government publication text, **not** the full audit report and not a physical site survey carried out here.

Separately, the published Stockland **2023 annual compliance report** for Kalina / EPBC 2014/7306 identifies the earlier action's commencement as **9 July 2018**, a *proponent-reported* date, not independently verified by this audit summary: https://www.stockland.com.au/globalassets/residential/qld/kalina/documents/annual-compliance-report-to-8-july-2023.pdf . Older 2019 reports describe a 25 September 2018 Department visit and letter finding compliance with *conditions 1 and 2 at that time* — also not confirmation of all 7.6-ha polygon impacts. Source: https://www.stockland.com.au/globalassets/residential/qld/kalina/news-and-events/annual-compliance-report-to-8-july-2019.pdf .

## Why this is material to the later approval audit

The actual January 2026 consultant preliminary documentation for EPBC **2019/8575** states that approximately **7.6 hectares** attributed to **EPBC 2014/7306** were excluded from the later action's residual habitat-impact quantity. The original signed 16 October 2026 decision identifies an overall **134.9-ha footprint** and species-specific **128-ha koala habitat clearance limit**. The arithmetic `134.9 - 7.6 = 127.3`, a further 0.7 ha from historical `128.0` input, is already source-written in `SensibLawWoogarooOperativeInstrumentEvidenceCut20261109Exact.agda`.

**The new audit pays one narrow original-source leaf**: Commonwealth independently inspected compliance for the distinct earlier action and reported a summary with no adverse findings within this scope. It does *not* pay the legally or physically decisive exclusion identity:
- exact mapped **2014/7306 permitted-impact polygon**, approval/version and legal effective extent;
- **actually cleared** polygon with date, source and matters of national environmental significance;
- exact **2019/8575 July Issue F impacted/residual polygon**, assessment-unit map and same habitat definitions;
- legally grounded overlap/exclusion rule avoiding double-counting or undercounting;
- area/geometry/rounding reconciliation of **7.6**, **127.3**, **128.0**, **134.9**; and
- whether the Commonwealth's **2019/8575** decision actually considered the 2014/7306 exclusion and applicable ecological impact on its own record.

This distinction cuts both ways. The earlier approval's audit makes it less tenable to claim that there was no other project-specific Commonwealth approval or regulatory history. It also does **not** make an ecological adequacy or legal arithmetic finding for the new approval. Do not present the 7 audited compliant conditions as evidence that the 2019/8575 offsets are adequate, or treat the four “not applicable” classifications as four completed obligations.

## Formal original-source provenance firewall

Added `DASHI/Law/SensibLawWoogarooPriorActionAuditScope20261110Exact.agda` and imported it into both `SensibLawWoogarooPreservationEverything` and `DASHI.Law.Everything`.

- `original2025AuditSummary`: **2014/7306** scoped 7-compliant/4-not-applicable/0-reported-noncompliant/11-audited category witness; does NOT specify condition-level classifications.
- `originalAuditCategorySum`: exact `7 + 4 + 0 ≡ 11`.
- `originalPriorAuditIsNotCurrentApprovalAudit`: rejects an identity proof between action scopes **2014/7306** and **2019/8575**. This is about project identity, not whether the landscapes overlap.
- The actual `originalPrior20147306ApprovedImpactPolygonJoin`, `originalPrior20147306ActualClearingPolygonJoin`, `original20198575ExcludedHabitatMapSameObject`, and `original95B95C136SameDecisionConsideration` remain **OPEN**.

Agda 2.9 **not available in this runtime**; source-written declarations are **NOT kernel certified**. Unlike hypothetical ecological data, the published government summary is a real original **textual** source. No original audit PDF, original VDEC, future accepted workbook, government s95C or independent field survey was obtained.

## Highest-alpha next source acquisition

Request the **full 2025 Commonwealth 2014/7306 audit report and scope schedules**, with the original 2014/7306 signed approval and any variation, clearing-layout GIS and 2025 audit inspection boundaries; separately obtain the **July 2026 final 2019/8575 PD Issue F polygon layer**. The real proof is the exact spatial and legal same-object join, not another rounded subtraction or an assumption from audit categories.

The immediate preservation-critical C24/C25 VDEC, commencement and threatened-work chronology remains higher urgency than this retrospective exclusion comparison. No request or regulatory/court filing has been sent.

## 10 November 2026 — earlier-action source map and executable intersection cut

**Genuinely located cartographic source**: Saunders Havill Group for Stockland Development Pty Ltd, *Annual Compliance Report*, 9 July 2022–8 July 2023 (Year 5), 6 October 2023, EPBC **2014/7306**: https://www.stockland.com.au/globalassets/residential/qld/kalina/documents/annual-compliance-report-to-8-july-2023.pdf . The retrieved report text at pp. 1, 4 and figure index reports **up to 39.75 ha** permitted impact to koala habitat for the older approval, works commenced **9 July 2018**, and no new vegetation clearing in the **2022–23** reporting year (other clearing reportedly in **2021–22**). These are **consultant/proponent report assertions**, not verified field measurements, official audit findings of every area or proof of the 7.6-ha excluded parcel. Figure 2 (printed report page 10), *Site Aerial*, labels **“EPBC Act approved Clearance Area”** with scale 1:7,000 and source CRS **GDA 1994 MGA Zone 56** (EPSG:28356); Figure 1 separately shows the approved clearance area at 1:50,000. Original PDF raster screenshot fetch failed because of its 25MB file size, so the figure has NOT been independently visually inspected, measured, georeferenced, or digitised. **Do not infer a GIS coordinate geometry from text alone.**

The report reproduces old approval documents in annexures (different source types from the report itself); its summary contains **inconsistent old-approval date strings** (one list says 12 June 2016, a summary says 14 September 2016). The actual original signed 2014/7306 instrument/version must settle the date, not an arbitrary selection of one reported value. Its stated legal description includes Lot 43 on SP2442290, but later aerials show changed lot identifiers; cadastral succession must be source-mapped before treating coordinates as the same land.

**New high-alpha executable geospatial owner:** `scripts/check_woogaroo_older_action_geometry_20261110.py` is source-committed to the PR. It requires four SHA-256-matched GeoJSON layers: `prior_approved_impact`, `prior_actual_clearing`, `current_excluded_habitat`, `current_final_impact`. Each layer must state exactly the same **projected metric CRS** (no degrees, mixed CRS or assumed reprojection), with valid polygon geometries; computes hectares for intersections and differences including excluded area inside prior authorisation *versus* prior physical clearing. These intersections are **not** a legal or ecological same-object/attribution proof. Only original GIS or properly documented georeferenced traces with uncertainty can pay the area-identity gate.

**Verification discipline:** A local independent *equivalent* Shapely/pyproj reference checker passed **9/9 synthetic tests** and Python syntax compilation, at SHA256 `706fe10cdc61f9e73f13c917517a61c8bfe3b184e8da733161cd580f7b59b643`. The exact GitHub committed script is a separately authored, functionally matching implementation and has **not yet been executed as exact byte-identical code**; do not claim a 9/9 exact-repository receipt. The example uses EPSG:7856 only for synthetic metre-square coordinates, whereas the historical map text identifies EPSG:28356: in real comparison, source-authoritative CRS/coordinate transform accuracy must be determined; never silently declare GDA94 and GDA2020 interchangeable.

**New target lemma/specification:** `originalPriorApprovedVersusActualClearingExcludedSameHabitatPolygon` — for the exact original 2014/7306 approved, actually cleared, 2019/8575 excluded and final impacted polygons, show legally appropriate intersections with a common coordinate system, correct habitat class and timeline. The strongest result would distinguish (i) genuine overlap inside both older approval and dated older clearing, (ii) excluded land within older approval but **not actually cleared**, (iii) excluded land outside older approval entirely, and (iv) whether the final 2019/8575 workbook consistently encodes those cases. None is presently proved for the actual site.

## 11 November 2026 — exact-blob GIS checker execution and projected-area safeguard

`scripts/check_woogaroo_older_action_geometry_20261110.py` now explicitly limits directly comparable projected-area inputs to the locally relevant MGA Zone 56 CRSs **GDA94 EPSG:28356** and **GDA2020 EPSG:7856**. This closes a false-positive path in the original tool where *any* projected metre CRS, including area-distorting Web Mercator EPSG:3857, was accepted for 7.6-ha comparisons. The tool continues to reject mixed CRSs, invalid geometry, path escapes, SHA256 mismatch, and unprovided source roles. **It does not transform coordinates across datums**, authenticate a record's asserted CRS, verify polygon survey precision or establish lawful exclusion.

**Exact-source receipt**: revised source commit `eb4aea6`, GitHub blob `4a9919b0677605ac41e4776be5417384b334cfdf`. The byte-identical locally reconstructed script has `git hash-object == 4a9919b0677605ac41e4776be5417384b334cfdf`; `python -m py_compile` **PASS**, `--self-test` **10/10 PASS**, including explicit EPSG:3857 rejection. Receipt `/mnt/data/woogaroo_geometry_exact_10case_receipt_20261111.json`. These are *synthetic* tests; no original approved, actually cleared, excluded or final-impact GIS layers were obtained. A local MGA56 grid area is not exactly an ellipsoidal/geodesic area; source-map geometric/scale tolerances require expert confirmation.

**Real remaining gate**: `originalPriorApprovedVersusActualClearingExcludedSameHabitatPolygon` still requires original source-verified signed prior approval and georeferenced clearance, independently dated actual clearing polygon, 2019/8575 final accepted excluded habitat and residual-impact polygon, valid datum transformation provenance, habitat type and legal exclusion criteria. The fact that a map is GDA94/MGA56 is a *source attribution*, not proof that any manually labelled GeoJSON values represent that map. Main live preservation A0 remains original C24/C25 Voluntary Declarations, commencement and physically dated works.
