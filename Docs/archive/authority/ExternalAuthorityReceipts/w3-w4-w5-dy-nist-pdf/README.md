# W3/W4/W5 Authority Receipt Bundle

Last refreshed: 2026-05-20.

This bundle freezes external authority artifacts for the empirical Drell-Yan,
physical-unit/calibration, chemistry, PDF, and functional-analysis lanes. These
artifacts are authority inputs only; they do not promote W3, W4, W5, W8, or the
terminal Paper 7 receipt.

## Corrections To Supplied Targets

The supplied HEPData and Springer targets were close but not exact for
CMS-SMP-20-003:

- Correct HEPData record: `https://www.hepdata.net/record/ins2079374`
- Correct HEPData DOI: `10.17182/hepdata.115656`
- Correct publication DOI: `10.1140/epjc/s10052-023-11631-7`
- Correct article: Eur. Phys. J. C 83 (2023) 628

The supplied `ins2627448` URL returned HTTP 404 during acquisition.

## Local Artifacts

| Lane | Local file | Source URL | SHA256 |
|---|---|---|---|
| W3/W4/W5 Drell-Yan | `cms-smp-20-003-page.html` | `https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/` | `f5c09ded5550d4c2d01dfbe712ef49682de270de2c8ccf4e29d70b696ab1666f` |
| W3/W4/W5 Drell-Yan | `cms-smp-20-003-epjc-83-628.pdf` | `https://scoap3-prod-backend.s3.cern.ch/media/files/79030/10.1140/epjc/s10052-023-11631-7_a.pdf` | `d494318f29e18c0a8314a1ac241208ed9cc44a618b8aa220e1786361ed16c21c` |
| W3/W4/W5 Drell-Yan | `cms-smp-20-003-hepdata-submission.yaml` | `https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/submission.yaml` | `917a23b6c873c2acc623758cd6938c47f010da956a4d4fd9cbcda258632ed74c` |
| W3 phi-star baseline | `cms-smp-20-003-phistar-mass-76-106.yaml` | CMS public `SMP-20-003_hepdata/phistar_mass_76-106.yaml` | `82161d46a14549f4f00e74a3068ea235b336c22e427dc310b22e879689204602` |
| W3 phi-star covariance | `cms-smp-20-003-cov-phistar-mass-76-106.yaml` | CMS public `SMP-20-003_hepdata/covariance_matrices_for_phistar_mass_76-106.yaml` | `334a17580247c08e7e64aab03ef35e3eb2933bc81b84f1bd2b5d97d59a725392` |
| W3/W4 ratio | `cms-smp-20-003-phistar-mass-50-76-over-76-106.yaml` | CMS public `SMP-20-003_hepdata/phistar_mass_50-76_over_mass_76-106.yaml` | `2878a27ff89162051c9822777acd445a679672e6154d4adb9b1a274bad0b1a51` |
| W3/W4 ratio | `cms-smp-20-003-phistar-mass-106-170-over-76-106.yaml` | CMS public `SMP-20-003_hepdata/phistar_mass_106-170_over_mass_76-106.yaml` | `b13fc46b690221604b15932183982c08686ca633a2659197e045263258a0cfe9` |
| W4 constants | `nist-codata-2022-allascii.txt` | `https://physics.nist.gov/cuu/Constants/Table/allascii.txt` | `77fb90e66c40db3e6eb16630bc9c88e4c7c8beddbe5e71be406f2f26e3f67e67` |
| W4 chemistry | `nist-chemistry-webbook.html` | `https://webbook.nist.gov/chemistry/` | `28daefaabe6e9267f1f8cb02a357ba36d673033afbecdb569645c1a8e55056de` |
| W5 PDFs | `lhapdf-home.html` | `https://lhapdf.hepforge.org/` | `728337eda96a56e3d26eb07344d14c0464adbe31869255fec701b20d36222a4f` |
| W5 PDFs | `nnpdf4-home.html` | `https://nnpdf.mi.infn.it/nnpdf4-0/` | `72c69032017d1b3b14e164615f169258a99140965ad91ff29bfbc5bcad5a732e` |
| W5 PDFs | `msht-grids.html` | `https://www.hep.ucl.ac.uk/msht/grids.shtml` | `345d69b32acc32995c60e1a93dc6f61c8d349a5ae58ed681ecd0f173aa970885` |
| W5 selected PDF grid | `NNPDF40_nnlo_as_01180.tar.gz` | `https://lhapdfsets.web.cern.ch/lhapdfsets/current/NNPDF40_nnlo_as_01180.tar.gz` | `6adff9ed17b71c0476b77342bf0295b300e7fa76332b6993ef678228a7d41eae` |
| W5 selected PDF grid | `MSHT20nnlo_as118.tar.gz` | `https://lhapdfsets.web.cern.ch/lhapdfsets/current/MSHT20nnlo_as118.tar.gz` | `772b745c1af7fd24561cee05724edd2f70975b697226c2ecc5f916f01829534f` |

## Functional-Analysis Authority Targets

These are bibliographic authority targets for `RealAnalysisAxioms` and
Hilbert/Stone/self-adjointness boundaries. They were not mirrored as local PDFs.

| Boundary | Target | URL |
|---|---|---|
| Functional analysis / spectral theorem / unbounded operators | Reed and Simon, *Methods of Modern Mathematical Physics I: Functional Analysis* | `https://archive.org/details/methodsofmodernm0001reed` |
| Perturbation/self-adjoint operator authority | Kato, *Perturbation Theory for Linear Operators* | `https://link.springer.com/book/10.1007/978-3-662-12678-3` |

## Receipt Boundaries

- W3 may consume the CMS/HEPData artifacts as empirical data authority, but still
  needs the local projection, comparison, uncertainty, and acceptance laws.
- W4 may consume NIST/CODATA and NIST Chemistry WebBook as physical-unit and
  molecular-data authorities, but still needs the DASHI dimensional preservation
  and calibration maps.
- W5 may consume the frozen `NNPDF40_nnlo_as_01180` and
  `MSHT20nnlo_as118` grids as selected PDF-set authorities, but still needs
  the local PDF-carrier adapter, convolution convention, and comparison law.
- W8 remains deliberately unfilled. Do not use a generic citation to promote W8;
  its receipt depends on the active origin route.
