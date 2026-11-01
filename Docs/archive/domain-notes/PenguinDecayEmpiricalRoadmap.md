# Penguin Decay Empirical Roadmap

Current state: `frozenEvaluableResidualTargetPromotionBlocked`.

Prediction-frontier sync `2026-05-28`: the `C9/P5'` lane is a
non-promoting prediction target only.  It records the intended Wilson/LHCb
residual comparison target and now binds the current full Run 1+2 HEPData
value/correlation table checksums.  The freeze tuple, Wilson authority digest,
projection-code hash, no-posterior-tuning attestation, and accepted
residual-vector construction remain absent.  No anomaly, discovery, accepted
residual, or empirical adequacy theorem is claimed.
The current public LHCb target is the full Run 1+2
`B0 -> K*0 mu+ mu-` angular analysis (`LHCb-PAPER-2025-041`,
`arXiv:2512.18053`, `CDS:2951844`, 8.4 fb^-1).  The 2020
`LHCb-PAPER-2020-002` / `arXiv:2003.04831` / `HEPData:ins1798504` route is
recorded as the stable machine-readable fallback only.  The asserted
`HEPData 160745` route is fail-closed here: the reachable/local artifacts
resolve to `HEPData:159893` / `INSPIRE:2922449` b-jet mass Table 16, not a
P5' value/covariance payload.  The local Table 16 YAML hash is
`47868e1936dc9f8b4bd20f2aa25ffe2350307737b346394d252d8c5b256ef256`; the
companion JSON hash is
`e182f28137dae0f43be0b99c11d728cd9509d09cc47f66cd64462a897738ea43`.  These
hashes are negative provenance for the P5' lane, not accepted P5' authority.
The current full Run 1+2 HEPData table is bound as
`10.17182/hepdata.167733.v1/t2`, local file
`scripts/data/hepdata/ins3094698/table-config-2-results-record-data-167733-1911073.json`,
SHA256 `8ee74f4e774889eced2090fe60bbdaf681dd327dc1a349add992e038c7f62623`.
The associated total/stat/syst correlation JSON resources are also bound with
SHA256 values `d3ce138b3d7a3fe0a2777fe87ebe2e9161f14ff4d1ca66ff576d6e271a03c624`,
`452a3252a6648dc1a0bd3d48907c271850f646c2c0339f07c8a151ab16edf5c0`, and
`d15787e808c195ce4126483b6f7d524b49f718320728a06555c1cb4f3b05a7d8`.
The follow-up `PenguinDecayCarrierDerivedC9ConstraintTargetReceipt` wires the
carrier CKM/Yukawa surfaces into the `C9_NP` sign/magnitude question, but keeps
the physical C9 value, Wilson acceptance, empirical constraint, and anomaly
claim false.

For this lane, empirical contact means the diagnostic surfaces are inhabited:

- `PenguinDecayProjectionDefectReceipt`
- `PenguinDecayObservableContract`
- `PenguinDecaySMBaselineAuthority`
- `PenguinDecayProjectionArtifact`
- `PenguinDecayResidualComparisonLaw`
- empirical candidate diagnostic aggregator

This is not a discovery claim. It does not promote a non-Standard-Model
effect, accepted external empirical authority, or empirical adequacy theorem.
The current Agda aggregator records contact as contract + authority + artifact
+ comparison diagnostic surfaces, with empirical promotion explicitly false.

The aggregator now imports the dedicated contract, authority, artifact, and
comparison-law modules directly. The selected lane has empirical contact in the
repo sense: typed diagnostic surfaces are present and wired, while the current
comparison outcome remains `insufficientAuthority` and promotion is false.

Second-wave validation and composition status: full `DASHI/Everything.agda`
validation passed with `-i . -i DCHoTT-Agda -i cubical -l standard-library`.
The Gate 8 partial-composition receipt consumes the penguin freeze status as a
current receipt, but only with `freezeGateOpen = false` and promotion false.
This consumption does not make the selected LHCb lane evaluable, does not
promote DR/Standard Model matching, and does not construct Paper 7.

The projection artifact request now includes a concrete freeze-hash
pre-registration tuple.  It names the selected dataset artifact and digest,
dataset authority binding, HEPData-or-equivalent record/table/checksum slots,
SM-baseline authority digest, flavio provider/version/package/environment/
parameter-card digest slots, Wilson-coefficient authority digest, CKM source
commit/source authority, projection-code freeze hash, and no-posterior-tuning
attestation.  The freeze gate remains closed until all of those authorities are
populated.

Current concrete freeze status:

- `PenguinDecaySMBaselineAuthority` no longer imports the Wilson authority
  module cyclically; it carries frozen Wilson provider/version/digest slots and
  stays fail-closed.
- `PenguinDecayWilsonCoefficientAuthority` packages the flavio provider
  version (`2.7.0`) with required package, runtime environment, and parameter
  card digest fields.  It now also records a concrete `C9SM/C10SM` authority
  digest slot with named missing blockers for C9 value, C10 value, sign/basis,
  scale/Hamiltonian convention, and the final authority digest.  These are
  required slots, not accepted digests.
- `PenguinDecayObservableContract` now has a dataset-source discriminator with
  two concrete candidates.  CMS HEPData record `ins2616304` v1, DOI
  `10.17182/hepdata.135675.v1/t1`, table id `1435213`, table `Results`, and
  local artifact `/home/c/Downloads/HEPData-ins2616304-v1-Results.yaml` are
  typed as an authority-candidate checksum receipt with SHA256
  `08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb`.  The
  original thread-selected LHCb PRD/CDS lane
  `10.1103/PhysRevD.105.012010` / `CERN-CDS:2779103` remains fail-closed
  until its own exact artifact/checksum is supplied.
- `PenguinDecayProjectionArtifact` separates SM-baseline and Wilson authority
  digest roles, adds HEPData record/table/checksum slots, records the CMS table
  checksum as a populated candidate, keeps
  `selectedThreadChecksumAuthorityPresent = false` for the LHCb-specific lane,
  records a concrete CKM source commit freeze slot, and records exact
  no-posterior-tuning blockers for dataset checksum, SM baseline, Wilson
  provider digest, CKM commit, projection-code hash, and signed attestation.
  It also exposes
  `canonicalPenguinCMSChecksumPopulatedReadinessReceipt`, a concrete readiness
  receipt proving CMS dataset checksum authority is present for HEPData
  `ins2616304` v1 Results table DOI `10.17182/hepdata.135675.v1/t1`, table id
  `1435213`, SHA256
  `08a244d15702168288d1bf414423bcbc05c5c176c229280b2e185c5cd0bee9eb`, while
  proving the selected LHCb thread checksum remains false.
- `PenguinDecayCKMLoopFactorProjection` exposes the CKM source commit and
  source-authority slots for the `Vtb Vts*` loop factor.  The canonical slot is
  required and not accepted here.
- `PenguinDecayResidualComparisonLaw` and
  `PenguinDecayEmpiricalCandidateDiagnostic` expose the conditional
  `acceptedResidualCandidate` bridge only as a parameterized typed path that
  requires a selected-thread SHA256 dataset checksum authority plus accepted
  authority, freeze, data, and controlled-theory prerequisites.  The canonical
  expected comparison record is now authority-gated as `insufficientAuthority`;
  there is no canonical accepted residual prerequisite witness fabricated while
  the selected LHCb checksum is absent.  The live canonical diagnostic reports
  CMS authority populated as a candidate but LHCb authority missing, so the
  current outcome remains `insufficientAuthority`.
- `PenguinDecayLHCbChecksumAcceptedResidualReceipt` now also records the CERN
  repository route as route evidence only.  The attempted `ins2101841` route is
  now recorded as a negative provenance check: HEPData `/record/ins2101841`
  returned 404 here, and INSPIRE `2101841` is unrelated to the selected LHCb
  DOI, which resolves as INSPIRE `1908217`.  The checked CDS supplementary ZIP
  contains only the supplementary PDF/TeX, README, and figure assets, so this
  still does not populate a value-table or covariance-table checksum.
- `PenguinDecayLHCbChecksumAcceptedResidualReceipt` also records the upgraded
  P5'/C9 target split: the 2025 full Run 1+2 public result
  (`LHCb-PAPER-2025-041` / `arXiv:2512.18053` / `CDS:2951844`) is the current
  target; `HEPData:ins1798504` remains fallback-only; and the supplied
  `HEPData 160745` / `ins2922449` Table 16 YAML/JSON artifacts are explicitly
  rejected because they encode b-jet mass, not P5' angular observables.  The
  typed residual law is
  `r = (obs - SM) / sqrt(stat^2 + syst^2 + th^2)` with published signed pulls
  `[4,6] = -2.8 sigma` and `[6,8] = -3.0 sigma`; the current classification is
  `p5PrimeBorderlineAnomalyCandidate`, while `acceptedResidualCandidate` and
  the frozen residual-vector artifact remain false.
  The current full Run 1+2 table/correlation checksum is bound separately from
  the stale 2020 fallback and the rejected `160745` route.

Reduced remaining blockers after the CMS checksum receipt:

- flavio provider/package digest;
- flavio runtime environment digest;
- Wilson coefficient authority digest;
- no-posterior-tuning attestation;
- projection-code freeze hash;
- accepted freeze tuple consuming the bound LHCb value/correlation checksums.

No accepted flavio package digest, SM-baseline digest, Wilson authority digest,
CKM commit receipt, projection artifact digest, no-posterior-tuning
attestation, or frozen residual-vector artifact has been supplied locally.
The current LHCb table/correlation checksums are concrete bound data, the CMS
table checksum is concrete authority-candidate data, and the rejected Table 16
hashes are concrete negative provenance.  None of these promotes the selected
LHCb-specific thread observable.  Therefore the canonical result remains fail-closed:
`currentOutcome = insufficientAuthority`, `freezeGateOpen = false`, and
promotion remains false.

Target state for the next integration pass: advance the lane from generic
`insufficientAuthority` toward a frozen, evaluable residual. That means:

- keep `PenguinDecayResidualComparisonLaw.currentOutcome` fail-closed until an
  accepted authority route exists;
- freeze the chosen penguin observable, dataset binding, covariance treatment,
  theory-uncertainty budget, and projection-artifact digest before comparison;
- replace every `required:` authority slot with an immutable external receipt
  before constructing any evaluable residual;
- wire CKM loop inputs through the existing carrier chain rather than treating
  the SM baseline as an opaque external input;
- consume the exact CKM/Yukawa carrier witnesses where available, including
  `CKMExactWitnesses`, `CKMCarrierDerived`, `CKMUnitarityFromCarrier`,
  `YukawaFromCarrier`, and `YukawaDHRIntertwinerCompatibility`;
- report an evaluable residual only after those frozen inputs and CKM-loop
  dependencies are visible in the typed receipt.

Promotion remains blocked even after the residual becomes evaluable. The
honest next state is a reproducible residual comparison artifact with CKM-loop
wiring and a named authority gap, not a physics discovery or empirical
adequacy theorem.
