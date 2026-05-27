# Penguin Decay Empirical Roadmap

Current state: `frozenEvaluableResidualTargetPromotionBlocked`.

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

Reduced remaining blockers after the CMS checksum receipt:

- flavio provider/package digest;
- flavio runtime environment digest;
- Wilson coefficient authority digest;
- no-posterior-tuning attestation;
- projection-code freeze hash;
- LHCb selected-thread artifact checksum if the lane stays on the original
  LHCb thread instead of the CMS checksum-populated candidate.

No LHCb penguin HEPData checksum, flavio package digest, SM-baseline digest,
Wilson authority digest, CKM commit receipt, or projection artifact digest has
been supplied locally.  The CMS table checksum is concrete authority-candidate
data, but it does not promote the selected LHCb-specific thread observable.
Therefore the canonical result remains fail-closed: `currentOutcome =
insufficientAuthority`, `freezeGateOpen = false`, and promotion remains false.

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
