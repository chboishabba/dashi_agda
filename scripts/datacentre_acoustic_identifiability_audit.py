#!/usr/bin/env python3
"""Illustrative acoustics audit: identical dBA can hide different tonal spectra.

No site data, human outcome, or acoustic safety claim is implied.
Python 3 standard library only.
"""
from dataclasses import dataclass
from math import log10, sqrt


@dataclass(frozen=True)
class Tone:
    hz: float
    db_spl: float


def a_weight_db(hz: float) -> float:
    """IEC-style analog frequency-response approximation, 0 dB at 1 kHz."""
    if hz <= 0:
        raise ValueError("frequency must be positive")
    f2 = hz * hz
    ra = (12194.0**2 * f2**2) / (
        (f2 + 20.6**2) *
        sqrt((f2 + 107.7**2) * (f2 + 737.9**2)) *
        (f2 + 12194.0**2)
    )
    return 20 * log10(ra) + 2.0


def combined_level_db(levels):
    levels = list(levels)
    if not levels:
        raise ValueError("at least one tone is required")
    return 10 * log10(sum(10**(v/10) for v in levels))


def a_weighted_level(tones):
    return combined_level_db(t.db_spl + a_weight_db(t.hz) for t in tones)


def flat_level(tones):
    return combined_level_db(t.db_spl for t in tones)


def claimed_percent_to_db(percent_increase: float, ratio_kind: str):
    """A percent comparison needs a named amplitude or power quantity."""
    if percent_increase < 0:
        raise ValueError("negative percent increase not supported")
    ratio = 1 + percent_increase / 100.0
    if ratio_kind == "pressure_amplitude":
        return 20 * log10(ratio)
    if ratio_kind == "acoustic_power":
        return 10 * log10(ratio)
    raise ValueError("specify pressure_amplitude or acoustic_power")


def same_la_example(la_target=35.0):
    low = Tone(31.5, la_target - a_weight_db(31.5))
    high = Tone(125.0, la_target - a_weight_db(125.0))
    assert abs(a_weighted_level([low]) - la_target) < 1e-8
    assert abs(a_weighted_level([high]) - la_target) < 1e-8
    assert abs(flat_level([low]) - flat_level([high])) > 20.0
    return low, high




# Operational source→receptor→outcome acceptance contracts for the ORIGINAL
# @itsgingertheory inquiry. A receipt is an original artifact's metadata, not
# independent authentication of its bytes, calibration, or conclusions.
# Distinct evidence families must not be collapsed by a common word "frequency".
from dataclasses import dataclass as _dataclass
from hashlib import sha256 as _sha256
import json as _json
import re as _re
import unittest as _unittest


@_dataclass(frozen=True)
class OriginalReceipt:
    """Claimed original artifact, provenance and same-site study window.

    Fields do NOT certify their contents: the audit tests only metadata,
    structural join eligibility and explicit independent-root claims.
    """
    kind: str
    site_id: str
    window_id: str
    root_id: str
    original_author: str
    original_date: str
    source_locator: str
    content_sha256: str



@_dataclass(frozen=True)
class PublicRepositoryRoot:
    """Original GitHub repository ancestry, not an observation of acoustic data."""
    apparent_owner: str
    apparent_repo: str
    source_owner: str
    source_repo: str
    is_fork: bool
    contents_domain: str


BENN_JORDAN_GITHUB_ROOTS = (
    PublicRepositoryRoot('bennjordan', 'MSEED2Wav_Android',
                         'dhilowitz', 'MSEED2Wav', True,
                         'seismology MiniSEED-to-WAV conversion code'),
    PublicRepositoryRoot('bennjordan', 'Datasets',
                         'MusicMoveArr', 'Datasets', True,
                         'MusicBrainz/Spotify/Tidal/Deezer metadata'),
)



from fractions import Fraction as _Fraction


def nominal_mseed_wav_playback_ratio(original_samples_per_second,
                                    output_wav_samples_per_second=96000):
    """A hypothetical sample-clock mismatch, NOT a sampled real waveform.

    dhilowitz/MSEED2Wav upstream Source/Main.cpp writes samples unchanged
    into WAV tagged at fixed 96000 sample/s; to interpret physical time
    one must retain the original MiniSEED sample rate and instrument
    response. Benn Jordan's fork is NOT evidence that he used this process.
    """
    for val in (original_samples_per_second, output_wav_samples_per_second):
        if type(val) not in (int, str, _Fraction):
            raise ValueError('exact positive sample rate required')
    try:
        old = _Fraction(original_samples_per_second)
        new = _Fraction(output_wav_samples_per_second)
    except (TypeError, ZeroDivisionError, ValueError, OverflowError) as exc:
        raise ValueError('valid rational sample rates required') from exc
    if old <= 0 or new <= 0:
        raise ValueError('sample rate must be positive')
    return new / old


def mseed_converter_metadata_witness():
    nominal = nominal_mseed_wav_playback_ratio(100)
    return {
        'upstream_original_author_root': 'dhilowitz/MSEED2Wav',
        'apparent_fork_distribution': 'bennjordan/MSEED2Wav_Android',
        'original_source_code_date': '2024-04',
        'example_original_samples_per_second': 100,
        'fixed_wav_output_samples_per_second': 96000,
        'nominal_acceleration_for_example': str(nominal),
        'example_3hz_physical_tone_would_play_at_hz': str(
            _Fraction(3) * nominal),
        'video_data_processing_use_proven': False,
        'raw_site_sound_pressure_calibration_proven': False,
    }


def original_repo_attribution(record):
    """GitHub fork cannot be promoted to independent original authorship."""
    if not isinstance(record, PublicRepositoryRoot):
        raise ValueError('expected typed repository root')
    if not all((record.apparent_owner, record.apparent_repo,
                record.source_owner, record.source_repo,
                record.contents_domain)):
        raise ValueError('all repository provenance roots are required')
    return {
        'apparent_repository': record.apparent_owner + '/' + record.apparent_repo,
        'upstream_original_repository':
            record.source_owner + '/' + record.source_repo,
        'original_repository_author_is_benn_jordan':
            not record.is_fork and record.source_owner == 'bennjordan',
        'is_independent_empirical_receptor_dataset': False,
        'content_description': record.contents_domain,
        'fork_presence_does_not_verify_use_in_2026_video': True,
    }


# Phase keys reference new *producer objects*, not ways to restate a review.
# Sound/vibration, RF, historical continuity and environmental mitigation
# have separate consumers and may NOT be inferred from one another.
REQUIRED_ORIGINALS = {
    'P2_calibrated_acoustic': (
        'facility_operating_log', 'original_sensor_waveforms',
        'source_pressure_spectrum', 'receptor_pressure_spectrum',
        'traceable_calibration', 'sensor_response_and_timebase',
        'processing_transform_manifest', 'weather_background_controls'),
    'P3_facility_attribution': (
        'matched_on_off_windows', 'receptor_spatial_gradient',
        'nonfacility_source_controls', 'uncertainty_budget'),
    'P4_health_outcome': (
        'prespecified_health_protocol', 'matched_person_or_site_outcomes',
        'outcome_confounder_and_attrition_audit',
        'independent_outcome_reproduction'),
    'P5_mitigation_policy': (
        'matched_before_after_mitigation', 'matched_facility_load',
        'receptor_metric_with_uncertainty',
        'applicable_site_jurisdiction_permit'),
    'P6_modern_rf_claim': (
        'calibrated_rf_field_source', 'receptor_rf_dosimetry',
        'authenticated_specific_device_record',
        'independently_observed_device_outcome',
        'documented_historical_to_modern_transfer'),
}

PARENT_PHASE = {
    'P3_facility_attribution': 'P2_calibrated_acoustic',
    'P4_health_outcome': 'P3_facility_attribution',
    'P5_mitigation_policy': 'P3_facility_attribution',
}


def audit_phase_receipts(receipts):
    """Fail-closed acceptance *inventory*, never physical/clinical validation.

    Accepts dict kind -> OriginalReceipt. A document can be cited without
    meeting any physical gate; synthetic matches certify only metadata shape.
    An RF manuscript or intelligence historical scan never pays an acoustic
    calibration receipt or a receptor health outcome.
    """
    if not isinstance(receipts, dict):
        raise ValueError('expected receipt dictionary')
    unknown = set(receipts).difference(
        kind for required in REQUIRED_ORIGINALS.values() for kind in required)
    if unknown:
        raise ValueError('unknown phase receipt type: ' + repr(sorted(unknown)))
    for kind, r in receipts.items():
        if not isinstance(r, OriginalReceipt) or r.kind != kind:
            raise ValueError('receipt kind must match typed key')
        for value in (r.site_id, r.window_id, r.root_id, r.original_author,
                      r.original_date, r.source_locator):
            if not isinstance(value, str) or not value.strip():
                raise ValueError('nonblank original identity/locator required')
        if (not isinstance(r.content_sha256, str) or
            not _re.fullmatch('[0-9a-f]{64}', r.content_sha256)):
            raise ValueError('64-character lowercase claimed content hash required')
    result = {}
    for phase, required in REQUIRED_ORIGINALS.items():
        listed = [k for k in required if k in receipts]
        missing = [k for k in required if k not in receipts]
        # These are common *study/comparison block* IDs, not identical
        # exposure instants. A site-independent replication and a historical
        # source may by design refer to DIFFERENT places, times and roots.
        # They must never be forced into the original receptor window.
        comparison_kinds = {
            'P2_calibrated_acoustic': (
                'facility_operating_log', 'original_sensor_waveforms',
                'source_pressure_spectrum', 'receptor_pressure_spectrum',
                'sensor_response_and_timebase',
                'processing_transform_manifest',
                'weather_background_controls'),
            'P3_facility_attribution': (
                'matched_on_off_windows', 'receptor_spatial_gradient',
                'nonfacility_source_controls', 'uncertainty_budget'),
            'P4_health_outcome': (
                'prespecified_health_protocol', 'matched_person_or_site_outcomes',
                'outcome_confounder_and_attrition_audit'),
            'P5_mitigation_policy': (
                'matched_before_after_mitigation', 'matched_facility_load',
                'receptor_metric_with_uncertainty'),
            'P6_modern_rf_claim': (
                'calibrated_rf_field_source', 'receptor_rf_dosimetry',
                'authenticated_specific_device_record',
                'independently_observed_device_outcome'),
        }[phase]
        joined = [k for k in comparison_kinds if k in receipts]
        site_ids = {receipts[k].site_id for k in joined}
        windows = {receipts[k].window_id for k in joined}
        parent = PARENT_PHASE.get(phase)
        parent_ready = True if parent is None else result[parent]['metadata_join_ready']
        same_site_window = len(site_ids) <= 1 and len(windows) <= 1
        # Parent and child stages of the main acoustic investigation need
        # the SAME site and study-block identity: do not join an unrelated
        # 'healthy control' site to another site's noise measurement.
        root_site = receipts.get('source_pressure_spectrum')
        if parent is not None and root_site is not None and joined:
            first = receipts[joined[0]]
            same_site_window = same_site_window and (
                first.site_id == root_site.site_id and
                first.window_id == root_site.window_id)
        # A genuine replication must have an independent provenance root
        # and may be at another site/time. This only checks CLAIMED roots.
        distinct_replica = True
        if (phase == 'P4_health_outcome' and
            'independent_outcome_reproduction' in receipts and
            'matched_person_or_site_outcomes' in receipts):
            distinct_replica = (
                receipts['independent_outcome_reproduction'].root_id !=
                receipts['matched_person_or_site_outcomes'].root_id)
        ready = not missing and same_site_window and parent_ready and distinct_replica
        result[phase] = {
            'expected_original_artifacts': list(required),
            'missing_original_artifacts': missing,
            'metadata_site_window_consistent': same_site_window,
            'claimed_replication_root_distinct': distinct_replica,
            'parent_phase': parent,
            'metadata_join_ready': ready,
            'independent_source_roots_claimed': len({
                receipts[k].root_id for k in listed}),
            'actual_calibration_or_bytes_authenticated': False,
            'facility_emission_identified': False,
            'health_causation_established': False,
            'intentional_rf_deployment_established': False,
        }
    return result


def original_inquiry_phase_status():
    """As-of-2026-10-27: no primary same-site study objects supplied here."""
    return {
        'creator_claim_original': 'Instagram reel DbqY4jLxuhs / uploaded SRT/screenshots',
        'review_not_observational_trial':
            'Pignatelli et al., Environments (2026), DOI 10.3390/environments13100568',
        'review_studies': 36,
        'environmental_pressure_only': 18,
        'receptor_exposure': 12,
        'modelled_health': 6,
        'observed_health': 0,
        'quantitative_estimates': 112,
        'without_comparator': 93,
        'reporting_confidence_interval_95pct': 11,
        'environmental_noise_studies': 5,
        'review_counts_are_study_level_not_original_trial_repetitions': True,
        'phases': audit_phase_receipts({}),
    }


class TestOriginalInquiryAcceptance(_unittest.TestCase):
    def _receipt(self, kind, site='synthetic-site', window='synthetic-window'):
        return OriginalReceipt(
            kind, site, window, 'synthetic-root-' + kind,
            'illustrative-author-not-a-site-investigator', '2026-01-01',
            'synthetic-fixture-only', _sha256(kind.encode()).hexdigest())

    def test_no_original_site_receipts_means_all_empirical_phases_open(self):
        state = audit_phase_receipts({})
        self.assertEqual(len(state), 5)
        self.assertTrue(all(not p['metadata_join_ready'] for p in state.values()))
        self.assertTrue(all(p['missing_original_artifacts'] for p in state.values()))


    def test_benn_jordan_repositories_are_forks_not_original_authorship(self):
        records = [original_repo_attribution(r)
                   for r in BENN_JORDAN_GITHUB_ROOTS]
        self.assertEqual([r['upstream_original_repository'] for r in records],
                         ['dhilowitz/MSEED2Wav', 'MusicMoveArr/Datasets'])
        self.assertTrue(all(not r['original_repository_author_is_benn_jordan']
                            for r in records))
        self.assertTrue(all(not r['is_independent_empirical_receptor_dataset']
                            for r in records))

    def test_converter_and_playback_do_not_fill_original_site_waveform_gate(self):
        available = audit_phase_receipts({})
        self.assertIn('original_sensor_waveforms', available[
            'P2_calibrated_acoustic']['missing_original_artifacts'])
        self.assertIn('sensor_response_and_timebase', available[
            'P2_calibrated_acoustic']['missing_original_artifacts'])
        self.assertIn('processing_transform_manifest', available[
            'P2_calibrated_acoustic']['missing_original_artifacts'])
        for false_kind in ('edited_video_audio', 'playback_wav',
                           'miniSEED_converter_fork', 'patreon_audio_preview'):
            with self.assertRaises(ValueError):
                audit_phase_receipts({false_kind:
                                     self._receipt(false_kind)})

    def test_identical_source_and_receptor_study_block_not_required_for_fork(self):
        # GitHub original author is repository-specific, not site/window
        # metadata and not proof anybody used the code to process recording.
        fork = BENN_JORDAN_GITHUB_ROOTS[0]
        self.assertTrue(original_repo_attribution(fork)[
            'fork_presence_does_not_verify_use_in_2026_video'])
        self.assertNotEqual(fork.source_owner, fork.apparent_owner)


    def test_forked_converter_100sps_96000wav_cannot_preserve_physical_hz(self):
        z = mseed_converter_metadata_witness()
        self.assertEqual(z['nominal_acceleration_for_example'], '960')
        self.assertEqual(z['example_3hz_physical_tone_would_play_at_hz'],
                         '2880')
        self.assertFalse(z['video_data_processing_use_proven'])
        self.assertFalse(z['raw_site_sound_pressure_calibration_proven'])

    def test_converter_rejects_nonphysical_ambiguous_rates(self):
        for old, new in ((0, 96000), (-1, 96000),
                         (100, 0), (True, 96000),
                         (100.0, 96000), ('nan', 96000)):
            with self.assertRaises(ValueError):
                nominal_mseed_wav_playback_ratio(old, new)

    def test_root_originals_are_required_before_downstream_join(self):
        r = {k: self._receipt(k)
             for k in REQUIRED_ORIGINALS['P3_facility_attribution']}
        z = audit_phase_receipts(r)
        self.assertFalse(z['P3_facility_attribution']['metadata_join_ready'])
        r.update({k: self._receipt(k)
                  for k in REQUIRED_ORIGINALS['P2_calibrated_acoustic']})
        z = audit_phase_receipts(r)
        self.assertTrue(z['P2_calibrated_acoustic']['metadata_join_ready'])
        self.assertTrue(z['P3_facility_attribution']['metadata_join_ready'])
        self.assertFalse(z['P4_health_outcome']['metadata_join_ready'])

    def test_metadata_complete_never_proves_causation_or_calibration(self):
        r = {k: self._receipt(k)
             for req in REQUIRED_ORIGINALS.values() for k in req}
        z = audit_phase_receipts(r)
        self.assertTrue(all(p['metadata_join_ready'] for p in z.values()))
        self.assertTrue(all(not p['health_causation_established']
                            for p in z.values()))
        self.assertTrue(all(not p['actual_calibration_or_bytes_authenticated']
                            for p in z.values()))
        self.assertFalse(z['P6_modern_rf_claim']['intentional_rf_deployment_established'])

    def test_same_site_window_cannot_be_silently_joined(self):
        keys = REQUIRED_ORIGINALS['P2_calibrated_acoustic']
        r = {k: self._receipt(k) for k in keys}
        r[keys[1]] = self._receipt(keys[1], site='another-site')
        z = audit_phase_receipts(r)
        self.assertFalse(z['P2_calibrated_acoustic']['metadata_site_window_consistent'])
        self.assertFalse(z['P2_calibrated_acoustic']['metadata_join_ready'])

    def test_same_site_different_time_cannot_be_silently_joined(self):
        keys = REQUIRED_ORIGINALS['P2_calibrated_acoustic']
        r = {k: self._receipt(k) for k in keys}
        r[keys[2]] = self._receipt(keys[2], window='other-window')
        self.assertFalse(audit_phase_receipts(r)[
            'P2_calibrated_acoustic']['metadata_join_ready'])

    def test_untyped_historical_or_reviews_cannot_pay_site_receipts(self):
        with self.assertRaises(ValueError):
            audit_phase_receipts({'historic_pandora_report':
                                  self._receipt('historic_pandora_report')})
        with self.assertRaises(ValueError):
            audit_phase_receipts({'data_centre_narrative_review':
                                  self._receipt('data_centre_narrative_review')})

    def test_fail_closed_identity_and_hash_validation(self):
        k = REQUIRED_ORIGINALS['P2_calibrated_acoustic'][0]
        a = self._receipt(k)
        for bad in (None, {}, {k: 'original'}, {k: a.__class__(
                k, '', a.window_id, a.root_id, a.original_author,
                a.original_date, a.source_locator, a.content_sha256)},
                {k: a.__class__(
                 k, a.site_id, a.window_id, a.root_id, a.original_author,
                 a.original_date, a.source_locator, 'unhashed')},
                {k: a.__class__(
                 'different', a.site_id, a.window_id, a.root_id,
                 a.original_author, a.original_date, a.source_locator,
                 a.content_sha256)}):
            with self.assertRaises(ValueError):
                audit_phase_receipts(bad)


    def test_cross_phase_different_site_cannot_claim_acoustic_attribution(self):
        r = {k: self._receipt(k)
             for k in REQUIRED_ORIGINALS['P2_calibrated_acoustic']}
        r.update({k: self._receipt(k, site='another-site')
                  for k in REQUIRED_ORIGINALS['P3_facility_attribution']})
        z = audit_phase_receipts(r)
        self.assertTrue(z['P2_calibrated_acoustic']['metadata_join_ready'])
        self.assertFalse(z['P3_facility_attribution']['metadata_join_ready'])

    def test_outcome_replication_may_be_independent_site_but_not_same_root(self):
        r = {k: self._receipt(k) for phase in (
             'P2_calibrated_acoustic', 'P3_facility_attribution',
             'P4_health_outcome') for k in REQUIRED_ORIGINALS[phase]}
        replica = 'independent_outcome_reproduction'
        r[replica] = self._receipt(
            replica, site='independent-site', window='later-independent-study')
        z = audit_phase_receipts(r)
        self.assertTrue(z['P4_health_outcome']['metadata_join_ready'])
        orig = r[replica]
        earlier = r['matched_person_or_site_outcomes']
        r[replica] = OriginalReceipt(
            orig.kind, orig.site_id, orig.window_id,
            earlier.root_id, orig.original_author, orig.original_date,
            orig.source_locator, orig.content_sha256)
        self.assertFalse(audit_phase_receipts(r)[
            'P4_health_outcome']['claimed_replication_root_distinct'])

    def test_historical_transfer_receipt_not_same_1977_sensor_site(self):
        r = {k: self._receipt(k)
             for k in REQUIRED_ORIGINALS['P6_modern_rf_claim']}
        old = r['documented_historical_to_modern_transfer']
        r[old.kind] = OriginalReceipt(
            old.kind, 'archival-office', '1966-record',
            old.root_id, old.original_author, old.original_date,
            old.source_locator, old.content_sha256)
        z = audit_phase_receipts(r)
        self.assertTrue(z['P6_modern_rf_claim']['metadata_join_ready'])
        self.assertFalse(z['P6_modern_rf_claim']['intentional_rf_deployment_established'])

    def test_review_levels_and_estimate_denominators_separate(self):
        w = original_inquiry_phase_status()
        self.assertEqual(
            w['environmental_pressure_only'] + w['receptor_exposure'] +
            w['modelled_health'] + w['observed_health'],
            w['review_studies'])
        self.assertEqual(w['without_comparator'], 93)
        self.assertEqual(w['quantitative_estimates'], 112)
        self.assertLessEqual(w['reporting_confidence_interval_95pct'],
                             w['quantitative_estimates'])
        self.assertEqual(w['observed_health'], 0)


if __name__ == "__main__":
    import sys as _sys
    if _sys.argv[1:] == ['--selftest']:
        suite = _unittest.defaultTestLoader.loadTestsFromTestCase(
            TestOriginalInquiryAcceptance)
        run = _unittest.TextTestRunner(verbosity=2).run(suite)
        raise SystemExit(0 if run.wasSuccessful() else 1)
    if _sys.argv[1:] == ['--phase-status']:
        status = original_inquiry_phase_status()
        status['related_public_github_fork_roots'] = [
            original_repo_attribution(r) for r in BENN_JORDAN_GITHUB_ROOTS]
        status['public_fork_converter_timebase_example'] = (
            mseed_converter_metadata_witness())
        status['verified_public_2026_site_sensor_or_participant_data'] = False
        status['paper_status_from_video_description'] = 'WIP, publication not verified'
        print(_json.dumps(status, indent=2))
        raise SystemExit(0)
    if _sys.argv[1:]:
        raise SystemExit('Use --selftest, --phase-status or no arguments.')
    low, high = same_la_example()
    print("Two idealised pure tones at identical 35 dB(A), NOT measured sites:")
    for tone in [low, high]:
        print(f"{tone.hz:6.1f} Hz | A {a_weight_db(tone.hz):6.2f} dB | "
              f"flat {tone.db_spl:6.2f} dB SPL | LA {a_weighted_level([tone]):.2f} dBA")
    print(f"Unweighted SPL difference: {low.db_spl-high.db_spl:.2f} dB")
    print("25,000% above baseline maps to different decibels by quantity:")
    print(f"pressure amplitude: {claimed_percent_to_db(25000, 'pressure_amplitude'):.2f} dB")
    print(f"acoustic power: {claimed_percent_to_db(25000, 'acoustic_power'):.2f} dB")
    print("Equal LA is NOT equal spectra; no biological inference follows.")
