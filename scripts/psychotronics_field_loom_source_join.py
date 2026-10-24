#!/usr/bin/env python3
"""S1 source-pair/calibration same-object replay, not lab authenticity.

A SHA-256 receipt for an unrelated file must not entitle a hand-written
derived pair. A valid input connects the same JSON rows, apparatus,
configuration, instrument, calibration IDs and source-stream byte hashes.
All files remain self-submitted; no independent external attribution here.
"""
import csv
import hashlib
import json
import math
from pathlib import Path
from psychotronics_field_loom_reducer import replay_si_csv, VERSION


def _read_bounded(path, max_bytes):
    p = Path(path)
    if not p.is_file() or p.stat().st_size > max_bytes:
        raise ValueError('file missing or exceeds bounded intake limit')
    return p.read_bytes()


def _sha256(x):
    return hashlib.sha256(x).hexdigest()


def _digest_ok(value):
    return isinstance(value,str) and len(value)==64 and all(c in '0123456789abcdef' for c in value)


def verify_pair_source(meta, pairs):
    """Return source identity receipt; no positive physics or source authenticity."""
    failures = []
    certified_offset = None
    replay_failures = []
    replay_result = None
    stream_bytes = None
    try:
        rb = _read_bounded(meta['raw_data_file'], 64*1024*1024)
        cb = _read_bounded(meta['calibration_file'], 2*1024*1024)
        if not (_digest_ok(meta.get('raw_data_sha256')) and
                _digest_ok(meta.get('calibration_sha256')) and
                _sha256(rb)==meta['raw_data_sha256'] and
                _sha256(cb)==meta['calibration_sha256']):
            raise ValueError('raw/calibration file hashes mismatch')
        raw, cal = json.loads(rb),json.loads(cb)
        if not isinstance(raw,dict) or not isinstance(cal,dict):
            raise ValueError('raw/calibration JSON objects required')
        for key in ('apparatus_id','configuration_revision','instrument_serial'):
            if not (raw.get(key)==cal.get(key)==meta.get(key)):
                failures.append('same_object_mismatch_'+key)
        if cal.get('calibration_revision')!=meta.get('calibration_revision'):
            failures.append('calibration_revision_mismatch')
        if raw.get('pairs') != pairs:
            failures.append('record_pairs_not_identical_to_hashed_source_rows')
        # The raw-file content must identify its instrument source-stream bytes
        # (rather than saying the analysis input itself was the raw sensor stream).
        stream=raw.get('instrument_source_stream_file')
        stream_hash=raw.get('instrument_source_stream_sha256')
        if not stream or not _digest_ok(stream_hash):
            failures.append('unlinked_instrument_source_stream')
        else:
            sb=_read_bounded(stream,256*1024*1024)
            if _sha256(sb)!=stream_hash:
                failures.append('instrument_stream_hash_mismatch')
            else:
                stream_bytes = sb
        # All moment/gradient groups must refer to the same calibration source.
        groups=cal.get('moment_calibration_groups')
        if not isinstance(groups,dict):
            failures.append('missing_moment_calibration_groups')
        else:
            for p in pairs:
                group=p.get('moment_calibration_id')
                g=groups.get(group)
                if not isinstance(g,dict):
                    failures.append('unknown_moment_calibration_group')
                    continue
                if (g.get('moment_am2')!=p.get('moment_am2')
                    or g.get('moment_std_am2')!=p.get('moment_std_am2')):
                    failures.append('moment_calibration_not_same_as_pair')
                if ('moment_covariance_group_id' in p and
                    g.get('shared_magnitude_id') != p.get('moment_covariance_group_id')):
                    failures.append('shared_magnet_covariance_group_not_in_calibration')
        if stream_bytes is None:
            replay_failures.append('instrument_stream_unavailable_for_reduction')
        elif raw.get('pair_to_stream_reducer') != VERSION:
            replay_failures.append('unimplemented_or_missing_raw_stream_reducer_version')
        else:
            try:
                replay_result = replay_si_csv(stream_bytes, raw, cal)
                if replay_result['pairs'] != pairs:
                    replay_failures.append('raw_stream_reduction_does_not_equal_pairs')
            except (ValueError, TypeError, KeyError, OverflowError, csv.Error) as exc:
                replay_failures.append('deterministic_raw_reduction_failed:' + type(exc).__name__)
        if cal.get('gradient_calibration_fractional_std')!=meta.get('gradient_calibration_fractional_std'):
            failures.append('field_scale_calibration_not_same_as_pair_metadata')
        max_systematic=max((p.get('common_systematic_std_n',float('nan')) for p in pairs), default=float('nan'))
        if (not isinstance(max_systematic,(int,float)) or not math.isfinite(max_systematic)
            or not isinstance(cal.get('common_force_offset_std_n'),(int,float))
            or isinstance(cal.get('common_force_offset_std_n'),bool)
            or not math.isfinite(cal['common_force_offset_std_n'])
            or cal['common_force_offset_std_n']<max_systematic):
            failures.append('force_systematic_floor_under_calibration_source')
        else:
            certified_offset = cal['common_force_offset_std_n']
    except (OSError,ValueError,KeyError,TypeError,json.JSONDecodeError) as err:
        failures.append('source_replay_unavailable_or_invalid:'+type(err).__name__)
    return {
        'bytes_and_exact_pair_source_join':not failures,
        'calibration_reported_common_force_offset_std_n':certified_offset if not failures else None,
        'raw_stream_replayed_to_pairs':not failures and not replay_failures and replay_result is not None,
        'factorial_settings_from_source':(replay_result['factorial_settings'] if
            replay_result is not None and not replay_failures and not failures else None),
        'temporal_counterbalance_from_source':(replay_result['temporal_counterbalance'] if
            replay_result is not None and not replay_failures and not failures else None),
        'reducer_version':VERSION if replay_result is not None and not replay_failures else None,
        'unpaid_source_joins':sorted(set(failures + replay_failures)),
        'independent_instrument_authentication':False,
        'independent_operator_and_replicate_authenticated':False,
        'gravitational_observation_established':False,
    }


def _selftest():
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        root=Path(td)
        stream=root/'sensor.csv'
        stream.write_text('t,force\n0,0\n',encoding='utf-8')
        pairs=[{'pair_id':'demo','session_id':'s1','moment_calibration_id':'cal1',
                'moment_am2':.01,'moment_std_am2':.001,'common_systematic_std_n':1e-6}]
        raw={'apparatus_id':'test','configuration_revision':'v1','instrument_serial':'S',
             'pairs':pairs,'instrument_source_stream_file':str(stream),
             'instrument_source_stream_sha256':_sha256(stream.read_bytes())}
        cal={'apparatus_id':'test','configuration_revision':'v1','instrument_serial':'S',
             'calibration_revision':'c1','gradient_calibration_fractional_std':.02,
             'common_force_offset_std_n':1e-6,
             'moment_calibration_groups':{'cal1':{'moment_am2':.01,'moment_std_am2':.001}}}
        a=root/'pair.json'
        b=root/'cal.json'
        a.write_text(json.dumps(raw));b.write_text(json.dumps(cal))
        meta={'raw_data_file':str(a),'calibration_file':str(b),
              'raw_data_sha256':_sha256(a.read_bytes()),'calibration_sha256':_sha256(b.read_bytes()),
              'apparatus_id':'test','configuration_revision':'v1','instrument_serial':'S',
              'calibration_revision':'c1','gradient_calibration_fractional_std':.02}
        assert verify_pair_source(meta,pairs)['bytes_and_exact_pair_source_join']
        assert not verify_pair_source(meta,[{**pairs[0],'moment_am2':.02}])['bytes_and_exact_pair_source_join']
        a.write_text(a.read_text().replace('cal1','cal2'))
        assert not verify_pair_source(meta,pairs)['bytes_and_exact_pair_source_join']
        print('S1 source joins: matching actual source bytes, mutated pair and raw hash regressions passed (synthetic)')


if __name__=='__main__':
    _selftest()
