#!/usr/bin/env python3
"""Matched-service screening for heating/cooling technology observations.

A reporting and quality-control tool, NOT an experimental calibration, an
external source authenticator, or a technology performance prediction.
One service/operating point per comparison.  Python standard library only.
"""
from dataclasses import dataclass
import csv
import json
import math
import argparse
import unittest

REQUIRED = ('technology', 'study_uri', 'source_kind', 'test_object',
            'test_protocol', 'mode', 'load_kw', 'hot_c', 'cold_c',
            'electric_kw', 'auxiliary_kw', 'calibration_ref', 'service_id')
KINDS = {'independent_measurement', 'author_experiment', 'simulation',
         'vendor_claim', 'literature_secondary'}


@dataclass(frozen=True)
class Point:
    technology: str
    study_uri: str
    source_kind: str
    test_object: str
    test_protocol: str
    mode: str
    load_kw: float
    hot_c: float
    cold_c: float
    electric_kw: float
    auxiliary_kw: float
    calibration_ref: str
    service_id: str

    @property
    def plug_cop(self):
        return self.load_kw / (self.electric_kw + self.auxiliary_kw)

    def validate(self):
        text_fields = (self.technology, self.study_uri, self.test_object,
                       self.test_protocol, self.calibration_ref, self.service_id)
        if any(not x.strip() for x in text_fields):
            raise ValueError('missing identity, protocol, or calibration locator')
        if self.source_kind not in KINDS or self.mode not in {'heating', 'cooling'}:
            raise ValueError('unknown source kind or service mode')
        values = (self.load_kw, self.hot_c, self.cold_c,
                  self.electric_kw, self.auxiliary_kw)
        if not all(math.isfinite(x) for x in values):
            raise ValueError('non-finite measurement')
        if (self.load_kw <= 0 or self.electric_kw < 0 or
                self.auxiliary_kw < 0 or
                self.electric_kw + self.auxiliary_kw <= 0 or
                self.hot_c <= self.cold_c or self.cold_c <= -273.15):
            raise ValueError('non-physical declared service point')


def read_points(path):
    with open(path, encoding='utf-8', newline='') as stream:
        reader = csv.DictReader(stream)
        if not set(REQUIRED).issubset(reader.fieldnames or []):
            raise ValueError('missing columns')
        points = []
        for row in reader:
            row = dict(row)
            for key in ('load_kw', 'hot_c', 'cold_c', 'electric_kw', 'auxiliary_kw'):
                row[key] = float(row[key])
            point = Point(**{key: row[key] for key in REQUIRED})
            point.validate()
            points.append(point)
    if not points:
        raise ValueError('empty dataset')
    return points


def compare(points):
    """Only like-for-like points; otherwise fail, never rank by raw COP."""
    if not points:
        raise ValueError('empty comparison')
    for p in points:
        p.validate()
    first = points[0]
    for p in points[1:]:
        if (p.service_id != first.service_id or p.mode != first.mode or
            abs(p.hot_c - first.hot_c) > 1e-9 or
            abs(p.cold_c - first.cold_c) > 1e-9 or
            abs(p.load_kw - first.load_kw) > 1e-9 or
            p.test_protocol != first.test_protocol):
            raise ValueError('unmatched service / load / test protocol')
    return {'service_id': first.service_id,
            'not_a_meta_analysis': True,
            'unpaid': ['instrument certificate validation',
                       'load uncertainty and seasonal part-load performance',
                       'material lifetime, water, embodied inputs and noise spectrum',
                       'same-protocol independent testing and cost normalization'],
            'observations': [dict(technology=p.technology, uri=p.study_uri,
                                  kind=p.source_kind, test_object=p.test_object,
                                  declared_plug_cop=round(p.plug_cop, 6),
                                  declared_experimental_source=(
                                      p.source_kind in {'independent_measurement',
                                                        'author_experiment'}))
                             for p in points]}


class Checks(unittest.TestCase):
    def setUp(self):
        self.a = Point('compressor', 'https://example.org/source-a',
                       'author_experiment', 'test-rig-A', 'protocol-01',
                       'cooling', 10, 35, 5, 4, 1, 'CAL-01', 'S-01')

    def test_matched(self):
        b = Point('caloric', 'https://example.org/source-b',
                  'simulation', 'model-B', 'protocol-01', 'cooling',
                  10, 35, 5, 3, 2, 'MODEL-CAL', 'S-01')
        d = compare([self.a, b])
        self.assertEqual([x['declared_plug_cop'] for x in d['observations']], [2, 2])
        self.assertFalse(d['observations'][1]['declared_experimental_source'])

    def test_reject_unmatched_temperature(self):
        b = Point(**{**vars(self.a), 'technology': 'different', 'hot_c': 45})
        with self.assertRaises(ValueError):
            compare([self.a, b])

    def test_reject_unmatched_source_duty(self):
        b = Point(**{**vars(self.a), 'technology': 'different', 'load_kw': 12})
        with self.assertRaises(ValueError):
            compare([self.a, b])

    def test_reject_free_power(self):
        b = Point(**{**vars(self.a), 'electric_kw': 0, 'auxiliary_kw': 0})
        with self.assertRaises(ValueError):
            compare([b])

    def test_reject_unmatched_protocol(self):
        b = Point(**{**vars(self.a), 'test_protocol': 'different'})
        with self.assertRaises(ValueError):
            compare([self.a, b])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--csv')
    parser.add_argument('--selftest', action='store_true')
    opts = parser.parse_args()
    if opts.selftest:
        result = unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(Checks))
        if not result.wasSuccessful():
            raise SystemExit(1)
    if opts.csv:
        print(json.dumps(compare(read_points(opts.csv)), indent=2))
    elif not opts.selftest:
        parser.error('pass --selftest or --csv')


if __name__ == '__main__':
    main()
