"""NOAA original-format GHCNd 1953 OBS-TIME clock-fixture regressions.

Synthetic file fixtures only. No original downloaded station CSV, NOAA
official-byte hash, actual July 1953 observation time, or device result.
Original NOAA/NCEI format credited to NOAA; test synthesis Johl Brown
with OpenAI ChatGPT assistance.
"""
import gzip
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_psychotronics_1953_observation_clock import (
    SITE_VALUES, clock_ambiguity_certificate, parse_clock, proposed_label_day,
    read_1953_rows, merge_1953_rows, report, self_test,
)


def make_station(sid, clock="0700", replace=None):
    rows = []
    for day, value in SITE_VALUES[sid].items():
        row = [sid, f"195307{day:02d}", "PRCP", str(value), "", "", "0", clock]
        if replace and day in replace:
            row[replace[day][0]] = replace[day][1]
        rows.append(",".join(row))
    return "\n".join(rows) + "\n"


class NOAAClockTests(unittest.TestCase):
    def test_exact_cutoff_partition(self):
        out = clock_ambiguity_certificate()
        self.assertEqual((out["candidate_cutoffs_label_july6"],
                          out["candidate_cutoffs_label_july7"]), (120, 1320))
        self.assertEqual(proposed_label_day(7 * 60), 7)
        self.assertEqual(proposed_label_day(23 * 60), 6)

    def test_clock_is_not_assumed_when_missing(self):
        self.assertIsNone(parse_clock(""))
        self.assertEqual(parse_clock("0000"), 0)
        self.assertEqual(parse_clock("2200"), 1320)

    def test_invalid_clock_is_not_silently_coerced(self):
        for item in ("2400", "2360", "7AM", "070", "9999", "０７００"):
            with self.subTest(clock=item), self.assertRaises(ValueError):
                parse_clock(item)

    def test_original_format_one_station_plain_file_and_missing_other(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "BarHarbor.csv"
            path.write_text(make_station("USC00170371"), encoding="ascii")
            actual = read_1953_rows(path)
            self.assertEqual(list(actual), ["USC00170371"])
            result = report([path])
            self.assertEqual(result["missing_station_clock_sources"], ["USW00014606"])
            self.assertFalse(result["full_original_dataset_publisher_byte_custody_verified"])

    def test_two_separate_station_files_and_gzip(self):
        with tempfile.TemporaryDirectory() as d:
            p1, p2 = Path(d) / "Bangor.csv", Path(d) / "BarHarbor.csv.gz"
            p1.write_text(make_station("USW00014606", "2200"), encoding="ascii")
            with gzip.open(p2, "wt", encoding="ascii") as f:
                f.write(make_station("USC00170371", "0700"))
            actual = merge_1953_rows([p1, p2])
            self.assertEqual(len(actual), 2)
            self.assertEqual(actual["USW00014606"][6]["obs_time"], "2200")
            self.assertEqual(actual["USC00170371"][7]["obs_time"], "0700")
            self.assertEqual(report([p1,p2])["missing_station_clock_sources"], [])

    def test_conflicting_duplicate_source_fails(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "Bangor.csv"
            p.write_text(make_station("USW00014606"), encoding="ascii")
            with self.assertRaises(ValueError):
                merge_1953_rows([p, p])

    def test_wrong_original_precipitation_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "Bangor.csv"
            p.write_text(make_station("USW00014606", replace={6:(3,"999")}), encoding="ascii")
            with self.assertRaises(ValueError):
                read_1953_rows(p)

    def test_unverified_hour_cannot_be_promoted(self):
        baseline = report()
        self.assertEqual(baseline["clock_acquisition_status"], "not_acquired")
        self.assertFalse(baseline["historical_same_site_hourly_Ellsworth_verified"])
        self.assertFalse(baseline["reich_device_weather_causality_verified"])
        self.assertTrue(self_test()["passed"])


if __name__ == "__main__":
    unittest.main()
