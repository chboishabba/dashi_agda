"""Source-excerpt and arithmetic regressions; no original 1910 logbook claims."""
from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/bom_sydney1910_conditional_impact.py"
spec = importlib.util.spec_from_file_location("bom_sydney1910", SCRIPT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
SOURCE = ROOT / "Docs/support/reference/bom_abc_mediawatch_station_excerpts_20261026.json"


class WeekTests(unittest.TestCase):
    def setUp(self):
        self.source = json.loads(SOURCE.read_text(encoding="utf-8"))

    def test_exact_numerical_week(self):
        values = mod.source_case(self.source)
        self.assertEqual(values, [Fraction(x, 10) for x in
                                   (172, 156, 171, 187, 179, 154, 184)])
        self.assertEqual(sum(values), Fraction(1203, 10))

    def test_observed_mean(self):
        r = mod.sensitivities(mod.source_case(self.source))
        self.assertEqual(r["observed_week_mean_C"], "1203/70")
        self.assertFalse(r["paper_record_authenticated"])
        self.assertNotIn("explicitly_hypothetical_week_mean_delta_C", r)

    def test_monthly_and_annual_coefficients(self):
        r = mod.sensitivities(mod.source_case(self.source))
        c = r["coefficient_of_true_minus_published_week_mean"]
        self.assertEqual(c["january_if_january_original_is_wrong"], "7/31")
        self.assertEqual(c["february_if_february_original_is_wrong"], "1/4")
        self.assertEqual(c["1910_station_year_if_one_week_is_wrong"], "7/365")

    def test_declared_hypothetical_one_degree(self):
        r = mod.sensitivities(mod.source_case(self.source), "1")
        d = r["explicitly_hypothetical_statistic_deltas_C"]
        self.assertEqual(d["february_if_february_original_is_wrong"], "1/4")
        self.assertEqual(d["1910_station_year_if_one_week_is_wrong"], "7/365")
        self.assertFalse(r["national_trend_impact_computed"])

    def test_reject_modified_source_values(self):
        self.source["cases"][0]["right"][0] = 17.3
        with self.assertRaises(ValueError):
            mod.source_case(self.source)

    def test_reject_claimed_paper_authentication(self):
        self.source["original_paper_records_authenticated"] = True
        with self.assertRaises(ValueError):
            mod.source_case(self.source)

    def test_reject_wrong_quality_receipts(self):
        self.source["cases"][0]["quality_flags_right"][0] = "N"
        with self.assertRaises(ValueError):
            mod.source_case(self.source)

    def test_reject_source_identity_mutation(self):
        self.source["cases"][0]["product_code"] = "IDCJAC0010"
        with self.assertRaises(ValueError):
            mod.source_case(self.source)

    def test_noaa_presented_minima_match_but_maxima_differ(self):
        other = json.loads((ROOT / "Docs/support/reference/bom_sydney1910_noaa_presentation_crosscheck.json").read_text())
        left, right = other["periods"]
        self.assertEqual(left["minimum_C"], right["minimum_C"])
        self.assertEqual(left["minimum_C"], self.source["cases"][0]["left"])
        self.assertNotEqual(left["maximum_C"], right["maximum_C"])
        self.assertNotEqual(left["rain_cm"], right["rain_cm"])
        self.assertFalse(other["independent_origin_established"])

    def test_noaa_presented_context_exact_sums(self):
        other = json.loads((ROOT / "Docs/support/reference/bom_sydney1910_noaa_presentation_crosscheck.json").read_text())
        left, right = other["periods"]
        self.assertEqual(sum(Fraction(str(x)) for x in left["maximum_C"]), Fraction(1689, 10))
        self.assertEqual(sum(Fraction(str(x)) for x in right["maximum_C"]), Fraction(1889, 10))
        self.assertEqual(sum(Fraction(str(x)) for x in left["rain_cm"]), Fraction(69, 20))
        self.assertEqual(sum(Fraction(str(x)) for x in right["rain_cm"]), Fraction(2, 25))


if __name__ == "__main__":
    unittest.main()
