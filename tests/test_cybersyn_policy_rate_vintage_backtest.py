from pathlib import Path
import sys, unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import cybersyn_policy_rate_vintage_backtest as m

F=[{"bank":"RBA","as_of_utc":"2026-11-13T00:00:00Z",
"decision_date":"2026-12-08","target_metric":"cash_rate_target_pct",
"point_rate_pct":4.85,
"source_url":"https://www.rba.gov.au/schedules-events/board-meeting-schedules.html"},
{"bank":"FOMC","as_of_utc":"2026-11-13T00:00:00Z",
"decision_date":"2026-12-09","target_metric":"fed_funds_target_midpoint_pct",
"point_rate_pct":4.125,
"source_url":"https://www.federalreserve.gov/monetarypolicy/fomccalendars.htm"}]

class VintageBacktestTests(unittest.TestCase):
 def test_future_decisions_pending(self):
  r=m.score(F,[],as_of="2026-11-13T10:00:00Z")
  self.assertEqual(r["scored"],0)
  self.assertEqual(r["pending"],2)
 def test_legacy_hindsight_rejected(self):
  f=[dict(F[0],as_of_utc="2026-12-10T00:00:00Z")]
  with self.assertRaises(m.VintageError):
   m.score(f,[],as_of="2026-12-15T00:00:00Z")
 def test_official_rba_decision_scores_only_when_published(self):
  official=[{"bank":"RBA","decision_date":"2026-12-08",
   "target_metric":"cash_rate_target_pct","rate_pct":4.85,
   "publication_utc":"2026-12-08T03:30:00Z",
   "official_source_url":"https://www.rba.gov.au/example-published-event"}]
  self.assertEqual(m.score(F,official,as_of="2026-11-13T10:00:00Z")["pending"],2)
  r=m.score(F,official,as_of="2026-12-10T00:00:00Z")
  self.assertEqual(r["scored"],1)
  self.assertEqual(r["forecasts"][0]["error_bp"],0)
 def test_rate_metric_mismatch_does_not_score(self):
  official=[{"bank":"RBA","decision_date":"2026-12-08",
  "target_metric":"interbank_rate_pct","rate_pct":4.85,
  "publication_utc":"2026-12-08T03:30:00Z",
  "official_source_url":"https://www.rba.gov.au/example"}]
  self.assertEqual(m.score(F,official,as_of="2026-12-10T00:00:00Z")["pending"],2)
if __name__=="__main__":unittest.main()
