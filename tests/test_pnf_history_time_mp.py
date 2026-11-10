"""Point-in-time / balanced-ternary PNF+economics MP regression tests.

Synthetic fixtures only. Existing MP backend is exercised rather than copied.
"""
import unittest
from scripts.pnf_history_time_mp import (
    asof_mp, TemporalObservation as Event, HistoricalFeature as Feature,
)

class TemporalMPTypedTests(unittest.TestCase):
    def fixture(self):
        features = [
            Feature("h1","feed","A",0), Feature("h1","feed","B",0),
            Feature("h1","feed","C",3),
            Feature("h2","feed","A",0), Feature("h2","feed","B",0),
            Feature("h1","other","Z",0),
        ]
        rows = [
            Event("h1",0,0,{"A":-1,"B":0}, "feed"),
            Event("h1",1,1,{"A":0,"B":1}, "feed"),
            Event("h1",2,2,{"A":1,"B":-1}, "feed"),
            Event("h1",3,3,{"A":-1,"B":0,"C":1}, "feed"),
            Event("h1",4,4,{"A":1,"B":1,"C":0}, "feed"),
            Event("h1",5,5,{"A":0,"B":-1,"C":-1}, "feed"),
            Event("h1",6,12,{"A":100,"B":100,"C":100}, "feed"),
            Event("h1",6,6,{"A":-1,"B":0,"C":1}, "other"),
            Event("h2",0,0,{"A":1,"B":1}, "feed"),
            Event("h2",1,1,{"A":-1,"B":0}, "feed"),
        ]
        return rows, features

    def get(self, time, history="h1", version="v0"):
        rows, features = self.fixture()
        return asof_mp(
            rows,features,history=history,asof=time,
            source="feed",measurement="trit_activation",
            consumer_version=version,balanced_trit_native=True)

    def test_time_index_and_dynamic_feature_dimension(self):
        early = self.get(2)
        later = self.get(5)
        self.assertEqual(early["feature_ids"],["A","B"])
        self.assertEqual(later["feature_ids"],["A","B","C"])
        self.assertEqual(early["mp_diagnostic"]["n"],3)
        self.assertEqual(later["mp_diagnostic"]["n"],3)
        self.assertEqual(early["mp_diagnostic"]["p"],2)
        self.assertEqual(later["mp_diagnostic"]["p"],3)
        self.assertEqual(later["source_event_times"],[3,4,5])
        # Newly admitted feature C cannot be backfilled into older rows.
        self.assertTrue(early["leakage_guard"] and later["leakage_guard"])

    def test_future_announcement_never_enters_past(self):
        at6 = self.get(6)
        self.assertNotIn(6,at6["source_event_times"])
        self.assertEqual(at6["mp_diagnostic"]["n"],3)
        self.assertEqual(at6["feature_ids"],["A","B","C"])

    def test_consumer_version_and_history_remain_distinct(self):
        r0=self.get(2,version="consumer-0")
        r1=self.get(2,version="consumer-1")
        self.assertEqual(r0["mp_diagnostic"]["trace"],r1["mp_diagnostic"]["trace"])
        self.assertNotEqual(r0["consumer_version"],r1["consumer_version"])
        other=self.get(1,history="h2")
        self.assertEqual(other["history"],"h2")
        self.assertEqual(other["mp_diagnostic"]["n"],2)

    def test_balanced_trit_guard(self):
        rows,features=self.fixture()
        rows.append(Event("h1",7,7,{"A":2,"B":0,"C":1},"feed"))
        with self.assertRaises(ValueError):
            asof_mp(rows,features,history="h1",asof=7,
                    source="feed",measurement="trit_activation",
                    consumer_version="v0",balanced_trit_native=True)

    def test_no_backfill_or_cross_history_universe(self):
        rows, features=self.fixture()
        with self.assertRaises(ValueError):
            asof_mp(rows,features,history="h1",asof=-1,
                    source="feed",measurement="trit_activation",
                    consumer_version="v0")
        with self.assertRaises(ValueError):
            asof_mp(rows,features,history="unknown",asof=2,
                    source="feed",measurement="trit_activation",
                    consumer_version="v0")

if __name__=="__main__": unittest.main()
