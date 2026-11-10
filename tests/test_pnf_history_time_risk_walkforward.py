"""Synthetic-only regression for PIT MP risk-quality evaluation."""
import unittest
from scripts.pnf_history_time_risk_walkforward import (
    forecast_one_step, assess_walkforward)
from scripts.pnf_history_time_mp import TemporalObservation as Event, HistoricalFeature as Feature


def source_fixture():
    features=[Feature("history-1","tape",name,0) for name in ("A","B","C")]
    rows=[]
    for i in range(16):
        # Deterministic nonconstant returns; each measurement becomes
        # available at its event time (no lookahead and no revision).
        values={"A": ((3*i)%11-5)/10,
                "B": ((5*i)%13-6)/10,
                "C": ((7*i)%17-8)/10}
        rows.append(Event("history-1",i,i,values,"tape"))
    return rows,features


class PointInTimeRiskTests(unittest.TestCase):
    def test_strictly_forward_holdout_and_no_authority(self):
        rows,features=source_fixture()
        receipts=[forecast_one_step(rows,features,history="history-1",
                                  source="tape",asof=t,
                                  consumer_version="v1",
                                  weights=[1/3,1/3,1/3])
                  for t in range(5,12)]
        self.assertEqual([r.evaluation_time for r in receipts],
                         list(range(6,13)))
        self.assertTrue(all(r.training_latest_time <= r.asof
                            and r.training_latest_available_at <= r.asof
                            for r in receipts))
        result=assess_walkforward(receipts,min_folds=5)
        self.assertEqual(result["folds"],7)
        self.assertFalse(result["trade_authority"])
        self.assertFalse(result["alpha_claim"])

    def test_late_availability_reduces_training(self):
        rows,features=source_fixture()
        old=rows[3]
        rows[3]=Event(old.history,old.event_time,30,old.values,old.source)
        r=forecast_one_step(rows,features,history="history-1",source="tape",
                            asof=9,consumer_version="v1",
                            weights=[.4,.3,.3])
        self.assertEqual(r.training_count,9)
        self.assertEqual(r.training_latest_available_at,9)

    def test_dynamic_universe_does_not_backfill(self):
        rows,features=source_fixture()
        features[2]=Feature("history-1","tape","C",10)
        # Later membership does not permit retrospective use of
        # pre-membership observations lacking C.
        for i in range(10):
            o=rows[i]
            rows[i]=Event(o.history,o.event_time,o.available_at,
                          {k:v for k,v in o.values.items() if k != "C"},
                          o.source)
        with self.assertRaises(ValueError):
            forecast_one_step(rows,features,history="history-1",
                              source="tape",asof=11,
                              consumer_version="v1",
                              weights=[1/3,1/3,1/3],min_training=5)

    def test_wrong_source_and_future_source_prohibited(self):
        rows,features=source_fixture()
        with self.assertRaises(ValueError):
            forecast_one_step(rows,features,history="history-1",
                              source="other",asof=10,
                              consumer_version="v1",
                              weights=[1/3,1/3,1/3])
        with self.assertRaises(ValueError):
            forecast_one_step(rows,features,history="history-1",
                              source="tape",asof=15,
                              consumer_version="v1",
                              weights=[1/3,1/3,1/3])

    def test_duplicate_or_anachronistic_target_rejected(self):
        rows,features=source_fixture()
        rows.append(rows[10])
        with self.assertRaises(ValueError):
            forecast_one_step(rows,features,history="history-1",
                              source="tape",asof=9,
                              consumer_version="v1",
                              weights=[1/3,1/3,1/3])
        rows,features=source_fixture()
        o=rows[2]
        rows[2]=Event(o.history,2,1,o.values,o.source)
        with self.assertRaises(ValueError):
            forecast_one_step(rows,features,history="history-1",
                              source="tape",asof=9,
                              consumer_version="v1",
                              weights=[1/3,1/3,1/3])

    def test_unqualified_number_of_folds_rejected(self):
        rows,features=source_fixture()
        r=forecast_one_step(rows,features,history="history-1",
                            source="tape",asof=10,consumer_version="v1",
                            weights=[1/3,1/3,1/3])
        with self.assertRaises(ValueError):
            assess_walkforward([r],min_folds=5)

if __name__=="__main__":
    unittest.main()
