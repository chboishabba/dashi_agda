import unittest
from scripts.macro_financial_event_clocks_20261121 import (
    Event, chronology, directional_flips, propagation_delay_seconds,
    first_market_response_lag_seconds, sentiment_available,
)

def row(id, disclosed, arrival, price_at, move):
    return Event(id, "2026-11-05T08:00:00Z", disclosed, arrival, price_at, move)

class ClockTests(unittest.TestCase):
    def test_unsorted_events_sorted_by_market_clock(self):
        a=row("late", "2026-11-05T09:00:00Z", "2026-11-05T09:01:00Z", "2026-11-05T09:02:00Z", -1)
        b=row("early", "2026-11-05T08:10:00Z", "2026-11-05T08:11:00Z", "2026-11-05T08:12:00Z", 1)
        self.assertEqual([e.source_id for e in chronology((a,b),"2026-11-06T00:00:00Z")], ["early","late"])
        self.assertEqual(directional_flips((a,b),"2026-11-06T00:00:00Z"), 1)

    def test_future_arrival_does_not_leak(self):
        event=row("late", "2026-11-05T09:00:00Z", "2026-11-05T09:30:00Z", "2026-11-05T09:05:00Z", -1)
        self.assertEqual(chronology([event],"2026-11-05T09:10:00Z"), ())
        self.assertEqual(first_market_response_lag_seconds(event), 300)
        self.assertEqual(propagation_delay_seconds(event), 1800)

    def test_future_market_quote_does_not_leak(self):
        a=row("advance", "2026-11-05T09:00:00Z", "2026-11-05T09:01:00Z", "2026-11-05T10:00:00Z", -1)
        self.assertEqual(chronology((a,),"2026-11-05T09:30:00Z"), ())
        self.assertEqual(chronology((a,),"2026-11-05T10:01:00Z"), (a,))

    def test_market_quote_may_precede_local_arrival(self):
        a=row("fast-market", "2026-11-05T09:00:00Z", "2026-11-05T09:30:00Z", "2026-11-05T09:05:00Z", -1)
        self.assertEqual(chronology((a,),"2026-11-05T09:20:00Z"), ())
        self.assertEqual(chronology((a,),"2026-11-05T09:35:00Z"), (a,))


    def test_psychological_price_threshold_asof(self):
        from scripts.macro_financial_event_clocks_20261121 import QuotedPrice, threshold_transitions
        ticks = [
            QuotedPrice("2026-11-19T10:03:00Z", 98, "venue"),
            QuotedPrice("2026-11-19T10:02:00Z", 101, "venue"),
            QuotedPrice("2026-11-19T10:04:00Z", 105, "venue"),
        ]
        self.assertEqual(threshold_transitions(ticks,100,"2026-11-19T10:03:30Z"),("cross-down",))
        self.assertEqual(threshold_transitions(ticks,100,"2026-11-19T10:05:00Z"),("cross-down","cross-up"))
        self.assertEqual(threshold_transitions(ticks,99,"2026-11-19T10:03:30Z"),("cross-down",))

    def test_threshold_does_not_create_missing_data(self):
        from scripts.macro_financial_event_clocks_20261121 import QuotedPrice, threshold_transitions
        self.assertEqual(threshold_transitions([], 100, "2026-11-19T10:05:00Z"), ())
        with self.assertRaises(ValueError):
            threshold_transitions([QuotedPrice("2026-11-19T10:04:00Z", -1, "venue")],100,"2026-11-19T10:05:00Z")

    def test_missing_move_is_unknown(self):
        a=row("unknown","2026-11-05T08:10:00Z","2026-11-05T08:11:00Z","2026-11-05T08:12:00Z",None)
        self.assertEqual(directional_flips((a,),"2026-11-06T00:00:00Z"),0)

    def test_bad_clocks_and_no_naive_time(self):
        with self.assertRaises(ValueError):
            row("bad","2026-11-05T08:10:00Z","2026-11-05T08:09:00Z","2026-11-05T08:11:00Z",1).validate()
        with self.assertRaises(ValueError):
            row("bad","2026-11-05T08:10:00","2026-11-05T08:11:00Z","2026-11-05T08:12:00Z",1).validate()

    def test_sentiment_publication_gate(self):
        self.assertIsNone(sentiment_available(7,"2026-11-05T09:01:00Z","2026-11-05T09:00:00Z"))
        self.assertEqual(sentiment_available(7,"2026-11-05T09:01:00Z","2026-11-05T09:02:00Z"),7)
        with self.assertRaises(ValueError):
            sentiment_available(101,"2026-11-05T09:01:00Z","2026-11-05T09:02:00Z")

if __name__ == "__main__":
    unittest.main()
