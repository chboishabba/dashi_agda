"""Reference acceptance for source/news clocks and signed market responses.

An observational diagnostic, not an execution signal or causal-intent claim.
Consumes generic, timestamped source observations; no private ingestion or
external application integration is assumed.
"""
from __future__ import annotations
from dataclasses import dataclass
from datetime import datetime, timezone
from math import isfinite
from typing import Iterable


def utc(text: str) -> datetime:
    instant = datetime.fromisoformat(text.replace("Z", "+00:00"))
    if instant.tzinfo is None:
        raise ValueError("timezone required")
    return instant.astimezone(timezone.utc)


@dataclass(frozen=True)
class Event:
    source_id: str
    event_time: str
    disclosed_at: str
    observer_received_at: str
    price_observed_at: str
    price_move: float | None
    settlement_at: str | None = None

    def validate(self) -> None:
        if not self.source_id.strip():
            raise ValueError("missing source")
        event, disclosure, receipt, price = (
            utc(self.event_time), utc(self.disclosed_at),
            utc(self.observer_received_at), utc(self.price_observed_at)
        )
        if event > disclosure or disclosure > receipt:
            raise ValueError("inconsistent event/disclosure/receipt clocks")
        if self.price_move is not None and not isfinite(self.price_move):
            raise ValueError("nonfinite price move")
        if self.settlement_at is not None and utc(self.settlement_at) < event:
            raise ValueError("settlement earlier than event")
        # The market can move before our observer receives news. Do not
        # require price >= receipt: that would delete the latency signal.
        _ = price


def chronology(events: Iterable[Event], as_of: str) -> tuple[Event, ...]:
    cutoff = utc(as_of)
    seen = set()
    eligible = []
    for e in events:
        e.validate()
        key = (e.source_id, e.observer_received_at)
        if key in seen:
            raise ValueError("duplicate source/arrival receipt")
        seen.add(key)
        if utc(e.observer_received_at) <= cutoff:
            eligible.append(e)
    return tuple(sorted(eligible, key=lambda e: (
        utc(e.price_observed_at), utc(e.observer_received_at), e.source_id
    )))


def directional_flips(events: Iterable[Event], as_of: str) -> int:
    signed = []
    for e in chronology(events, as_of):
        if e.price_move is None:
            continue  # Unknown is not zero.
        if e.price_move != 0:
            signed.append(1 if e.price_move > 0 else -1)
    return sum(a != b for a, b in zip(signed, signed[1:]))


def propagation_delay_seconds(event: Event) -> float:
    event.validate()
    return (utc(event.observer_received_at) - utc(event.disclosed_at)).total_seconds()


def first_market_response_lag_seconds(event: Event) -> float:
    event.validate()
    return (utc(event.price_observed_at) - utc(event.disclosed_at)).total_seconds()


def sentiment_available(score: float | None, published_at: str, as_of: str) -> float | None:
    if score is None or utc(published_at) > utc(as_of):
        return None
    if not isfinite(score) or not 0 <= score <= 100:
        raise ValueError("fear-greed index outside 0..100")
    return score
