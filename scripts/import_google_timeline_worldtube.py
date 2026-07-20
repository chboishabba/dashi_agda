#!/usr/bin/env python3
"""Normalize Google Timeline exports into DASHI world-tube JSON.

The importer is deliberately conservative: uncertain/inferred fields retain
provenance, and gaps are emitted explicitly rather than silently interpolated.
"""
from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Iterator

EARTH_RADIUS_M = 6378137.0


@dataclass(frozen=True)
class Observation:
    index: int
    timestamp_ms: int
    latitude: float
    longitude: float
    altitude_m: float | None
    accuracy_m: float | None
    source: str
    place_label: str | None
    motion_mode: str | None
    vendor_inference: bool


@dataclass(frozen=True)
class Segment:
    start_index: int
    end_index: int
    status: str
    gap_ms: int


def parse_timestamp(value: Any) -> int | None:
    if value is None:
        return None
    if isinstance(value, (int, float)):
        n = int(value)
        return n if n > 10_000_000_000 else n * 1000
    text = str(value).strip()
    if text.isdigit():
        return parse_timestamp(int(text))
    try:
        return int(datetime.fromisoformat(text.replace("Z", "+00:00")).timestamp() * 1000)
    except ValueError:
        return None


def decode_e7(value: Any) -> float | None:
    if value is None:
        return None
    try:
        number = float(value)
    except (TypeError, ValueError):
        return None
    return number / 1e7 if abs(number) > 180 else number


def first(mapping: dict[str, Any], *keys: str) -> Any:
    for key in keys:
        if key in mapping and mapping[key] is not None:
            return mapping[key]
    return None


def walk(value: Any) -> Iterator[dict[str, Any]]:
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def candidate_observations(document: Any, source_name: str) -> Iterable[Observation]:
    seen: set[tuple[int, float, float]] = set()
    index = 0
    for row in walk(document):
        lat = decode_e7(first(row, "latitudeE7", "latitude", "lat"))
        lon = decode_e7(first(row, "longitudeE7", "longitude", "lng", "lon"))
        ts = parse_timestamp(first(row, "timestampMs", "timestamp", "startTime", "time"))
        if lat is None or lon is None or ts is None:
            continue
        if not (-90 <= lat <= 90 and -180 <= lon <= 180):
            continue
        key = (ts, round(lat, 7), round(lon, 7))
        if key in seen:
            continue
        seen.add(key)
        accuracy = first(row, "accuracy", "accuracyMeters", "horizontalAccuracy")
        altitude = first(row, "altitude", "altitudeMeters")
        place = first(row, "name", "placeName", "address")
        activity = first(row, "activityType", "type", "motionMode")
        inferred = any(k in row for k in ("activity", "activityType", "placeId", "semanticType"))
        yield Observation(
            index=index,
            timestamp_ms=ts,
            latitude=lat,
            longitude=lon,
            altitude_m=float(altitude) if altitude is not None else None,
            accuracy_m=float(accuracy) if accuracy is not None else None,
            source=source_name,
            place_label=str(place) if place is not None else None,
            motion_mode=str(activity) if activity is not None else None,
            vendor_inference=inferred,
        )
        index += 1


def ecef(lat_deg: float, lon_deg: float, altitude_m: float = 0.0) -> tuple[float, float, float]:
    lat = math.radians(lat_deg)
    lon = math.radians(lon_deg)
    radius = EARTH_RADIUS_M + altitude_m
    return (
        radius * math.cos(lat) * math.cos(lon),
        radius * math.cos(lat) * math.sin(lon),
        radius * math.sin(lat),
    )


def build_segments(observations: list[Observation], maximum_gap_ms: int) -> list[Segment]:
    segments: list[Segment] = []
    for left, right in zip(observations, observations[1:]):
        gap = right.timestamp_ms - left.timestamp_ms
        if gap < 0:
            status = "conflicting"
        elif gap > maximum_gap_ms:
            status = "unknown_gap"
        else:
            status = "observed_interval"
        segments.append(Segment(left.index, right.index, status, gap))
    return segments


def normalize(path: Path, maximum_gap_ms: int) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        document = json.load(handle)
    observations = sorted(candidate_observations(document, path.name), key=lambda row: row.timestamp_ms)
    observations = [Observation(index=i, **{k: v for k, v in asdict(row).items() if k != "index"}) for i, row in enumerate(observations)]
    segments = build_segments(observations, maximum_gap_ms)
    rows = []
    for row in observations:
        x, y, z = ecef(row.latitude, row.longitude, row.altitude_m or 0.0)
        payload = asdict(row)
        payload["ecef_m"] = {"x": x, "y": y, "z": z}
        payload["exact_position"] = False
        rows.append(payload)
    return {
        "schema": "dashi.worldtube.v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source": str(path),
        "coordinate_frame": "ECEF-WGS84-spherical-approximation",
        "observations": rows,
        "segments": [asdict(segment) for segment in segments],
        "missing_rows_acknowledged": True,
        "complete_experience_claim": False,
        "authority_claim": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--maximum-gap-hours", type=float, default=6.0)
    args = parser.parse_args()
    result = normalize(args.input, int(args.maximum_gap_hours * 3_600_000))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(f"wrote {len(result['observations'])} observations to {args.output}")


if __name__ == "__main__":
    main()
