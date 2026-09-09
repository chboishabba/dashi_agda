#!/usr/bin/env python3
"""Normalize private health evidence into provenance-preserving TSV/JSON receipts.

Semantics:
- preserve raw source identity, row identity, timestamps, values, units, and source columns;
- canonicalize parseable timestamps *without* mutating the raw source value;
- do not diagnose, infer causation, or silently repair source errors;
- temporal joins report relations only and preserve event precision.

Commands:
  google-health-points  Flattened Google Health/Fitbit points TSV -> normalized observations
  qcat-transcription    Canonical QCAT health transcription TSV -> normalized observations
  event-join            Normalized observations + event TSV -> temporal relation TSV
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Optional


PROCESSOR_CONTRACT = "sensiblaw-health-evidence-v2"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def write_tsv(path: Path, fieldnames: list[str], rows: Iterable[dict[str, str]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames, delimiter="\t", extrasaction="ignore")
        w.writeheader()
        for row in rows:
            w.writerow({k: row.get(k, "") for k in fieldnames})
            count += 1
    return count


def read_tsv(path: Path) -> Iterable[dict[str, str]]:
    with path.open("r", encoding="utf-8-sig", newline="") as f:
        yield from csv.DictReader(f, delimiter="\t")


def nonempty(row: dict[str, str], key: str) -> str:
    v = row.get(key, "")
    return "" if v is None else str(v).strip()


def civil_date(row: dict[str, str], prefix: str) -> str:
    y = nonempty(row, f"{prefix}.date.year")
    m = nonempty(row, f"{prefix}.date.month")
    d = nonempty(row, f"{prefix}.date.day")
    if y and m and d:
        return f"{int(y):04d}-{int(m):02d}-{int(d):02d}"
    return ""


def canonical_iso(value: str) -> tuple[str, str]:
    """Return (canonical, status) without altering the raw source string."""
    raw = value.strip()
    if not raw:
        return "", "missing"
    try:
        dt = datetime.fromisoformat(raw.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            return dt.isoformat(timespec="seconds"), "parsed-naive"
        return dt.isoformat(timespec="seconds"), "parsed-offset"
    except ValueError:
        return "", "unparsed"


def canonical_qcat_datetime(date_raw: str, time_raw: str) -> tuple[str, str]:
    date_raw = date_raw.strip()
    time_raw = time_raw.strip()
    if not date_raw:
        return "", "missing-date"

    date_value = None
    for fmt in ("%d/%m/%Y", "%d/%m/%y", "%d-%m-%Y", "%d-%m-%y"):
        try:
            date_value = datetime.strptime(date_raw, fmt).date()
            break
        except ValueError:
            pass
    if date_value is None:
        return "", "unparsed-date"

    if not time_raw:
        return date_value.isoformat(), "date-only"

    time_value = None
    for fmt in ("%H:%M:%S", "%H:%M", "%I:%M %p", "%I:%M:%S %p"):
        try:
            time_value = datetime.strptime(time_raw, fmt).time()
            break
        except ValueError:
            pass
    if time_value is None:
        return date_value.isoformat(), "unparsed-time"

    return datetime.combine(date_value, time_value).isoformat(timespec="seconds"), "parsed-naive"


@dataclass(frozen=True)
class MetricSpec:
    data_type: str
    metric: str
    value_column: str
    unit: str
    timestamp_column: Optional[str] = None
    date_prefix: Optional[str] = None


GOOGLE_HEALTH_SPECS = (
    MetricSpec("heart-rate", "heart-rate", "heartRate.beatsPerMinute", "beats/min",
               "heartRate.sampleTime.physicalTime"),
    MetricSpec("oxygen-saturation", "oxygen-saturation", "oxygenSaturation.percentage", "%",
               "oxygenSaturation.sampleTime.physicalTime"),
    MetricSpec("heart-rate-variability", "hrv-rmssd",
               "heartRateVariability.rootMeanSquareOfSuccessiveDifferencesMilliseconds", "ms",
               "heartRateVariability.sampleTime.physicalTime"),
    MetricSpec("daily-resting-heart-rate", "daily-resting-heart-rate",
               "dailyRestingHeartRate.beatsPerMinute", "beats/min",
               date_prefix="dailyRestingHeartRate"),
    MetricSpec("daily-oxygen-saturation", "daily-oxygen-saturation-average",
               "dailyOxygenSaturation.averagePercentage", "%",
               date_prefix="dailyOxygenSaturation"),
    MetricSpec("daily-respiratory-rate", "daily-respiratory-rate",
               "dailyRespiratoryRate.breathsPerMinute", "breaths/min",
               date_prefix="dailyRespiratoryRate"),
    MetricSpec("daily-heart-rate-variability", "daily-hrv-average",
               "dailyHeartRateVariability.averageHeartRateVariabilityMilliseconds", "ms",
               date_prefix="dailyHeartRateVariability"),
    MetricSpec("daily-sleep-temperature-derivations", "nightly-temperature",
               "dailySleepTemperatureDerivations.nightlyTemperatureCelsius", "degC",
               date_prefix="dailySleepTemperatureDerivations"),
    MetricSpec("steps", "steps", "steps.count", "count", "steps.interval.startTime"),
    MetricSpec("distance", "distance", "distance.millimeters", "mm", "distance.interval.startTime"),
    MetricSpec("active-energy-burned", "active-energy-burned",
               "activeEnergyBurned.kcal", "kcal", "activeEnergyBurned.interval.startTime"),
    MetricSpec("active-zone-minutes", "active-zone-minutes",
               "activeZoneMinutes.activeZoneMinutes", "minutes",
               "activeZoneMinutes.interval.startTime"),
)

SPEC_BY_TYPE: dict[str, list[MetricSpec]] = {}
for spec in GOOGLE_HEALTH_SPECS:
    SPEC_BY_TYPE.setdefault(spec.data_type, []).append(spec)

NORMALIZED_FIELDS = [
    "source_id", "source_sha256", "source_row", "source_data_type",
    "metric", "timestamp_raw", "timestamp", "timestamp_status",
    "value", "unit", "source_column", "status"
]


def normalize_google_health_points(input_path: Path, out_dir: Path, source_id: str) -> dict:
    digest = sha256_file(input_path)
    out_path = out_dir / "normalized_observations.tsv"
    type_counts: dict[str, int] = {}
    emitted_counts: dict[str, int] = {}
    timestamp_status_counts: dict[str, int] = {}
    rows_out: list[dict[str, str]] = []

    for i, row in enumerate(read_tsv(input_path), start=2):
        typ = nonempty(row, "data_type")
        type_counts[typ] = type_counts.get(typ, 0) + 1
        for spec in SPEC_BY_TYPE.get(typ, ()):
            value = nonempty(row, spec.value_column)
            if not value:
                continue
            if spec.timestamp_column:
                raw_ts = nonempty(row, spec.timestamp_column)
                canonical_ts, ts_status = canonical_iso(raw_ts)
            else:
                raw_ts = civil_date(row, spec.date_prefix or "")
                canonical_ts, ts_status = (raw_ts, "date-only") if raw_ts else ("", "missing")
            timestamp_status_counts[ts_status] = timestamp_status_counts.get(ts_status, 0) + 1
            rows_out.append({
                "source_id": source_id,
                "source_sha256": digest,
                "source_row": str(i),
                "source_data_type": typ,
                "metric": spec.metric,
                "timestamp_raw": raw_ts,
                "timestamp": canonical_ts,
                "timestamp_status": ts_status,
                "value": value,
                "unit": spec.unit,
                "source_column": spec.value_column,
                "status": "source-value",
            })
            emitted_counts[spec.metric] = emitted_counts.get(spec.metric, 0) + 1

    emitted = write_tsv(out_path, NORMALIZED_FIELDS, rows_out)
    receipt = {
        "processor_contract": PROCESSOR_CONTRACT,
        "command": "google-health-points",
        "source_id": source_id,
        "source_path": input_path.name,
        "source_sha256": digest,
        "input_row_count": sum(type_counts.values()),
        "input_data_type_counts": type_counts,
        "normalized_observation_count": emitted,
        "normalized_metric_counts": emitted_counts,
        "timestamp_status_counts": timestamp_status_counts,
        "output": out_path.name,
        "semantic_boundaries": {
            "diagnosis_inferred": False,
            "causation_inferred": False,
            "missing_values_imputed": False,
            "raw_timestamps_mutated": False,
            "unsupported_data_types_promoted": False,
        },
    }
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8")
    return receipt


QCAT_NUMERIC_METRICS = (
    ("o2", "oxygen-saturation", "%"),
    ("o2_bpm", "oxygen-device-bpm", "beats/min"),
    ("systolic", "blood-pressure-systolic", "mmHg"),
    ("diastolic", "blood-pressure-diastolic", "mmHg"),
    ("bp_bpm", "blood-pressure-device-bpm", "beats/min"),
)


def normalize_qcat_transcription(input_path: Path, out_dir: Path, source_id: str) -> dict:
    digest = sha256_file(input_path)
    rows_out: list[dict[str, str]] = []
    input_count = 0
    note_count = 0
    timestamp_status_counts: dict[str, int] = {}

    for i, row in enumerate(read_tsv(input_path), start=2):
        input_count += 1
        date_raw = nonempty(row, "date_raw")
        time_raw = nonempty(row, "time_raw")
        raw_ts = f"{date_raw} {time_raw}".strip()
        canonical_ts, ts_status = canonical_qcat_datetime(date_raw, time_raw)
        timestamp_status_counts[ts_status] = timestamp_status_counts.get(ts_status, 0) + 1
        subject = nonempty(row, "subject")
        source_row = nonempty(row, "source_row") or str(i)

        for col, metric, unit in QCAT_NUMERIC_METRICS:
            value = nonempty(row, col)
            if not value:
                continue
            rows_out.append({
                "source_id": source_id,
                "source_sha256": digest,
                "source_row": source_row,
                "source_data_type": f"qcat-physiology:{subject}",
                "metric": metric,
                "timestamp_raw": raw_ts,
                "timestamp": canonical_ts,
                "timestamp_status": ts_status,
                "value": value,
                "unit": unit,
                "source_column": col,
                "status": nonempty(row, "transcription_status") or "source-value",
            })

        note = nonempty(row, "note")
        if note:
            note_count += 1
            rows_out.append({
                "source_id": source_id,
                "source_sha256": digest,
                "source_row": source_row,
                "source_data_type": f"qcat-note:{subject}",
                "metric": "contemporaneous-note-present",
                "timestamp_raw": raw_ts,
                "timestamp": canonical_ts,
                "timestamp_status": ts_status,
                "value": "true",
                "unit": "boolean",
                "source_column": "note",
                "status": nonempty(row, "transcription_status") or "source-note",
            })

    out_path = out_dir / "normalized_observations.tsv"
    emitted = write_tsv(out_path, NORMALIZED_FIELDS, rows_out)
    receipt = {
        "processor_contract": PROCESSOR_CONTRACT,
        "command": "qcat-transcription",
        "source_id": source_id,
        "source_path": input_path.name,
        "source_sha256": digest,
        "input_row_count": input_count,
        "rows_with_notes": note_count,
        "normalized_observation_count": emitted,
        "timestamp_status_counts": timestamp_status_counts,
        "output": out_path.name,
        "semantic_boundaries": {
            "diagnosis_inferred": False,
            "causation_inferred": False,
            "source_typos_repaired": False,
            "literal_failure_cells_dropped": False,
            "private_note_text_republished": False,
            "raw_timestamps_mutated": False,
        },
    }
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8")
    return receipt


JOIN_FIELDS = [
    "observation_source_id", "observation_source_row", "observation_timestamp",
    "event_id", "event_timestamp", "event_precision",
    "relation", "delta_seconds", "delta_days", "event_reference"
]


def parse_canonical(value: str) -> Optional[datetime]:
    value = value.strip()
    if not value:
        return None
    try:
        dt = datetime.fromisoformat(value.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt
    except ValueError:
        return None


def relation_for(obs: datetime, event: datetime, precision: str,
                 near_after_hours: float) -> tuple[str, str, str]:
    if precision == "day":
        delta_days = (obs.date() - event.date()).days
        if delta_days == 0:
            return "sameDay", "", "0"
        return ("after" if delta_days > 0 else "before"), "", str(delta_days)

    delta = int((obs - event).total_seconds())
    delta_days = (obs.date() - event.date()).days
    if delta == 0:
        return "sameTimestamp", str(delta), str(delta_days)
    if obs.date() == event.date():
        return "sameDay", str(delta), str(delta_days)
    if 0 < delta <= int(near_after_hours * 3600):
        return "nearAfter", str(delta), str(delta_days)
    if delta > 0:
        return "after", str(delta), str(delta_days)
    return "before", str(delta), str(delta_days)


def temporal_join(observations_path: Path, events_path: Path, out_path: Path,
                  near_after_hours: float) -> dict:
    observations = list(read_tsv(observations_path))
    events = list(read_tsv(events_path))
    rows = []
    unresolved_observations = 0
    unresolved_events = 0

    parsed_events = []
    for ev in events:
        precision = nonempty(ev, "event_precision") or "timestamp"
        event_ts = nonempty(ev, "event_timestamp")
        et = parse_canonical(event_ts)
        if et is None:
            unresolved_events += 1
            continue
        parsed_events.append((ev, et, precision))

    for obs in observations:
        ot = parse_canonical(nonempty(obs, "timestamp"))
        if ot is None:
            unresolved_observations += 1
            continue
        for ev, et, precision in parsed_events:
            relation, delta_seconds, delta_days = relation_for(ot, et, precision, near_after_hours)
            rows.append({
                "observation_source_id": nonempty(obs, "source_id"),
                "observation_source_row": nonempty(obs, "source_row"),
                "observation_timestamp": nonempty(obs, "timestamp"),
                "event_id": nonempty(ev, "event_id"),
                "event_timestamp": nonempty(ev, "event_timestamp"),
                "event_precision": precision,
                "relation": relation,
                "delta_seconds": delta_seconds,
                "delta_days": delta_days,
                "event_reference": nonempty(ev, "event_reference"),
            })

    count = write_tsv(out_path, JOIN_FIELDS, rows)
    receipt = {
        "processor_contract": PROCESSOR_CONTRACT,
        "command": "event-join",
        "observation_source_sha256": sha256_file(observations_path),
        "event_source_sha256": sha256_file(events_path),
        "observation_row_count": len(observations),
        "event_row_count": len(events),
        "join_row_count": count,
        "unparseable_observation_timestamps": unresolved_observations,
        "unparseable_event_timestamps": unresolved_events,
        "near_after_hours": near_after_hours,
        "semantic_boundaries": {
            "temporal_relation_is_causation": False,
            "same_day_is_causation": False,
            "near_after_is_causation": False,
            "event_identity_is_harm_identity": False,
            "day_precision_invents_clock_time": False,
        },
    }
    receipt_path = out_path.with_suffix(out_path.suffix + ".receipt.json")
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8")
    return receipt


def main() -> int:
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="command", required=True)

    gh = sub.add_parser("google-health-points")
    gh.add_argument("input", type=Path)
    gh.add_argument("--out-dir", type=Path, required=True)
    gh.add_argument("--source-id", default="google-health-points")

    qc = sub.add_parser("qcat-transcription")
    qc.add_argument("input", type=Path)
    qc.add_argument("--out-dir", type=Path, required=True)
    qc.add_argument("--source-id", default="qcat-health-pp82-83")

    j = sub.add_parser("event-join")
    j.add_argument("observations", type=Path)
    j.add_argument("events", type=Path,
                   help="TSV columns: event_id,event_timestamp,event_precision,event_reference")
    j.add_argument("--out", type=Path, required=True)
    j.add_argument("--near-after-hours", type=float, default=72.0)

    args = p.parse_args()
    if args.command == "google-health-points":
        receipt = normalize_google_health_points(args.input, args.out_dir, args.source_id)
    elif args.command == "qcat-transcription":
        receipt = normalize_qcat_transcription(args.input, args.out_dir, args.source_id)
    else:
        receipt = temporal_join(args.observations, args.events, args.out, args.near_after_hours)

    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
