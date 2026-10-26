#!/usr/bin/env python3
"""Fail-closed Phase-0 audit of the existing 18 Agda screenshot receipts.

Consumes the *original existing* ScreenshotEvidence declarations, not
uploaded image bytes. A declared screenshot SHA256 is an attributed claim
about an attachment, not a freshly computed or source-publisher video hash.
Original visible objects and captions remain user/media-source attributed.
DASHI critical source inventory under Johl Brown's direction, with
OpenAI ChatGPT assisted implementation. No maker/physics inference.
"""
from __future__ import annotations
import argparse
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Cognition/PsychotronicsScreenshotDiscriminationExact.agda"
PATTERN = re.compile(
    r'(?m)^([a-zA-Z]\w*) : ScreenshotEvidence\n'
    r'\1 = screenshot-evidence\n'
    r'  "([^"\n]+\.png)"\n'
    r'  "([0-9a-f]{64})"\n'
    r'  (\w+) (\w+)\n'
    r'  "([^"\n]+)"\n'
    r'  "([^"\n]+)"\n'
    r'  (true|false) (true|false) (true|false) (true|false)$'
)
EXPECTED = 18

def inspect(text: str) -> dict:
    names = re.findall(r"(?m)^([a-zA-Z]\w*) : ScreenshotEvidence\n\1 = screenshot-evidence$", text)
    evidence = list(PATTERN.finditer(text))
    if len(names) != EXPECTED or len(evidence) != EXPECTED:
        raise ValueError("incomplete/altered screenshot record count or shape")
    creators = set(re.findall(r"(?m)^\s+([a-zA-Z]\w*) : Creator$", text))
    scenes = set(re.findall(r"(?m)^\s+([a-zA-Z]\w*) : StillScene$", text))
    refs, files, hashes, maker, scene = [], [], [], [], []
    for m in evidence:
        ref, filename, digest, account, kind, direct, claim, *flags = m.groups()
        refs.append(ref)
        files.append(filename)
        hashes.append(digest)
        maker.append(account)
        scene.append(kind)
        if account not in creators or kind not in scenes:
            raise ValueError("unrecognised creator or scene kind")
        if any(x == "true" for x in flags):
            raise ValueError("a native-media/spectrum/calibration flag changed: require separate original evidence review")
        if not direct or not claim:
            raise ValueError("missing visual observation or caption attribution")
    if set(names) != set(refs) or len(set(refs)) != EXPECTED:
        raise ValueError("duplicate or missing Agda screenshot binding")
    if len(set(files)) != EXPECTED or len(set(hashes)) != EXPECTED:
        raise ValueError("duplicate screenshot filename/hash declaration")

    # The ordinal "fifthImage" is a reference to an existing observed PNG
    # receipt, not a new independent screenshot/source observation.
    aliases = re.findall(
        r"(?m)^([a-zA-Z]\w*) : ScreenshotEvidence\n\1 = ([a-zA-Z]\w+)$",
        text,
    )
    if aliases != [("fifthImage", "oudinCoil")]:
        raise ValueError("missing/changed original fifthImage alias")
    if aliases[0][1] not in set(refs) or aliases[0][0] in set(refs):
        raise ValueError("alias cannot create an original observation")

    return {
        "screenshot_receipts": EXPECTED,
        "unique_declared_screenshot_hashes": EXPECTED,
        "additional_original_stills_from_alias": 0,
        "display_fifthImage_aliases_original_oudinCoil": True,
        "unique_declared_attachment_filenames": EXPECTED,
        "distinct_creator_tags": len(set(maker)),
        "creator_groups": dict(sorted(Counter(maker).items())),
        "scene_groups": dict(sorted(Counter(scene).items())),
        "original_reels_verifiably_inspected": 0,
        "spectrum_measurements_verified": 0,
        "instrument_calibrations_verified": 0,
        "screenshot_image_bytes_rehashed_now": False,
        "same_SKU_or_original_media_from_still_proved": False,
        "phase0_declared_evidence_completeness_only": True,
    }

def self_test(text: str) -> dict:
    inspect(text)
    found = list(PATTERN.finditer(text))
    if len(found) != EXPECTED:
        raise AssertionError("record extraction failure")
    first, second = found[0], found[1]
    tests = {
        "duplicate_filename": text[:second.start(2)] + first.group(2) + text[second.end(2):],
        "duplicate_hash": text[:second.start(3)] + first.group(3) + text[second.end(3):],
        "malformed_hash": text[:first.start(3)] + "!" + first.group(3)[1:] + text[first.end(3):],
        "unknown_creator": text[:first.start(4)] + "unsupportedMaker" + text[first.end(4):],
        "unknown_scene": text[:first.start(5)] + "unreportedPhenomenon" + text[first.end(5):],
        "fake_video_verified": text[:first.start(8)] + "true" + text[first.end(8):],
        "missing_record": text[:first.start()] + text[first.end():],
        "false_nineteenth_still": text.replace("fifthImage = oudinCoil", "fifthImage = newFictionalStill"),
    }
    count = 0
    for key, altered in tests.items():
        try:
            inspect(altered)
        except ValueError:
            count += 1
        else:
            raise AssertionError("adverse screenshot mutation accepted: " + key)
    assert count == len(tests) == 8
    return {"adversarial_source_mutations_rejected": count}

def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    original = OWNER.read_text(encoding="utf-8")
    result = inspect(original)
    if args.self_test:
        result["self_test"] = self_test(original)
    print(json.dumps(result, sort_keys=True, indent=2))

if __name__ == "__main__":
    main()
