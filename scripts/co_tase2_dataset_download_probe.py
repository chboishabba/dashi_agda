"""Probe the public UCF STARS native Co1/4TaSe2 dataset endpoint.

This is intentionally a probe, not a scraper.  It records HTTP status and never
substitutes synthetic data.  The 2026-10-08 execution environment observed 403
for the native viewcontent endpoint while the landing page remained public.
"""
import json
import urllib.error
import urllib.request

LANDING = "https://stars.library.ucf.edu/datasets/30/"
NATIVE = "https://stars.library.ucf.edu/context/datasets/article/1050/type/native/viewcontent"


def probe():
    req = urllib.request.Request(NATIVE, headers={"User-Agent": "dashi-research-replication/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return {"landing": LANDING, "native": NATIVE, "status": r.status,
                    "content_type": r.headers.get("Content-Type"),
                    "content_length": r.headers.get("Content-Length"),
                    "acquired": r.status == 200}
    except urllib.error.HTTPError as e:
        return {"landing": LANDING, "native": NATIVE, "status": e.code,
                "reason": str(e.reason), "acquired": False}


if __name__ == "__main__":
    print(json.dumps(probe(), indent=2))
