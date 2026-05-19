import json
from itertools import combinations

def canonical_summary_family(vec15):
    """
    vec15: iterable of DefectOrbitSummary-like objects or dicts
    Produces a stable tuple representation of the full Vec15 family.
    """
    out = []
    for s in vec15:
        if isinstance(s, dict):
            d = s
        else:
            d = s.__dict__
        out.append((
            int(d["forcedStableCount"]),
            int(d["motifChangeCount"]),
            int(d["totalDrift"]),
            int(d["repatterningCount"]),
            int(d["contractiveCount"]),
            int(d["expansiveCount"]),
        ))
    return tuple(out)

def find_separator(generator_names, profile_summary_family_fn):
    encoded = {}
    for name in generator_names:
        encoded[name] = canonical_summary_family(profile_summary_family_fn(name))

    for a, b in combinations(generator_names, 2):
        if encoded[a] != encoded[b]:
            return {
                "separates": True,
                "left": a,
                "right": b,
                "left_summary": encoded[a],
                "right_summary": encoded[b],
            }

    return {
        "separates": False,
        "collapse_classes": encoded,
    }

if __name__ == "__main__":
    print("Wire `generator_names` and `profile_summary_family_fn` to your repo runtime.")
