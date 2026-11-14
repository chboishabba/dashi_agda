#!/usr/bin/env python3
"""E1 source-treatment join test; deliberately synthetic, not pigeon data."""
from ksw668_movebank_original_treatment_join import reconstruct
gps=[{"individual-local-identifier":"controlA",
      "timestamp":"2026-07-04T14:30:00Z",
      "location-lat":"50.5","location-long":"8.5"}]
meta=[
{"individual-local-identifier":"controlA","treatment":"control",
 "release_timestamp_utc":"2026-07-04T13:00:00Z",
 "loft_lat":"50.5","loft_lon":"8.5","session_id":"dummy",
 "overcast":"true","same_day_tracking_complete":"true"},
{"individual-local-identifier":"depletedB","treatment":"macrophage_depleted",
 "release_timestamp_utc":"2026-07-04T13:00:00Z",
 "loft_lat":"50.5","loft_lon":"8.5","session_id":"dummy",
 "overcast":"true","same_day_tracking_complete":"false"}
]
result=reconstruct(gps,meta,"Europe/Berlin",300)
assert result["groups"]["control"]["arrived_same_local_day"]==1
assert result["groups"]["control"]["arrived_under_70min"]==0
assert result["groups"]["macrophage_depleted"]["censored"]==1
assert result["published_result_reproduced"] is False
print("PASS original-data join safeguards; no absent-GPS inference")
