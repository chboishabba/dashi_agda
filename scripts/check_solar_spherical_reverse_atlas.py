"""Separate timed acceptance lane for the common structural spherical atlas."""
import json
from check_solar_spherical_reverse_integration import run
if __name__=='__main__':
    print(json.dumps(run(common_atlas=True),indent=2))
