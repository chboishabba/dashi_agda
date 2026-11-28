"""Exact source-ledger negative-control regression; no physical promotion."""
import copy,json,tempfile
from pathlib import Path
from check_engineered_gravity_proof_dag import audit,DEFAULT,LANES

def main():
    original=json.loads(DEFAULT.read_text())
    data=audit(original)
    assert tuple(data)==LANES and len(data)==12
    assert sum(len(x["unpaid"]) for x in data.values())==36
    assert all(x["status"]=="OPEN" for x in data.values())
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp)
        blocked=audit(original,root)
        assert all("MISSING" in x["owners"].values() for x in blocked.values())
        owner=original["lanes"]["A_shielding"]["owner"][0]
        p=root/owner;p.parent.mkdir(parents=True);p.write_text("print('PASS symbolically')\n")
        accepted=audit(original,root)["A_shielding"]
        assert len(accepted["owners"][owner])==64 and accepted["status"]=="OPEN"
        # A standalone mathematical fixture must NOT match the pinned original owner.
        assert owner in accepted.get("mismatched_w1_sources",[])
    for which in ("fake_stage","fake_lane","no_owner","repeat_weld","w1_physical_promotion","w1_bad_lane","w1_bad_blob"):
        m=copy.deepcopy(original)
        if which=="fake_stage":m["lanes"]["A_shielding"]["unpaid_stages"].append("PROMOTED")
        elif which=="fake_lane":m["lanes"]["Fake_closure"]={}
        elif which=="no_owner":m["lanes"]["A_shielding"]["owner"]=[]
        elif which=="repeat_weld":m["cross_lane_shared_welds"]["ward_source"].append("A_shielding")
        elif which=="w1_physical_promotion":m["w1_source_boundary_welds"]["tov_mass_traction_israel"]["physical_paid"]=True
        elif which=="w1_bad_lane":m["w1_source_boundary_welds"]["tov_mass_traction_israel"]["lanes"].append("nonexistent_lane")
        else:m["w1_source_boundary_welds"]["tov_mass_traction_israel"]["source_git_blob_sha1"]="not-a-git-blob"
        try:audit(m)
        except (AssertionError,KeyError):pass
        else:raise AssertionError("admitted "+which)
    print("PASS 12 lanes, 36 unpaid results, source presence nonpromotion, 7 malformed-claim controls")

if __name__=="__main__":main()
