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
        owner=original["w1_source_boundary_welds"]["reciprocal_controller_ward"]["source_owner"]
        p=root/owner;p.parent.mkdir(parents=True);p.write_text("print('PASS symbolically')\n")
        accepted=audit(original,root)["A_shielding"]
        assert len(accepted["owners"][owner])==64 and accepted["status"]=="OPEN"
        # A standalone mathematical fixture must NOT match the pinned original owner.
        assert owner in accepted.get("mismatched_w1_sources",[])
    for which in ("fake_stage","fake_lane","no_owner","repeat_weld","w1_physical_promotion","w1_bad_lane","w1_bad_blob","w2_physical_promotion","w2_wrong_source_pin","w2_flux_promotion","w2_flux_bad_blob","w2_mass_flux_promotion","w2_wall_frame_bad_pin","w2_constraint_family_bad_lane","w2_material_flux_promotion","w2_material_flux_bad_pin","w2_euler_frozen_false_promotion","w2_euler_firstjet_bad_pin","w3_false_promotion","w3_bad_source_pin"):
        m=copy.deepcopy(original)
        if which=="fake_stage":m["lanes"]["A_shielding"]["unpaid_stages"].append("PROMOTED")
        elif which=="fake_lane":m["lanes"]["Fake_closure"]={}
        elif which=="no_owner":m["lanes"]["A_shielding"]["owner"]=[]
        elif which=="repeat_weld":m["cross_lane_shared_welds"]["ward_source"].append("A_shielding")
        elif which=="w1_physical_promotion":m["w1_source_boundary_welds"]["tov_mass_traction_israel"]["physical_paid"]=True
        elif which=="w1_bad_lane":m["w1_source_boundary_welds"]["tov_mass_traction_israel"]["lanes"].append("nonexistent_lane")
        elif which=="w1_bad_blob":m["w1_source_boundary_welds"]["tov_mass_traction_israel"]["source_git_blob_sha1"]="not-a-git-blob"
        elif which=="w2_physical_promotion":m["w2_boundary_packets"]["moving_tov_timelike"]["physical_paid"]=True
        elif which=="w2_wrong_source_pin":m["w2_boundary_packets"]["three_source_reverse"]["checker_git_blob_sha1"]="bad-pin"
        elif which=="w2_flux_promotion":m["w2_boundary_packets"]["dynamic_tov_flux_israel"]["physical_paid"]=True
        elif which=="w2_flux_bad_blob":m["w2_boundary_packets"]["dynamic_tov_flux_israel"]["checker_git_blob_sha1"]="bad-pin"
        elif which=="w2_mass_flux_promotion":m["w2_boundary_packets"]["mass_flux_surface"]["physical_paid"]=True
        elif which=="w2_wall_frame_bad_pin":m["w2_boundary_packets"]["wall_frame_stress_inverse"]["checker_git_blob_sha1"]="bad-pin"
        elif which=="w2_constraint_family_bad_lane":m["w2_boundary_packets"]["moving_constraint_family"]["lanes"].append("false_physical_lane")
        elif which=="w2_material_flux_promotion":m["w2_boundary_packets"]["original_material_flux_weld"]["physical_paid"]=True
        elif which=="w2_material_flux_bad_pin":m["w2_boundary_packets"]["original_material_flux_weld"]["checker_git_blob_sha1"]="bad-pin"
        elif which=="w2_euler_frozen_false_promotion":m["w2_boundary_packets"]["original_euler_frozen_surface"]["physical_paid"]=True
        elif which=="w2_euler_firstjet_bad_pin":m["w2_boundary_packets"]["original_euler_firstjet"]["checker_git_blob_sha1"]="bad-pin"
        elif which=="w3_false_promotion":m["w3_original_action_boundary"]["quadratic_mass_constraint"]["physical_paid"]=True
        else:m["w3_original_action_boundary"]["surface_gradient_repair"]["source_git_blob_sha1"]="bad-pin"
        try:audit(m)
        except (AssertionError,KeyError):pass
        else:raise AssertionError("admitted "+which)
    print("PASS 12 lanes, 36 unpaid results, source presence nonpromotion, 20 malformed-claim controls")

if __name__=="__main__":main()
