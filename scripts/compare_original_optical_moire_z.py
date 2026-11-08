#!/usr/bin/env python3
"""Source-data z-plane comparison for Dev & Shen (2026), DOI
10.1038/s41377-026-02533-w; original DR-NTU dataset 10.21979/N9/AJB6FD.
DASHI owns this independent analysis, not the original science.
An original six-channel dataset file is NOT automatically an experimental frame.
"""
import argparse, json
from pathlib import Path
import numpy as np
from replicate_dev_shen_original_matlab import discover, channels, stokes, charge, sha256

def compare(root,prefix,z_labels,stokes_floor=.001,max_pair_mismatch=.1):
    cases=discover(root)
    labels=[f"{prefix}/{z}" for z in z_labels]
    missing=[x for x in labels if x not in cases or len(cases[x])!=6]
    if missing:
        return {"status":"SOURCE_DATA_MISSING","requested":labels,
                "missing":missing,"experimental_replication_certified":False}
    frames=[]
    for label in labels:
        paths=cases[label]
        n,valid,quality=stokes(channels(paths),intensity_fraction=stokes_floor)
        if quality["pair_totals_relative_mismatch"]>max_pair_mismatch:
            return {"status":"CALIBRATION_UNRESOLVED","case":label,"quality":quality,
                    "experimental_replication_certified":False}
        frames.append((label,n,valid,quality,{k:sha256(v) for k,v in paths.items()}))
    if len({f[1].shape for f in frames})!=1:
        return {"status":"IMAGE_REGISTRATION_UNRESOLVED","experimental_replication_certified":False}
    base=frames[0]
    result=[]
    for label,n,v,quality,hashes in frames:
        good=base[2]&v
        if not good.any():
            return {"status":"NO_COMMON_VALID_STOKES","case":label,
                    "experimental_replication_certified":False}
        cosine=np.clip(np.sum(base[1][:,good]*n[:,good],axis=0),-1,1)
        angles=np.arccos(cosine)
        q=charge(n,v)
        result.append({"case":label,"mean_Poincare_angle_rad":float(np.mean(angles)),
                       "p95_Poincare_angle_rad":float(np.quantile(angles,.95)),
                       "common_valid_fraction":float(good.mean()),
                       "open_patch_charge":q["open_patch_charge"],
                       "incomplete_cells":q["incomplete_cells"],
                       "raw_array_sha256":hashes,"image_registration_certified":False,
                       "integer_degree_certified":False,"quality":quality})
    return {"status":"SOURCE_DATA_COMPUTED_NOT_EXPERIMENTALLY_CALIBRATED",
            "original_authors":["Vasu Dev","Yijie Shen"],
            "original_article_doi":"10.1038/s41377-026-02533-w",
            "original_dataset_doi":"10.21979/N9/AJB6FD",
            "source_dataset_type":"simulation data",
            "warning":"No pixel registration, independent apparatus calibration, uncertainty model or per-file experimental status implied",
            "frames":result,"experimental_replication_certified":False}

def test():
    from tempfile import TemporaryDirectory
    from scipy.io import savemat
    with TemporaryDirectory() as temp:
        root=Path(temp)
        x,y=np.meshgrid(np.linspace(-1,1,33),np.linspace(-1,1,33))
        n=np.stack((np.sin(x),np.sin(y),np.ones_like(x)))
        n=n/np.linalg.norm(n,axis=0)
        vals={"IH":(1+n[0])/2,"IV":(1-n[0])/2,
              "ID":(1+n[1])/2,"IA":(1-n[1])/2,
              "IR":(1+n[2])/2,"IL":(1-n[2])/2}
        for z in ("0","10"):
            folder=root/"C4"/"10_35"/z;folder.mkdir(parents=True)
            for k,v in vals.items():savemat(folder/(k+".mat"),{k:v})
        good=compare(root,"C4/10_35",["0","10"])
        assert good["status"]=="SOURCE_DATA_COMPUTED_NOT_EXPERIMENTALLY_CALIBRATED"
        assert len(good["frames"])==2
        assert good["frames"][1]["mean_Poincare_angle_rad"]<1e-7
        bad=compare(root,"C4/10_35",["0","20"])
        assert bad["status"]=="SOURCE_DATA_MISSING"
        return {"two_plane_synthetic_regression":"PASS",
                "missing_original_plane_fail_closed":"PASS",
                "actual_original_arrays_processed":False}

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--test",action="store_true")
    parser.add_argument("--root",type=Path)
    parser.add_argument("--prefix",default="C4/10_35")
    parser.add_argument("--z",nargs="+",default=["0","10","20","30","40"])
    parser.add_argument("--out",type=Path)
    a=parser.parse_args()
    if a.test: result=test()
    elif a.root: result=compare(a.root,a.prefix,a.z)
    else: parser.error("use --test or --root original source directory")
    if a.out:
        a.out.parent.mkdir(parents=True,exist_ok=True)
        a.out.write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
