#!/usr/bin/env python3
"""Matched-envelope HTML SDF candidate comparison, Kozyrev PR #1404.

Three geometry families share exact inner and outer radii, source and input.
Only a bounded screened experiment; no global-optimal or Maxwell claim.
Uses the SAME html page simulator API for all candidates.
"""
import argparse
import itertools
import json
import math
from pathlib import Path
from playwright.sync_api import sync_playwright
C=299792458.

def normalized_geometry(scene, family, turns, outer):
    geometry=scene["geometry"]
    inner=geometry["inner"]
    theta=2*math.pi*turns
    geometry["family"]=family
    geometry["turns"]=turns
    geometry["growth"]=(math.log(outer/inner)/theta if family=="log"
                        else (outer-inner)/theta)
    geometry["correction"]=.05 if family=="segmented" else 0.
    return scene

def run(html_path, source_scene_path, output, ray_count=8):
    seed=json.loads(Path(source_scene_path).read_text(encoding="utf-8"))
    g=seed["geometry"]
    if g.get("family","arch")!="arch":
        raise ValueError("source must be Archimedean to fix outer radius")
    outer=g["inner"]+g["growth"]*2*math.pi*g["turns"]
    rows=[]
    with sync_playwright() as p:
        browser=p.chromium.launch(headless=True)
        page=browser.new_page()
        page.set_content(Path(html_path).read_text(encoding="utf-8"))
        for family, turns, angle, target in itertools.product(
                ("arch","log","segmented"),(1.25,1.5,1.75),
                (-97.,-90.,-83.),(False,True)):
            scene=normalized_geometry(json.loads(json.dumps(seed)),family,turns,outer)
            scene["emitter"]["ang"]=angle
            scene["tracer"]["targetOn"]=target
            scene["tracer"]["rays"]=ray_count
            try:
                result=page.evaluate("""s=>{
                    window.__spiralAudit.loadScene(s);
                    const r=window.__spiralAudit.simulate();
                    return {torque_Nm:r.sumT,target_W:r.sumTarget,
                      entered:r.gateRays,
                      unresolved:r.nUnresolved+r.nBounded,
                      reflections:r.nHit,wall_absorbed_W:r.sumAbs,
                      escaped_W:r.sumExit};
                }""",scene)
                result["admissible"]=result["entered"]==ray_count and result["unresolved"]==0
                result["clockwise_coefficient"]=-result["torque_Nm"]*C/(scene["tracer"]["watt"]*outer)
                rows.append(dict(scene=scene,metrics=result))
            except Exception as error:
                rows.append(dict(scene=scene,error=str(error)))
        browser.close()
    report=dict(schema="kozyrev-matched-envelope/1",
                source_scene=source_scene_path, outer_radius_m=outer,
                rays_per_screen=ray_count, rows=rows,
                status="bounded 2D SDF screen, no independent curve-intersection verification")
    Path(output).write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    return report

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--html",required=True)
    ap.add_argument("--scene",required=True)
    ap.add_argument("--output",required=True)
    ap.add_argument("--rays",type=int,default=8)
    args=ap.parse_args()
    print(len(run(args.html,args.scene,args.output,args.rays)["rows"]))
