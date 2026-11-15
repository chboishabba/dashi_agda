#!/usr/bin/env python3
"""Run 3x3x3 ternary experiment on the *same browser* collision engine.

Not an Agda theorem, a Maxwell solver, a universal optimum, or a physical
measurement. Original experiment runner: Kozyrev PR #1404; optical mechanics,
C3/S3 indexing, and existing physics theorems retain external/prior owners.
Requires local browser engine HTML whose API exposes __spiralAudit.
"""
import argparse
import itertools
import json
from pathlib import Path
from playwright.sync_api import sync_playwright

def run(html, seed_scene, *, rays=16):
    rows=[]
    with sync_playwright() as p:
        browser=p.chromium.launch(headless=True, executable_path="/usr/bin/chromium",
                                  args=["--no-sandbox"])
        page=browser.new_page()
        page.set_content(Path(html).read_text(encoding="utf-8"))
        for family in ("arch","log","segmented"):
            # 27 ternary configurations per family; absorber ON/OFF paired.
            for level,turns,delta in itertools.product(range(3),
                                                       (1.25,1.5,1.75),
                                                       (-7.,0.,7.)):
                for absorber in (False,True):
                    scene=json.loads(json.dumps(seed_scene))
                    g=scene["geometry"]
                    g["family"]=family
                    g["growth"]=([.34,.402,.46] if family!="log"
                                 else [.10,.133702762,.17])[level]
                    g["correction"]=([-.07,0,.07][level] if family=="segmented" else 0)
                    g["turns"]=turns
                    scene["emitter"]["ang"]=-90+delta
                    scene["tracer"]["targetOn"]=absorber
                    scene["tracer"]["rays"]=rays
                    try:
                        page.evaluate("(s)=>window.__spiralAudit.loadScene(s)",scene)
                        metrics=page.evaluate("""()=>{
                          const r=window.__spiralAudit.simulate();
                          return {torque_Nm:r.sumT,receiver_W:r.sumTarget,
                                  collisions:r.nHit,entered:r.gateRays,
                                  unresolved:r.nUnresolved+r.nBounded,
                                  escaped_W:r.sumExit,wall_heat_W:r.sumAbs}
                        }""")
                        metrics["eligible"]=metrics["entered"]==rays and metrics["unresolved"]==0
                        rows.append(dict(scene=scene,metrics=metrics))
                    except Exception as exc:
                        rows.append(dict(scene=scene,error=str(exc)))
        browser.close()
    return {"schema":"kozyrev-html-cross-family-ternary/1",
            "cases":rows,"count":len(rows),
            "limits":"SDF ray numerical comparison only; not EM WGM/physical optimum"}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--html",required=True)
    ap.add_argument("--scene",required=True)
    ap.add_argument("--output",required=True)
    args=ap.parse_args()
    with open(args.scene,encoding="utf-8") as f:seed=json.load(f)
    result=run(args.html,seed)
    Path(args.output).write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
if __name__=="__main__":main()
