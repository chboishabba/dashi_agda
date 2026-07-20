#!/usr/bin/env python3
"""Render normalized DASHI world-tube JSON as a self-contained Three.js page."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

HTML = r'''<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width,initial-scale=1" />
<title>DASHI spacetime history world-tube</title>
<style>
html,body{margin:0;height:100%;overflow:hidden;background:#080a10;color:#eee;font-family:system-ui}
#hud{position:fixed;z-index:2;left:12px;top:12px;background:#111a;padding:12px;border-radius:10px;max-width:360px}
#hud input{width:100%} canvas{display:block}
.small{font-size:12px;opacity:.8}
</style>
<script type="importmap">{"imports":{"three":"https://unpkg.com/three@0.166.1/build/three.module.js","three/addons/":"https://unpkg.com/three@0.166.1/examples/jsm/"}}</script>
</head>
<body>
<div id="hud">
  <strong>DASHI world-tube</strong>
  <div class="small">Horizontal: local ECEF displacement. Vertical: normalized time. Tube radius: reported uncertainty.</div>
  <label>Present slice <input id="slice" type="range" min="0" max="1000" value="1000"></label>
  <label>Time height <input id="height" type="range" min="10" max="500" value="180"></label>
  <div id="status" class="small"></div>
</div>
<script id="worldtube-data" type="application/json">__DATA__</script>
<script type="module">
import * as THREE from 'three';
import {OrbitControls} from 'three/addons/controls/OrbitControls.js';
const data=JSON.parse(document.getElementById('worldtube-data').textContent);
const rows=data.observations||[];
const scene=new THREE.Scene();
scene.background=new THREE.Color(0x080a10);
const camera=new THREE.PerspectiveCamera(55,innerWidth/innerHeight,.1,10000);
camera.position.set(180,140,220);
const renderer=new THREE.WebGLRenderer({antialias:true});
renderer.setPixelRatio(devicePixelRatio); renderer.setSize(innerWidth,innerHeight); document.body.appendChild(renderer.domElement);
const controls=new OrbitControls(camera,renderer.domElement); controls.enableDamping=true;
scene.add(new THREE.GridHelper(400,20));
const light=new THREE.DirectionalLight(0xffffff,2); light.position.set(100,200,100); scene.add(light); scene.add(new THREE.AmbientLight(0xffffff,.5));
const group=new THREE.Group(); scene.add(group);
const slicePlane=new THREE.Mesh(new THREE.PlaneGeometry(420,420),new THREE.MeshBasicMaterial({color:0xffffff,transparent:true,opacity:.08,side:THREE.DoubleSide}));
slicePlane.rotation.x=-Math.PI/2; scene.add(slicePlane);
const first=rows[0]?.ecef_m||{x:0,y:0,z:0};
const t0=rows[0]?.timestamp_ms||0, t1=rows.at(-1)?.timestamp_ms||t0+1;
const span=Math.max(1,t1-t0);
const scale=.001;
function point(row,height){return new THREE.Vector3((row.ecef_m.x-first.x)*scale,((row.timestamp_ms-t0)/span)*height,(row.ecef_m.y-first.y)*scale)}
function rebuild(){
  group.clear(); const height=+document.getElementById('height').value;
  const pts=rows.map(r=>point(r,height));
  if(pts.length>1){const curve=new THREE.CatmullRomCurve3(pts); const geom=new THREE.TubeGeometry(curve,Math.max(16,pts.length*2),1.2,8,false); const mat=new THREE.MeshStandardMaterial({color:0x68a7ff,roughness:.45,metalness:.1}); group.add(new THREE.Mesh(geom,mat));}
  rows.forEach((r,i)=>{const radius=Math.max(.7,Math.min(8,(r.accuracy_m||5)*.08)); const mesh=new THREE.Mesh(new THREE.SphereGeometry(radius,10,8),new THREE.MeshStandardMaterial({color:r.vendor_inference?0xffb86b:0x8affb5})); mesh.position.copy(pts[i]); group.add(mesh);});
  updateSlice(); document.getElementById('status').textContent=`${rows.length} observations · ${data.segments?.length||0} intervals`;
}
function updateSlice(){const height=+document.getElementById('height').value; slicePlane.position.y=(+document.getElementById('slice').value/1000)*height;}
document.getElementById('slice').addEventListener('input',updateSlice); document.getElementById('height').addEventListener('input',rebuild);
addEventListener('resize',()=>{camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();renderer.setSize(innerWidth,innerHeight)});
rebuild(); renderer.setAnimationLoop(()=>{controls.update();renderer.render(scene,camera)});
</script>
</body></html>'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text(encoding="utf-8"))
    payload = json.dumps(data).replace("</", "<\\/")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(HTML.replace("__DATA__", payload), encoding="utf-8")
    print(f"wrote renderer to {args.output}")


if __name__ == "__main__":
    main()
