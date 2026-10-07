import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=next(p for p in HERE.parents if (p/'scripts/aws-archive-migration').is_dir())
WEB=REPO.parent/'Quantyra-Website'
repair=(WEB/'scripts/aws-migration/source-lifecycle/repair.test.mjs').read_text()
overlay=repair[repair.index('function overlayFixture()'):repair.index("\ntest('S3157 committed overlay")]
prefix="""import fs from 'node:fs';import path from 'node:path';import os from 'node:os';import assert from 'node:assert/strict';import {spawnSync} from 'node:child_process';import {pins,hash} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/core.mjs';import {oldRecord} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/retirement-overlay.mjs';\n"""
(HERE/'overlay-derived-fixture.mjs').write_text(prefix+overlay+'\nexport {overlayFixture};\n')
route=WEB/'scripts/aws-migration/route53.mjs'
source=route.read_text()
def extract(start,end):return source[source.index('async function '+start):source.index('async function '+end)]
code=extract('importZone(','fetchSource(')+extract('plan(','parentChecks(')
ports="""import fs from 'node:fs';import path from 'node:path';import {parseExport,normalizeRecords,compareSets,valueKey} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/zone-import.mjs';import {fqdn} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/dns-wire.mjs';import {suppressRetired,assertDesiredReplay} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/retirement-overlay.mjs';import {hash as sha} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/core.mjs';
export function harness(ports){
const {root,config,websiteLoad,clients,identity,send,loadOverlay,ownedZone,gate,listRecords,route}=ports;
const folder=path.join(root,'route-evidence'),zoneName='quantyra.org.',stamp=()=>new Date().toISOString();
const save=(name,data)=>{fs.mkdirSync(folder,{recursive:true});fs.writeFileSync(path.join(folder,name),JSON.stringify(data,null,2)+'\\n');};
const has=name=>fs.existsSync(path.join(folder,name));const load=name=>JSON.parse(fs.readFileSync(path.join(folder,name)));
"""
(HERE/'route-derived-harness.mjs').write_text(ports+code+'\nreturn {importZone,plan,stage,save,load,folder};\n}\n')
(HERE/'route-probe-provenance.json').write_text(json.dumps({'route_source':str(route),'sha256':hashlib.sha256(route.read_bytes()).hexdigest(),'method':'Exact importZone/plan/stage function bodies from final owned path. Rebind AWS/control/filesystem ports into retained local synthetic fixture; real overlay and record-normalization modules imported read-only. No production code or cloud writes.'},indent=2)+'\n')
