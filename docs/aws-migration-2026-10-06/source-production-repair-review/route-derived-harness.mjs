import fs from 'node:fs';import path from 'node:path';import {parseExport,normalizeRecords,compareSets,valueKey} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/zone-import.mjs';import {fqdn} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/dns-wire.mjs';import {suppressRetired,assertDesiredReplay} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/retirement-overlay.mjs';import {hash as sha} from 'file:///C:/Users/dfred/Desktop/Projects/Quantyra-Website/scripts/aws-migration/source-lifecycle/core.mjs';
export function harness(ports){
const {root,config,websiteLoad,clients,identity,send,loadOverlay,ownedZone,gate,listRecords,route}=ports;
const folder=path.join(root,'route-evidence'),zoneName='quantyra.org.',stamp=()=>new Date().toISOString();
const save=(name,data)=>{fs.mkdirSync(folder,{recursive:true});fs.writeFileSync(path.join(folder,name),JSON.stringify(data,null,2)+'\n');};
const has=name=>fs.existsSync(path.join(folder,name));const load=name=>JSON.parse(fs.readFileSync(path.join(folder,name)));
async function importZone(file){
  if(!file)throw Error('ExportPathRequired');const bytes=fs.readFileSync(path.resolve(file));if(bytes.length>4*1024*1024)throw Error('ExportByteBoundExceeded');const hash=sha(bytes),records=parseExport(bytes.toString('utf8'));const overlay=loadOverlay();suppressRetired(records,overlay);
  const cache=path.join(root,'.migration-cache/dns');fs.mkdirSync(cache,{recursive:true});fs.writeFileSync(path.join(cache,hash),bytes);
  // Caller must supply an actual complete authoritative provider export, not public query output.
  const known=has('public-source-discovery.json')?load('public-source-discovery.json').records:[];
  const missing=known.filter(r=>!['SOA','NS'].includes(r.Type)&&!records.some(x=>x.Name===r.Name&&x.Type===r.Type&&JSON.stringify(x.ResourceRecords.map(v=>valueKey(x.Type,v.Value)).sort())===JSON.stringify(r.ResourceRecords.map(v=>valueKey(r.Type,v.Value)).sort())));
  if(missing.length){save('export-coverage-failure.json',{utc:stamp(),sha256:hash,missing:missing.map(x=>({name:x.Name,type:x.Type}))});throw Error('ExportDoesNotCoverKnownAuthoritativeRecords');}
  save('source-export-'+hash+'.json',{utc:stamp(),sha256:hash,records});save('source-export.json',{utc:stamp(),sha256:hash,authority:'operator-supplied authoritative provider zone export',records,complete:true});
  save('source-inventory-status.json',{utc:stamp(),complete:true,exportPresent:true,sha256:hash,recordSets:records.length,rawCustody:'.migration-cache/dns/'+hash});console.log(JSON.stringify({stage:'import',recordSets:records.length,sha256:hash}));
}
async function plan(){
  await identity(clients('destination'),'destination');const website=websiteLoad('destination-state.json'),cert=await send(clients('destination'),'acm','DescribeCertificate',{CertificateArn:website.certificate});
  const source=has('source-export.json')?load('source-export.json'):has('public-source-discovery.json')?load('public-source-discovery.json'):{records:[],complete:false};
  const overlay=loadOverlay();
  const records=suppressRetired(source.records,overlay).filter(r=>!(r.Name===zoneName&&['NS','SOA'].includes(r.Type))&&!(['quantyra.org.','www.quantyra.org.'].includes(r.Name)&&['A','AAAA','CNAME'].includes(r.Type)));
  const overrides=[];
  for(const name of config.domains)for(const type of ['A','AAAA']){const r={Name:fqdn(name),Type:type,AliasTarget:{HostedZoneId:'Z2FDTNDATAQYW2',DNSName:fqdn(website.domain),EvaluateTargetHealth:false}};overrides.push(r);}
  for(const v of cert.Certificate.DomainValidationOptions||[]){if(!v.ResourceRecord)throw Error('CertificateValidationRecordNotReady');overrides.push({Name:fqdn(v.ResourceRecord.Name),Type:'CNAME',TTL:600,ResourceRecords:[{Value:fqdn(v.ResourceRecord.Value)}]});}
  for(const name of ['_.quantyra.org.','_www.quantyra.org.'])overrides.push({Name:name,Type:'TXT',TTL:600,ResourceRecords:[{Value:JSON.stringify(website.domain)}]});
  for(const r of overrides){const existing=records.find(x=>x.Name===r.Name&&x.Type===r.Type);if(existing&&JSON.stringify(existing.ResourceRecords)!==JSON.stringify(r.ResourceRecords))throw Error('MigrationRecordConflictsWithSource');if(!existing)records.push(r);}
  assertDesiredReplay(records,overlay);
  const excluded=source.records.filter(r=>!records.some(x=>x.Name===r.Name&&x.Type===r.Type));
  const report={utc:stamp(),retirementOverlay:overlay,completeSourceInventory:source.complete===true,sourceExportSha256:source.sha256||null,certificateStatus:cert.Certificate.Status,certificate:website.certificate,distribution:website.distribution,distributionDomain:website.domain,records,excluded,expectedChanges:'Provider apex NS/SOA replaced; apex/www web records replaced by destination A/AAAA aliases; all other source records retained.'};
  const exact=Buffer.from(JSON.stringify(report,null,2)+'\n');save('record-plan-'+sha(exact)+'.json',report);save('record-plan.json',report);console.log(JSON.stringify({stage:'plan',recordSets:records.length,completeSourceInventory:report.completeSourceInventory,certificateStatus:report.certificateStatus}));
}
async function stage(){
  const s=await ownedZone();await plan();const p=load('record-plan.json');const overlay=loadOverlay();assertDesiredReplay(p.records,overlay);await gate(['route53:ChangeResourceRecordSets'],'arn:aws:route53:::hostedzone/'+s.id.replace('/hostedzone/',''));
  const actual=await listRecords(s.id);suppressRetired(actual,overlay);const checks=compareSets(p.records,actual),changes=[];
  const previouslyStaged=suppressRetired(has('staged-records.json')?load('staged-records.json').records:[],overlay);
  for(let i=0;i<p.records.length;i++)if(!checks[i].match){const r=p.records[i],old=actual.find(x=>fqdn(x.Name)===r.Name&&x.Type===r.Type);if(old&&!compareSets([old],previouslyStaged)[0].match)throw Error('ExistingStagedRecordConflict_ReviewRequired');changes.push({Action:old?'UPSERT':'CREATE',ResourceRecordSet:r});}
  // Preserve the exact previous owned staging state before export-driven updates; never delete records.
  if(changes.length)save('staging-before-change-'+Date.now()+'.json',{utc:stamp(),records:actual});
  for(let start=0;start<changes.length;start+=50){const batch=changes.slice(start,start+50);const currentOverlay=loadOverlay();if(JSON.stringify(currentOverlay)!==JSON.stringify(overlay))throw Error('RetirementOverlayChangedBeforeStage');assertDesiredReplay(batch.map(c=>c.ResourceRecordSet),currentOverlay);if(JSON.stringify(batch).length>32000)throw Error('ChangeBatchByteBoundExceeded');const x=await route('ChangeResourceRecordSets',{HostedZoneId:s.id,ChangeBatch:{Comment:'S3157 staged '+(p.completeSourceInventory?'authoritative export':'known records; inventory incomplete'),Changes:batch}});save('change-'+Date.now()+'.json',{utc:stamp(),id:x.ChangeInfo.Id,status:x.ChangeInfo.Status,recordPlanSha256:sha(fs.readFileSync(path.join(folder,'record-plan.json'))),changes:batch.length});save('staged-records.json',{utc:stamp(),records:await listRecords(s.id)});}
  save('staged-records.json',{utc:stamp(),records:await listRecords(s.id)});console.log(JSON.stringify({stage:'stage',created:changes.length,completeSourceInventory:p.completeSourceInventory}));
}

return {importZone,plan,stage,save,load,folder};
}
