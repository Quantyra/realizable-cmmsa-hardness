// S3 normalizes ordering and singleton Action/Resource/Principal fields.
export function policyCanonical(value,key='') {
  if(['Action','Resource','AWS'].includes(key)&&typeof value==='string')value=[value];
  if(Array.isArray(value))return value.map(v=>policyCanonical(v)).sort((a,b)=>JSON.stringify(a).localeCompare(JSON.stringify(b)));
  if(value&&typeof value==='object')return Object.fromEntries(Object.keys(value).sort().map(k=>[k,policyCanonical(value[k],k)]));
  return value;
}
export const samePolicy=(a,b)=>JSON.stringify(policyCanonical(a))===JSON.stringify(policyCanonical(b));
