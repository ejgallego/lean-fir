import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {DIRECT_CONSTRUCTION_API,createDirectConstructionSession} from './direct-construction-session.mjs';
import * as p from './providers.mjs';
import React from 'react';
import {renderToStaticMarkup} from 'react-dom/server';
const NativeTextEncoder=globalThis.TextEncoder;
const encodeEvents=[];
let encodeFailureValue;
globalThis.TextEncoder=class InstrumentedTextEncoder{
  constructor(){this.inner=new NativeTextEncoder();}
  encode(value){return this.inner.encode(value);}
  encodeInto(value,destination){
    encodeEvents.push({value,destination});
    if(value===encodeFailureValue)throw new Error('controlled UTF-8 conversion failure');
    return this.inner.encodeInto(value,destination);
  }
};
const read=file=>readFileSync(new URL(file,import.meta.url));
const baseline='./';
const module=await WebAssembly.compile(read('component.wasm'));
let mathFactoryCalls=0,mathRenderCalls=0;
const MathSentinel=props=>{mathRenderCalls++;return React.createElement('span',{'data-fir-math':'consumed'},props.value??'math');};
const bindings={...p.createJsCollectionHostBindings(),...p.createJsValueHostBindings(),
  ...p.createBrowserEventHostBindings(),...p.createBrowserReactHostBindings(),...p.createJsonValueHostBindings(),
  'previewDemo.now':()=>100.125,
  'previewDemo.mathComponent':()=>{mathFactoryCalls++;return MathSentinel;}};
let stringControl;
const stringProvider=bindings['js.string.value'];
bindings['js.string.value']=value=>{if(stringControl)stringControl();return stringProvider(value);};
const options={apiVersion:DIRECT_CONSTRUCTION_API,module,bindings,manifest:JSON.parse(read('component.wasm.json')),
  hostBoundary:JSON.parse(read('host-boundary.json')),
  callbackBoundary:JSON.parse(read(baseline+'callback-boundary.json')),
  entryBoundary:JSON.parse(read(baseline+'entry-boundary.json')),
  constructorLayouts:JSON.parse(read('constructor-layouts.json'))};
const originalInstantiate=WebAssembly.instantiate;
const instances=[];
let allocationControl;
WebAssembly.instantiate=async(...args)=>{
  const value=await originalInstantiate(...args);instances.push(value);
  const exports=Object.create(null);
  for(const name of Object.keys(value.exports))exports[name]=value.exports[name];
  const allocate=exports.fir_heap_alloc;
  exports.fir_heap_alloc=(...callArgs)=>{allocationControl?.();return allocate(...callArgs);};
  return {exports};
};
let host,other;
try{host=await createDirectConstructionSession(options);other=await createDirectConstructionSession(options);}
finally{WebAssembly.instantiate=originalInstantiate;}
const previews=JSON.parse(read(baseline+'previews.json'));
const rich=structuredClone(previews[0]);
rich.ready.document.focus=null;
const part=rich.ready.document.document;
part.titleString='λ😀\0 title';
part.metadata={authors:['λ😀\0'],htmlSplit:'default',searchPriority:99,
  number:true,draft:false,htmlToc:true,assignedNumber:'😀',
  shortTitle:'short λ\0',date:'2026',tag:{provided:{name:'unicode'}}};
part.content.push(
  {para:[{math:{mode:'display',str:'α\0'}},{emph:[{text:'λ😀\0'}]},
    {link:{content:[{text:'link'}],url:'https://example.invalid/λ'}},
    {image:{alt:'λ😀',url:'data:image/svg+xml,λ'}}]},
  {ol:{start:-9007199254740991,items:[{contents:[{code:'λ😀\0'}]}]}},
  {dl:[{term:[{text:'term'}],contents:[{blockquote:[{para:[{text:'body'}]}]}]}]});
part.content[1].other.container.properties={title:'λ😀\0',dataKind:'fixture','«λ😀»':'Unicode property'};
part.content[1].other.container.data.extra={'λ😀\0':-9007199254740991};
previews.push(rich);
let equivalent=0,renders=0;
assert.equal(mathFactoryCalls,2,'each session must consume exactly one supplied math component');
let sawMath=false;
for(const preview of previews){
  const direct=host.directParsed(preview),checked=host.browserParsed(preview);
  assert.equal(host.equivalent(direct,checked),true);equivalent++;
  const directHtml=renderToStaticMarkup(host.renderTimedDecoded(direct,{requested:10.125,received:20.25,notified:25.5,decodedAt:30.875}));
  const checkedHtml=renderToStaticMarkup(host.renderTimedDecoded(checked,{requested:10.125,received:20.25,notified:25.5,decodedAt:30.875}));
  assert.equal(directHtml,checkedHtml);sawMath ||= directHtml.includes('data-fir-math="consumed"');renders+=2;
}
assert.equal(sawMath,true,'supplied math component must render document math');
assert.ok(mathRenderCalls>=2,'math component must run for direct and checked values');
const first=host.directParsed(previews[0]);
assert.throws(()=>host.equivalent(first,other.directParsed(previews[0])),/foreign/);
for(const pages of [0,1]){
  instances[0].exports.memory.grow(pages);
  assert.equal(host.equivalent(host.directParsed(previews[0]),host.browserParsed(previews[0])),true);equivalent++;
}
for(const bad of [undefined,{}, {ready:{document:{}}}, {loading:{message:17}}]){
  assert.throws(()=>host.directParsed(bad));assert.equal(host.stats().disposed,false);
  assert.equal(host.equivalent(host.directParsed(previews[0]),first),true);equivalent++;
}
const callback=host.diagnostics.retainedFunction('sink λ😀\0');
const value={};assert.equal(callback(value),value);assert.equal(value.answer,'sink λ😀\0');
// Keep the outer slot leased across allocator reentry. The nested conversion
// must use another JavaScript-owned slot, while the next depth-zero call reuses
// the original slot.
const outerString='outer scratch λ😀',innerString='inner scratch λ😀',afterString='after scratch λ😀';
allocationControl=()=>{
  allocationControl=undefined;
  const nested=host.diagnostics.retainedFunction(innerString);
  assert.equal(nested(value),value);
};
const outer=host.diagnostics.retainedFunction(outerString);
assert.equal(outer(value),value);
const after=host.diagnostics.retainedFunction(afterString);
assert.equal(after(value),value);
const destinationFor=text=>encodeEvents.find(event=>event.value===text)?.destination;
assert.ok(destinationFor(outerString) instanceof Uint8Array);
assert.ok(destinationFor(innerString) instanceof Uint8Array);
assert.notEqual(destinationFor(outerString),destinationFor(innerString));
assert.equal(destinationFor(outerString),destinationFor(afterString));
// The destination view must be acquired after allocation because this hook
// grows module memory from inside the allocation boundary.
allocationControl=()=>{allocationControl=undefined;instances[0].exports.memory.grow(1);};
const grown=host.diagnostics.retainedFunction('growth scratch λ😀');
assert.equal(grown(value),value);
for(const failure of [undefined,null,{error:'sink provider identity'}]){
  stringControl=()=>{throw failure;};
  let thrown=false;
  try{host.directParsed(previews[0]);}catch(error){thrown=true;assert.equal(error,failure);}
  finally{stringControl=undefined;}
  assert.equal(thrown,true);assert.equal(host.stats().disposed,false);
  assert.equal(callback(value),value);
  assert.equal(host.equivalent(host.directParsed(previews[0]),first),true);equivalent++;
}
for(const pages of [0,1]){
  stringControl=()=>{
    stringControl=undefined;
    instances[0].exports.memory.grow(pages);
    assert.equal(callback(value),value);
  };
  assert.equal(host.equivalent(host.directParsed(previews[0]),first),true);equivalent++;
}
// Preserve the baseline's fail-closed conversion semantics. `finally` must
// release the leased slot even though the guarded boundary poisons this second
// session, and disposal must invalidate its retained resources.
encodeFailureValue='controlled scratch failure';
assert.throws(()=>other.diagnostics.retainedFunction(encodeFailureValue),/controlled UTF-8 conversion failure/);
encodeFailureValue=undefined;
assert.equal(other.stats().disposed,true);
assert.throws(()=>other.directParsed(previews[0]),/disposed|invalidated/);
assert.equal(host.equivalent(host.directParsed(previews[0]),first),true);equivalent++;
assert.equal(callback(value),value);
host.dispose();assert.equal(other.dispose(),false);
assert.throws(()=>callback({}),/disposed|invalidated/);
assert.throws(()=>host.equivalent(first,first),/disposed/);
globalThis.TextEncoder=NativeTextEncoder;
console.log(JSON.stringify({pass:true,equivalent,renders,mathFactoryCalls,mathRenderCalls,imports:WebAssembly.Module.imports(module).length,
  exports:WebAssembly.Module.exports(module).length,encodeIntoCalls:encodeEvents.length,
  scratch:{nestedDistinct:true,depthZeroReuse:true,growth:true,failure:true,disposal:true},
  scope:'Private Node constructor traversal; consumer browser/performance acceptance separate'}));
