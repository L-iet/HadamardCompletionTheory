# SPDX-License-Identifier: Apache-2.0
"""Audit compiler-generated transitive axiom profiles with bounded memory.

Lean4.35's #print axioms uses exportedAxiomsExt for imported declarations.
Read that same stock cache from each defining olean without initializing its
proof/tactic imports. Independent Comparator kernels still check actual terms.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,os,re,subprocess
from comparison_groups import load_groups, declaration_names
from native_runtime import native_lean_args
from run_local_comparator import check_source_inventory,digest
ROOT=Path(__file__).resolve().parents[1]
ALLOWED={'propext','Quot.sound','Classical.choice'}
CACHE_DRIVER=r"""/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Diagnostic only. Uses Lean4.35's stock compiler-generated transitive axiom cache.
The erased entry cast follows the pinned PersistentEnvExtension ABI; no theorem
or axiom is declared here. Actual proof terms require independent kernel checks.
-/
module
import Lean
import all Lean.Util.CollectAxioms
open Lean
public unsafe def main (args : List String) : IO UInt32 := do
  let [requestFile] := args | throw (IO.userError "Expected one JSON request file")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (System.FilePath.mk requestFile)))
  let requests ← IO.ofExcept json.getArr?
  for request in requests do
    let file ← IO.ofExcept (request.getObjValAs? String "file")
    let owner ← IO.ofExcept (request.getObjValAs? String "module")
    let targets ← IO.ofExcept (request.getObjValAs? (Array String) "targets")
    let (data, _region) ← readModuleData (System.FilePath.mk file)
    let extension := exportedAxiomsExt.name
    let some (_, raw) := data.entries.find? (fun entry => entry.1 == extension) |
      throw (IO.userError "Missing stock transitive axiom extension")
    let entries : Array (Name × Array Name) := unsafeCast raw
    for text in targets do
      let name := text.toName
      unless data.constNames.contains name do
        throw (IO.userError s!"Target not defined in this olean: {name}")
      let some (_, axs) := entries.find? (fun entry => entry.1 == name) |
        throw (IO.userError s!"Missing stock axiom profile: {name}")
      IO.println ((Json.mkObj [("declaration",toJson text),("module",toJson owner),
        ("axioms",toJson (axs.map Name.toString)),("extension",toJson extension.toString)]).compress)
  return 0
"""

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def write(path,text):path.write_text(text,encoding='utf-8',newline='\n')
def standard(profiles):
    extra={x for values in profiles.values() for x in values}-ALLOWED
    if extra:raise ValueError('Nonstandard proof axioms: '+', '.join(sorted(extra)))

def run(command,work,label,expect_failure=False):
    env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
    result=subprocess.run(command,cwd=ROOT,env=env,capture_output=True,text=True,encoding='utf-8')
    write(work/(label+'.log'),result.stdout+result.stderr)
    if result.returncode and not expect_failure:
        raise SystemExit('Axiom audit failed: '+str(work/(label+'.log'))+'\n'+result.stdout+result.stderr)
    return result

def owner_lookup(module,names,work,label,native_args,control=False):
    array='#['+', '.join(json.dumps(n,ensure_ascii=False) for n in names)+']'
    imports=list(dict.fromkeys([module,'Lean']))
    text='module\n'+'\n'.join('import '+m for m in imports)+'\nopen Lean Elab Command\n'
    text+='run_cmd do\n  let env ← getEnv\n  for text in '+array+' do\n'
    text+='    let name := text.toName\n    unless env.contains name do throwError "Missing declaration {name}"\n'
    text+='    let some idx := env.getModuleIdxFor? name | throwError "Missing defining module {name}"\n'
    text+='    let owner := env.header.moduleNames[idx]!\n    let file ← liftIO (findOLean owner)\n'
    text+='    liftIO <| IO.println ("AXIOM_OWNER " ++ (Json.mkObj [("declaration",toJson text),("module",toJson owner.toString),("file",toJson file.toString)]).compress)\n'
    if control:text+='\n'+'\n'.join('#print axioms '+n for n in names)+'\n'
    source=work/(label+'.lean');write(source,text)
    # This is only name/module lookup, using the existing export-preflight cap.
    # No mathematical proof or axiom-closure check runs at this diagnostic cap.
    cap='-M1024' if control else '-M4096'
    result=run(['lake','env','lean',cap,*native_args,str(source)],work,label)
    records=[json.loads(line[len('AXIOM_OWNER '):]) for line in result.stdout.splitlines() if line.startswith('AXIOM_OWNER ')]
    if len(records)!=len(names) or {x['declaration'] for x in records}!=set(names):raise SystemExit('Incomplete owner lookup: '+label)
    for entry in records:
        file=Path(entry['file'])
        if not file.is_absolute():file=ROOT/file
        entry['file']=str(file.resolve())
        if not control:
            source=ROOT.joinpath(*entry['module'].split('.')).with_suffix('.lean')
            expected=ROOT/'.lake/build/lib/lean'/Path(*entry['module'].split('.')).with_suffix('.olean')
            if not source.is_file() or expected.resolve()!=Path(entry['file']):raise SystemExit('Unexpected nonowned defining module: '+entry['module'])
    return records,result.stdout

def cache_read(records,work,label,expect_failure=False):
    jobs={}
    for entry in records:
        key=(entry['module'],entry['file'])
        jobs.setdefault(key,[]).append(entry['declaration'])
    requests=[{'module':m,'file':f,'targets':list(dict.fromkeys(names))} for (m,f),names in jobs.items()]
    request=work/(label+'.json');write(request,json.dumps(requests,indent=2)+'\n')
    result=run(['lake','env','lean','-M1024','--root='+str(work),'--run',str(work/'AxiomCacheDriver.lean'),str(request)],work,label,expect_failure)
    if result.returncode:return {},result
    found={}
    owners={x['declaration']:(x['module'],x['file']) for x in records}
    for line in result.stdout.splitlines():
        if not line.strip():continue
        entry=json.loads(line);name=entry['declaration']
        if name in found or name not in owners or owners[name][0]!=entry['module']:raise SystemExit('Unexpected/repeated axiom profile')
        if not entry['extension'].endswith('.Lean.exportedAxiomsExt'):raise SystemExit('Unexpected stock cache extension')
        found[name]=entry['axioms']
    if set(found)!=set(owners):raise SystemExit('Incomplete stock cache coverage')
    return found,result

def self_test(work):
    names=['Nat.add_comm','Classical.choice','sorryAx']
    records,text=owner_lookup('Lean',names,work,'stock-controls',[],control=True)
    stock={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text)}
    for n in re.findall(r"'([^']+)' does not depend on any axioms",text):stock[n]=[]
    actual,_=cache_read(records,work,'cache-controls')
    if actual!=stock or set(actual)!=set(names) or actual['Nat.add_comm']!=[]:raise SystemExit('Stock axiom/cache cross-check failed')
    try:standard({'sorryAx':actual['sorryAx']})
    except ValueError as e:
        if 'sorryAx' not in str(e):raise
    else:raise SystemExit('Nonstandard builtin control was accepted')
    bad=[{**records[0],'declaration':'DefinitelyMissingAxiomAuditControl'}]
    _,result=cache_read(bad,work,'missing-control',True)
    if result.returncode==0 or 'Target not defined in this olean' not in result.stdout+result.stderr:raise SystemExit('Missing-target control failed')
    return {'status':'passed','stockPrintAxiomsMatched':True,'axiomFreeControlMatched':True,'nonstandardBuiltinRejected':True,'missingTargetRejected':True,'controlProfiles':actual}

def main():
    script_before=sha(Path(__file__))
    if (ROOT/'lean-toolchain').read_text(encoding='utf-8').strip()!='leanprover/lean4:v4.35.0':raise SystemExit('Axiom cache ABI is pinned to Lean4.35.0')
    groups=load_groups(ROOT);names=declaration_names(groups)
    if not names:raise SystemExit('No targets')
    work=ROOT/'.lake/axiom-audit';work.mkdir(exist_ok=True)
    write(work/'AxiomCacheDriver.lean',CACHE_DRIVER)
    controls=self_test(work);native_args=native_lean_args();records={}
    for group in groups:
        found,_=owner_lookup(group['config']['solution_module'],declaration_names([group]),work,'owners-'+group['id'],native_args)
        for entry in found:
            name=entry['declaration']
            if name in records and records[name]!=entry:raise SystemExit('Different defining modules for shared target: '+name)
            records[name]=entry
        print('Resolved actual defining modules:',group['id'],len(found),'targets',flush=True)
    bindings={}
    for entry in records.values():
        owner=entry['module'];source=ROOT.joinpath(*owner.split('.')).with_suffix('.lean');file=Path(entry['file'])
        if owner not in bindings:bindings[owner]={'sourceFile':source.relative_to(ROOT).as_posix(),'sourceSHA256':digest(source),'oleanFile':file.relative_to(ROOT).as_posix(),'oleanSHA256':sha(file)}
    profiles,_=cache_read(list(records.values()),work,'all-profiles');standard(profiles)
    for owner,entry in bindings.items():
        if digest(ROOT/entry['sourceFile'])!=entry['sourceSHA256'] or sha(ROOT/entry['oleanFile'])!=entry['oleanSHA256']:raise SystemExit('Source/olean changed during axiom audit: '+owner)
    if set(profiles)!=set(names):raise SystemExit('Incomplete axiom audit coverage')
    # Cross-check the newly integrated group with the stock command at the same cap.
    cyclic=next(g for g in groups if g['id']=='cyclic-existence');cn=declaration_names([cyclic])
    source=work/'StockCyclic.lean';write(source,'module\nimport '+cyclic['config']['solution_module']+'\n'+'\n'.join('#print axioms '+n for n in cn)+'\n')
    check=run(['lake','env','lean','-M1024',*native_args,str(source)],work,'stock-cyclic')
    stock={n:[x.strip() for x in a.split(',') if x.strip()] for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",check.stdout)}
    for n in re.findall(r"'([^']+)' does not depend on any axioms",check.stdout):stock[n]=[]
    if stock!={n:profiles[n] for n in cn}:raise SystemExit('New cyclic profiles differ from stock #print axioms')
    if sha(Path(__file__))!=script_before:raise SystemExit('Axiom audit script changed during execution')
    data={'checkedAtUTC':datetime.now(timezone.utc).isoformat(),'status':'passed','declarations':profiles,
      'comparisonGroups':[{'id':g['id'],'config':g['path']} for g in groups],
      'method':'Pinned Lean4.35 compiler-generated transitive exportedAxiomsExt cache; same data used by stock #print axioms. No target/tactic initializer execution in the profile reader. Actual proof terms checked independently by Comparator.',
      'profileReaderLimit':'-M1024','nameOnlyDiagnosticLimit':'-M4096 (existing export-preflight cap)',
      'auditScriptSHA256':script_before,'cacheDriverSHA256':sha(work/'AxiomCacheDriver.lean'),
      'selfTests':controls,'stockCyclicCrossCheck':{'status':'passed','declarations':len(cn),'memoryLimit':'-M1024'},'compiledModuleBindings':bindings,
      'scope':'Every configured comparison declaration; full build and paper coverage are separate source-bound gates.'}
    snapshot=ROOT/'submission/proof-hashes.json'
    if snapshot.exists():
        hashes=json.loads(snapshot.read_text(encoding='utf-8'))
        try:
            check_source_inventory(hashes)
            current=all((ROOT/n).is_file() and digest(ROOT/n)==value for n,value in hashes.items())
        except SystemExit:current=False
        if current:data['proofHashes']=hashes
    write(ROOT/'submission/axioms.json',json.dumps(data,indent=2)+'\n')
    write(ROOT/'.lake/axioms.log',(work/'all-profiles.log').read_text(encoding='utf-8'))
    print('Audited',len(profiles),'declarations across',len(groups),'groups; stock controls and all20cyclic profiles matched at-M1024.',flush=True)
if __name__=='__main__':main()
