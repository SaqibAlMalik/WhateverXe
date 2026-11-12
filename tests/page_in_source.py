#!/usr/bin/env python3
"""Pin the cs_validate page-in patcher wiring (source contract, no donor):
one route pair for every table, installed once, and each table's own gate."""
from pathlib import Path
import re
root = Path(__file__).resolve().parents[1]
sources = {p: p.read_text(encoding='utf-8') for p in (root / 'WhateverXe').iterdir() if p.suffix in {'.cpp', '.hpp', '.inc'}}
s = sources[root / 'WhateverXe/kern_xe.cpp']

def body(name):
    # The definition (a declaration ends with ';' before its first '{').
    at = s.index(name)
    while s.find(';', at) < s.find('{', at):
        at = s.index(name, at + 1)
    return s[at:s.index('\n}\n', at)]

# Single route rule: one RouteRequest per validator in the whole tree, both in
# installPageInPatcher, which runs once (pageInRouted) from processKernel only.
for symbol in ('_cs_validate_range', '_cs_validate_page'):
    routes = [(p.name, m) for p, t in sources.items() for m in re.findall(r'RouteRequest \w+ \{"' + symbol + '"', t)]
    assert len(routes) == 1 and routes[0][0] == 'kern_xe.cpp', (symbol, routes)
install = body('static void installPageInPatcher(KernelPatcher &patcher) {')
assert install.count('RouteRequest') == 2 and install.count('routeMultipleLong(KernelPatcher::KernelID') == 2
assert re.search(r'\{\n if\(pageInRouted\)return;', install), 'second call must not route again'
assert install.index('pageInRouted=true;') < install.index('routeMultipleLong')
assert sum(t.count('installPageInPatcher(') for t in sources.values()) == 2  # definition + one call
assert 'installPageInPatcher(patcher);' in body('void XE::processKernel(KernelPatcher &patcher, DeviceInfo *info) {')
assert 'installMTLPoshFix' not in s and 'mtlPoshValidate' not in s
# Routes only when a table can act; tables are decided before routing.
gate = re.search(r'if\((.*?)\) \{\n  pageInRouted=true;', install).group(1)
assert gate == 'mtlPoshActive || vaNullGuardActive || vaVFEG12Active', gate
for flag in ('mtlPoshActive=', 'vaNullGuardActive=', 'vaVFEG12Active='):
    assert install.index(flag) < install.index('pageInRouted=true;')
assert 'mtlPoshActive=mtl && noPOSH;' in install
assert 'vaVFEG12Active=vaVFEG12Requested && noPOSH && checkKernelArgument("-wex-tgl-gpurec");' in install

# Dispatch: MTL keeps its tglNoPOSHEnabled scan gate; VA tables need a clean range.
dispatch = body('static void pageInScan(')
assert 'if(mtlPoshActive)mtlPoshScan(data,size);' in dispatch
assert 'if(clean && (vaNullGuardActive || vaVFEG12Active))vaFixScan(offset,data,size);' in dispatch
mtl = body('static void mtlPoshScan(')
assert 'tglNoPOSHEnabled' in mtl.split('forEachMatch')[0]
assert 'pageInScan(offset,data,size,!(tainted && *tainted));' in body('static boolean_t pageInValidateRange(')
assert 'pageInScan(offset,data,PageFix::PageSize,true);' in body('static void pageInValidatePage(')

# VA tables: each scans only under its own switch; VFEG12 through the latch.
scan = body('static void vaFixScan(')
assert 'if(vaNullGuardActive)PageFix::scan(VAFix::NullGuard,' in scan
assert 'if(vaVFEG12Active)PageFix::scan(VAFix::VFEG12,' in scan
# Byte search is the local PageFix::findByte: lilu_os_memchr exists only from
# Lilu 1.5.1 and tools/build.py declares an older Lilu (no new link dependency).
assert scan.count(',offset,PageFix::findByte,[](size_t i,uint8_t *at,bool pinned) {') == 2
assert not any('lilu_os_memchr' in line.split('//')[0] for t in sources.values() for line in t.splitlines())
null_part, vfe_part = scan.split(' // -wex-va-vfeg12:')
assert 'PageFix::single(pinned)' in null_part and 'vaVFEG12' not in null_part
assert 'PageFix::member(&vaVFEG12Latch,vaVFEG12Gate(),pinned)' in vfe_part
# NullGuard writes through vaFixWrite, VFEG12 members through vaVFEG12Write.
assert null_part.count('vaFixWrite(') == 1 and 'vaFixWrite(' not in vfe_part
assert vfe_part.count('vaVFEG12Write(VAFix::VFEG12[i],at)') == 1
for result, slot in (('Done', 'vaFixPatched(vaVFEG12Counts,i,VAFix::VFEG12[i])'), ('Skipped', 'GateSkips'), ('Failed', 'WriteFailures')):
    case = vfe_part[vfe_part.index('case PageFix::Write::' + result + ':'):]
    assert slot in case.split('\n')[0], (result, slot)
write = body('static bool vaFixWrite(')
assert write.index('setKernelWriting(true') < write.index('PageFix::apply(') < write.index('setKernelWriting(false')
# VFEG12 latch: an unpinned hit never poisons (PageFix::member); the only
# poison is a write window that cannot be opened, inside vaVFEG12Write, and
# PageFix::poison itself only acts while no member window was written.
vwrite = body('static PageFix::Write vaVFEG12Write(')
fail = vwrite[vwrite.index('if(MachInfo::setKernelWriting(true,KernelPatcher::kernelWriteLock)!=KERN_SUCCESS) {'):]
assert fail.index('PageFix::poison(&vaVFEG12Latch);') < fail.index('return PageFix::Write::Failed;') < fail.index('PageFix::applyMember(&vaVFEG12Latch,a,at)')
assert vwrite.index('PageFix::applyMember(&vaVFEG12Latch,a,at)') < vwrite.index('setKernelWriting(false')
assert s.count('PageFix::poison(') == 1 and 'PageFix::poison(&vaVFEG12Latch);' in vwrite
# VFEG12 gate: install state (not the command line) and a complete route set.
vgate = body('static bool vaVFEG12Gate() {')
assert 'checkKernelArgument' not in vgate
for need in ('tglGpuRecRegistersEnabled', 'tglNoPOSHEnabled', 'PageFix::routesComplete(__atomic_load_n(&pageInRoutes'):
    assert need in vgate, need
gpurec = body('bool tglInstallGpuRec(')
assert gpurec.index('g.registers=patcher.routeMultiple(') < gpurec.index('__atomic_store_n(&tglGpuRecRegistersEnabled,g.registers,__ATOMIC_RELEASE);')
assert s.count('__atomic_store_n(&tglGpuRecRegistersEnabled,') == 1  # the only writer
assert not re.search(r'tglGpuRecRegistersEnabled\s*=', s.replace('bool tglGpuRecRegistersEnabled {};', ''))

# accel+0x1191 bit 0 (initModeRegisters' FORCE_TO_NONPRIV gate, 0x28EBA): sampled
# once after a successful IntelAccelerator::start, only with -wex-va-vfeg12;
# published in the WEXVAFix ready mask, never part of the VFEG12 gate.
start = body('bool XE::wrapTGLAcceleratorStart(IOService *that, IOService *provider) {')
assert 'if (result && vaVFEG12Requested) vaSampleL3Whitelist(that);' in start
assert start.index('FunctionCast(wrapTGLAcceleratorStart, callbackXE->orgTGLAcceleratorStart)(that, provider);') < start.index('vaSampleL3Whitelist(that);')
assert s.count('vaSampleL3Whitelist(') == 2  # definition + the one call
assert 'vaL3Whitelist' not in vgate
assert '__atomic_load_n(&vaL3Whitelist,__ATOMIC_ACQUIRE)' in body('static bool vaFixSerialize(')
assert '[0x1191]' in body('static void vaSampleL3Whitelist(')

# Publication: WEXVAFix and WEXVAFixReady only when a VA switch is given.
pub = install[install.index('WEXVAFixReady') - 200:]
assert re.search(r'if\(vaNullGuardActive \|\| vaVFEG12Requested\) \{\n  root->setProperty\("WEXVAFixReady"', install)
assert s.count('"WEXVAFix"') == 1 and s.count('"WEXVAFixReady"') == 1 and 'vaFixSerialize' in pub
print('page_in_source: ok')
