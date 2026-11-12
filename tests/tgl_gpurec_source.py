#!/usr/bin/env python3
"""Pin the -wex-tgl-gpurec / -wex-mtl-poshfix wiring in kern_xe.cpp (source contract, no donor)."""
from pathlib import Path
import re
s = (Path(__file__).resolve().parents[1] / 'WhateverXe/kern_xe.cpp').read_text()

# Ordering fix: every reset-list write goes through tglGpuRecRestoreList, which
# re-applies the RCS whitelist after the list (TGLGpuRec::restoreList).
assert s.count('tglGpuRecRestoreList(owner,bar,') == 2, 'sibling and own restores must both use tglGpuRecRestoreList'
assert 'TGLGpuRec::writeList(' not in s, 'direct list writes would skip the whitelist re-fix'
body = s[s.index('uint32_t tglGpuRecRestoreList('):]
body = body[:body.index('\n}\n')]
assert 'TGLGpuRec::restoreList(' in body

# Sibling halt: only a running sibling, flagged so the pre-STOP bridge ignores it.
assert 'haltWanted(g.halt,kick,siblingInUse) && snapshot[0] && schedulerOK' in s
assert re.search(r'__atomic_store_n\(&g\.halting,true,__ATOMIC_RELEASE\);\s*reinterpret_cast<void \(\*\)\(void \*,uint32_t\)>\(g\.haltStreamer\)', s)
wake = s[s.index('extern "C" void tglHangPreStopWake(void *owner'):]
wake = wake[:wake.index('\n}\n')]
assert wake.index('tglGpuRec.halting') < wake.index('tglHangPreStopState'), 'halting check must precede the one-shot capture'
assert 'wakeKnown' in s and 'wakeTarget==reinterpret_cast<uintptr_t>(tglHangPreStopBridge)' in s
# Resume: masked clear only, never the native polling resume.
assert '(g.resumeStreamer)(' not in s

# poshfix: patch pages only while kernel no-POSH is actually installed.
scan = s[s.index('static void mtlPoshScan('):]
scan = scan[:scan.index('\n}\n')]
assert 'tglNoPOSHEnabled' in scan.split('forEachMatch')[0]
print('tgl_gpurec_source: ok')
