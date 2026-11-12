#include "kern_va_fix.hpp"
#include <cassert>
#include <cstdio>
#include <cstring>
#include <vector>
// PageFix engine and the VAFix tables on a synthetic file image: the anchors
// are placed at their file offsets in filler bytes and the image is "paged
// in" (validated range by range) in many orders, mirroring the kern_xe.cpp
// table callbacks (vaFixScan).

// The kext's own byte search (PageFix::findByte), counting the passes that
// start at the range base.
static const uint8_t *passBase;
static unsigned passStarts;
static void *chr(const void *p,int c,size_t n) {
    if(p==passBase)++passStarts;
    return PageFix::findByte(p,c,n);
}

struct Counts {uint32_t s[VAFix::TableSlots] {};};
struct Run {
    bool nullGuard=true,vfe=true,gate=true;
    bool race=false; // a racing validation edits each window between scan and write
    unsigned raced=0;
    // VFEG12 member write attempts (after member() said Patch), 1-based: the
    // attempt numbered failOpen cannot open the kernel write window (nothing
    // written, as vaVFEG12Write); the one numbered corrupt finds its window
    // changed to neither `from` nor `to` after the scan matched it.
    unsigned writes=0,failOpen=0,corrupt=0;
    uint32_t latch=PageFix::Undecided;
    Counts ng,vf;
};

static void pageIn(std::vector<uint8_t> &file,uint64_t offset,uint64_t size,Run &r) {
    uint8_t *data=file.data()+offset;
    passBase=data;
    if(r.nullGuard)PageFix::scan(VAFix::NullGuard,VAFix::NullGuardAnchors,data,size,offset,chr,[&](size_t i,uint8_t *at,bool pinned) {
        if(PageFix::single(pinned)!=PageFix::Action::Patch) {r.ng.s[VAFix::OffsetMismatch]++;return;}
        if(r.race)r.raced+=PageFix::apply(VAFix::NullGuard[i],at);
        if(!PageFix::apply(VAFix::NullGuard[i],at)) {r.ng.s[VAFix::WriteFailures]++;return;}
        r.ng.s[VAFix::Patched0+i]++;r.ng.s[VAFix::Sites]+=VAFix::NullGuard[i].sites;
    });
    if(r.vfe)PageFix::scan(VAFix::VFEG12,VAFix::VFEG12Anchors,data,size,offset,chr,[&](size_t i,uint8_t *at,bool pinned) {
        switch(PageFix::member(&r.latch,r.gate,pinned)) {
            case PageFix::Action::SkipOffset:r.vf.s[VAFix::OffsetMismatch]++;return;
            case PageFix::Action::SkipGate:r.vf.s[VAFix::GateSkips]++;return;
            case PageFix::Action::Patch:break;
        }
        const auto &a=VAFix::VFEG12[i];
        ++r.writes;
        if(r.race)r.raced+=PageFix::applyMember(&r.latch,a,at)==PageFix::Write::Done;
        if(r.writes==r.corrupt)at[a.length-1]^=0x5A;
        // vaVFEG12Write: a window that cannot be opened poisons (Armed only).
        if(r.writes==r.failOpen) {PageFix::poison(&r.latch);r.vf.s[VAFix::WriteFailures]++;return;}
        switch(PageFix::applyMember(&r.latch,a,at)) {
            case PageFix::Write::Done:r.vf.s[VAFix::Patched0+i]++;r.vf.s[VAFix::Sites]+=a.sites;return;
            case PageFix::Write::Skipped:r.vf.s[VAFix::GateSkips]++;return;
            case PageFix::Write::Failed:r.vf.s[VAFix::WriteFailures]++;return;
        }
    });
}

static const size_t FileSize=0x320000;
static const PageFix::Anchor *const tables[2] {VAFix::NullGuard,VAFix::VFEG12};
static const size_t tableAnchors[2] {VAFix::NullGuardAnchors,VAFix::VFEG12Anchors};
static std::vector<uint8_t> image(bool patched) {
    std::vector<uint8_t> f(FileSize,0xCC);
    for(size_t t=0;t<2;++t) for(size_t i=0;i<tableAnchors[t];++i) {
        const auto &a=tables[t][i];
        memcpy(&f[a.fileOffset],patched?a.to:a.from,a.length);
    }
    return f;
}
static uint32_t lcg(uint32_t &s) {s=s*1664525u+1013904223u;return s>>8;}
// WEXVAFix ready mask: route bits 0..3 and the VA bits never overlap.
static_assert(((PageFix::RangeRouted|PageFix::PageRouted|PageFix::RangePresent|PageFix::PagePresent)&
               (VAFix::NullGuardActive|VAFix::VFEG12Requested|VAFix::VFEG12Active|VAFix::VFEG12Gate|
                VAFix::L3WhitelistSampled|VAFix::L3Whitelisted))==0 &&
              ((VAFix::NullGuardActive|VAFix::VFEG12Requested|VAFix::VFEG12Active|VAFix::VFEG12Gate)&
               (VAFix::L3WhitelistSampled|VAFix::L3Whitelisted))==0 && VAFix::Words==17,"WEXVAFix layout");

static unsigned hexByte(const char *s) {
    auto nibble=[](char c) {return static_cast<unsigned>(c<='9'?c-'0':(c|0x20)-'a'+10);};
    return nibble(s[0])<<4|nibble(s[1]);
}
// Bytes of `to` differ from `from` only inside [start, start+length) spans;
// a span with hex strings must hold exactly those bytes before and after.
struct Span {uint64_t start;uint16_t length;const char *from,*to;};
static void checkSpans(const PageFix::Anchor &a,const Span *spans,size_t n) {
    for(size_t k=0;k<a.length;++k) {
        const uint64_t at=a.fileOffset+k;
        bool inside=false;
        for(size_t s=0;s<n;++s)inside=inside || (at>=spans[s].start && at<spans[s].start+spans[s].length);
        if(!inside)assert(a.from[k]==a.to[k]);
    }
    for(size_t s=0;s<n;++s) {
        assert(spans[s].start>=a.fileOffset && spans[s].start+spans[s].length<=a.fileOffset+a.length);
        if(!spans[s].from)continue;
        assert(strlen(spans[s].from)==2u*spans[s].length && strlen(spans[s].to)==2u*spans[s].length);
        for(size_t k=0;k<spans[s].length;++k) {
            assert(a.from[spans[s].start-a.fileOffset+k]==hexByte(spans[s].from+2*k));
            assert(a.to[spans[s].start-a.fileOffset+k]==hexByte(spans[s].to+2*k));
        }
    }
}

int main() {
    // findByte has memchr semantics (first match, NULL when absent or n == 0,
    // the key compared as an unsigned byte).
    {
        const uint8_t b[] {0x10,0xE8,0x20,0xE8,0xFF};
        const int keys[] {0x10,0xE8,0x20,0xFF,0x00,0x30,-0x18};
        for(int c:keys)
            for(size_t n=0;n<=sizeof(b);++n)assert(PageFix::findByte(b,c,n)==memchr(b,c,n));
        assert(PageFix::findByte(b,0xE8,sizeof(b))==b+1 && PageFix::findByte(b+2,0xE8,3)==b+3);
    }
    // Table invariants: >= 32 bytes, one page, distinct replacement, site totals.
    unsigned sites[2] {};
    for(size_t t=0;t<2;++t) for(size_t i=0;i<tableAnchors[t];++i) {
        const auto &a=tables[t][i];
        assert(a.length>=32 && a.fileOffset+a.length<=FileSize);
        assert(a.fileOffset/PageFix::PageSize==(a.fileOffset+a.length-1)/PageFix::PageSize);
        assert(memcmp(a.from,a.to,a.length));
        sites[t]+=a.sites;
    }
    assert(sites[0]==VAFix::NullGuardSites && sites[1]==VAFix::VFEG12Sites && sites[0]==3 && sites[1]==8);
    // NullGuard: every anchor starts with a call rel32 (one search pass).
    for(const auto &a:VAFix::NullGuard)assert(a.from[0]==0xE8);
    // NullGuard rewrites: the reported store, guarded spans, calls in place.
    {
        const Span n1[] {{0x1336E1,22,nullptr,nullptr}},n2[] {{0x130E84,28,nullptr,nullptr}},n3[] {{0x12D30A,18,nullptr,nullptr}};
        checkSpans(VAFix::NullGuard[0],n1,1);checkSpans(VAFix::NullGuard[1],n2,1);checkSpans(VAFix::NullGuard[2],n3,1);
        // The reported store at 0x1336f3 keeps its address, now storing rcx (= this+0x2cb0).
        assert(!memcmp(&VAFix::N1From[0x1336F3 - 0x1336BF],"\x48\x89\x57\x08",4) &&
               !memcmp(&VAFix::N1To[0x1336F3 - 0x1336BF],"\x48\x89\x4F\x08",4));
        assert(!memcmp(&VAFix::N1To[0x1336EE - 0x1336BF],"\x48\x85\xFF\x74\x04",5)); // test rdi,rdi; je +4
        assert(!memcmp(&VAFix::N2To[0x130E92 - 0x130E7B],"\x48\x85\xFF\x74\x0E",5)); // test rdi,rdi; je 0x130ea5
        assert(!memcmp(&VAFix::N3To[0x12D312 - 0x12D301],"\x48\x85\xFF\x74\x0C",5)); // test rdi,rdi; je 0x12d323
        assert(!memcmp(&VAFix::N2To[0x130EA0 - 0x130E7B],"\xE8\x7B\x56\xFF\xFF",5) &&
               !memcmp(&VAFix::N2From[0x130EA0 - 0x130E7B],"\xE8\x7B\x56\xFF\xFF",5));
        assert(!memcmp(&VAFix::N3To[0x12D31C - 0x12D301],"\xFF\x51\x48",3) &&
               !memcmp(&VAFix::N3From[0x12D31C - 0x12D301],"\xFF\x51\x48",3));
        // N3's NULL path (cmp [rbp-0x30],0 / jne / status 5) is part of the anchor, unchanged.
        assert(!memcmp(&VAFix::N3To[0x12D32B - 0x12D301],"\x48\x83\x7D\xD0\x00\x0F\x85\x0C\x00\x00\x00\xC7\x45\xE4\x05",15));
    }
    // VFEG12: exactly eight sites on two pages; the MEDIA_VFE_STATE template
    // page 0x31d000 (also read by the 0x17a7f builder family) is not touched.
    {
        const Span v1[] {{0x1C2A,10,"48b80000000040000080","48b834b10000200000d0"}};
        const Span v2[] {{0x2C9AE,6,"81ca00100000","81ca40100000"},  // path A DW3: or edx,0x1000 -> 0x1040
                         {0x2CA03,3,"8b5020","31d290"},              // path B DW8: mov edx,[rax+0x20] -> xor edx,edx; nop
                         {0x2CA08,4,"488b5018","31d26690"},          // path B DW6:DW7: mov rdx,[rax+0x18] -> xor edx,edx; xchg ax,ax
                         {0x2CA22,6,"81c900100000","81c940100000"},  // path B DW3: or ecx,0x1000 -> 0x1040
                         {0x2CA47,4,"804ffb80","0f1f4000"},          // path B DW6 bit 31
                         {0x2CA4D,4,"4c8957f8","0f1f4000"},          // path A scoreboard type 2
                         {0x2CA53,4,"4c895ff8","0f1f4000"}};         // path A scoreboard type 1
        checkSpans(VAFix::VFEG12[0],v1,1);checkSpans(VAFix::VFEG12[1],v2,7);
        assert(VAFix::VFEG12Anchors==2 && VAFix::VFEG12[0].fileOffset/PageFix::PageSize==1 &&
               VAFix::VFEG12[1].fileOffset/PageFix::PageSize==0x2C);
        // The V2 anchor holds the builder's call of the V1 helper (0x2c8fc ->
        // 0x1c1b) and its template pointer (lea rax,[rip+0x2f0dc3] = 0x31d720),
        // both unchanged.
        const auto &v=VAFix::VFEG12[1];
        assert(v.fileOffset==0x2C8FC && v.from[0]==0xE8 && VAFix::VFEG12[0].from[0]==0xE8);
        assert(!memcmp(v.from,"\xE8\x1A\x53\xFD\xFF",5) && 0x2C8FC+5+(int32_t)0xFFFD531A==0x1C1B);
        assert(!memcmp(&v.from[0x2C956-0x2C8FC],"\x48\x8D\x05\xC3\x0D\x2F\x00",7) && 0x2C95D+0x2F0DC3==0x31D720);
        assert(!memcmp(&v.to[0x2C956-0x2C8FC],&v.from[0x2C956-0x2C8FC],7));
        for(const auto &a:VAFix::VFEG12)assert(a.fileOffset/PageFix::PageSize!=0x31D);
    }
    // Latch rules.
    {
        uint32_t l=PageFix::Undecided;
        assert(PageFix::member(&l,false,true)==PageFix::Action::SkipGate && l==PageFix::Off);
        assert(PageFix::member(&l,true,true)==PageFix::Action::SkipGate); // decided once
        l=PageFix::Undecided;
        assert(PageFix::member(&l,true,true)==PageFix::Action::Patch && l==PageFix::Armed);
        assert(PageFix::member(&l,false,true)==PageFix::Action::Patch);   // decided once
        // An unpinned hit is skipped and never changes the latch, in any state.
        const uint32_t states[] {PageFix::Undecided,PageFix::Armed,PageFix::Off,PageFix::Poisoned,PageFix::Committed};
        for(uint32_t s:states) {
            uint32_t x=s;
            assert(PageFix::member(&x,true,false)==PageFix::Action::SkipOffset && x==s);
            assert(PageFix::member(&x,false,false)==PageFix::Action::SkipOffset && x==s);
        }
        // commit: Armed -> Committed (idempotent); final states refuse.
        l=PageFix::Armed;
        assert(PageFix::commit(&l) && l==PageFix::Committed && PageFix::commit(&l) && l==PageFix::Committed);
        assert(PageFix::member(&l,false,true)==PageFix::Action::Patch);   // committed: every later page follows
        // poison: only Armed (nothing written yet) becomes Poisoned.
        PageFix::poison(&l);
        assert(l==PageFix::Committed);
        l=PageFix::Armed;PageFix::poison(&l);
        assert(l==PageFix::Poisoned && !PageFix::commit(&l) && l==PageFix::Poisoned);
        assert(PageFix::member(&l,true,true)==PageFix::Action::SkipGate);
        l=PageFix::Off;PageFix::poison(&l);
        assert(l==PageFix::Off && !PageFix::commit(&l) && l==PageFix::Off);
        l=PageFix::Undecided;PageFix::poison(&l);
        assert(l==PageFix::Undecided && !PageFix::commit(&l) && l==PageFix::Undecided);
        // applyMember on one window: `to` -> Done (no commit needed); a window
        // that is neither -> Failed, poisons while Armed, only counted once
        // Committed; `from` while Poisoned -> Skipped, nothing written.
        const auto &a=VAFix::VFEG12[0];
        uint8_t w[1024],before[1024];
        assert(a.length<=sizeof(w));
        l=PageFix::Armed;memcpy(w,a.to,a.length);
        assert(PageFix::applyMember(&l,a,w)==PageFix::Write::Done && l==PageFix::Armed);
        memcpy(w,a.from,a.length);w[a.length-1]^=0x5A;memcpy(before,w,a.length);
        assert(PageFix::applyMember(&l,a,w)==PageFix::Write::Failed && l==PageFix::Poisoned && !memcmp(w,before,a.length));
        memcpy(w,a.from,a.length);
        assert(PageFix::applyMember(&l,a,w)==PageFix::Write::Skipped && !memcmp(w,a.from,a.length));
        l=PageFix::Armed;
        assert(PageFix::applyMember(&l,a,w)==PageFix::Write::Done && l==PageFix::Committed && !memcmp(w,a.to,a.length));
        memcpy(w,before,a.length);
        assert(PageFix::applyMember(&l,a,w)==PageFix::Write::Failed && l==PageFix::Committed && !memcmp(w,before,a.length));
        assert(PageFix::applyMember(&l,a,nullptr)==PageFix::Write::Failed && l==PageFix::Committed);
        assert(PageFix::single(true)==PageFix::Action::Patch && PageFix::single(false)==PageFix::Action::SkipOffset);
        assert(!PageFix::routesComplete(0) && !PageFix::routesComplete(PageFix::RangePresent|PageFix::PagePresent));
        assert(PageFix::routesComplete(PageFix::RangeRouted|PageFix::PageRouted|PageFix::RangePresent|PageFix::PagePresent));
        assert(!PageFix::routesComplete(PageFix::RangeRouted|PageFix::RangePresent|PageFix::PagePresent));
        assert(PageFix::routesComplete(PageFix::RangeRouted|PageFix::RangePresent));
        assert(PageFix::routesComplete(PageFix::PageRouted|PageFix::PagePresent));
    }
    const auto original=image(false),expected=image(true);
    const size_t pages=FileSize/PageFix::PageSize;
    // Page-in in forward, reverse and shuffled orders: every anchor once.
    for(uint32_t seed=0;seed<12;++seed) {
        std::vector<size_t> order(pages);
        for(size_t i=0;i<pages;++i)order[i]=seed==1?pages-1-i:i;
        if(seed>1) {uint32_t s=seed;for(size_t i=pages-1;i>0;--i) {size_t j=lcg(s)%(i+1);size_t t=order[i];order[i]=order[j];order[j]=t;}}
        auto f=original;Run r;
        for(size_t p:order)pageIn(f,p*PageFix::PageSize,PageFix::PageSize,r);
        assert(!memcmp(f.data(),expected.data(),FileSize));
        for(unsigned i=0;i<VAFix::NullGuardAnchors;++i)assert(r.ng.s[VAFix::Patched0+i]==1);
        for(unsigned i=0;i<3;++i)assert(r.vf.s[VAFix::Patched0+i]==(i<VAFix::VFEG12Anchors?1u:0u));
        assert(r.ng.s[VAFix::Sites]==3 && r.vf.s[VAFix::Sites]==VAFix::VFEG12Sites && r.latch==PageFix::Committed);
        assert(!r.ng.s[VAFix::OffsetMismatch] && !r.vf.s[VAFix::OffsetMismatch] && !r.vf.s[VAFix::GateSkips]);
        // Re-validation (eviction) of edited pages finds nothing to do.
        Run again=r;
        for(size_t p:order)pageIn(f,p*PageFix::PageSize,PageFix::PageSize,again);
        assert(!memcmp(f.data(),expected.data(),FileSize) && again.ng.s[VAFix::Sites]==3 && again.vf.s[VAFix::Sites]==VAFix::VFEG12Sites);
    }
    // A page evicted and read back from disk is edited again under the same decision.
    {
        auto f=original;Run r;
        for(size_t p=0;p<pages;++p)pageIn(f,p*PageFix::PageSize,PageFix::PageSize,r);
        const size_t last=VAFix::VFEG12Anchors-1;
        const uint64_t page=VAFix::VFEG12[last].fileOffset&~(PageFix::PageSize-1);
        memcpy(&f[page],&original[page],PageFix::PageSize);
        pageIn(f,page,PageFix::PageSize,r);
        assert(!memcmp(f.data(),expected.data(),FileSize) && r.vf.s[VAFix::Patched0+last]==2 && r.latch==PageFix::Committed);
    }
    // Race: another validation of the same page edits each window after the
    // scan matched `from` and before this write. apply() sees `to` and is done
    // without writing: no write failure, the set is not poisoned.
    {
        auto f=original;Run r;r.race=true;
        for(size_t p=0;p<pages;++p)pageIn(f,p*PageFix::PageSize,PageFix::PageSize,r);
        assert(!memcmp(f.data(),expected.data(),FileSize) && r.latch==PageFix::Committed && r.raced==VAFix::NullGuardAnchors+VAFix::VFEG12Anchors);
        assert(!r.ng.s[VAFix::WriteFailures] && !r.vf.s[VAFix::WriteFailures]);
        assert(r.ng.s[VAFix::Sites]==3 && r.vf.s[VAFix::Sites]==VAFix::VFEG12Sites);
        // apply() itself: `to` -> done, unchanged; `from` -> edited; neither -> refused, unchanged.
        for(size_t t=0;t<2;++t) for(size_t i=0;i<tableAnchors[t];++i) {
            const auto &a=tables[t][i];
            uint8_t w[1024],before[1024];
            assert(a.length<=sizeof(w));
            memcpy(w,a.to,a.length);
            assert(PageFix::apply(a,w) && !memcmp(w,a.to,a.length));
            memcpy(w,a.from,a.length);
            assert(PageFix::apply(a,w) && !memcmp(w,a.to,a.length));
            memcpy(w,a.from,a.length);w[a.length-1]^=0x5A;
            memcpy(before,w,a.length);
            assert(!PageFix::apply(a,w) && !memcmp(w,before,a.length));
        }
        assert(!PageFix::apply(VAFix::NullGuard[0],nullptr));
    }
    // Multi-page ranges, and one search pass per distinct first byte.
    {
        auto f=original;Run r;r.vfe=false;
        passStarts=0;
        pageIn(f,0,FileSize,r);
        assert(passStarts==1); // three NullGuard anchors, one key byte
        assert(r.ng.s[VAFix::Sites]==3);
        Run v;v.nullGuard=false;passStarts=0;
        pageIn(f,0,FileSize,v);
        assert(passStarts==1 && v.vf.s[VAFix::Sites]==VAFix::VFEG12Sites); // V1 and V2 both start with a call (E8)
        assert(!memcmp(f.data(),expected.data(),FileSize));
    }
    // Gate closed at the first hit: nothing in the set is ever written.
    {
        auto f=original;Run r;r.nullGuard=false;r.gate=false;
        pageIn(f,0x1000,PageFix::PageSize,r);          // V1 page decides Off
        r.gate=true;
        for(size_t p=0;p<pages;++p)pageIn(f,p*PageFix::PageSize,PageFix::PageSize,r);
        assert(!memcmp(f.data(),original.data(),FileSize) && r.latch==PageFix::Off && r.vf.s[VAFix::GateSkips]==1+VAFix::VFEG12Anchors);
    }
    // An anchor away from its file offset (another file, or a slice at a
    // different offset): both tables count it and write nothing there; the
    // VFEG12 latch is untouched, so the real set afterwards is edited whole.
    const uint64_t moved=0x200000;
    {
        std::vector<uint8_t> f(FileSize,0xCC);
        memcpy(&f[moved],VAFix::N1From,sizeof(VAFix::N1From));
        memcpy(&f[moved+0x800],VAFix::VFEG12[1].from,VAFix::VFEG12[1].length);
        const auto before=f;
        Run r;
        pageIn(f,moved,PageFix::PageSize,r);
        assert(!memcmp(f.data(),before.data(),FileSize));
        assert(r.ng.s[VAFix::OffsetMismatch]==1 && r.vf.s[VAFix::OffsetMismatch]==1 && r.latch==PageFix::Undecided);
        auto g=original;
        for(size_t p=0;p<pages;++p)pageIn(g,p*PageFix::PageSize,PageFix::PageSize,r);
        assert(!memcmp(g.data(),expected.data(),FileSize) && r.latch==PageFix::Committed);
        assert(r.vf.s[VAFix::Sites]==VAFix::VFEG12Sites && !r.vf.s[VAFix::GateSkips] && !r.vf.s[VAFix::WriteFailures]);
    }
    // Eviction after an unpinned hit: the set is committed, another file's
    // clean page holds a member window at a different offset (counted, no
    // write, latch unchanged), then each member page is evicted and read back
    // from disk: it is edited again, so the set never splits.
    for(size_t k=0;k<VAFix::VFEG12Anchors;++k) {
        auto f=original;Run r;
        for(size_t p=0;p<pages;++p)pageIn(f,p*PageFix::PageSize,PageFix::PageSize,r);
        assert(r.latch==PageFix::Committed);
        const auto &a=VAFix::VFEG12[k];
        std::vector<uint8_t> other(FileSize,0xCC);
        memcpy(&other[moved+0x100],a.from,a.length);
        pageIn(other,moved,PageFix::PageSize,r);
        assert(r.vf.s[VAFix::OffsetMismatch]==1 && r.latch==PageFix::Committed && !memcmp(&other[moved+0x100],a.from,a.length));
        const uint64_t page=a.fileOffset&~(PageFix::PageSize-1);
        memcpy(&f[page],&original[page],PageFix::PageSize);
        pageIn(f,page,PageFix::PageSize,r);
        assert(!memcmp(f.data(),expected.data(),FileSize) && r.vf.s[VAFix::Patched0+k]==2 && !r.vf.s[VAFix::GateSkips]);
    }
    // A write that fails before any member window was written (the kernel
    // write window cannot be opened, or the window changed to neither `from`
    // nor `to`) poisons the set: no member is ever written this boot.
    for(unsigned mode=0;mode<2;++mode) {
        auto f=original;Run r;r.nullGuard=false;
        (mode?r.corrupt:r.failOpen)=1;
        for(size_t p=0;p<pages;++p)pageIn(f,p*PageFix::PageSize,PageFix::PageSize,r);
        assert(r.latch==PageFix::Poisoned && r.vf.s[VAFix::WriteFailures]==1 && !r.vf.s[VAFix::Sites]);
        assert(r.vf.s[VAFix::GateSkips]==VAFix::VFEG12Anchors-1);
        for(const auto &a:VAFix::VFEG12)assert(memcmp(&f[a.fileOffset],a.to,a.length)); // none edited
        for(size_t p=0;p<pages;++p)pageIn(f,p*PageFix::PageSize,PageFix::PageSize,r);   // later validations
        assert(!r.vf.s[VAFix::Sites] && r.latch==PageFix::Poisoned);
    }
    // The same failure after a member window was written leaves the set
    // committed: it is counted, and the failed page is edited at its next
    // validation (here: evicted and read back).
    for(unsigned mode=0;mode<2;++mode) {
        auto f=original;Run r;r.nullGuard=false;
        (mode?r.corrupt:r.failOpen)=2;
        for(size_t p=0;p<pages;++p)pageIn(f,p*PageFix::PageSize,PageFix::PageSize,r);
        assert(r.latch==PageFix::Committed && r.vf.s[VAFix::WriteFailures]==1);
        assert(r.vf.s[VAFix::Patched0]==1 && !r.vf.s[VAFix::Patched1]);   // member 1 (second in file order) failed
        const auto &a=VAFix::VFEG12[1];
        const uint64_t page=a.fileOffset&~(PageFix::PageSize-1);
        memcpy(&f[page],&original[page],PageFix::PageSize);
        pageIn(f,page,PageFix::PageSize,r);
        auto want=original;
        for(const auto &b:VAFix::VFEG12)memcpy(&want[b.fileOffset],b.to,b.length);
        assert(!memcmp(f.data(),want.data(),FileSize) && r.vf.s[VAFix::Patched1]==1 && r.latch==PageFix::Committed);
    }
    // Truncated windows, one changed byte and NULL data never match.
    {
        auto f=original;Run r;
        const auto &a=VAFix::NullGuard[0];
        pageIn(f,a.fileOffset,a.length-1,r);
        f[VAFix::VFEG12[1].fileOffset+5]^=1;
        pageIn(f,VAFix::VFEG12[1].fileOffset&~(PageFix::PageSize-1),PageFix::PageSize,r);
        assert(!r.ng.s[VAFix::Sites] && !r.vf.s[VAFix::Sites] && r.latch==PageFix::Undecided);
        assert(PageFix::scan(VAFix::NullGuard,VAFix::NullGuardAnchors,nullptr,0x1000,0,chr,[](size_t,uint8_t *,bool) {assert(false);})==0);
        uint8_t buf[64];memcpy(buf,a.from,sizeof(buf));
        assert(!PageFix::apply(VAFix::NullGuard[1],buf) && !memcmp(buf,a.from,sizeof(buf)));
    }
    puts("va_fix: ok");
    return 0;
}
