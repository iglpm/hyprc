//! Writing ELF64 relocatable objects (x86-64).

use crate::x86_64::asm::{Reloc, RelocKind};
use rustc_hash::FxHashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Section {
    Text,
    Rodata,
    Data,
    Bss,
    Undef,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SymKind {
    Func,
    Object,
    NoType,
}

#[derive(Clone, Debug)]
pub struct Symbol {
    pub name: String,
    pub section: Section,
    pub offset: u64,
    pub size: u64,
    pub global: bool,
    pub kind: SymKind,
}

#[derive(Default)]
pub struct Object {
    pub text: Vec<u8>,
    pub rodata: Vec<u8>,
    pub data: Vec<u8>,
    pub bss_size: u64,
    pub symbols: Vec<Symbol>,
    /// Relocations: the section they patch, and the relocation (offset within it).
    pub relocs: Vec<(Section, Reloc)>,
    pub text_align: u64,
    pub data_align: u64,
    pub rodata_align: u64,
}

const SHT_PROGBITS: u32 = 1;
const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_RELA: u32 = 4;
const SHT_NOBITS: u32 = 8;
const SHF_WRITE: u64 = 1;
const SHF_ALLOC: u64 = 2;
const SHF_EXECINSTR: u64 = 4;
const SHF_INFO_LINK: u64 = 0x40;

struct Strtab {
    data: Vec<u8>,
    map: FxHashMap<String, u32>,
}

impl Strtab {
    fn new() -> Strtab {
        Strtab {
            data: vec![0],
            map: FxHashMap::default(),
        }
    }

    fn add(&mut self, s: &str) -> u32 {
        if s.is_empty() {
            return 0;
        }
        if let Some(&o) = self.map.get(s) {
            return o;
        }
        let o = self.data.len() as u32;
        self.data.extend_from_slice(s.as_bytes());
        self.data.push(0);
        self.map.insert(s.to_string(), o);
        o
    }
}

struct Shdr {
    name: u32,
    kind: u32,
    flags: u64,
    offset: u64,
    size: u64,
    link: u32,
    info: u32,
    align: u64,
    entsize: u64,
}

fn push_u16(v: &mut Vec<u8>, x: u16) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_u32(v: &mut Vec<u8>, x: u32) {
    v.extend_from_slice(&x.to_le_bytes());
}
fn push_u64(v: &mut Vec<u8>, x: u64) {
    v.extend_from_slice(&x.to_le_bytes());
}

fn pad_to(v: &mut Vec<u8>, align: u64) {
    while v.len() as u64 % align != 0 {
        v.push(0);
    }
}

impl Object {
    pub fn write(&self) -> Vec<u8> {
        // Section indices: 1 .text, 2 .rodata, 3 .data, 4 .bss, then the rest.
        let sec_index = |s: Section| -> u16 {
            match s {
                Section::Text => 1,
                Section::Rodata => 2,
                Section::Data => 3,
                Section::Bss => 4,
                Section::Undef => 0,
            }
        };
        let mut strtab = Strtab::new();
        let mut shstrtab = Strtab::new();
        // Symbols: the null symbol, locals, then globals (ELF requires locals first).
        let mut order: Vec<usize> = (0..self.symbols.len())
            .filter(|&i| !self.symbols[i].global)
            .collect();
        let first_global = order.len() + 1;
        order.extend((0..self.symbols.len()).filter(|&i| self.symbols[i].global));
        let mut sym_index: FxHashMap<&str, u32> = FxHashMap::default();
        let mut symtab = vec![0u8; 24];
        for (n, &i) in order.iter().enumerate() {
            let s = &self.symbols[i];
            sym_index.insert(&s.name, n as u32 + 1);
            let name = strtab.add(&s.name);
            let bind = if s.global { 1u8 } else { 0u8 };
            let ty = match s.kind {
                SymKind::Func => 2u8,
                SymKind::Object => 1u8,
                SymKind::NoType => 0u8,
            };
            push_u32(&mut symtab, name);
            symtab.push((bind << 4) | ty);
            symtab.push(0);
            push_u16(&mut symtab, sec_index(s.section));
            push_u64(&mut symtab, s.offset);
            push_u64(&mut symtab, s.size);
        }
        let mut rela: FxHashMap<Section, Vec<u8>> = FxHashMap::default();
        for (sec, r) in &self.relocs {
            let sym = *sym_index
                .get(r.symbol.as_str())
                .unwrap_or_else(|| panic!("relocation to unknown symbol `{}`", r.symbol));
            let ty: u64 = match r.kind {
                RelocKind::Abs64 => 1,
                RelocKind::Pc32 => 2,
                RelocKind::Plt32 => 4,
            };
            let out = rela.entry(*sec).or_default();
            push_u64(out, r.offset);
            push_u64(out, ((sym as u64) << 32) | ty);
            push_u64(out, r.addend as u64);
        }

        let mut out = vec![0u8; 64];
        let mut shdrs: Vec<Shdr> = vec![Shdr {
            name: 0,
            kind: 0,
            flags: 0,
            offset: 0,
            size: 0,
            link: 0,
            info: 0,
            align: 0,
            entsize: 0,
        }];
        let mut add_section = |out: &mut Vec<u8>,
                               shdrs: &mut Vec<Shdr>,
                               name: &str,
                               kind: u32,
                               flags: u64,
                               data: &[u8],
                               align: u64,
                               link: u32,
                               info: u32,
                               entsize: u64| {
            pad_to(out, align.max(1));
            let offset = out.len() as u64;
            if kind != SHT_NOBITS {
                out.extend_from_slice(data);
            }
            shdrs.push(Shdr {
                name: shstrtab.add(name),
                kind,
                flags,
                offset,
                size: data.len() as u64,
                link,
                info,
                align,
                entsize,
            });
        };
        add_section(
            &mut out,
            &mut shdrs,
            ".text",
            SHT_PROGBITS,
            SHF_ALLOC | SHF_EXECINSTR,
            &self.text,
            self.text_align.max(16),
            0,
            0,
            0,
        );
        add_section(
            &mut out,
            &mut shdrs,
            ".rodata",
            SHT_PROGBITS,
            SHF_ALLOC,
            &self.rodata,
            self.rodata_align.max(16),
            0,
            0,
            0,
        );
        add_section(
            &mut out,
            &mut shdrs,
            ".data",
            SHT_PROGBITS,
            SHF_ALLOC | SHF_WRITE,
            &self.data,
            self.data_align.max(16),
            0,
            0,
            0,
        );
        // .bss: no bytes in the file; its size is set below.
        add_section(
            &mut out,
            &mut shdrs,
            ".bss",
            SHT_NOBITS,
            SHF_ALLOC | SHF_WRITE,
            &[],
            16,
            0,
            0,
            0,
        );
        shdrs[4].size = self.bss_size;
        let symtab_index = 5 + [Section::Text, Section::Rodata, Section::Data]
            .iter()
            .filter(|s| rela.contains_key(s))
            .count() as u32;
        for (sec, name) in [
            (Section::Text, ".rela.text"),
            (Section::Rodata, ".rela.rodata"),
            (Section::Data, ".rela.data"),
        ] {
            if let Some(data) = rela.get(&sec) {
                add_section(
                    &mut out,
                    &mut shdrs,
                    name,
                    SHT_RELA,
                    SHF_INFO_LINK,
                    data,
                    8,
                    symtab_index,
                    sec_index(sec) as u32,
                    24,
                );
            }
        }
        add_section(
            &mut out,
            &mut shdrs,
            ".symtab",
            SHT_SYMTAB,
            0,
            &symtab,
            8,
            symtab_index + 1,
            first_global as u32,
            24,
        );
        let strtab_data = strtab.data.clone();
        add_section(
            &mut out,
            &mut shdrs,
            ".strtab",
            SHT_STRTAB,
            0,
            &strtab_data,
            1,
            0,
            0,
            0,
        );
        add_section(
            &mut out,
            &mut shdrs,
            ".note.GNU-stack",
            SHT_PROGBITS,
            0,
            &[],
            1,
            0,
            0,
            0,
        );
        let shstrtab_name = shstrtab.add(".shstrtab");
        let shstrtab_data = shstrtab.data.clone();
        pad_to(&mut out, 1);
        let sh_off_data = out.len() as u64;
        out.extend_from_slice(&shstrtab_data);
        shdrs.push(Shdr {
            name: shstrtab_name,
            kind: SHT_STRTAB,
            flags: 0,
            offset: sh_off_data,
            size: shstrtab_data.len() as u64,
            link: 0,
            info: 0,
            align: 1,
            entsize: 0,
        });
        pad_to(&mut out, 8);
        let shoff = out.len() as u64;
        for s in &shdrs {
            push_u32(&mut out, s.name);
            push_u32(&mut out, s.kind);
            push_u64(&mut out, s.flags);
            push_u64(&mut out, 0);
            push_u64(&mut out, s.offset);
            push_u64(&mut out, s.size);
            push_u32(&mut out, s.link);
            push_u32(&mut out, s.info);
            push_u64(&mut out, s.align);
            push_u64(&mut out, s.entsize);
        }
        // The ELF header.
        let mut h = Vec::with_capacity(64);
        h.extend_from_slice(&[0x7F, b'E', b'L', b'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        push_u16(&mut h, 1); // ET_REL
        push_u16(&mut h, 62); // EM_X86_64
        push_u32(&mut h, 1);
        push_u64(&mut h, 0);
        push_u64(&mut h, 0);
        push_u64(&mut h, shoff);
        push_u32(&mut h, 0);
        push_u16(&mut h, 64);
        push_u16(&mut h, 0);
        push_u16(&mut h, 0);
        push_u16(&mut h, 64);
        push_u16(&mut h, shdrs.len() as u16);
        push_u16(&mut h, shdrs.len() as u16 - 1);
        out[..64].copy_from_slice(&h);
        out
    }
}
