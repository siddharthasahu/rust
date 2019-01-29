extern crate rustc_demangle;

use rustc::hir::def_id::{CrateNum, DefId};
use rustc::hir::map::{DefPathData, DisambiguatedDefPathData};
use rustc::ty::{self, Ty, TyCtxt, TypeFoldable};
use rustc::ty::print::{PrettyPrinter, Printer, Print};
use rustc::ty::subst::{Kind, Subst, UnpackedKind};
use rustc_mir::monomorphize::Instance;

use std::cell::RefCell;
use std::fmt::{self, Write as FmtWrite};
use std::fs::{self, File};
use std::io::Write;
use std::ops::Range;
use std::path::PathBuf;
use std::time::SystemTime;

use symbol_names::{self as old, mw, new};

thread_local!(static OUT_DIR: Option<PathBuf> = {
    std::env::var_os("RUST_SYMBOL_DUMP_DIR").map(PathBuf::from)
});
thread_local!(static OUTPUT: RefCell<Option<File>> = RefCell::new(None));

pub fn record(
    tcx: TyCtxt<'_, 'tcx, 'tcx>,
    instance: Instance<'tcx>,
    old_mangling: &str,
    old_hash: u64,
) -> String {
    let header = "old+generics,old,mw,mw+compression,new,new+compression";

    // Always compute all forms of mangling.
    let def_id = instance.def_id();
    // FIXME(eddyb) this should ideally not be needed.
    let substs =
        tcx.normalize_erasing_regions(ty::ParamEnv::reveal_all(), instance.substs);

    let old_mangling_plus_generics = {
        let mut symbol_path = old::SymbolPrinter {
            tcx,
            path: old::SymbolPath::new(),
            keep_within_component: false,
        }.print_def_path(def_id, substs).unwrap().path;

        if instance.is_vtable_shim() {
            symbol_path.finalize_pending_component();
            old::sanitize(&mut symbol_path.temp_buf, "{{vtable-shim}}");
        }

        symbol_path.finish(old_hash)
    };

    let (mw_mangling, mw_mangling_plus_compression) = mw::mangle(tcx, instance)
        .unwrap_or((String::new(), String::new()));
    let (new_mangling, new_mangling_plus_compression) = new::mangle(tcx, instance);

    OUTPUT.with(|out| {
        let mut out = out.borrow_mut();
        if out.is_none() {
            OUT_DIR.with(|out_dir| {
                if let Some(out_dir) = out_dir {
                    let mut opts = fs::OpenOptions::new();
                    opts.write(true).create_new(true);

                    let mut time = SystemTime::now()
                        .duration_since(SystemTime::UNIX_EPOCH)
                        .map(|d| d.as_secs())
                        .unwrap_or(0);
                    let mut file = loop {
                        let file_path = out_dir.join(format!("{}-{}.{}.csv",
                            tcx.crate_name,
                            tcx.sess.local_crate_disambiguator(),
                            time,
                        ));

                        match opts.open(&file_path) {
                            Ok(file) => break file,
                            Err(e) => {
                                if e.kind() == std::io::ErrorKind::AlreadyExists {
                                    time += 1;
                                    continue;
                                }
                                bug!("can't open symbol dump file `{}`: {:?}",
                                    file_path.display(), e);
                            }
                        }
                    };
                    writeln!(file, "{}", header).unwrap();
                    *out = Some(file);
                }
            })
        }

        if let Some(out) = out.as_mut() {
            writeln!(out, "{},{},{},{},{},{}",
                old_mangling_plus_generics,
                old_mangling,
                mw_mangling,
                mw_mangling_plus_compression,
                new_mangling,
                new_mangling_plus_compression,
            ).unwrap();
        }
    });

    // Build the expected output of demangling, via `ty::print`.
    let make_expected_demangling = |alternate| {
        let cx = DemanglingPrinter {
            tcx,
            out: String::new(),
            alternate,
            in_value: true,
            binders: vec![],
        };
        if instance.is_vtable_shim() {
            cx.path_append_ns(
                |cx| cx.print_def_path(def_id, substs),
                'S',
                0,
                "",
            ).unwrap().out
        } else {
            cx.print_def_path(def_id, substs).unwrap().out
        }
    };
    let expected_demangling_alt = make_expected_demangling(true);
    let expected_demangling = make_expected_demangling(false);

    for mangling in &[&new_mangling, &new_mangling_plus_compression] {
        match rustc_demangle::try_demangle(mangling) {
            Ok(demangling) => {
                let demangling_alt = format!("{:#}", demangling);
                if demangling_alt.contains('?') {
                    bug!("demangle(alt) printing failed for {:?}\n{:?}", mangling, demangling_alt);
                }
                assert_eq!(demangling_alt, expected_demangling_alt);

                let demangling = format!("{}", demangling);
                if demangling.contains('?') {
                    bug!("demangle printing failed for {:?}\n{:?}", mangling, demangling);
                }
                assert_eq!(demangling, expected_demangling);
            }
            Err(_) => bug!("try_demangle failed for {:?}", mangling),
        }
    }

    new_mangling_plus_compression
}

struct BinderLevel {
    lifetime_depths: Range<u32>,
}

// Our expectation of the output of demangling,
// relying on `ty::print` / `PrettyPrinter`.
struct DemanglingPrinter<'a, 'tcx> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    out: String,

    /// Equivalent to `rustc-demangle`'s `{:#}` printing.
    alternate: bool,

    in_value: bool,
    binders: Vec<BinderLevel>,
}

impl fmt::Write for DemanglingPrinter<'_, '_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.out.write_str(s)
    }
}

impl DemanglingPrinter<'_, '_> {
    fn path_append_ns(
        mut self,
        print_prefix: impl FnOnce(Self) -> Result<Self, fmt::Error>,
        ns: char,
        disambiguator: u64,
        name: &str,
    ) -> Result<Self, fmt::Error> {
        self = print_prefix(self)?;
        self.write_str("::")?;

        if let 'A'..='Z' = ns {
            self.write_str("{")?;
            match ns {
                'C' => self.write_str("closure")?,
                'S' => self.write_str("shim")?,
                _ => write!(self, "{}", ns)?,
            }
            if !name.is_empty() {
                write!(self, ":{}", name)?;
            }
            write!(self, "#{}", disambiguator)?;
            self.write_str("}")?;
        } else {
            self.write_str(&name)?;
        }

        Ok(self)
    }

    fn print_lifetime_at_depth(&mut self, depth: u64) -> Result<(), fmt::Error> {
        if depth < 26 {
            write!(self, "'{}", (b'a' + depth as u8) as char)
        } else {
            write!(self, "'_{}", depth)
        }
    }
}

impl Printer<'tcx, 'tcx> for DemanglingPrinter<'_, 'tcx> {
    type Error = fmt::Error;

    type Path = Self;
    type Region = Self;
    type Type = Self;
    type DynExistential = Self;

    fn tcx(&'a self) -> TyCtxt<'a, 'tcx, 'tcx> {
        self.tcx
    }

    fn print_impl_path(
        self,
        impl_def_id: DefId,
        substs: &'tcx [Kind<'tcx>],
        mut self_ty: Ty<'tcx>,
        mut impl_trait_ref: Option<ty::TraitRef<'tcx>>,
    ) -> Result<Self::Path, Self::Error> {
        let mut param_env = self.tcx.param_env(impl_def_id)
            .with_reveal_all();
        if !substs.is_empty() {
            param_env = param_env.subst(self.tcx, substs);
        }

        match &mut impl_trait_ref {
            Some(impl_trait_ref) => {
                assert_eq!(impl_trait_ref.self_ty(), self_ty);
                *impl_trait_ref =
                    self.tcx.normalize_erasing_regions(param_env, *impl_trait_ref);
                self_ty = impl_trait_ref.self_ty();
            }
            None => {
                self_ty = self.tcx.normalize_erasing_regions(param_env, self_ty);
            }
        }

        self.path_qualified(self_ty, impl_trait_ref)
    }

    fn print_region(
        mut self,
        region: ty::Region<'_>,
    ) -> Result<Self::Region, Self::Error> {
        match *region {
            ty::ReErased => write!(self, "'_")?,

            ty::ReLateBound(debruijn, ty::BrAnon(i)) => {
                let binder = &self.binders[self.binders.len() - 1 - debruijn.index()];
                let depth = binder.lifetime_depths.start + i;
                self.print_lifetime_at_depth(depth as u64)?;
            }

            _ => bug!("symbol_names::dump: non-erased region `{:?}`", region),
        }

        Ok(self)
    }

    fn print_type(
        mut self,
        ty: Ty<'tcx>,
    ) -> Result<Self::Type, Self::Error> {
        match ty.sty {
            // Mangled as paths (unlike `pretty_print_type`).
            ty::FnDef(def_id, substs) |
            ty::Opaque(def_id, substs) |
            ty::Projection(ty::ProjectionTy { item_def_id: def_id, substs }) |
            ty::UnnormalizedProjection(ty::ProjectionTy { item_def_id: def_id, substs }) |
            ty::Closure(def_id, ty::ClosureSubsts { substs }) |
            ty::Generator(def_id, ty::GeneratorSubsts { substs }, _) => {
                self.print_def_path(def_id, substs)
            }

            // Mangled as placeholders.
            ty::Param(_) | ty::Bound(..) | ty::Placeholder(_) |
            ty::Infer(_) | ty::Error => {
                write!(self, "_")?;
                Ok(self)
            }

            // Demangled with explicit type for constants (`len` here).
            ty::Array(ty, len) if !self.alternate => {
                write!(self, "[")?;
                self = ty.print(self)?;
                write!(self, "; ")?;
                match len {
                    ty::LazyConst::Unevaluated(_def_id, _substs) => {
                        write!(self, "_")?;
                    }
                    ty::LazyConst::Evaluated(c) => {
                        write!(self, "{}", c.unwrap_usize(self.tcx))?;
                    }
                }
                write!(self, ": usize]")?;
                Ok(self)
            }

            // Demangled without anyparens.
            ty::Dynamic(data, r) => {
                let print_r = self.region_should_not_be_omitted(r);
                write!(self, "dyn ")?;
                self = data.print(self)?;
                if print_r {
                    write!(self, " + ")?;
                    self = r.print(self)?;
                }
                Ok(self)
            }

            _ => self.pretty_print_type(ty),
        }
    }

    fn print_dyn_existential(
        mut self,
        predicates: &'tcx ty::List<ty::ExistentialPredicate<'tcx>>,
    ) -> Result<Self::DynExistential, Self::Error> {
        // Generate the main trait ref, including associated types.
        let mut first = true;

        if let Some(principal) = predicates.principal() {
            self = self.print_def_path(principal.def_id, &[])?;

            // Use a type that can't appear in defaults of type parameters.
            let dummy_self = self.tcx().mk_infer(ty::FreshTy(0));
            let principal = principal.with_self_ty(self.tcx(), dummy_self);

            let args = self.generic_args_to_print(
                self.tcx().generics_of(principal.def_id),
                principal.substs,
            );

            // Don't print any regions if they're all erased.
            let print_regions = args.iter().any(|arg| {
                match arg.unpack() {
                    UnpackedKind::Lifetime(r) => *r != ty::ReErased,
                    _ => false,
                }
            });
            let mut args = args.iter().cloned().filter(|arg| {
                match arg.unpack() {
                    UnpackedKind::Lifetime(_) => print_regions,
                    _ => true,
                }
            });
            let mut projections = predicates.projection_bounds();

            let arg0 = args.next();
            let projection0 = projections.next();
            if arg0.is_some() || projection0.is_some() {
                let args = arg0.into_iter().chain(args);
                let projections = projection0.into_iter().chain(projections);

                self = self.generic_delimiters(|mut cx| {
                    cx = cx.comma_sep(args)?;
                    if arg0.is_some() && projection0.is_some() {
                        write!(cx, ", ")?;
                    }
                    cx.comma_sep(projections)
                })?;
            }
            first = false;
        }

        for def_id in predicates.auto_traits() {
            if !first {
                write!(self, " + ")?;
            }
            first = false;

            self = self.print_def_path(def_id, &[])?;
        }

        Ok(self)
    }

    fn path_crate(
        mut self,
        cnum: CrateNum,
    ) -> Result<Self::Path, Self::Error> {
        self.write_str(&self.tcx.original_crate_name(cnum).as_str())?;
        let fingerprint = self.tcx.crate_disambiguator(cnum).to_fingerprint();
        if !self.alternate {
            write!(self, "[{:x}]", fingerprint.to_smaller_hash())?;
        }
        Ok(self)
    }
    fn path_qualified(
        self,
        self_ty: Ty<'tcx>,
        trait_ref: Option<ty::TraitRef<'tcx>>,
    ) -> Result<Self::Path, Self::Error> {
        self.generic_delimiters(|mut cx| {
            cx = self_ty.print(cx)?;
            if let Some(trait_ref) = trait_ref {
                write!(cx, " as ")?;
                cx = trait_ref.print(cx)?;
            }
            Ok(cx)
        })
    }

    fn path_append_impl(
        self,
        _print_prefix: impl FnOnce(Self) -> Result<Self::Path, Self::Error>,
        _disambiguated_data: &DisambiguatedDefPathData,
        _self_ty: Ty<'tcx>,
        _trait_ref: Option<ty::TraitRef<'tcx>>,
    ) -> Result<Self::Path, Self::Error> {
        unreachable!()
    }
    fn path_append(
        self,
        print_prefix: impl FnOnce(Self) -> Result<Self::Path, Self::Error>,
        disambiguated_data: &DisambiguatedDefPathData,
    ) -> Result<Self::Path, Self::Error> {
        let ns = match disambiguated_data.data {
            DefPathData::StructCtor => return print_prefix(self),
            DefPathData::ClosureExpr => 'C',
            _ => '_',
        };

        let name = disambiguated_data.data.get_opt_name().map(|s| s.as_str());
        let name = name.as_ref().map_or("", |s| &s[..]);

        self.path_append_ns(
            print_prefix,
            ns,
            disambiguated_data.disambiguator as u64,
            name,
        )
    }
    fn path_generic_args(
        mut self,
        print_prefix: impl FnOnce(Self) -> Result<Self::Path, Self::Error>,
        args: &[Kind<'tcx>],
    )  -> Result<Self::Path, Self::Error> {
        self = print_prefix(self)?;

        // Don't print any regions if they're all erased.
        let print_regions = args.iter().any(|arg| {
            match arg.unpack() {
                UnpackedKind::Lifetime(r) => *r != ty::ReErased,
                _ => false,
            }
        });
        let args = args.iter().cloned().filter(|arg| {
            match arg.unpack() {
                UnpackedKind::Lifetime(_) => print_regions,
                _ => true,
            }
        });

        if args.clone().next().is_some() {
            if self.in_value {
                write!(self, "::")?;
            }
            self.generic_delimiters(|cx| cx.comma_sep(args))
        } else {
            Ok(self)
        }
    }
}

impl PrettyPrinter<'tcx, 'tcx> for DemanglingPrinter<'_, 'tcx> {
    fn region_should_not_be_omitted(
        &self,
        region: ty::Region<'_>,
    ) -> bool {
        *region != ty::ReErased
    }

    fn generic_delimiters(
        mut self,
        f: impl FnOnce(Self) -> Result<Self, Self::Error>,
    ) -> Result<Self, Self::Error> {
        write!(self, "<")?;
        let was_in_value = ::std::mem::replace(&mut self.in_value, false);
        self = f(self)?;
        self.in_value = was_in_value;
        write!(self, ">")?;
        Ok(self)
    }

    fn in_binder<T>(
        mut self,
        value: &ty::Binder<T>,
    ) -> Result<Self, Self::Error>
        where T: Print<'tcx, 'tcx, Self, Output = Self, Error = Self::Error> + TypeFoldable<'tcx>
    {
        let regions = if value.has_late_bound_regions() {
            self.tcx.collect_referenced_late_bound_regions(value)
        } else {
            Default::default()
        };

        let mut lifetime_depths =
            self.binders.last().map(|b| b.lifetime_depths.end).map_or(0..0, |i| i..i);

        let lifetimes = regions.into_iter().map(|br| {
            match br {
                ty::BrAnon(i) => i + 1,
                _ => bug!("symbol_names: non-anonymized region `{:?}` in `{:?}`", br, value),
            }
        }).max().unwrap_or(0);

        lifetime_depths.end += lifetimes;

        if lifetimes > 0 {
            write!(self, "for<")?;
            for i in lifetime_depths.clone() {
                if i > lifetime_depths.start {
                    write!(self, ", ")?;
                }
                self.print_lifetime_at_depth(i as u64)?;
            }
            write!(self, "> ")?;
        }

        self.binders.push(BinderLevel { lifetime_depths });
        self = value.skip_binder().print(self)?;
        self.binders.pop();

        Ok(self)
    }
}
