use delimited::Delimited;
use super::*;

ast_enum_of_structs! {
    /// The different kinds of types recognized by the compiler
    pub enum Type {
        /// A variable-length array (`[T]`)
        pub Slice(TypeSlice {
            pub ty: Box<Type>,
            pub bracket_token: tokens::Bracket,
        }),
        /// A fixed length array (`[T; n]`)
        pub Array(TypeArray {
            pub bracket_token: tokens::Bracket,
            pub ty: Box<Type>,
            pub semi_token: Token![;],
            pub amt: Expr,
        }),
        /// A raw pointer (`*const T` or `*mut T`)
        pub Ptr(TypePtr {
            pub star_token: Token![*],
            pub const_token: Option<Token![const]>,
            pub ty: Box<MutType>,
        }),
        /// A reference (`&'a T` or `&'a mut T`)
        pub Reference(TypeReference {
            pub and_token: Token![&],
            pub lifetime: Option<Lifetime>,
            pub ty: Box<MutType>,
        }),
        /// A bare function (e.g. `fn(usize) -> bool`)
        pub BareFn(TypeBareFn {
            pub ty: Box<BareFnType>,
        }),
        /// The never type (`!`)
        pub Never(TypeNever {
            pub bang_token: Token![!],
        }),
        /// A tuple (`(A, B, C, D, ...)`)
        pub Tup(TypeTup {
            pub paren_token: tokens::Paren,
            pub tys: Delimited<Type, Token![,]>,
            pub lone_comma: Option<Token![,]>,
        }),
        /// A path (`module::module::...::Type`), optionally
        /// "qualified", e.g. `<Vec<T> as SomeTrait>::SomeType`.
        ///
        /// Type parameters are stored in the Path itself
        pub Path(TypePath {
            pub qself: Option<QSelf>,
            pub path: Path,
        }),
        /// A trait object type `Bound1 + Bound2 + Bound3`
        /// where `Bound` is a trait or a lifetime.
        pub TraitObject(TypeTraitObject {
            pub bounds: Delimited<TypeParamBound, Token![+]>,
        }),
        /// An `impl Bound1 + Bound2 + Bound3` type
        /// where `Bound` is a trait or a lifetime.
        pub ImplTrait(TypeImplTrait {
            pub impl_token: Token![impl],
            pub bounds: Delimited<TypeParamBound, Token![+]>,
        }),
        /// No-op; kept solely so that we can pretty-print faithfully
        pub Paren(TypeParen {
            pub paren_token: tokens::Paren,
            pub ty: Box<Type>,
        }),
        /// No-op: kept solely so that we can pretty-print faithfully
        pub Group(TypeGroup {
            pub group_token: tokens::Group,
            pub ty: Box<Type>,
        }),
        /// TypeKind::Infer means the type should be inferred instead of it having been
        /// specified. This can appear anywhere in a type.
        pub Infer(TypeInfer {
            pub underscore_token: Token![_],
        }),
        /// A macro in the type position.
        pub Macro(Macro),
    }
}

ast_struct! {
    pub struct MutType {
        pub ty: Type,
        pub mutability: Mutability,
    }
}

ast_enum! {
    #[cfg_attr(feature = "clone-impls", derive(Copy))]
    pub enum Mutability {
        Mutable(Token![mut]),
        Immutable,
    }
}

ast_struct! {
    /// A "Path" is essentially Rust's notion of a name.
    ///
    /// It's represented as a sequence of identifiers,
    /// along with a bunch of supporting information.
    ///
    /// E.g. `std::cmp::PartialEq`
    pub struct Path {
        /// A `::foo` path, is relative to the crate root rather than current
        /// module (like paths in an import).
        pub leading_colon: Option<Token![::]>,
        /// The segments in the path: the things separated by `::`.
        pub segments: Delimited<PathSegment, Token![::]>,
    }
}

impl Path {
    pub fn global(&self) -> bool {
        self.leading_colon.is_some()
    }
}

#[cfg(feature = "printing")]
#[cfg_attr(feature = "extra-traits", derive(Debug, Eq, PartialEq, Hash))]
#[cfg_attr(feature = "clone-impls", derive(Clone))]
pub struct PathTokens<'a>(pub &'a Option<QSelf>, pub &'a Path);

impl<T> From<T> for Path
    where T: Into<PathSegment>
{
    fn from(segment: T) -> Self {
        Path {
            leading_colon: None,
            segments: vec![(segment.into(), None)].into(),
        }
    }
}

ast_struct! {
    /// A segment of a path: an identifier, an optional lifetime, and a set of types.
    ///
    /// E.g. `std`, `String` or `Box<T>`
    pub struct PathSegment {
        /// The identifier portion of this path segment.
        pub ident: Ident,
        /// Type/lifetime parameters attached to this path. They come in
        /// two flavors: `Path<A,B,C>` and `Path(A,B) -> C`. Note that
        /// this is more than just simple syntactic sugar; the use of
        /// parens affects the region binding rules, so we preserve the
        /// distinction.
        pub parameters: PathParameters,
    }
}

impl<T> From<T> for PathSegment
    where T: Into<Ident>
{
    fn from(ident: T) -> Self {
        PathSegment {
            ident: ident.into(),
            parameters: PathParameters::None,
        }
    }
}

ast_enum! {
    /// Parameters of a path segment.
    ///
    /// E.g. `<A, B>` as in `Foo<A, B>` or `(A, B)` as in `Foo(A, B)`
    pub enum PathParameters {
        None,
        /// The `<'a, A, B, C>` in `foo::bar::baz::<'a, A, B, C>`
        AngleBracketed(AngleBracketedParameterData),
        /// The `(A, B)` and `C` in `Foo(A, B) -> C`
        Parenthesized(ParenthesizedParameterData),
    }
}

impl Default for PathParameters {
    fn default() -> Self {
        PathParameters::None
    }
}

impl PathParameters {
    pub fn is_empty(&self) -> bool {
        match *self {
            PathParameters::None => true,
            PathParameters::AngleBracketed(ref bracketed) => {
                bracketed.lifetimes.is_empty() && bracketed.types.is_empty() &&
                bracketed.bindings.is_empty()
            }
            PathParameters::Parenthesized(_) => false,
        }
    }
}

ast_struct! {
    /// A path like `Foo<'a, T>`
    pub struct AngleBracketedParameterData {
        pub turbofish: Option<Token![::]>,
        pub lt_token: Token![<],
        /// The lifetime parameters for this path segment.
        pub lifetimes: Delimited<Lifetime, Token![,]>,
        /// The type parameters for this path segment, if present.
        pub types: Delimited<Type, Token![,]>,
        /// Bindings (equality constraints) on associated types, if present.
        ///
        /// E.g., `Foo<A=Bar>`.
        pub bindings: Delimited<TypeBinding, Token![,]>,
        pub gt_token: Token![>],
    }
}

ast_struct! {
    /// Bind a type to an associated type: `A=Foo`.
    pub struct TypeBinding {
        pub ident: Ident,
        pub eq_token: Token![=],
        pub ty: Type,
    }
}


ast_struct! {
    /// A path like `Foo(A,B) -> C`
    pub struct ParenthesizedParameterData {
        pub paren_token: tokens::Paren,
        /// `(A, B)`
        pub inputs: Delimited<Type, Token![,]>,
        /// `C`
        pub output: ReturnType,
    }
}

ast_struct! {
    pub struct PolyTraitRef {
        /// The `for<'a>` in `for<'a> Foo<&'a T>`
        pub bound_lifetimes: Option<BoundLifetimes>,
        /// The `Foo<&'a T>` in `<'a> Foo<&'a T>`
        pub trait_ref: Path,
    }
}

ast_struct! {
    /// The explicit Self type in a "qualified path". The actual
    /// path, including the trait and the associated item, is stored
    /// separately. `position` represents the index of the associated
    /// item qualified with this Self type.
    ///
    /// ```rust,ignore
    /// <Vec<T> as a::b::Trait>::AssociatedItem
    ///  ^~~~~     ~~~~~~~~~~~~~~^
    ///  ty        position = 3
    ///
    /// <Vec<T>>::AssociatedItem
    ///  ^~~~~    ^
    ///  ty       position = 0
    /// ```
    pub struct QSelf {
        pub lt_token: Token![<],
        pub ty: Box<Type>,
        pub position: usize,
        pub as_token: Option<Token![as]>,
        pub gt_token: Token![>],
    }
}

ast_struct! {
    pub struct BareFnType {
        pub lifetimes: Option<BoundLifetimes>,
        pub unsafety: Unsafety,
        pub abi: Option<Abi>,
        pub fn_token: Token![fn],
        pub paren_token: tokens::Paren,
        pub inputs: Delimited<BareFnArg, Token![,]>,
        pub variadic: Option<Token![...]>,
        pub output: ReturnType,
    }
}

ast_enum! {
    #[cfg_attr(feature = "clone-impls", derive(Copy))]
    pub enum Unsafety {
        Unsafe(Token![unsafe]),
        Normal,
    }
}

ast_struct! {
    pub struct Abi {
        pub extern_token: Token![extern],
        pub kind: AbiKind,
    }
}

ast_enum! {
    pub enum AbiKind {
        Named(Lit),
        Default,
    }
}

ast_struct! {
    /// An argument in a function type.
    ///
    /// E.g. `bar: usize` as in `fn foo(bar: usize)`
    pub struct BareFnArg {
        pub name: Option<(BareFnArgName, Token![:])>,
        pub ty: Type,
    }
}

ast_enum! {
    /// Names of arguments in the `BareFnArg` structure
    pub enum BareFnArgName {
        /// Argument with the provided name
        Named(Ident),
        /// Argument matched with `_`
        Wild(Token![_]),
    }
}

ast_enum! {
    pub enum ReturnType {
        /// Return type is not specified.
        ///
        /// Functions default to `()` and
        /// closures default to inference. Span points to where return
        /// type would be inserted.
        Default,
        /// Everything else
        Type(Type, Token![->]),
    }
}

#[cfg(feature = "parsing")]
pub mod parsing {
    use super::*;
    use synom::Synom;

    impl Synom for Type {
        named!(parse -> Self, call!(ambig_ty, true));

        fn description() -> Option<&'static str> {
            Some("type")
        }
    }

    impl Type {
        /// In some positions, types may not contain the `+` character, to
        /// disambiguate them. For example in the expression `1 as T`, T may not
        /// contain a `+` character.
        ///
        /// This parser does not allow a `+`, while the default parser does.
        named!(pub without_plus -> Self, call!(ambig_ty, false));
    }

    named!(ambig_ty(allow_plus: bool) -> Type, alt!(
        syn!(TypeGroup) => { Type::Group }
        |
        // must be before mac
        syn!(TypeParen) => { Type::Paren }
        |
        // must be before path
        syn!(Macro) => { Type::Macro }
        |
        // must be before ty_poly_trait_ref
        call!(ty_path, allow_plus)
        |
        syn!(TypeSlice) => { Type::Slice }
        |
        syn!(TypeArray) => { Type::Array }
        |
        syn!(TypePtr) => { Type::Ptr }
        |
        syn!(TypeReference) => { Type::Reference }
        |
        syn!(TypeBareFn) => { Type::BareFn }
        |
        syn!(TypeNever) => { Type::Never }
        |
        syn!(TypeTup) => { Type::Tup }
        |
        // Don't try parsing poly_trait_ref if we aren't allowing it
        call!(ty_poly_trait_ref, allow_plus)
        |
        syn!(TypeImplTrait) => { Type::ImplTrait }
        |
        syn!(TypeInfer) => { Type::Infer }
    ));

    impl Synom for TypeSlice {
        named!(parse -> Self, map!(
            brackets!(syn!(Type)),
            |(ty, b)| TypeSlice {
                ty: Box::new(ty),
                bracket_token: b,
            }
        ));
    }

    impl Synom for TypeArray {
        named!(parse -> Self, map!(
            brackets!(do_parse!(
                elem: syn!(Type) >>
                    semi: punct!(;) >>
                    len: syn!(Expr) >>
                    (elem, semi, len)
            )),
            |((elem, semi, len), brackets)| {
                TypeArray {
                    ty: Box::new(elem),
                    amt: len,
                    bracket_token: brackets,
                    semi_token: semi,
                }
            }
        ));
    }

    impl Synom for TypePtr {
        named!(parse -> Self, do_parse!(
            star: punct!(*) >>
            mutability: alt!(
                keyword!(const) => { |c| (Mutability::Immutable, Some(c)) }
                |
                keyword!(mut) => { |m| (Mutability::Mutable(m), None) }
            ) >>
            target: call!(Type::without_plus) >>
            (TypePtr {
                const_token: mutability.1,
                star_token: star,
                ty: Box::new(MutType {
                    ty: target,
                    mutability: mutability.0,
                }),
            })
        ));
    }

    impl Synom for TypeReference {
        named!(parse -> Self, do_parse!(
            amp: punct!(&) >>
            life: option!(syn!(Lifetime)) >>
            mutability: syn!(Mutability) >>
            // & binds tighter than +, so we don't allow + here.
            target: call!(Type::without_plus) >>
            (TypeReference {
                lifetime: life,
                ty: Box::new(MutType {
                    ty: target,
                    mutability: mutability,
                }),
                and_token: amp,
            })
        ));
    }

    impl Synom for TypeBareFn {
        named!(parse -> Self, do_parse!(
            lifetimes: option!(syn!(BoundLifetimes)) >>
            unsafety: syn!(Unsafety) >>
            abi: option!(syn!(Abi)) >>
            fn_: keyword!(fn) >>
            parens: parens!(do_parse!(
                inputs: call!(Delimited::parse_terminated) >>
                variadic: option!(cond_reduce!(inputs.is_empty() || inputs.trailing_delim(),
                                                punct!(...))) >>
                (inputs, variadic)
            )) >>
            output: syn!(ReturnType) >>
            (TypeBareFn {
                ty: Box::new(BareFnType {
                    unsafety: unsafety,
                    abi: abi,
                    lifetimes: lifetimes,
                    output: output,
                    variadic: (parens.0).1,
                    fn_token: fn_,
                    paren_token: parens.1,
                    inputs: (parens.0).0,
                }),
            })
        ));
    }

    impl Synom for TypeNever {
        named!(parse -> Self, map!(
            punct!(!),
            |b| TypeNever { bang_token: b }
        ));
    }

    impl Synom for TypeInfer {
        named!(parse -> Self, map!(
            punct!(_),
            |u| TypeInfer { underscore_token: u }
        ));
    }

    impl Synom for TypeTup {
        named!(parse -> Self, do_parse!(
            data: parens!(call!(Delimited::parse_terminated)) >>
            (TypeTup {
                tys: data.0,
                paren_token: data.1,
                lone_comma: None, // TODO: does this just not parse?
            })
        ));
    }

    named!(ty_path(allow_plus: bool) -> Type, do_parse!(
        qpath: qpath >>
        parenthesized: cond!(
            qpath.1.segments.get(qpath.1.segments.len() - 1).item().parameters.is_empty(),
            option!(syn!(ParenthesizedParameterData))
        ) >>
        // Only allow parsing additional bounds if allow_plus is true.
        bounds: alt!(
            cond_reduce!(
                allow_plus,
                many0!(tuple!(punct!(+), syn!(TypeParamBound)))
            )
            |
            value!(vec![])
        ) >>
        ({
            let (qself, mut path) = qpath;
            if let Some(Some(parenthesized)) = parenthesized {
                let parenthesized = PathParameters::Parenthesized(parenthesized);
                let len = path.segments.len();
                path.segments.get_mut(len - 1).item_mut().parameters = parenthesized;
            }
            if bounds.is_empty() {
                TypePath { qself: qself, path: path }.into()
            } else {
                let path = TypeParamBound::Trait(
                    PolyTraitRef {
                        bound_lifetimes: None,
                        trait_ref: path,
                    },
                    TraitBoundModifier::None,
                );
                let mut new_bounds = Delimited::new();
                new_bounds.push_first(path);
                for (_tok, bound) in bounds {
                    new_bounds.push_default(bound);
                }
                TypeTraitObject { bounds: new_bounds }.into()
            }
        })
    ));

    named!(pub qpath -> (Option<QSelf>, Path), alt!(
        map!(syn!(Path), |p| (None, p))
        |
        do_parse!(
            lt: punct!(<) >>
            this: syn!(Type) >>
            path: option!(do_parse!(
                as_: keyword!(as) >>
                path: syn!(Path) >>
                (as_, path)
            )) >>
            gt: punct!(>) >>
            colon2: punct!(::) >>
            rest: call!(Delimited::parse_separated_nonempty) >>
            ({
                let (pos, as_, path) = match path {
                    Some((as_, mut path)) => {
                        let pos = path.segments.len();
                        if !path.segments.is_empty() && !path.segments.trailing_delim() {
                            path.segments.push_trailing(colon2);
                        }
                        for item in rest {
                            path.segments.push(item);
                        }
                        (pos, Some(as_), path)
                    }
                    None => {
                        (0, None, Path {
                            leading_colon: Some(colon2),
                            segments: rest,
                        })
                    }
                };
                (Some(QSelf {
                    lt_token: lt,
                    ty: Box::new(this),
                    position: pos,
                    as_token: as_,
                    gt_token: gt,
                }), path)
            })
        )
        |
        map!(keyword!(self), |s| (None, s.into()))
    ));

    impl Synom for ParenthesizedParameterData {
        named!(parse -> Self, do_parse!(
            data: parens!(call!(Delimited::parse_terminated)) >>
            output: syn!(ReturnType) >>
            (ParenthesizedParameterData {
                paren_token: data.1,
                inputs: data.0,
                output: output,
            })
        ));
    }

    impl Synom for ReturnType {
        named!(parse -> Self, alt!(
            do_parse!(
                arrow: punct!(->) >>
                ty: syn!(Type) >>
                (ReturnType::Type(ty, arrow))
            )
            |
            epsilon!() => { |_| ReturnType::Default }
        ));
    }

    // Only allow multiple trait references if allow_plus is true.
    named!(ty_poly_trait_ref(allow_plus: bool) -> Type, alt!(
        cond_reduce!(allow_plus, call!(Delimited::parse_separated_nonempty)) => {
            |x| TypeTraitObject { bounds: x }.into()
        }
        |
        syn!(TypeParamBound) => {
            |x| TypeTraitObject { bounds: vec![x].into() }.into()
        }
    ));

    impl Synom for TypeImplTrait {
        named!(parse -> Self, do_parse!(
            impl_: keyword!(impl) >>
            // NOTE: rust-lang/rust#34511 includes discussion about whether or
            // not + should be allowed in ImplTrait directly without ().
            elem: call!(Delimited::parse_separated_nonempty) >>
            (TypeImplTrait {
                impl_token: impl_,
                bounds: elem,
            })
        ));
    }

    impl Synom for TypeGroup {
        named!(parse -> Self, do_parse!(
            data: grouped!(syn!(Type)) >>
            (TypeGroup {
                group_token: data.1,
                ty: Box::new(data.0),
            })
        ));
    }

    impl Synom for TypeParen {
        named!(parse -> Self, do_parse!(
            data: parens!(syn!(Type)) >>
            (TypeParen {
                paren_token: data.1,
                ty: Box::new(data.0),
            })
        ));
    }

    impl Synom for Mutability {
        named!(parse -> Self, alt!(
            keyword!(mut) => { Mutability::Mutable }
            |
            epsilon!() => { |_| Mutability::Immutable }
        ));
    }

    impl Synom for Path {
        named!(parse -> Self, do_parse!(
            colon: option!(punct!(::)) >>
            segments: call!(Delimited::parse_separated_nonempty) >>
            (Path {
                leading_colon: colon,
                segments: segments,
            })
        ));

        fn description() -> Option<&'static str> {
            Some("path")
        }
    }

    impl Synom for PathSegment {
        named!(parse -> Self, alt!(
            do_parse!(
                ident: syn!(Ident) >>
                turbofish: option!(punct!(::)) >>
                lt: punct!(<) >>
                lifetimes: call!(Delimited::parse_terminated) >>
                types: cond!(
                    lifetimes.is_empty() || lifetimes.trailing_delim(),
                    call!(Delimited::parse_terminated_with,
                            ty_no_eq_after)
                ) >>
                bindings: cond!(
                    match types {
                        Some(ref t) => t.is_empty() || t.trailing_delim(),
                        None => lifetimes.is_empty() || lifetimes.trailing_delim(),
                    },
                    call!(Delimited::parse_terminated)
                ) >>
                gt: punct!(>) >>
                (PathSegment {
                    ident: ident,
                    parameters: PathParameters::AngleBracketed(
                        AngleBracketedParameterData {
                            turbofish: turbofish,
                            lt_token: lt,
                            lifetimes: lifetimes,
                            types: types.unwrap_or_default(),
                            bindings: bindings.unwrap_or_default(),
                            gt_token: gt,
                        }
                    ),
                })
            )
            |
            mod_style_path_segment
        ));
    }

    named!(ty_no_eq_after -> Type, terminated!(syn!(Type), not!(punct!(=))));

    impl Path {
        named!(pub parse_mod_style -> Self, do_parse!(
            colon: option!(punct!(::)) >>
            segments: call!(Delimited::parse_separated_nonempty_with,
                            mod_style_path_segment) >>
            (Path {
                leading_colon: colon,
                segments: segments,
            })
        ));
    }

    named!(mod_style_path_segment -> PathSegment, alt!(
        map!(syn!(Ident), Into::into)
        |
        alt!(
            keyword!(super) => { Into::into }
            |
            keyword!(self) => { Into::into }
            |
            keyword!(Self) => { Into::into }
        )
    ));

    impl Synom for TypeBinding {
        named!(parse -> Self, do_parse!(
            id: syn!(Ident) >>
            eq: punct!(=) >>
            ty: syn!(Type) >>
            (TypeBinding {
                ident: id,
                eq_token: eq,
                ty: ty,
            })
        ));
    }

    impl Synom for PolyTraitRef {
        named!(parse -> Self, do_parse!(
            bound_lifetimes: option!(syn!(BoundLifetimes)) >>
            trait_ref: syn!(Path) >>
            parenthesized: option!(cond_reduce!(
                trait_ref.segments.get(trait_ref.segments.len() - 1).item().parameters.is_empty(),
                syn!(ParenthesizedParameterData)
            )) >>
            ({
                let mut trait_ref = trait_ref;
                if let Some(parenthesized) = parenthesized {
                    let parenthesized = PathParameters::Parenthesized(parenthesized);
                    let len = trait_ref.segments.len();
                    trait_ref.segments.get_mut(len - 1).item_mut().parameters = parenthesized;
                }
                PolyTraitRef {
                    bound_lifetimes: bound_lifetimes,
                    trait_ref: trait_ref,
                }
            })
        ));
    }

    impl Synom for BareFnArg {
        named!(parse -> Self, do_parse!(
            name: option!(do_parse!(
                name: syn!(BareFnArgName) >>
                not!(punct!(::)) >>
                colon: punct!(:) >>
                (name, colon)
            )) >>
            ty: syn!(Type) >>
            (BareFnArg {
                name: name,
                ty: ty,
            })
        ));
    }

    impl Synom for BareFnArgName {
        named!(parse -> Self, alt!(
            map!(syn!(Ident), BareFnArgName::Named)
            |
            map!(punct!(_), BareFnArgName::Wild)
        ));
    }

    impl Synom for Unsafety {
        named!(parse -> Self, alt!(
            keyword!(unsafe) => { Unsafety::Unsafe }
            |
            epsilon!() => { |_| Unsafety::Normal }
        ));
    }

    impl Synom for Abi {
        named!(parse -> Self, do_parse!(
            extern_: keyword!(extern) >>
            // TODO: this parses all literals, not just strings
            name: option!(syn!(Lit)) >>
            (Abi {
                extern_token: extern_,
                kind: match name {
                    Some(name) => AbiKind::Named(name),
                    None => AbiKind::Default,
                },
            })
        ));
    }
}

#[cfg(feature = "printing")]
mod printing {
    use super::*;
    use quote::{Tokens, ToTokens};

    impl ToTokens for TypeSlice {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.bracket_token.surround(tokens, |tokens| {
                self.ty.to_tokens(tokens);
            });
        }
    }

    impl ToTokens for TypeArray {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.bracket_token.surround(tokens, |tokens| {
                self.ty.to_tokens(tokens);
                self.semi_token.to_tokens(tokens);
                self.amt.to_tokens(tokens);
            });
        }
    }

    impl ToTokens for TypePtr {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.star_token.to_tokens(tokens);
            match self.ty.mutability {
                Mutability::Mutable(ref tok) => tok.to_tokens(tokens),
                Mutability::Immutable => {
                    TokensOrDefault(&self.const_token).to_tokens(tokens);
                }
            }
            self.ty.ty.to_tokens(tokens);
        }
    }

    impl ToTokens for TypeReference {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.and_token.to_tokens(tokens);
            self.lifetime.to_tokens(tokens);
            self.ty.mutability.to_tokens(tokens);
            self.ty.ty.to_tokens(tokens);
        }
    }

    impl ToTokens for TypeBareFn {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.ty.to_tokens(tokens)
        }
    }

    impl ToTokens for TypeNever {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.bang_token.to_tokens(tokens);
        }
    }

    impl ToTokens for TypeTup {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.paren_token.surround(tokens, |tokens| {
                self.tys.to_tokens(tokens);
                // XXX: I don't think (,) is a thing.
                self.lone_comma.to_tokens(tokens);
            })
        }
    }

    impl ToTokens for TypePath {
        fn to_tokens(&self, tokens: &mut Tokens) {
            PathTokens(&self.qself, &self.path).to_tokens(tokens);
        }
    }

    impl<'a> ToTokens for PathTokens<'a> {
        fn to_tokens(&self, tokens: &mut Tokens) {
            let qself = match *self.0 {
                Some(ref qself) => qself,
                None => return self.1.to_tokens(tokens),
            };
            qself.lt_token.to_tokens(tokens);
            qself.ty.to_tokens(tokens);

            // XXX: Gross.
            let pos = if qself.position > 0 && qself.position >= self.1.segments.len() {
                self.1.segments.len() - 1
            } else {
                qself.position
            };
            let mut segments = self.1.segments.iter();
            if pos > 0 {
                TokensOrDefault(&qself.as_token).to_tokens(tokens);
                self.1.leading_colon.to_tokens(tokens);
                for (i, segment) in (&mut segments).take(pos).enumerate() {
                    if i + 1 == pos {
                        segment.item().to_tokens(tokens);
                        qself.gt_token.to_tokens(tokens);
                        segment.delimiter().to_tokens(tokens);
                    } else {
                        segment.to_tokens(tokens);
                    }
                }
            } else {
                qself.gt_token.to_tokens(tokens);
                self.1.leading_colon.to_tokens(tokens);
            }
            for segment in segments {
                segment.to_tokens(tokens);
            }
        }
    }

    impl ToTokens for TypeTraitObject {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.bounds.to_tokens(tokens);
        }
    }

    impl ToTokens for TypeImplTrait {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.impl_token.to_tokens(tokens);
            self.bounds.to_tokens(tokens);
        }
    }

    impl ToTokens for TypeGroup {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.group_token.surround(tokens, |tokens| {
                self.ty.to_tokens(tokens);
            });
        }
    }

    impl ToTokens for TypeParen {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.paren_token.surround(tokens, |tokens| {
                self.ty.to_tokens(tokens);
            });
        }
    }

    impl ToTokens for TypeInfer {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.underscore_token.to_tokens(tokens);
        }
    }

    impl ToTokens for Mutability {
        fn to_tokens(&self, tokens: &mut Tokens) {
            if let Mutability::Mutable(ref t) = *self {
                t.to_tokens(tokens);
            }
        }
    }

    impl ToTokens for Path {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.leading_colon.to_tokens(tokens);
            self.segments.to_tokens(tokens);
        }
    }

    impl ToTokens for PathSegment {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.ident.to_tokens(tokens);
            self.parameters.to_tokens(tokens);
        }
    }

    impl ToTokens for PathParameters {
        fn to_tokens(&self, tokens: &mut Tokens) {
            match *self {
                PathParameters::None => {}
                PathParameters::AngleBracketed(ref parameters) => {
                    parameters.to_tokens(tokens);
                }
                PathParameters::Parenthesized(ref parameters) => {
                    parameters.to_tokens(tokens);
                }
            }
        }
    }

    impl ToTokens for AngleBracketedParameterData {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.turbofish.to_tokens(tokens);
            self.lt_token.to_tokens(tokens);
            self.lifetimes.to_tokens(tokens);
            if !self.lifetimes.empty_or_trailing() && !self.types.is_empty() {
                <Token![,]>::default().to_tokens(tokens);
            }
            self.types.to_tokens(tokens);
            if (
                // If we have no trailing delimiter after a non-empty types list, or
                !self.types.empty_or_trailing() ||
                // If we have no trailing delimiter after a non-empty lifetimes
                // list before an empty types list, and
                (self.types.is_empty() && !self.lifetimes.empty_or_trailing())) &&
                // We have some bindings, then we need a comma.
                !self.bindings.is_empty()
            {
                <Token![,]>::default().to_tokens(tokens);
            }
            self.bindings.to_tokens(tokens);
            self.gt_token.to_tokens(tokens);
        }
    }

    impl ToTokens for TypeBinding {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.ident.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
        }
    }

    impl ToTokens for ParenthesizedParameterData {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.paren_token.surround(tokens, |tokens| {
                self.inputs.to_tokens(tokens);
            });
            self.output.to_tokens(tokens);
        }
    }

    impl ToTokens for ReturnType {
        fn to_tokens(&self, tokens: &mut Tokens) {
            match *self {
                ReturnType::Default => {}
                ReturnType::Type(ref ty, ref arrow) => {
                    arrow.to_tokens(tokens);
                    ty.to_tokens(tokens);
                }
            }
        }
    }

    impl ToTokens for PolyTraitRef {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.bound_lifetimes.to_tokens(tokens);
            self.trait_ref.to_tokens(tokens);
        }
    }

    impl ToTokens for BareFnType {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.lifetimes.to_tokens(tokens);
            self.unsafety.to_tokens(tokens);
            self.abi.to_tokens(tokens);
            self.fn_token.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.inputs.to_tokens(tokens);
                if self.variadic.is_some() && !self.inputs.empty_or_trailing() {
                    <Token![,]>::default().to_tokens(tokens);
                }
                self.variadic.to_tokens(tokens);
            });
            self.output.to_tokens(tokens);
        }
    }

    impl ToTokens for BareFnArg {
        fn to_tokens(&self, tokens: &mut Tokens) {
            if let Some((ref name, ref colon)) = self.name {
                name.to_tokens(tokens);
                colon.to_tokens(tokens);
            }
            self.ty.to_tokens(tokens);
        }
    }

    impl ToTokens for BareFnArgName {
        fn to_tokens(&self, tokens: &mut Tokens) {
            match *self {
                BareFnArgName::Named(ref t) => t.to_tokens(tokens),
                BareFnArgName::Wild(ref t) => t.to_tokens(tokens),
            }
        }
    }

    impl ToTokens for Unsafety {
        fn to_tokens(&self, tokens: &mut Tokens) {
            match *self {
                Unsafety::Unsafe(ref t) => t.to_tokens(tokens),
                Unsafety::Normal => {
                    // nothing
                }
            }
        }
    }

    impl ToTokens for Abi {
        fn to_tokens(&self, tokens: &mut Tokens) {
            self.extern_token.to_tokens(tokens);
            match self.kind {
                AbiKind::Named(ref named) => named.to_tokens(tokens),
                AbiKind::Default => {}
            }
        }
    }
}
