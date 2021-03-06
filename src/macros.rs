macro_rules! ast_struct {
    (
        $(#[$attr:meta])*
        pub struct $name:ident #full $($rest:tt)*
    ) => {
        #[cfg(feature = "full")]
        $(#[$attr])*
        #[cfg_attr(feature = "extra-traits", derive(Debug, Eq, PartialEq, Hash))]
        #[cfg_attr(feature = "clone-impls", derive(Clone))]
        pub struct $name $($rest)*

        #[cfg(not(feature = "full"))]
        $(#[$attr])*
        #[cfg_attr(feature = "extra-traits", derive(Debug, Eq, PartialEq, Hash))]
        #[cfg_attr(feature = "clone-impls", derive(Clone))]
        pub struct $name {
            _noconstruct: (),
        }
    };

    (
        $(#[$attr:meta])*
        pub struct $name:ident $($rest:tt)*
    ) => {
        $(#[$attr])*
        #[cfg_attr(feature = "extra-traits", derive(Debug, Eq, PartialEq, Hash))]
        #[cfg_attr(feature = "clone-impls", derive(Clone))]
        pub struct $name $($rest)*
    };
}

macro_rules! ast_enum {
    (
        $(#[$enum_attr:meta])*
        pub enum $name:ident { $($variants:tt)* }
    ) => (
        $(#[$enum_attr])*
        #[cfg_attr(feature = "extra-traits", derive(Debug, Eq, PartialEq, Hash))]
        #[cfg_attr(feature = "clone-impls", derive(Clone))]
        pub enum $name {
            $($variants)*
        }
    )
}

macro_rules! ast_enum_of_structs {
    (
        $(#[$enum_attr:meta])*
        pub enum $name:ident {
            $(
                $(#[$variant_attr:meta])*
                pub $variant:ident($member:ident $($rest:tt)*),
            )*
        }

        $($remaining:tt)*
    ) => (
        ast_enum! {
            $(#[$enum_attr])*
            pub enum $name {
                $(
                    $(#[$variant_attr])*
                    $variant($member),
                )*
            }
        }

        $(
            maybe_ast_struct! {
                $(#[$variant_attr])*
                pub struct $member $($rest)*
            }

            impl From<$member> for $name {
                fn from(e: $member) -> $name {
                    $name::$variant(e)
                }
            }
        )*

        #[cfg(feature = "printing")]
        generate_to_tokens! {
            $($remaining)*
            enum $name { $($variant [$($rest)*],)* }
        }
    )
}

#[cfg(feature = "printing")]
macro_rules! generate_to_tokens {
    (do_not_generate_to_tokens $($foo:tt)*) => ();

    (enum $name:ident { $($variant:ident [$($rest:tt)*],)* }) => (
        impl ::quote::ToTokens for $name {
            fn to_tokens(&self, tokens: &mut ::quote::Tokens) {
                match *self {
                    $(
                        $name::$variant(ref _e) =>
                            to_tokens_call!(_e, tokens, $($rest)*),
                    )*
                }
            }
        }
    );
}

#[cfg(all(feature = "printing", feature = "full"))]
macro_rules! to_tokens_call {
    ($e:ident, $tokens:ident, $($rest:tt)*) => {
        $e.to_tokens($tokens)
    };
}

#[cfg(all(feature = "printing", not(feature = "full")))]
macro_rules! to_tokens_call {
    // If the variant is marked as #full, don't auto-generate to-tokens for it.
    ($e:ident, $tokens:ident, #full $($rest:tt)*) => {
        unreachable!()
    };
    ($e:ident, $tokens:ident, $($rest:tt)*) => {
        $e.to_tokens($tokens)
    };
}

macro_rules! maybe_ast_struct {
    (
        $(#[$attr:meta])*
        pub struct $name:ident
    ) => ();

    ($($rest:tt)*) => (ast_struct! { $($rest)* });
}

#[cfg(all(feature = "full", feature = "parsing"))]
macro_rules! impl_synom {
    ($t:ident $description:tt $($parser:tt)+) => {
        impl Synom for $t {
            named!(parse -> Self, $($parser)+);

            fn description() -> Option<&'static str> {
                Some($description)
            }
        }
    }
}
