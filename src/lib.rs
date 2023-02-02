#![forbid(
    rust_2018_idioms,
    future_incompatible,
    elided_lifetimes_in_paths,
    unsafe_code
)]
#![warn(
    missing_debug_implementations,
    missing_docs,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unused_import_braces,
    unused_qualifications
)]

//! An attribute to create an atomic wrapper around a C-style enum.
//!
//! Internally, the generated wrapper uses an `AtomicT` to store the value.
//! The atomic operations have the same semantics as the equivalent operations
//! of `AtomicT`.
//!
//! `AtomicT` is `AtomicUsize` by default
//! or another atomic variant based on the enum's `repr`.
//!
//! # Example
//!
//! ```
//! # use atomic_enum::atomic_enum;
//! # use std::sync::atomic::Ordering;
//! #[atomic_enum]
//! #[derive(PartialEq)]
//! enum CatState {
//!     Dead = 0,
//!     BothDeadAndAlive,
//!     Alive,
//! }
//!
//! let state = AtomicCatState::new(CatState::Dead);
//! state.store(CatState::Alive, Ordering::Relaxed);
//!
//! assert_eq!(state.load(Ordering::Relaxed), CatState::Alive);
//! ```
//!
//! This attribute does not use or generate any unsafe code.
//!
//! The crate can be used in a `#[no_std]` environment.

use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, quote_spanned};
use syn::{
    parse_macro_input, spanned::Spanned, Attribute, Ident, ItemEnum, Meta, NestedMeta, Variant,
    Visibility,
};

fn enum_definition<'a>(
    attrs: impl IntoIterator<Item = Attribute>,
    vis: &Visibility,
    ident: &Ident,
    variants: impl IntoIterator<Item = &'a Variant>,
) -> TokenStream2 {
    let attrs = attrs.into_iter();
    let variants = variants.into_iter();

    quote! {
        #(#attrs)*
        #[derive(Debug, Clone, Copy)]
        #vis enum #ident {
            #( #variants ),*
        }
    }
}

fn atomic_enum_definition(
    vis: &Visibility,
    ident: &Ident,
    atomic_ident: &Ident,
    atomic_target_type: &Ident,
) -> TokenStream2 {
    let atomic_ident_docs = format!(
        "A wrapper around [`{ident}`] which can be safely shared between threads.

This type uses an `{atomic_target_type}` to store the enum value.

[`{ident}`]: enum.{ident}.html"
    );

    quote! {
        #[doc = #atomic_ident_docs]
        #vis struct #atomic_ident(core::sync::atomic::#atomic_target_type);
    }
}

fn enum_to_type(ident: &Ident, target_type: &Ident) -> TokenStream2 {
    let name = Ident::new(&format!("to_{target_type}"), Span::call_site());
    quote! {
        const fn #name(val: #ident) -> #target_type {
            val as #target_type
        }
    }
}

fn enum_from_type(
    ident: &Ident,
    variants: impl IntoIterator<Item = Variant>,
    target_type: &Ident,
) -> TokenStream2 {
    let variants_with_const_names: Vec<_> = variants
        .into_iter()
        .map(|v| v.ident)
        .map(|id| {
            let c_id = Ident::new(
                &format!("{}_{}", target_type.to_string().to_uppercase(), &id),
                id.span(),
            );
            (id, c_id)
        })
        .collect();

    let variant_consts = variants_with_const_names
        .iter()
        .map(|(id, c_id)| quote! { const #c_id: #target_type = #ident::#id as #target_type; });

    let variants_back = variants_with_const_names
        .iter()
        .map(|(id, c_id)| quote! { #c_id => #ident::#id, });

    let name = Ident::new(&format!("from_{target_type}"), Span::call_site());
    quote! {
        fn #name(val: #target_type) -> #ident {
            #![allow(non_upper_case_globals)]
            #(#variant_consts)*

            match val {
                #(#variants_back)*
                _ => panic!("Invalid enum discriminant"),
            }
        }
    }
}

fn atomic_enum_new(
    ident: &Ident,
    atomic_ident: &Ident,
    target_type: &Ident,
    atomic_target_type: &Ident,
) -> TokenStream2 {
    let to = Ident::new(&format!("to_{target_type}"), Span::call_site());
    let atomic_ident_docs = format!(
        "Creates a new atomic [`{ident}`].

[`{ident}`]: enum.{ident}.html"
    );

    quote! {
        #[doc = #atomic_ident_docs]
        pub const fn new(v: #ident) -> #atomic_ident {
            #atomic_ident(core::sync::atomic::#atomic_target_type::new(Self::#to(v)))
        }
    }
}

fn atomic_enum_into_inner(ident: &Ident, target_type: &Ident) -> TokenStream2 {
    let from = Ident::new(&format!("from_{target_type}"), Span::call_site());
    quote! {
        /// Consumes the atomic and returns the contained value.
        ///
        /// This is safe because passing self by value guarantees that no other threads are concurrently accessing the atomic data.
        pub fn into_inner(self) -> #ident {
            Self::#from(self.0.into_inner())
        }
    }
}

fn atomic_enum_set(ident: &Ident, target_type: &Ident) -> TokenStream2 {
    let to = Ident::new(&format!("to_{target_type}"), Span::call_site());
    quote! {
        /// Sets the value of the atomic without performing an atomic operation.
        ///
        /// This is safe because the mutable reference guarantees that no other threads are concurrently accessing the atomic data.
        pub fn set(&mut self, v: #ident) {
            *self.0.get_mut() = Self::#to(v);
        }
    }
}

fn atomic_enum_get(ident: &Ident, target_type: &Ident) -> TokenStream2 {
    let from = Ident::new(&format!("from_{target_type}"), Span::call_site());
    quote! {
        /// Gets the value of the atomic without performing an atomic operation.
        ///
        /// This is safe because the mutable reference guarantees that no other threads are concurrently accessing the atomic data.
        pub fn get(&mut self) -> #ident {
            Self::#from(*self.0.get_mut())
        }
    }
}

fn atomic_enum_swap_mut(ident: &Ident) -> TokenStream2 {
    quote! {
        /// Stores a value into the atomic, returning the previous value, without performing an atomic operation.
        ///
        /// This is safe because the mutable reference guarantees that no other threads are concurrently accessing the atomic data.
        pub fn swap_mut(&mut self, v: #ident) -> #ident {
            let r = self.get();
            self.set(v);
            r
        }
    }
}

fn atomic_enum_load(ident: &Ident, target_type: &Ident) -> TokenStream2 {
    let name = Ident::new(&format!("from_{target_type}"), Span::call_site());
    quote! {
        /// Loads a value from the atomic.
        ///
        /// `load` takes an `Ordering` argument which describes the memory ordering of this operation. Possible values are `SeqCst`, `Acquire` and `Relaxed`.
        ///
        /// # Panics
        ///
        /// Panics if order is `Release` or `AcqRel`.
        pub fn load(&self, order: core::sync::atomic::Ordering) -> #ident {
            Self::#name(self.0.load(order))
        }
    }
}

fn atomic_enum_store(ident: &Ident, target_type: &Ident) -> TokenStream2 {
    let to = Ident::new(&format!("to_{target_type}"), Span::call_site());
    quote! {
        /// Stores a value into the atomic.
        ///
        /// `store` takes an `Ordering` argument which describes the memory ordering of this operation. Possible values are `SeqCst`, `Release` and `Relaxed`.
        ///
        /// # Panics
        ///
        /// Panics if order is `Acquire` or `AcqRel`.
        pub fn store(&self, val: #ident, order: core::sync::atomic::Ordering) {
            self.0.store(Self::#to(val), order)
        }
    }
}

fn atomic_enum_swap(ident: &Ident, target_type: &Ident) -> TokenStream2 {
    let to = Ident::new(&format!("to_{target_type}"), Span::call_site());
    let from = Ident::new(&format!("from_{target_type}"), Span::call_site());
    quote! {
        /// Stores a value into the atomic, returning the previous value.
        ///
        /// `swap` takes an `Ordering` argument which describes the memory ordering of this operation.
        /// All ordering modes are possible. Note that using `Acquire` makes the store part of this operation `Relaxed`,
        /// and using `Release` makes the load part `Relaxed`.
        pub fn swap(&self, val: #ident, order: core::sync::atomic::Ordering) -> #ident {
            Self::#from(self.0.swap(Self::#to(val), order))
        }
    }
}

fn atomic_enum_compare_and_swap(ident: &Ident, target_type: &Ident) -> TokenStream2 {
    let to = Ident::new(&format!("to_{target_type}"), Span::call_site());
    let from = Ident::new(&format!("from_{target_type}"), Span::call_site());
    quote! {
        /// Stores a value into the atomic if the current value is the same as the `current` value.
        ///
        /// The return value is always the previous value. If it is equal to `current`, then the value was updated.
        ///
        /// `compare_and_swap` also takes an `Ordering` argument which describes the memory ordering of this operation.
        /// Notice that even when using `AcqRel`, the operation might fail and hence just perform an `Acquire` load, but
        /// not have `Release` semantics. Using `Acquire` makes the store part of this operation `Relaxed` if it happens,
        /// and using `Release` makes the load part `Relaxed`.
        #[allow(deprecated)]
        #[deprecated(note = "Use `compare_exchange` or `compare_exchange_weak` instead")]
        pub fn compare_and_swap(
            &self,
            current: #ident,
            new: #ident,
            order: core::sync::atomic::Ordering
        ) -> #ident {
            Self::#from(self.0.compare_and_swap(
                Self::#to(current),
                Self::#to(new),
                order
            ))
        }
    }
}

fn atomic_enum_compare_exchange(ident: &Ident, target_type: &Ident) -> TokenStream2 {
    let to = Ident::new(&format!("to_{target_type}"), Span::call_site());
    let from = Ident::new(&format!("from_{target_type}"), Span::call_site());
    quote! {
        /// Stores a value into the atomic if the current value is the same as the `current` value.
        ///
        /// The return value is a result indicating whether the new value was written and containing the previous value.
        /// On success this value is guaranteed to be equal to `current`.
        ///
        /// `compare_exchange` takes two `Ordering` arguments to describe the memory ordering of this operation. The first
        /// describes the required ordering if the operation succeeds while the second describes the required ordering when
        /// the operation fails. Using `Acquire` as success ordering makes the store part of this operation `Relaxed`, and
        /// using `Release` makes the successful load `Relaxed`. The failure ordering can only be `SeqCst`, `Acquire` or
        /// `Relaxed` and must be equivalent to or weaker than the success ordering.
        pub fn compare_exchange(
            &self,
            current: #ident,
            new: #ident,
            success: core::sync::atomic::Ordering,
            failure: core::sync::atomic::Ordering
        ) -> Result<#ident, #ident> {
            self.0
                .compare_exchange(
                    Self::#to(current),
                    Self::#to(new),
                    success,
                    failure
                )
                .map(Self::#from)
                .map_err(Self::#from)
        }
    }
}

fn atomic_enum_compare_exchange_weak(ident: &Ident, target_type: &Ident) -> TokenStream2 {
    let to = Ident::new(&format!("to_{target_type}"), Span::call_site());
    let from = Ident::new(&format!("from_{target_type}"), Span::call_site());
    quote! {
        /// Stores a value into the atomic if the current value is the same as the `current` value.
        ///
        /// Unlike `compare_exchange`, this function is allowed to spuriously fail even when the comparison succeeds,
        /// which can result in more efficient code on some platforms. The return value is a result indicating whether
        /// the new value was written and containing the previous value.
        ///
        /// `compare_exchange_weak` takes two `Ordering` arguments to describe the memory ordering of this operation.
        /// The first describes the required ordering if the operation succeeds while the second describes the required
        /// ordering when the operation fails. Using `Acquire` as success ordering makes the store part of this operation
        /// `Relaxed`, and using `Release` makes the successful load `Relaxed`. The failure ordering can only be `SeqCst`,
        /// `Acquire` or `Relaxed` and must be equivalent to or weaker than the success ordering.
        pub fn compare_exchange_weak(
            &self,
            current: #ident,
            new: #ident,
            success: core::sync::atomic::Ordering,
            failure: core::sync::atomic::Ordering
        ) -> Result<#ident, #ident> {
            self.0
                .compare_exchange_weak(
                    Self::#to(current),
                    Self::#to(new),
                    success,
                    failure
                )
                .map(Self::#from)
                .map_err(Self::#from)
        }
    }
}

fn from_impl(ident: &Ident, atomic_ident: &Ident) -> TokenStream2 {
    quote! {
        impl From<#ident> for #atomic_ident {
            fn from(val: #ident) -> #atomic_ident {
                #atomic_ident::new(val)
            }
        }
    }
}

fn debug_impl(atomic_ident: &Ident) -> TokenStream2 {
    quote! {
        impl core::fmt::Debug for #atomic_ident {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                self.load(core::sync::atomic::Ordering::SeqCst).fmt(f)
            }
        }
    }
}

fn target_type<'a>(attrs: impl IntoIterator<Item = &'a Attribute>) -> Ident {
    let mut ident = None;
    for attr in attrs {
        if !attr.path.is_ident("repr") {
            continue;
        }

        let list = match attr.parse_meta() {
            Ok(Meta::List(list)) => list,
            Ok(_) => continue,
            Err(e) => panic!("can't parse repr: {e}"),
        };

        for meta in list.nested {
            match meta {
                NestedMeta::Meta(Meta::Path(p)) => {
                    ident = Some(p.get_ident().expect("need repr ident").clone());
                    break;
                }
                _ => panic!("not supported"),
            }
        }

        if ident.is_some() {
            break;
        }
    }

    ident.unwrap_or_else(|| Ident::new("usize", Span::call_site()))
}

fn atomic_target_type(typ: &Ident) -> Ident {
    let typ = typ.to_string();
    let f = typ[0..1].to_uppercase();
    let rest = &typ[1..];
    Ident::new(&format!("Atomic{f}{rest}"), Span::call_site())
}

#[proc_macro_attribute]
/// Creates an atomic wrapper around a C-style enum.
///
/// The generated type is a wrapper around `AtomicT` that transparently
/// converts between the stored integer and the enum type. This attribute
/// also automatically derives the `Debug`, `Copy` and `Clone` traits on
/// the enum type.
///
/// `AtomicT` is `AtomicUsize` by default
/// or another atomic variant based on the enum's `repr`.
///
/// The name of the atomic type is the name of the enum type, prefixed with
/// `Atomic`.
///
/// ```
/// # use atomic_enum::atomic_enum;
/// #[atomic_enum]
/// enum State {
///     On,
///     Off,
/// }
///
/// let state = AtomicState::new(State::Off);
/// ```
///
/// The name can be overridden by passing an identifier
/// as an argument to the attribute.
///
/// ```
/// # use atomic_enum::atomic_enum;
/// #[atomic_enum(StateAtomic)]
/// enum State {
///     On,
///     Off,
/// }
///
/// let state = StateAtomic::new(State::Off);
/// ```
pub fn atomic_enum(args: TokenStream, input: TokenStream) -> TokenStream {
    // Parse the input
    let ItemEnum {
        attrs,
        vis,
        ident,
        generics,
        variants,
        ..
    } = parse_macro_input!(input as ItemEnum);

    // We only support C-style enums: No generics, no fields
    if !generics.params.is_empty() {
        let span = generics.span();
        let err = quote_spanned! {span=> compile_error!("Expected an enum without generics."); };
        return err.into();
    }

    for variant in variants.iter() {
        if !matches!(variant.fields, syn::Fields::Unit) {
            let span = variant.fields.span();
            let err =
                quote_spanned! {span=> compile_error!("Expected a variant without fields."); };
            return err.into();
        }
    }

    let target_type = target_type(&attrs);
    let atomic_target_type = atomic_target_type(&target_type);

    // Define the enum
    let mut output = enum_definition(attrs, &vis, &ident, &variants);

    // Define the atomic wrapper
    let atomic_ident = parse_macro_input!(args as Option<Ident>)
        .unwrap_or_else(|| Ident::new(&format!("Atomic{ident}"), ident.span()));
    output.extend(atomic_enum_definition(
        &vis,
        &ident,
        &atomic_ident,
        &atomic_target_type,
    ));

    // Write the impl block for the atomic wrapper
    let enum_to_type = enum_to_type(&ident, &target_type);
    let enum_from_type = enum_from_type(&ident, variants, &target_type);
    let atomic_enum_new = atomic_enum_new(&ident, &atomic_ident, &target_type, &atomic_target_type);
    let atomic_enum_into_inner = atomic_enum_into_inner(&ident, &target_type);
    let atomic_enum_set = atomic_enum_set(&ident, &target_type);
    let atomic_enum_get = atomic_enum_get(&ident, &target_type);
    let atomic_enum_swap_mut = atomic_enum_swap_mut(&ident);
    let atomic_enum_load = atomic_enum_load(&ident, &target_type);
    let atomic_enum_store = atomic_enum_store(&ident, &target_type);
    let atomic_enum_swap = atomic_enum_swap(&ident, &target_type);
    let atomic_enum_compare_and_swap = atomic_enum_compare_and_swap(&ident, &target_type);
    let atomic_enum_compare_exchange = atomic_enum_compare_exchange(&ident, &target_type);
    let atomic_enum_compare_exchange_weak = atomic_enum_compare_exchange_weak(&ident, &target_type);

    output.extend(quote! {
        impl #atomic_ident {
            #enum_to_type
            #enum_from_type
            #atomic_enum_new
            #atomic_enum_into_inner
            #atomic_enum_set
            #atomic_enum_get
            #atomic_enum_swap_mut
            #atomic_enum_load
            #atomic_enum_store
            #atomic_enum_swap
            #atomic_enum_compare_and_swap
            #atomic_enum_compare_exchange
            #atomic_enum_compare_exchange_weak
        }
    });

    // Implement the from and debug traits
    output.extend(from_impl(&ident, &atomic_ident));
    output.extend(debug_impl(&atomic_ident));

    output.into()
}
