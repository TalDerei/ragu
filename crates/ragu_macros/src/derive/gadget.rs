use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{
    AngleBracketedGenericArguments, Attribute, Data, DeriveInput, Error, Fields, GenericArgument,
    GenericParam, Generics, Ident, Lifetime, Result, parse_quote, spanned::Spanned,
};

use crate::{
    helpers::{GenericDriver, attr_is},
    path_resolution::RaguCorePath,
    substitution::{
        replace_driver_field_in_generic_param, replace_driver_field_in_where_predicate,
    },
};

/// Finds `#[ragu(name = path)]` among the given attributes and returns the path.
///
/// Returns `Ok(None)` if the attribute is not present. Returns an error if the
/// attribute is malformed or specified more than once.
fn extract_ragu_path(attrs: &[Attribute], name: &str) -> Result<Option<syn::Path>> {
    let mut found: Option<syn::Path> = None;
    for attr in attrs {
        if !attr.path().is_ident("ragu") {
            continue;
        }
        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident(name) {
                let value = meta.value()?;
                let path: syn::Path = value.parse()?;
                if found.is_some() {
                    return Err(meta.error(format!("duplicate `{name}` attribute")));
                }
                found = Some(path);
            } else if meta.input.peek(syn::Token![=]) {
                // Consume the value of an unrelated name-value entry so
                // `parse_nested_meta` can advance past it.
                let _value = meta.value()?;
                let _: syn::Expr = _value.parse()?;
            }
            Ok(())
        })?;
    }
    Ok(found)
}

/// Finds `#[ragu(name = "...")]` among the given attributes and parses the
/// string as a comma-separated list of where predicates.
///
/// Returns `Ok(None)` if the attribute is not present. Returns an error if the
/// attribute is malformed or specified more than once.
fn extract_ragu_where_predicates(
    attrs: &[Attribute],
    name: &str,
) -> Result<Option<syn::punctuated::Punctuated<syn::WherePredicate, syn::Token![,]>>> {
    let mut found = None;
    for attr in attrs {
        if !attr.path().is_ident("ragu") {
            continue;
        }
        attr.parse_nested_meta(|meta| {
            if meta.path.is_ident(name) {
                let value = meta.value()?;
                let lit: syn::LitStr = value.parse()?;
                let clause: syn::WhereClause = syn::parse_str(&format!("where {}", lit.value()))
                    .map_err(|e| meta.error(format!("invalid where predicates: {e}")))?;
                if found.is_some() {
                    return Err(meta.error(format!("duplicate `{name}` attribute")));
                }
                found = Some(clause.predicates);
            } else if meta.input.peek(syn::Token![=]) {
                let _value = meta.value()?;
                let _: syn::Expr = _value.parse()?;
            }
            Ok(())
        })?;
    }
    Ok(found)
}

impl GenericDriver {
    fn gadget_params(&self) -> AngleBracketedGenericArguments {
        let driver_ident = &self.ident;
        let lifetime = &self.lifetime;

        parse_quote!( <#lifetime, #driver_ident> )
    }

    fn kind_arguments(
        &self,
        ty_generics: &AngleBracketedGenericArguments,
        ragu_core_path: &RaguCorePath,
    ) -> AngleBracketedGenericArguments {
        let driver_ident = &self.ident;
        let static_lifetime = Lifetime::new("'static", Span::call_site());
        let current_lifetime = &self.lifetime;
        let args = ty_generics.args.iter().map(move |gp| { match gp {
            GenericArgument::Type(ty) if self.is_ty(ty) => parse_quote!( ::core::marker::PhantomData<<#driver_ident as #ragu_core_path::drivers::Driver<#current_lifetime>>::F> ),
            GenericArgument::Lifetime(lt) if self.is_lt(lt) => parse_quote!( #static_lifetime ),
            a => parse_quote!( #a ),
        }}).collect::<Vec<GenericArgument>>();
        parse_quote!( < #( #args ),* > )
    }

    fn rebind_arguments(
        &self,
        ty_generics: &AngleBracketedGenericArguments,
    ) -> AngleBracketedGenericArguments {
        let driver_ident = &self.ident;
        let lifetime = &self.lifetime;
        let args = ty_generics
            .args
            .iter()
            .map(move |gp| match gp {
                GenericArgument::Type(ty) if self.is_ty(ty) => parse_quote!( #driver_ident ),
                GenericArgument::Lifetime(lt) if self.is_lt(lt) => {
                    parse_quote!( #lifetime )
                }
                a => parse_quote!( #a ),
            })
            .collect::<Vec<GenericArgument>>();
        parse_quote!( < #( #args ),* > )
    }
}

pub fn derive(input: DeriveInput, ragu_core_path: RaguCorePath) -> Result<TokenStream> {
    let DeriveInput {
        ident: struct_ident,
        generics,
        data,
        attrs,
        ..
    } = &input;

    let enforce_equal_slice_override = extract_ragu_path(attrs, "enforce_equal_slice_with")?;
    let impl_where_predicates = extract_ragu_where_predicates(attrs, "impl_where")?;

    let driver = &GenericDriver::extract(generics)?;
    let driverfield_ident = format_ident!("DriverField");

    // impl_generics = <'a, 'b: 'a, C: Cycle, D: Driver, const N: usize>
    // ty_generics = <'a, 'b, C, D, N>
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let impl_generics = {
        let mut impl_generics: Generics = parse_quote!( #impl_generics );
        impl_generics.params.iter_mut().for_each(|gp| match gp {
            GenericParam::Type(ty) if ty.ident == driver.ident => {
                // Strip out driver attribute if present
                ty.attrs.retain(|a| !attr_is(a, "driver"));
            }
            _ => {}
        });
        impl_generics
    };
    let ty_generics: AngleBracketedGenericArguments = { parse_quote!( #ty_generics ) };

    let gadget_args = driver.gadget_params();

    enum FieldType {
        Value,
        Wire,
        Gadget,
        Phantom,
    }

    let fields: Vec<(Ident, FieldType, syn::Type)> = match data {
        Data::Struct(s) => {
            let fields = match &s.fields {
                Fields::Named(named) => &named.named,
                _ => {
                    return Err(Error::new(
                        s.struct_token.span(),
                        "Gadget derive only works on structs with named fields",
                    ));
                }
            };

            let mut res = vec![];

            for f in fields {
                let fid = f.ident.clone().expect("fields contains only named fields");
                let fty = f.ty.clone();
                let is_value = f.attrs.iter().any(|a| attr_is(a, "value"));
                let is_wire = f.attrs.iter().any(|a| attr_is(a, "wire"));
                let is_gadget = f.attrs.iter().any(|a| attr_is(a, "gadget"));
                let is_phantom = f.attrs.iter().any(|a| attr_is(a, "phantom"));

                match (is_value, is_wire, is_gadget, is_phantom) {
                    (true, false, false, false) => {
                        res.push((fid, FieldType::Value, fty));
                    }
                    (false, true, false, false) => {
                        res.push((fid, FieldType::Wire, fty));
                    }
                    (false, false, true, false) => {
                        res.push((fid, FieldType::Gadget, fty));
                    }
                    (false, false, false, true) => {
                        res.push((fid, FieldType::Phantom, fty));
                    }
                    (false, false, false, false) => {
                        // Default to gadget when no annotation is present
                        res.push((fid, FieldType::Gadget, fty));
                    }
                    _ => {
                        return Err(Error::new(
                            fid.span(),
                            "field cannot have multiple annotations; use only one of: #[ragu(value)], #[ragu(wire)], #[ragu(gadget)], or #[ragu(phantom)]",
                        ));
                    }
                }
            }

            res
        }
        _ => {
            return Err(Error::new(
                Span::call_site(),
                "Gadget derive only works on structs",
            ));
        }
    };

    let clone_impl_inits = fields.iter().map(|(id, ty, _)| {
        let init = match ty {
            FieldType::Value => {
                let driver_id = &driver.ident;
                quote! { {
                    use #ragu_core_path::maybe::Maybe;
                    #driver_id::just(|| self.#id.as_ref().take().clone())
                } }
            }
            _ => quote! { ::core::clone::Clone::clone(&self.#id) },
        };
        quote! { #id: #init }
    });

    // Build a where clause that merges the struct's own where clause with any
    // `#[ragu(impl_where = "...")]` predicates supplied by the user. These
    // extra bounds are applied only to the derived impls — not to the struct
    // definition — so they don't virally propagate to use sites.
    let impl_where_clause = {
        let mut predicates: syn::punctuated::Punctuated<syn::WherePredicate, syn::Token![,]> =
            where_clause
                .map(|wc| wc.predicates.clone())
                .unwrap_or_default();
        if let Some(extra) = &impl_where_predicates {
            for p in extra {
                predicates.push(p.clone());
            }
        }
        if predicates.is_empty() {
            quote! {}
        } else {
            quote! { where #predicates }
        }
    };

    let clone_impl = quote! {
        #[automatically_derived]
        impl #impl_generics ::core::clone::Clone for #struct_ident #ty_generics #impl_where_clause {
            fn clone(&self) -> Self {
                #struct_ident {
                    #( #clone_impl_inits, )*
                }
            }
        }
    };

    // Group gadget fields by type so same-kind fields can be batched
    // through `enforce_equal_gadget_slice` for reduced constraints.
    let mut gadget_groups: Vec<(String, Vec<Ident>)> = Vec::new();
    for (id, ft, fty) in &fields {
        if matches!(ft, FieldType::Gadget) {
            let key = quote!(#fty).to_string();
            if let Some(group) = gadget_groups.iter_mut().find(|(k, _)| k == &key) {
                group.1.push(id.clone());
            } else {
                gadget_groups.push((key, vec![id.clone()]));
            }
        }
    }

    let mut equality_calls: Vec<TokenStream> = Vec::new();
    let mut emitted_groups: Vec<String> = Vec::new();
    for (id, ft, fty) in &fields {
        match ft {
            FieldType::Wire => {
                equality_calls.push(
                    quote! { #ragu_core_path::drivers::Driver::enforce_equal(dr, &a.#id, &b.#id)? },
                );
            }
            FieldType::Gadget => {
                let key = quote!(#fty).to_string();
                let group = gadget_groups.iter().find(|(k, _)| k == &key).unwrap();
                if group.1.len() > 1 {
                    if !emitted_groups.contains(&key) {
                        emitted_groups.push(key);
                        let ids = &group.1;
                        let a_elems = ids
                            .iter()
                            .map(|id| quote! { ::core::clone::Clone::clone(&a.#id) });
                        let b_elems = ids
                            .iter()
                            .map(|id| quote! { ::core::clone::Clone::clone(&b.#id) });
                        equality_calls.push(quote! { {
                            let __a = [#(#a_elems),*];
                            let __b = [#(#b_elems),*];
                            #ragu_core_path::gadgets::Gadget::enforce_equal_slice(dr, &__a, &__b)?
                        } });
                    }
                } else {
                    equality_calls.push(
                        quote! { #ragu_core_path::gadgets::Gadget::enforce_equal(&a.#id, dr, &b.#id)? },
                    );
                }
            }
            _ => {}
        }
    }

    let kind_ty_arguments = driver.kind_arguments(&ty_generics, &ragu_core_path);

    let gadget_impl = {
        quote! {
            #[automatically_derived]
            impl #impl_generics #ragu_core_path::gadgets::Gadget #gadget_args for #struct_ident #ty_generics #impl_where_clause {
                type Kind = #struct_ident #kind_ty_arguments;
            }
        }
    };

    let gadget_kind_generic_params: Generics = {
        let mut params: Vec<GenericParam> = impl_generics
            .clone()
            .params
            .into_iter()
            .filter(|gp| match gp {
                // strip out driver
                GenericParam::Type(ty) if ty.ident == driver.ident => false,
                // strip out driver lifetime
                GenericParam::Lifetime(lt) if lt.lifetime.ident == driver.lifetime.ident => false,
                _ => true,
            })
            .collect();
        for param in &mut params {
            replace_driver_field_in_generic_param(param, &driver.ident, &driverfield_ident);
        }
        params.push(parse_quote!( #driverfield_ident: ::ff::Field ));

        parse_quote!( < #( #params ),* >)
    };

    let kind_subst_arguments = driver.kind_subst_arguments(&ty_generics);
    let rebind_arguments = driver.rebind_arguments(&ty_generics);

    let gadget_impl_inits = fields.iter().map(|(id, ty, _)| {
        let init = match ty {
            FieldType::Value => quote! {
                {
                    use #ragu_core_path::maybe::Maybe;

                    let tmp = just::<WM::Dst, _>(|| this.#id.as_ref().take().clone());
                    is_send(&tmp);
                    tmp
                }
            },
            FieldType::Wire => {
                quote! { #ragu_core_path::convert::WireMap::convert_wire(wm, &this.#id)? }
            }
            FieldType::Gadget => {
                quote! { #ragu_core_path::gadgets::Gadget::map(&this.#id, wm)? }
            }
            FieldType::Phantom => quote! { ::core::marker::PhantomData },
        };
        quote! { #id: #init }
    });

    // Transform the where clause for the GadgetKind impl by replacing D::F
    // with DriverField. Merges the struct's where clause with any
    // `#[ragu(impl_where)]` predicates.
    let kind_where_clause = {
        let mut predicates: syn::punctuated::Punctuated<syn::WherePredicate, syn::Token![,]> =
            where_clause
                .map(|wc| wc.predicates.clone())
                .unwrap_or_default();
        if let Some(extra) = &impl_where_predicates {
            for p in extra {
                predicates.push(p.clone());
            }
        }
        for predicate in predicates.iter_mut() {
            replace_driver_field_in_where_predicate(predicate, &driver.ident, &driverfield_ident);
        }
        if predicates.is_empty() {
            quote! {}
        } else {
            quote! { where #predicates }
        }
    };

    let gadgetkind_impl = {
        let driver_ident = &driver.ident;
        let driver_lifetime = &driver.lifetime;
        let enforce_equal_slice_method = enforce_equal_slice_override.as_ref().map(|path| {
            quote! {
                fn enforce_equal_gadget_slice<
                    #driver_lifetime,
                    D1: #ragu_core_path::drivers::Driver<#driver_lifetime, F = #driverfield_ident>,
                    D2: #ragu_core_path::drivers::Driver<
                        #driver_lifetime,
                        F = #driverfield_ident,
                        Wire = <D1 as #ragu_core_path::drivers::Driver<#driver_lifetime>>::Wire,
                    >,
                >(
                    dr: &mut D1,
                    a: &[#ragu_core_path::gadgets::Bound<#driver_lifetime, D2, Self>],
                    b: &[#ragu_core_path::gadgets::Bound<#driver_lifetime, D2, Self>],
                ) -> #ragu_core_path::Result<()> {
                    #path(dr, a, b)
                }
            }
        });
        quote! {
            #[automatically_derived]
            unsafe impl #gadget_kind_generic_params #ragu_core_path::gadgets::GadgetKind<#driverfield_ident> for #struct_ident #kind_subst_arguments #kind_where_clause {
                type Rebind<#driver_lifetime, #driver_ident: #ragu_core_path::drivers::Driver<#driver_lifetime, F = #driverfield_ident>> = #struct_ident #rebind_arguments;

                fn map_gadget<#driver_lifetime, 'dst, WM: #ragu_core_path::convert::WireMap<#driverfield_ident, Src: #ragu_core_path::drivers::Driver<#driver_lifetime, F = #driverfield_ident>, Dst: #ragu_core_path::drivers::Driver<'dst, F = #driverfield_ident>>>(
                    this: &#ragu_core_path::gadgets::Bound<#driver_lifetime, WM::Src, Self>,
                    wm: &mut WM,
                ) -> #ragu_core_path::Result<#ragu_core_path::gadgets::Bound<'dst, WM::Dst, Self>> {
                    fn is_send<T: Send>(_: &T) { }
                    fn just<D: #ragu_core_path::drivers::DriverTypes, R: Send>(f: impl FnOnce() -> R) -> #ragu_core_path::drivers::DriverValue<D, R> {
                        <#ragu_core_path::drivers::DriverValue<D, R> as #ragu_core_path::maybe::Maybe<R>>::just(f)
                    }

                    Ok(#struct_ident {
                        #( #gadget_impl_inits, )*
                    })
                }

                fn enforce_equal_gadget<#driver_lifetime, D1: #ragu_core_path::drivers::Driver<#driver_lifetime, F = #driverfield_ident>, D2: #ragu_core_path::drivers::Driver<#driver_lifetime, F = #driverfield_ident, Wire = <D1 as #ragu_core_path::drivers::Driver<#driver_lifetime>>::Wire>>(
                    dr: &mut D1,
                    a: &#ragu_core_path::gadgets::Bound<#driver_lifetime, D2, Self>,
                    b: &#ragu_core_path::gadgets::Bound<#driver_lifetime, D2, Self>,
                ) -> #ragu_core_path::Result<()> {
                    #( #equality_calls; )*
                    Ok(())
                }

                #enforce_equal_slice_method
            }
        }
    };

    Ok(quote! {
        #clone_impl

        #gadget_impl

        #gadgetkind_impl
    })
}

#[test]
fn test_fail_enum() {
    let input: DeriveInput = parse_quote! {
        #[derive(Gadget)]
        enum Boolean<'my_dr, #[ragu(driver)] MyD: ragu_core::Driver<'my_dr>> {
            Is(MyD::W),
            Not(MyD::W)
        }
    };

    assert!(
        derive(input, RaguCorePath::default()).is_err(),
        "Expected error for enum usage"
    );
}

#[test]
fn test_where_clause() {
    let input: DeriveInput = parse_quote! {
        #[derive(Gadget)]
        struct Boolean<'my_dr, #[ragu(driver)] MyD: ragu_core::Driver<'my_dr>>
            where MyD: Any
        {
            #[ragu(wire)]
            wire: MyD::W,
            #[ragu(value)]
            value: DriverValue<MyD, bool>,
        }
    };

    assert!(
        derive(input, RaguCorePath::default()).is_ok(),
        "Where clauses should be supported"
    );
}

#[test]
fn test_where_clause_driver_field_substitution() {
    let input: DeriveInput = parse_quote! {
        #[derive(Gadget)]
        struct Foo<'my_dr, #[ragu(driver)] MyD: ragu_core::Driver<'my_dr>>
            where MyD::F: PrimeField
        {
            #[ragu(wire)]
            wire: MyD::W,
            #[ragu(value)]
            value: DriverValue<MyD, bool>,
        }
    };

    let output =
        derive(input, RaguCorePath::default()).expect("Where clause with D::F should be supported");
    let code = output.to_string();

    // The GadgetKind impl's where clause should substitute MyD::F with the
    // DriverField ident. (The Clone and Gadget impls legitimately keep
    // MyD::F because they are still parameterized over MyD.)
    assert!(
        code.contains("DriverField : PrimeField"),
        "GadgetKind where clause should reference DriverField, not MyD::F"
    );
}

#[test]
fn test_fail_multi_annotations() {
    let input: DeriveInput = parse_quote! {
        #[derive(Gadget)]
        struct Boolean<'my_dr, #[ragu(driver)] MyD: ragu_core::Driver<'my_dr>> {
            #[ragu(wire)]
            wire: MyD::W,
            #[ragu(value)]
            #[ragu(wire)]
            value: DriverValue<MyD, bool>,
        }
    };

    assert!(
        derive(input, RaguCorePath::default()).is_err(),
        "Expected error for multiple annotations on field"
    );
}

#[test]
fn test_fail_unnamed_struct() {
    let input: DeriveInput = parse_quote! {
        #[derive(Gadget)]
        struct Boolean<'my_dr, #[ragu(driver)] MyD: ragu_core::Driver<'my_dr>>
        (
            MyD::W,
            Witness<'my_dr, MyD, bool>,
        );
    };

    assert!(
        derive(input, RaguCorePath::default()).is_err(),
        "Expected error for unnamed struct fields"
    );
}

#[rustfmt::skip]
#[test]
fn test_gadget_derive_boolean_customdriver() {
    use syn::parse_quote;

    let input: DeriveInput = parse_quote! {
        #[derive(Gadget)]
        struct Boolean<'my_dr, #[ragu(driver)] MyD: ragu_core::Driver<'my_dr>> {
            #[ragu(wire)]
            wire: MyD::W,
            #[ragu(value)]
            value: DriverValue<MyD, bool>,
        }
    };

    let result = derive(input, RaguCorePath::default()).unwrap();

    assert_eq!(
        result.to_string(),
        quote!(
            #[automatically_derived]
            impl<'my_dr, MyD: ragu_core::Driver<'my_dr> > ::core::clone::Clone for Boolean<'my_dr, MyD> {
                fn clone(&self) -> Self {
                    Boolean {
                        wire: ::core::clone::Clone::clone(&self.wire),
                        value: {
                            use ::ragu_core::maybe::Maybe;
                            MyD::just(|| self.value.as_ref().take().clone())
                        },
                    }
                }
            }
            #[automatically_derived]
            impl<'my_dr, MyD: ragu_core::Driver<'my_dr> > ::ragu_core::gadgets::Gadget<'my_dr, MyD>
                for Boolean<'my_dr, MyD>
            {
                type Kind =
                    Boolean<'static, ::core::marker::PhantomData< <MyD as ::ragu_core::drivers::Driver<'my_dr> >::F> >;
            }
            #[automatically_derived]
            unsafe impl<DriverField: ::ff::Field> ::ragu_core::gadgets::GadgetKind<DriverField>
                for Boolean<'static, ::core::marker::PhantomData<DriverField> >
            {
                type Rebind<'my_dr, MyD: ::ragu_core::drivers::Driver<'my_dr, F = DriverField>> =
                    Boolean<'my_dr, MyD>;

                fn map_gadget<'my_dr, 'dst, WM: ::ragu_core::convert::WireMap<DriverField, Src: ::ragu_core::drivers::Driver<'my_dr, F = DriverField>, Dst: ::ragu_core::drivers::Driver<'dst, F = DriverField>>>(
                    this: &::ragu_core::gadgets::Bound<'my_dr, WM::Src, Self>,
                    wm: &mut WM,
                ) -> ::ragu_core::Result<::ragu_core::gadgets::Bound<'dst, WM::Dst, Self>> {
                    fn is_send<T: Send>(_: &T) { }
                    fn just<D: ::ragu_core::drivers::DriverTypes, R: Send>(f: impl FnOnce() -> R) -> ::ragu_core::drivers::DriverValue<D, R> {
                        <::ragu_core::drivers::DriverValue<D, R> as ::ragu_core::maybe::Maybe<R>>::just(f)
                    }

                    Ok(Boolean {
                        wire: ::ragu_core::convert::WireMap::convert_wire(wm, &this.wire)?,
                        value: {
                            use ::ragu_core::maybe::Maybe;

                            let tmp = just::<WM::Dst, _>(|| this.value.as_ref().take().clone());
                            is_send(&tmp);
                            tmp
                        },
                    })
                }

                fn enforce_equal_gadget<
                    'my_dr,
                    D1: ::ragu_core::drivers::Driver<'my_dr, F = DriverField>,
                    D2: ::ragu_core::drivers::Driver<
                            'my_dr,
                            F = DriverField,
                            Wire = <D1 as ::ragu_core::drivers::Driver<'my_dr>>::Wire>>
                (
                    dr: &mut D1,
                    a: &::ragu_core::gadgets::Bound<'my_dr, D2, Self>,
                    b: &::ragu_core::gadgets::Bound<'my_dr, D2, Self>,
                ) -> ::ragu_core::Result<()> {
                    ::ragu_core::drivers::Driver::enforce_equal(dr, &a.wire, &b.wire)?;
                    Ok(())
                }
            }
        ).to_string()
    );
}

#[rustfmt::skip]
#[test]
fn test_gadget_derive() {
    use syn::parse_quote;

    let input: DeriveInput = parse_quote! {
        #[derive(Gadget)]
        pub struct MyGadget<'mydr, #[ragu(driver)] MyD: Driver<'mydr>, C: Blah<MyD::F>, const N: usize> {
            #[ragu(value)]
            witness_field: DriverValue<MyD, MyD::F>,
            #[ragu(wire)]
            wire_field: MyD::W,
            #[ragu(gadget)]
            map_field: Lol<'mydr, MyD>,
            #[ragu(phantom)]
            phantom_field: ::core::marker::PhantomData<C>,
        }
    };

    let result = derive(input, RaguCorePath::default()).unwrap();

    assert_eq!(
        result.to_string(),
        quote!(
            #[automatically_derived]
            impl<'mydr, MyD: Driver<'mydr>, C: Blah<MyD::F>, const N: usize> ::core::clone::Clone for MyGadget<'mydr, MyD, C, N> {
                fn clone(&self) -> Self {
                    MyGadget {
                        witness_field: {
                            use ::ragu_core::maybe::Maybe;
                            MyD::just(|| self.witness_field.as_ref().take().clone())
                        },
                        wire_field: ::core::clone::Clone::clone(&self.wire_field),
                        map_field: ::core::clone::Clone::clone(&self.map_field),
                        phantom_field: ::core::clone::Clone::clone(&self.phantom_field),
                    }
                }
            }

            #[automatically_derived]
            impl<'mydr, MyD: Driver<'mydr>, C: Blah<MyD::F>, const N: usize> ::ragu_core::gadgets::Gadget<'mydr, MyD> for MyGadget<'mydr, MyD, C, N> {
                type Kind = MyGadget<'static, ::core::marker::PhantomData< <MyD as ::ragu_core::drivers::Driver<'mydr> >::F >, C, N>;
            }

            #[automatically_derived]
            unsafe impl<C: Blah<DriverField>, const N: usize, DriverField: ::ff::Field> ::ragu_core::gadgets::GadgetKind<DriverField>
                for MyGadget<'static, ::core::marker::PhantomData< DriverField >, C, N>
            {
                type Rebind<'mydr, MyD: ::ragu_core::drivers::Driver<'mydr, F = DriverField>> = MyGadget<'mydr, MyD, C, N>;

                fn map_gadget<'mydr, 'dst, WM: ::ragu_core::convert::WireMap<DriverField, Src: ::ragu_core::drivers::Driver<'mydr, F = DriverField>, Dst: ::ragu_core::drivers::Driver<'dst, F = DriverField>>>(
                    this: &::ragu_core::gadgets::Bound<'mydr, WM::Src, Self>,
                    wm: &mut WM,
                ) -> ::ragu_core::Result<::ragu_core::gadgets::Bound<'dst, WM::Dst, Self>> {
                    fn is_send<T: Send>(_: &T) { }
                    fn just<D: ::ragu_core::drivers::DriverTypes, R: Send>(f: impl FnOnce() -> R) -> ::ragu_core::drivers::DriverValue<D, R> {
                        <::ragu_core::drivers::DriverValue<D, R> as ::ragu_core::maybe::Maybe<R>>::just(f)
                    }

                    Ok(MyGadget {
                        witness_field: {
                            use ::ragu_core::maybe::Maybe;

                            let tmp = just::<WM::Dst, _>(|| this.witness_field.as_ref().take().clone());
                            is_send(&tmp);
                            tmp
                        },
                        wire_field: ::ragu_core::convert::WireMap::convert_wire(wm, &this.wire_field)?,
                        map_field: ::ragu_core::gadgets::Gadget::map(&this.map_field, wm)?,
                        phantom_field: ::core::marker::PhantomData,
                    })
                }

                fn enforce_equal_gadget<
                    'mydr,
                    D1: ::ragu_core::drivers::Driver<'mydr, F = DriverField>,
                    D2: ::ragu_core::drivers::Driver<
                            'mydr,
                            F = DriverField,
                            Wire = <D1 as ::ragu_core::drivers::Driver<'mydr>>::Wire>>
                (
                    dr: &mut D1,
                    a: &::ragu_core::gadgets::Bound<'mydr, D2, Self>,
                    b: &::ragu_core::gadgets::Bound<'mydr, D2, Self>,
                ) -> ::ragu_core::Result<()> {
                    ::ragu_core::drivers::Driver::enforce_equal(dr, &a.wire_field, &b.wire_field)?;
                    ::ragu_core::gadgets::Gadget::enforce_equal(&a.map_field, dr, &b.map_field)?;
                    Ok(())
                }
            }

        ).to_string()
    );
}

#[rustfmt::skip]
#[test]
fn test_gadget_derive_default_gadget() {
    use syn::parse_quote;

    // Test that gadget fields are assumed by default (no annotation needed)
    let input: DeriveInput = parse_quote! {
        #[derive(Gadget)]
        pub struct CompositeGadget<'mydr, #[ragu(driver)] MyD: Driver<'mydr>> {
            // No annotation: should default to gadget
            field_a: SomeGadget<'mydr, MyD>,
            // Explicit annotation still works
            #[ragu(gadget)]
            field_b: AnotherGadget<'mydr, MyD>,
            // Wire and value still need explicit annotations
            #[ragu(wire)]
            wire_field: MyD::W,
            #[ragu(value)]
            value_field: DriverValue<MyD, bool>,
        }
    };

    let result = derive(input, RaguCorePath::default()).unwrap();

    // Verify both field_a (no annotation) and field_b (explicit annotation) are treated as gadgets
    let result_str = result.to_string();

    // Both should call Gadget::map
    assert!(result_str.contains("Gadget :: map (& this . field_a"), "missing Gadget::map for field_a");
    assert!(result_str.contains("Gadget :: map (& this . field_b"), "missing Gadget::map for field_b");

    // Both should call Gadget::enforce_equal
    assert!(result_str.contains("Gadget :: enforce_equal (& a . field_a"), "missing enforce_equal for field_a");
    assert!(result_str.contains("Gadget :: enforce_equal (& a . field_b"), "missing enforce_equal for field_b");

    // Wire should use Driver::enforce_equal
    assert!(result_str.contains("Driver :: enforce_equal (dr , & a . wire_field"), "missing Driver::enforce_equal for wire_field");

    // Wire should use WireMap::convert_wire
    assert!(result_str.contains("WireMap :: convert_wire (wm , & this . wire_field"), "missing WireMap::convert_wire");
}

#[test]
fn test_enforce_equal_slice_with_override() {
    let input: DeriveInput = parse_quote! {
        #[derive(Gadget)]
        #[ragu(enforce_equal_slice_with = my_packed_eq)]
        struct Boolean<'dr, #[ragu(driver)] D: ragu_core::Driver<'dr>> {
            #[ragu(wire)]
            wire: D::W,
            #[ragu(value)]
            value: DriverValue<D, bool>,
        }
    };

    let result = derive(input, RaguCorePath::default()).unwrap();
    let result_str = result.to_string();

    // The GadgetKind impl should include an `enforce_equal_gadget_slice` method
    // that delegates to the user's function.
    assert!(
        result_str.contains("fn enforce_equal_gadget_slice"),
        "missing enforce_equal_gadget_slice override",
    );
    assert!(
        result_str.contains("my_packed_eq (dr , a , b)"),
        "override should delegate to user's function",
    );
}

#[test]
fn test_enforce_equal_slice_without_override() {
    // Without the attribute, no custom slice method should be emitted.
    let input: DeriveInput = parse_quote! {
        #[derive(Gadget)]
        struct Boolean<'dr, #[ragu(driver)] D: ragu_core::Driver<'dr>> {
            #[ragu(wire)]
            wire: D::W,
            #[ragu(value)]
            value: DriverValue<D, bool>,
        }
    };

    let result = derive(input, RaguCorePath::default()).unwrap();
    let result_str = result.to_string();

    assert!(
        !result_str.contains("fn enforce_equal_gadget_slice"),
        "should not emit slice override without attribute",
    );
}
