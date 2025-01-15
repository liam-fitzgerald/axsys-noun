use axsys_noun::hoon;

#[proc_macro]
pub fn define_type(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    hoon::define_type(input.into()).into()
}
