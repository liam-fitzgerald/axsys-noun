//! A library for parsing a minimal subset of Hoon.
use std::collections::HashMap;

use crate::cell::axes::peg;
use crate::Atom;
use nom::{
    bytes::complete::tag,
    combinator::map, IResult,
};
use nom_supreme::error::ErrorTree;
use proc_macro2::TokenStream;
use quote::quote;

pub type IRes<I, O> = IResult<I, O, ErrorTree<I>>;

#[derive(Debug, PartialEq, Clone)]
pub struct AtomType {
    pub aura: String,
    pub cold: Option<Atom>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FaceType {
    pub face: String,
    pub ty: Box<HoonType>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct LikeType {
    pub like: String,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TupleType {
    pub tuple: Vec<Box<HoonType>>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct ListType {
    pub list: Box<HoonType>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct CoreType {
    pub core: HashMap<String, Box<HoonType>>,
}

#[derive(Debug, PartialEq, Clone)]
pub enum HoonType {
    Atom(AtomType),
    Face(FaceType),
    Like(LikeType),
    Tuple(TupleType),
    List(ListType),
    Core(CoreType),
}

mod parse {
    
    

    use super::*;
    use nom::branch::alt as pose;
    use nom::bytes::complete::{is_not, tag as jest};
    use nom::character::complete::{multispace0, multispace1, satisfy};
    use nom::character::complete::{char, newline};
    use nom::character::{is_alphabetic, is_alphanumeric};
    use nom::combinator::map as cook;
    use nom::combinator::recognize;
    use nom::error::ParseError;
    use nom::multi::{
        many0 as star, many1 as plus, separated_list1 as most,
    };
    use nom::sequence::{delimited as ifix, tuple as plug};
    use nom::{sequence::Tuple, Parser};
    use nom_supreme::error::ErrorTree;
    use nom_supreme::parser_ext::ParserExt;

    use super::HoonType;

    pub fn dbg_dmp_str<'a, F, O: std::fmt::Debug, E: std::fmt::Debug>(
        mut f: F,
        context: &'static str,
    ) -> impl Parser<&'a str, O, E>
    where
        F: Parser<&'a str, O, E>,
    {
        move |i: &'a str| match f.parse(i) {
            Err(e) => {
                println!("{:#?}: Error({:#?}) at:\n{:#?}", context, e, i);
                Err(e)
            }
            Ok((i, o)) => {
                println!("{:#?}: Ok({:#?}) at:\n{:#?}", context, o, i);
                Ok((i, o))
            }
        }
    }

    pub fn pfix<I, O1, O2, E: ParseError<I>, F, G>(mut ignore: F, mut l: G) -> impl Parser<I, O2, E>
    where
        F: Parser<I, O1, E>,
        G: Parser<I, O2, E>,
    {
        move |i: I| {
            let (i, _) = ignore.parse(i)?;
            l.parse(i)
        }
    }

    pub fn sfix<I, O1, O2, E: ParseError<I>, F, G>(mut l: F, mut ignore: G) -> impl Parser<I, O1, E>
    where
        F: Parser<I, O1, E>,
        G: Parser<I, O2, E>,
    {
        move |i: I| {
            let (i, o) = l.parse(i)?;
            let (i, _) = ignore.parse(i)?;
            Ok((i, o))
        }
    }

    // pub fn sear<I, O1, O2, E: ParseError<I>, F, G>(mut rule: F, err: E, mut f: G) -> impl Parser<I, O2, E>
    // where
    //     F: Parser<I, O1, E>,
    //     G: FnMut(O1) -> Option<O2>,
    // {
    //     move |i: I| {
    //         let (i, o) = rule.parse(i)?;
    //         let o = f(o);
    //         if let Some(o) = o {
    //             Ok((i, o))
    //         } else {
    //             Err(E::from_error_kind(i, nom::error::ErrorKind::Fail))
    //         }
    //     }
    // }
    fn hep<'a>() -> impl Parser<&'a str, char, ErrorTree<&'a str>> {
        char('-')
    }

    fn alf<'a>() -> impl Parser<&'a str, char, ErrorTree<&'a str>> {
        satisfy(|c| is_alphabetic(c as u8))
    }

    fn aln<'a>() -> impl Parser<&'a str, char, ErrorTree<&'a str>> {
        satisfy(|c| is_alphanumeric(c as u8))
    }

    fn alp<'a>() -> impl Parser<&'a str, char, ErrorTree<&'a str>> {
        pose((aln(), hep()))
    }

    fn sel<'a>() -> impl Parser<&'a str, char, ErrorTree<&'a str>> {
        char('[')
    }

    fn ser<'a>() -> impl Parser<&'a str, char, ErrorTree<&'a str>> {
        char(']')
    }

    fn par<'a>() -> impl Parser<&'a str, char, ErrorTree<&'a str>> {
        char('(')
    }

    fn pal<'a>() -> impl Parser<&'a str, char, ErrorTree<&'a str>> {
        char(')')
    }

    fn pat<'a>() -> impl Parser<&'a str, char, ErrorTree<&'a str>> {
        char('@')
    }

    fn tis(input: &str) -> IRes<&str, char> {
        char('=').parse(input)
    }

    fn ace<'a>() -> impl Parser<&'a str, char, ErrorTree<&'a str>> {
        char(' ')
    }

    fn cold<'a, I, O1, O2, E: ParseError<I>, F>(mut f: F, g: O2) -> impl Parser<I, O2, E>
    where
        F: Parser<I, O1, E>,
        O2: Clone,
    {
        move |i: I| {
            let (i, _) = f.parse(i)?;
            let g = g.clone();
            Ok((i, g))
        }
    }

    pub fn term(input: &str) -> IRes<&str, String> {
        cook(recognize(plug((alf(), star(aln())))), |s| {
            let t = s.to_string();
            println!("parsed term {:#?} {:#?}", t, s);
            t
        })
        .context("Parsing term")
        .parse(input)
    }

    pub fn face_inner<'a>() -> impl Parser<&'a str, Box<HoonType>, ErrorTree<&'a str>> {
        map(
            plug((term, pfix(tis, wide))).context("Parsing face"),
            |(s, ty)| Box::new(HoonType::Face(FaceType { face: s, ty })),
        )
    }

    pub fn face<'a>() -> impl Parser<&'a str, Box<HoonType>, ErrorTree<&'a str>> {
        dbg_dmp_str(face_inner(), "Parsing face")
    }

    pub fn aura_inner(input: &str) -> IRes<&str, Box<HoonType>> {
        let (i, _) = pat().parse(input)?;
        let (i, term) = term.parse(i).unwrap_or_else(|e| (i, "".to_string()));

        Ok((
            i,
            Box::new(HoonType::Atom(AtomType {
                aura: term.to_string(),
                cold: None,
            })),
        ))
    }
    pub fn aura(input: &str) -> IRes<&str, Box<HoonType>> {
        aura_inner(input)
    }

    pub fn like(input: &str) -> IRes<&str, Box<HoonType>> {
        let (input, term) = term.parse(input)?;
        Ok((input, Box::new(HoonType::Like(LikeType { like: term }))))
    }

    fn tuple_inner(input: &str) -> IRes<&str, Box<HoonType>> {
        let (next, inner) = ifix(sel(), is_not("]"), ser())(input)?;
        println!("parsed tuple inner {:#?} {:#?}", inner, input);
        let a = ace();
        let (_empty, types) = most(a, wide)(inner)?;
        println!("parsed tuple vec {:#?} {:#?}", inner, types);
        Ok((
            next,
            Box::new(HoonType::Tuple(TupleType {
                tuple: types.into_iter().collect(),
            })),
        ))
    }

    pub fn tuple<'a>() -> impl Parser<&'a str, Box<HoonType>, ErrorTree<&'a str>> {
        move |input: &'a str| tuple_inner(input)
    }

    pub fn list<'a>() -> impl Parser<&'a str, Box<HoonType>, ErrorTree<&'a str>> {
        cook(
            ifix(jest("(list "), wide, char(')')).context("Parsing list"),
            |v| Box::new(HoonType::List(ListType { list: v })),
        )
    }

    pub fn wide(input: &str) -> IRes<&str, Box<HoonType>> {
        let rule = pose((tuple(), face(), list(), aura, like)).context("Parsing wide");
        let mut rule = dbg_dmp_str(rule, "Parsing wide");
        rule.parse(input)
    }

    pub fn arm(input: &str) -> IRes<&str, (String, Box<HoonType>)> {
        let rule = plug((ifix(plug((jest("++"), white())), term, white()), wide));
        let mut rule = dbg_dmp_str(rule, "Parsing arm");
        rule.parse(input)
    }

    pub fn gap<'a>() -> impl Parser<&'a str, (), ErrorTree<&'a str>> {
        cold(pose((jest("\n"), jest("  "))), ())
    }
    pub fn white<'a>() -> impl Parser<&'a str, (), ErrorTree<&'a str>> {
        cold(plus(gap()), ())
    }
    pub fn ret(input: &str) -> IRes<&str, ()> {
        cold(newline, ()).parse(input)
    }

    pub fn core(input: &str) -> IRes<&str, Box<HoonType>> {
        let (i, _) = multispace0(input)?;
        let (i, _) = tag("|%")(i)?;
        let (i, _) = multispace1(i)?;
        let (i, arms) = most(multispace1, arm)(i)?;
        let (i, _) = multispace0(i)?;
        let (i, _) = tag("--")(i)?;
        let (i, _) = multispace0(i)?;
        Ok((
            i,
            Box::new(HoonType::Core(CoreType {
                core: arms.into_iter().collect(),
            })),
        ))
    }

    #[cfg(test)]
    mod test {
        use super::*;

        #[test]
        fn test_term() {
            let input = "foo";
            let (input, res) = parse::term(input).expect("Failed to parse term");
            assert_eq!(input, "");
            assert_eq!(res, "foo");

            let input = "foo@";
            let (rest, res) = parse::term(input).expect("Failed to parse term");
            assert_eq!(rest, "@");
            assert_eq!(res, "foo");

            let input = "bar=";
            let (rest, res) = parse::term(input).expect("Failed to parse term");
            assert_eq!(rest, "=");
            assert_eq!(res, "bar");
        }

        #[test]
        fn test_aura() {
            let input = "@ud";
            let (input, res) = parse::aura(input).expect("Failed to parse aura");
            assert_eq!(input, "");
            assert_eq!(
                res,
                Box::new(HoonType::Atom(AtomType {
                    aura: "ud".to_string(),
                    cold: None,
                })),
            );
        }

        #[test]
        fn test_face_two() {
            let input = "foo=@ud";
            let (input, res) = parse::wide(input).expect("Failed to parse wide");
            assert_eq!(input, "");
            assert_eq!(
                res,
                Box::new(HoonType::Face(FaceType {
                    face: "foo".to_string(),
                    ty: Box::new(HoonType::Atom(AtomType {
                        aura: "ud".to_string(),
                        cold: None,
                    })),
                }))
            );
        }

        #[test]
        fn test_tuple() {
            let input = "[a=@ud b=@u]";
            let mut tuple = parse::tuple();
            let res = tuple.parse(input);
            if res.is_err() {
                println!("{:#?}", res.unwrap_err());
                panic!("Failed to parse tuple");
            }
            let (input, res) = res.unwrap();
            assert_eq!(input, "");
            assert_eq!(
                res,
                Box::new(HoonType::Tuple(TupleType {
                    tuple: vec![
                        Box::new(HoonType::Face(FaceType {
                            face: "a".to_string(),
                            ty: Box::new(HoonType::Atom(AtomType {
                                aura: "ud".to_string(),
                                cold: None,
                            })),
                        })),
                        Box::new(HoonType::Face(FaceType {
                            face: "b".to_string(),
                            ty: Box::new(HoonType::Atom(AtomType {
                                aura: "u".to_string(),
                                cold: None,
                            })),
                        })),
                    ]
                    .into_iter()
                    .collect(),
                })),
            );
        }

        #[test]
        fn test_face() {
            let input = "foo=@ud";
            let res = parse::wide(input);
            if res.is_err() {
                println!("{:#?}", res.unwrap_err());
                panic!("Failed to parse face type");
            }
            let (input, res) = res.unwrap();
            assert_eq!(input, "");
            assert_eq!(
                res,
                Box::new(HoonType::Face(FaceType {
                    face: "foo".to_string(),
                    ty: Box::new(HoonType::Atom(AtomType {
                        aura: "ud".to_string(),
                        cold: None,
                    })),
                }))
            );
        }
        fn get_arm_one() -> &'static str {
            "++  foo  [one=@ two=@ux]"
        }

        fn get_arm_one_type() -> Box<HoonType> {
            Box::new(HoonType::Tuple(TupleType {
                tuple: vec![
                    Box::new(HoonType::Face(FaceType {
                        face: "one".to_string(),
                        ty: Box::new(HoonType::Atom(AtomType {
                            aura: "".to_string(),
                            cold: None,
                        })),
                    })),
                    Box::new(HoonType::Face(FaceType {
                        face: "two".to_string(),
                        ty: Box::new(HoonType::Atom(AtomType {
                            aura: "ux".to_string(),
                            cold: None,
                        })),
                    })),
                ]
                .into_iter()
                .collect(),
            }))
        }

        fn get_arm_two() -> &'static str {
            "++  bar  [three=@ four=@]"
        }

        fn get_arm_two_type() -> Box<HoonType> {
            Box::new(HoonType::Tuple(TupleType {
                tuple: vec![
                    Box::new(HoonType::Face(FaceType {
                        face: "three".to_string(),
                        ty: Box::new(HoonType::Atom(AtomType {
                            aura: "".to_string(),
                            cold: None,
                        })),
                    })),
                    Box::new(HoonType::Face(FaceType {
                        face: "four".to_string(),
                        ty: Box::new(HoonType::Atom(AtomType {
                            aura: "".to_string(),
                            cold: None,
                        })),
                    })),
                ]
                .into_iter()
                .collect(),
            }))
        }

        #[test]
        fn test_arm() {
            // let arm = "++  foo  [one=@ two=@ux]";
            let arm = get_arm_one();
            let (input, res) = parse::arm(arm).expect("Failed to parse arm");
            assert_eq!(input, "");
            assert_eq!(res, ("foo".to_string(), get_arm_one_type()));

            let arm = get_arm_two();
            let (input, res) = parse::arm(arm).expect("Failed to parse arm");
            assert_eq!(input, "");
            assert_eq!(res, ("bar".to_string(), get_arm_two_type()));
        }

        #[test]
        fn test_core() {
            let input = r#"
|%
++  foo  [one=@ two=@ux]
++  bar  [three=@ four=@]
--
"#;
            let (input, res) = parse::core(input).expect("Failed to parse core type");
            println!("parsed core {:#?}", res);
            assert_eq!(input, "");
            assert_eq!(
                res,
                Box::new(HoonType::Core(CoreType {
                    core: HashMap::from([
                        ("foo".to_string(), get_arm_one_type()),
                        ("bar".to_string(), get_arm_two_type())
                    ])
                }))
            );
        }
    }
}

pub fn axis_for_list_idx(idx: usize) -> usize {
    if idx == 0 {
        return 2;
    }
    (1 << (idx + 1)) - 2
}

pub fn tuple_idx_for_axis(idx: usize, len: usize) -> usize {
    if idx == 0 {
        2
    } else if idx == (len - 1) {
        return axis_for_list_idx(idx - 1) + 1;
    } else {
        return axis_for_list_idx(idx);
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct AxisInfo<'a> {
    pub face: Option<String>,
    pub axis: usize,
    pub ty: &'a HoonType,
}

pub fn get_axes(ty: &HoonType) -> Vec<AxisInfo<'_>> {
    let cur_axis = 1;
    let mut next = vec![(ty, cur_axis)];
    let mut axes: Vec<AxisInfo> = vec![];
    while let Some((t, ax)) = next.pop() {
        match t {
            HoonType::Atom(ref _a) => {
                axes.push(AxisInfo {
                    face: None,
                    axis: ax,
                    ty: t,
                });
            }
            HoonType::Face(ref f) => {
                axes.push(AxisInfo {
                    face: Some(f.face.clone()),
                    axis: ax,
                    ty: f.ty.as_ref(),
                });
            }
            HoonType::Tuple(ref t) => {
                let len = t.tuple.len();
                let iter = t.tuple.iter().enumerate();
                for (i, t) in iter {
                    let c = tuple_idx_for_axis(i, len);
                    let ax = peg(ax, c);
                    next.push((t, ax));
                }
            }
            _ => (),
        }
    }
    axes
}

pub fn traverse<R>(ty: &HoonType, f: impl Fn((&HoonType, usize, &mut R)) -> bool) -> R
where
    R: Default,
{
    let mut tys = vec![(ty, 1)];
    let mut r = R::default();
    while let Some((t, a)) = tys.pop() {
        let stop = f((t, a, &mut r));
        if stop {
            continue;
        }
        match t {
            HoonType::Atom(ref _a) => (),
            HoonType::Face(ref _f) => (),
            HoonType::Tuple(ref t) => {
                let len = t.tuple.len();
                let iter = t.tuple.iter().enumerate();
                for (i, t) in iter {
                    let c = tuple_idx_for_axis(i, len);
                    let ax = peg(a, c);
                    tys.push((t, ax));
                }
            }
            HoonType::List(ref _l) => {
                // tys.push((l.list, a + 1));
            }
            HoonType::Like(ref _l) => (),
            _ => (),
        }
    }
    r
}

/// Convert kebab-case to camelCase
pub fn sanitize_string(input: String) -> String {
    let mut result = String::new();
    let mut capitalize_next = false;

    for (i, c) in input.chars().enumerate() {
        if c == '-' {
            capitalize_next = true;
        } else if capitalize_next {
            result.push(c.to_ascii_uppercase());
            capitalize_next = false;
        } else if i == 0 {
            result.push(c.to_ascii_lowercase());
        } else {
            result.push(c);
        }
    }

    result
}

pub fn sanitize_type(input: String) -> String {
    let res = sanitize_string(input);
    let char = res.chars().next().unwrap();
    let mut result = String::from(char.to_ascii_uppercase());
    result.push_str(&res[1..]);
    result
}

pub fn define_type(input: String) -> TokenStream {
    let res = parse::core(&input);
    if res.is_err() {
        println!("{:#?}", res.unwrap_err());
        panic!("Failed to parse core type");
    }

    let (_, ty) = res.unwrap();
    let arms = match ty.as_ref() {
        HoonType::Core(core) => core.core.clone(),
        _ => panic!("Expected a core type"),
    };

    for (face, ty) in &arms {
        println!("{} {:?}", face, ty);
    }

    let mut result = TokenStream::new();

    for (face, ty) in &arms {
        let axes = get_axes(ty);
        let fields = axes.iter().map(|axis| {
            // Convert the field name string to an ident
            let field_name = syn::Ident::new(
                &sanitize_string(axis.face.as_ref().expect("Expected face").clone()),
                proc_macro2::Span::call_site(),
            );

            
            match axis.ty {
                HoonType::Atom(ref a) => {
                    if a.aura.is_empty() {
                        quote! { pub #field_name: Atom }
                    } else {
                        // TODO: map auras to rust types properly
                        quote! { pub #field_name: Atom }
                    }
                }
                _ => quote! { pub #field_name: Noun }, // TODO: handle other types
            }
        });

        // Convert the type name string to an ident
        let name = syn::Ident::new(&sanitize_type(face.clone()), proc_macro2::Span::call_site());

        println!("{:#?}", axes);

        let builder = axes.iter().map(|axis| {
            let field_name = syn::Ident::new(
                &sanitize_string(axis.face.as_ref().expect("Expected face").clone()),
                proc_macro2::Span::call_site(),
            );
            let axis = axis.axis;
            quote! {
                #field_name: input.get_axis(#axis).unwrap()
            }
        });

        // generate the struct definition
        let expanded = quote! {
            #[derive(Debug)]
            struct #name {
                #(#fields),*
            }

            impl #name {
                fn new(input: Rc<Noun>) -> Self {
                    let input = input.as_cell().unwrap();
                    Self {
                        #(#builder),*
                    }
                }
            }
        };
        result.extend(expanded);
    }

    result
}

pub fn sloe(ty: &HoonType) -> Vec<(String, usize)> {
    
    traverse::<Vec<(String, usize)>>(ty, |(t, a, r)| {
        if let HoonType::Face(ref f) = t {
            r.push((f.face.clone(), a));
            return true;
        }
        false
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_define_type() {
        let s = r#"
|%
++  foo  [one=@ two=@ux]
++  bar  [three=@ four=@]
--
"#;
        let expanded = define_type(String::from(s));
        println!("{}", expanded);
        let expected = quote! {
            #[derive(Debug)]
            struct Foo {
                pub two: Atom,
                pub one: Atom
            }

            impl Foo {
                fn new(input: Rc<Noun>) -> Self {
                    let input = input.as_cell().unwrap();
                    Self {
                        two: input.get_axis(3usize).unwrap(),
                        one: input.get_axis(2usize).unwrap()
                    }
                }
            }

            #[derive(Debug)]
            struct Bar {
                pub four: Atom,
                pub three: Atom
            }

            impl Bar {
                fn new(input: Rc<Noun>) -> Self {
                    let input = input.as_cell().unwrap();
                    Self {
                        four: input.get_axis(3usize).unwrap(),
                        three: input.get_axis(2usize).unwrap()
                    }
                }
            }
        };

        let expanded_str = prettyplease::unparse(&syn::parse2(expanded.clone()).unwrap());
        let expected_str = prettyplease::unparse(&syn::parse2(expected).unwrap());

        assert_eq!(expanded_str, expected_str);
    }
}
