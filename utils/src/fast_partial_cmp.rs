#[macro_export]
macro_rules! partial_order {
    ($field1:ident, $($field:ident),*) => {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            std::cmp::PartialOrd::partial_cmp(&self.$field1, &other.$field1)
                $(
                    .and_then(|o| {
                        let no = std::cmp::PartialOrd::partial_cmp(&self.$field, &other.$field);
                        no.map(|nno| o.then(nno))
                    })
                )*
        }
    };
}
