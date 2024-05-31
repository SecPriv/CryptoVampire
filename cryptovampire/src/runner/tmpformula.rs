use itertools::Itertools;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TmpFormula {
    head: String,
    args: Vec<TmpFormula>,
}

impl TmpFormula {
    pub fn new(head: String, args: Vec<TmpFormula>) -> Self {
        Self { head, args }
    }
    pub fn new_ref(head: &str, args: &[TmpFormula]) -> Self {
        Self {
            head: head.to_string(),
            args: args.to_vec(),
        }
    }

    pub fn parse(str: &str) -> Option<Self> {
        Self::parse_next(&mut str.trim_start())
    }

    /// parses `str` setting it to leftover string after parsing.
    ///
    ///  - no space in the begining of `str``
    ///  - may modify `str` even when returning `None`
    fn parse_next(str: &mut &str) -> Option<Self> {
        let head = Self::parse_head(str)?;
        let mut chars = str.chars();
        if let Some('(') = chars.next() {
            let mut args = vec![];
            let mut tail = chars.as_str().trim_start();
            loop {
                args.push(Self::parse_next(&mut tail)?);

                let tmp = tail.trim_start();
                let mut chars = tmp.chars();
                let c = chars.next();
                tail = chars.as_str().trim_start();
                match c {
                    Some(')') => break,
                    Some(',') => (),
                    _ => return None,
                }
            }
            *str = tail;
            Some(Self::new(head.to_string(), args))
        } else {
            Some(Self::new(head.to_string(), vec![]))
        }
    }

    /// parses the head function
    /// - no space at the start
    fn parse_head<'a>(str: &mut &'a str) -> Option<&'a str> {
        let tail = *str;
        if let Some(i) = tail.find(|c: char| !c.is_alphanumeric()) {
            let (head, tail) = tail.split_at(i);
            *str = tail;
            Some(head)
        } else {
            *str = "";
            Some(tail)
        }
    }

    pub fn head(&self) -> &str {
        &self.head
    }

    pub fn args(&self) -> &[TmpFormula] {
        &self.args
    }
}

#[cfg(test)]
mod tests {
    use crate::runner::tmpformula::TmpFormula;

    #[test]
    fn tmpformula_parsing_success() {
        let str = "f(a, b,g( c))";
        assert_eq!(
            TmpFormula::parse(str),
            Some(TmpFormula::new_ref(
                "f",
                &[
                    TmpFormula::new_ref("a", &[]),
                    TmpFormula::new_ref("b", &[]),
                    TmpFormula::new_ref("g", &[TmpFormula::new_ref("c", &[])])
                ]
            ))
        )
    }

    #[test]
    fn tmpformula_parsing_faillure() {
        let str = "f(a, b,g( c)";
        assert_eq!(TmpFormula::parse(str), None)
    }
}
