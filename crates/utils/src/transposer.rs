use std::marker::PhantomData;

use itertools::{izip, Itertools};

use crate::ereturn_if;

pub struct VecTranspose<'a, I, U> {
    content: &'a [I],
    state: Box<[usize]>,
    item: PhantomData<&'a U>,
}

impl<'a, I, U> VecTranspose<'a, I, U>
where
    I: AsRef<[U]>,
{
    pub fn new(content: &'a [I]) -> Self {
        Self {
            content,
            state: vec![].into_boxed_slice(),
            item: Default::default(),
        }
    }

    fn idx_next(&mut self) -> Option<&[usize]> {
        ereturn_if!(self.is_empty(), None);
        let Self { content, state, .. } = self;

        if state.is_empty() {
            *state = vec![0; content.len()].into_boxed_slice();
            Some(&self.state)
        } else {
            for i in 0..state.len() {
                if state[i] < content[i].as_ref().len() - 1 {
                    state[i] += 1;
                    return Some(&self.state);
                } else {
                    state[i] = 0;
                    continue;
                }
            }
            unreachable!("empty iter skipped the empty check")
        }
    }

    // TODO: improve
    // this can be done with only one iteration
    pub fn len(&self) -> usize {
        ereturn_if!(self.is_empty(), 0);

        // think

        // ∏ᵢ₌₀ⁿ⁻¹ c[i].len()
        let total = self
            .content
            .iter()
            .map(|x| x.as_ref().len())
            .product::<usize>();

        // 1 + ∑ᵢ₌₀ⁿ⁻¹s[i]*∏ⱼ₌₀ⁱ⁻¹ c[i].len()
        let done = self
                .state
                .iter()
                .enumerate()
                .map(|(i, s)| {
                    self.content[0..i]
                        .iter()
                        .map(|x| x.as_ref().len())
                        .product::<usize>()
                        * s
                })
                .sum::<usize>()
                // due to when we call
                + (!self.state.is_empty() as usize);

        total - done
    }

    pub fn is_empty(&self) -> bool {
        let Self { content, state, .. } = self;
        content.is_empty()
            || if state.is_empty() {
                content.iter().any(|x| x.as_ref().is_empty())
            } else {
                izip!(state.iter(), content.iter()).all(|(&s, c)| s >= c.as_ref().len() - 1)
            }
    }
}

impl<'a, I, U> Iterator for VecTranspose<'a, I, U>
where
    I: AsRef<[U]>,
{
    type Item = Box<[&'a U]>;

    fn next(&mut self) -> Option<Self::Item> {
        ereturn_if!(self.is_empty(), None);

        if self.state.len() != self.content.len() {
            ereturn_if!(self.content.iter().any(|x| x.as_ref().is_empty()), None);
            self.state = vec![0; self.content.len()].into_boxed_slice();
        } else {
            self.idx_next()?;
        };

        let res = self
            .content
            .iter()
            .enumerate()
            .map(|(i, c)| &c.as_ref()[self.state[i]])
            .collect();

        Some(res)
    }
}

#[test]
fn sound_vec_iter() {
    let tmp = vec![
        vec![11, 21, 31, 41, 51, 61],
        vec![12, 22, 32],
        vec![13, 23, 33, 43],
    ];
    let res = VecTranspose::new(&tmp).collect_vec();
    assert!(res.iter().all_unique());
    assert_eq!(res.len(), 6 * 3 * 4);
}

#[test]
fn sound_vec_iter2() {
    let tmp = vec![
        vec![11, 21, 31, 41, 51, 61],
        vec![12, 22, 32],
        vec![13, 23, 33, 43],
    ];
    let n = 6 * 3 * 4;
    let mut iter = VecTranspose::new(&tmp);
    assert_eq!(iter.len(), 6 * 3 * 4);
    let mut res = Vec::with_capacity(n);
    for i in 0..n {
        assert_eq!(iter.len(), 6 * 3 * 4 - i);
        res.push(iter.next().unwrap());
    }
    assert!(res.iter().all_unique());
    assert!(iter.is_empty())
}

pub trait Transposable<U> {
    type I: AsRef<[U]>;

    fn transpose<'a>(&'a self) -> VecTranspose<'a, Self::I, U>;
}

impl<I, U> Transposable<U> for &[I]
where
    I: AsRef<[U]>,
{
    type I = I;

    fn transpose<'a>(&'a self) -> VecTranspose<'a, I, U> {
        VecTranspose::new(self)
    }
}
