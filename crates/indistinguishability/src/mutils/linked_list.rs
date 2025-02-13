use std::rc::Rc;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum InnerRcLinkedList<U> {
    Nil,
    Cons {
        head: U,
        tail: Rc<InnerRcLinkedList<U>>,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct RcLinkedList<U> {
    start: Rc<RcLinkedList<U>>,
    end: Rc<RcLinkedList<U>>,
}

struct RcLinkedListIterator<'a, U>(&'a InnerRcLinkedList<U>);

impl<'a, U> Iterator for RcLinkedListIterator<'a, U> {
    type Item = &'a U;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0 {
            InnerRcLinkedList::Nil => None,
            InnerRcLinkedList::Cons { head, tail, .. } => {
                self.0 = tail.as_ref();
                Some(head)
            }
        }
    }
}

impl<U> RcLinkedList<U> {
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a U> {
        RcLinkedListIterator(&self.start)
    }

    pub fn len(&self) -> usize {
        self.iter().count()
    }

    pub fn new() -> Self {
        Self::default()
    }

    pub fn push_front(&self, head: U) -> Self {
        let RcLinkedList { start, end } = self;
        RcLinkedList {
            start: Rc::new(InnerRcLinkedList::Cons {
                head,
                tail: Rc::clone(start),
            }),
            end: Rc::clone(end),
        }
    }

    pub fn merge(self, other: Self) -> Self {
        let RcLinkedList { start, end } = self;
        let RcLinkedList {
            start: start_o,
            end: end_o,
        } = other;
    }
}

impl<U> Default for RcLinkedList<U> {
    fn default() -> Self {
        Rc::new(Self::Nil)
    }
}

impl<U> FromIterator<U> for RcLinkedList<U> {
    fn from_iter<T: IntoIterator<Item = U>>(iter: T) -> Self {
        iter.into_iter()
            .fold(Default::default(), |acc, head| acc.push_front(head))
    }
}
