use std::cell::{Ref, RefCell};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Holder<T, U: 'static> {
    dynamique: RefCell<Vec<*const T>>,
    statique: RefCell<Vec<&'static U>>, // static was taken so I'm using french
}

impl<T, U: 'static> Holder<T, U> {
    pub fn insert_dynamic<'a>(&'a self, e: T) -> &'a T {
        let ptr = Box::into_raw(Box::new(e));
        self.dynamique.borrow_mut().push(ptr);
        unsafe { ptr.as_ref() }.unwrap() // just created hence non null and valid. It will never be drop during 'a
    }

    pub fn insert_static<'a>(&'a self, e: &'static U) -> &'a U {
        self.statique.borrow_mut().push(e);
        e
    }

    pub fn get_dyn<'a>(&'a self, i: usize) -> Option<&'a T> {
        self.dynamique
            .borrow()
            .get(i)
            .map(|ptr| unsafe { ptr.as_ref() }.unwrap())
    }

    pub fn get_stat<'a>(&'a self, i: usize) -> Option<&'a U> {
        self.statique.borrow().get(i).map(|ptr| *ptr)
    }
}

impl<T, U: 'static> Drop for Holder<T, U> {
    fn drop(&mut self) {
        for &ptr in self.dynamique.borrow().iter() {
            drop(unsafe { Box::from_raw(ptr as *mut T) }) // the only reference to *ptr is ptr and it never was droped before
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DynOrStat<T, U> {
    Dyn(T),
    Stat(U),
}

impl<T> DynOrStat<T, T> {
    pub fn get(self) -> T {
        match self {
            DynOrStat::Dyn(t) | DynOrStat::Stat(t) => t,
        }
    }
}

pub struct HolderIter<'a, T: 'a, U: 'static> {
    holder: &'a Holder<T, U>,
    i: DynOrStat<usize, usize>,
}

impl<'a, T: 'a, U: 'static> Iterator for HolderIter<'a, T, U> {
    type Item = DynOrStat<&'a T, &'a U>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.i {
            DynOrStat::Dyn(i) => {
                if let Some(t) = self.holder.get_dyn(i) {
                    self.i = DynOrStat::Dyn(i + 1);
                    Some(DynOrStat::Dyn(t))
                } else {
                    self.i = DynOrStat::Stat(0);
                    self.next()
                }
            }
            DynOrStat::Stat(i) => self.holder.get_stat(i).map(|u| {
                self.i = DynOrStat::Stat(i + 1);
                DynOrStat::Stat(u)
            }),
        }
    }
}
