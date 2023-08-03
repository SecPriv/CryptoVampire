use super::reference::{Reference, RefPointee};

pub trait Container<'bump, R> where R:Reference<'bump> {
    fn allocate(&'bump self, content: R::Inner) -> &'bump RefPointee<'bump, R>;
    fn allocate_uninit(&'bump self) -> &'bump RefPointee<'bump, R> {
        self.allocate(Default::default())
    }
}