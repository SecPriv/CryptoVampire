# Rust

## Ideas & co

### Database for `Sort` and `Function`
I plan on simply using an [`Arena`](https://docs.rs/typed-arena/latest/typed_arena/struct.Arena.html) for now. And then I can keep a `Vec<&T>` for all the `Sort`s and `Function`s that need declaration in smt.

One downside is that `Arena` is not thread-safe. So maybe, one day, I'll do something different... There exists:
 - [`FrozenVec`](https://docs.rs/elsa/latest/elsa/sync/struct.FrozenVec.html)
 - [`LockFreeFrozenVec`](https://docs.rs/elsa/latest/elsa/sync/struct.LockFreeFrozenVec.html)

But both are "experimental" despite being used in `rustc` apparently. 