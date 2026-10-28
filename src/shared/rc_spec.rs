//! Trusted specifications of the three `Rc` functions that [`SharedDbm`]
//! calls and the pinned version of creusot-std leaves unspecified.
//!
//! This file is part of the **trusted base** (`verification/PROOF_STATUS.md`).
//! creusot-std already models `Rc<T>` as an immutable value of type `T`
//! (`#[trusted(positive(T))] type Rc<T>`, with specifications of `Rc::new`,
//! `Clone`, `Deref`, `AsRef` and `Rc::ptr_eq`); the contracts below are
//! stated in that model and copy the documented behaviour of the standard
//! library. They say nothing about addresses, so they cannot contradict the
//! `Rc::ptr_eq` specification. `SharedDbm` never creates a `Weak`.
//!
//! [`SharedDbm`]: super::SharedDbm

use creusot_std::prelude::*;
use std::alloc::Allocator;
use std::rc::Rc;

extern_spec! {
    impl<T: ?Sized, A: Allocator> Rc<T, A> {
        /// std: "Returns a mutable reference into the given `Rc`, if there
        /// are no other `Rc` or `Weak` pointers to the same allocation.
        /// Returns `None` otherwise, because it is not safe to mutate a
        /// shared value." With `Some`, the handle is unique, so writing
        /// through the reference changes this handle's value and no other.
        #[check(terminates)]
        #[ensures(match result {
            Some(r) => *r == *(*this)@ && *(^this)@ == ^r,
            None => ^this == *this,
        })]
        fn get_mut(this: &mut Rc<T, A>) -> Option<&mut T>;

        /// std: "Gets the number of strong (`Rc`) pointers to this
        /// allocation." Only used to choose between two outcomes that are
        /// both proved correct, so no postcondition is needed.
        #[check(terminates)]
        fn strong_count(this: &Rc<T, A>) -> usize;
    }

    impl<T: Clone, A: Allocator> Rc<T, A> {
        /// std: "If we have the only reference to `T` then unwrap it.
        /// Otherwise, clone `T` and return the clone." The clone is made by
        /// `T::clone`, so it satisfies `T::clone`'s postcondition.
        #[ensures(result == *this@ || T::clone.postcondition((&*this@,), result))]
        fn unwrap_or_clone(this: Rc<T, A>) -> T;
    }
}
