use core::sync::atomic::Ordering;

use atomic_traits::{
    //fetch::{And, Nand, Or, Xor},
    //Bitwise,
    fetch::{Add, Max, Min, Sub, Update},
    Atomic,
    NumOps,
};

use crate::AtomicF32;

impl Atomic for AtomicF32 {
    type Type = f32;

    fn new(v: Self::Type) -> Self {
        Self::new(v)
    }

    fn get_mut(&mut self) -> &mut Self::Type {
        Self::get_mut(self)
    }

    fn into_inner(self) -> Self::Type {
        Self::into_inner(self)
    }

    fn load(&self, order: Ordering) -> Self::Type {
        Self::load(&self, order)
    }

    fn store(&self, val: Self::Type, order: Ordering) {
        Self::store(&self, val, order)
    }

    fn swap(&self, val: Self::Type, order: Ordering) -> Self::Type {
        Self::swap(&self, val, order)
    }

    fn compare_and_swap(
        &self,
        current: Self::Type,
        new: Self::Type,
        order: Ordering,
    ) -> Self::Type {
        Self::compare_and_swap(&self, current, new, order)
    }

    fn compare_exchange(
        &self,
        current: Self::Type,
        new: Self::Type,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Self::Type, Self::Type> {
        Self::compare_exchange(&self, current, new, success, failure)
    }

    fn compare_exchange_weak(
        &self,
        current: Self::Type,
        new: Self::Type,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Self::Type, Self::Type> {
        Self::compare_exchange_weak(&self, current, new, success, failure)
    }
}

impl Add for AtomicF32 {
    type Type = f32;

    fn fetch_add(&self, val: Self::Type, order: Ordering) -> Self::Type {
        Self::fetch_add(&self, val, order)
    }
}

//impl And for AtomicF32 {
//    type Type = f32;
//
//    fn fetch_and(&self, val: Self::Type, order: Ordering) -> Self::Type {
//        Self::fetch_and(&self, val, order)
//    }
//}

impl Max for AtomicF32 {
    type Type = f32;

    fn fetch_max(&self, val: Self::Type, order: Ordering) -> Self::Type {
        Self::fetch_max(&self, val, order)
    }
}

impl Min for AtomicF32 {
    type Type = f32;

    fn fetch_min(&self, val: Self::Type, order: Ordering) -> Self::Type {
        Self::fetch_min(&self, val, order)
    }
}

//impl Nand for AtomicF32 {
//    type Type = f32;
//
//    fn fetch_nand(&self, val: Self::Type, order: Ordering) -> Self::Type {
//        Self::fetch_nand(&self, val, order)
//    }
//}

//impl Or for AtomicF32 {
//    type Type = f32;
//
//    fn fetch_or(&self, val: Self::Type, order: Ordering) -> Self::Type {
//        Self::fetch_or(&self, val, order)
//    }
//}

impl Sub for AtomicF32 {
    type Type = f32;

    fn fetch_sub(&self, val: Self::Type, order: Ordering) -> Self::Type {
        Self::fetch_sub(&self, val, order)
    }
}

impl Update for AtomicF32 {
    type Type = f32;

    fn fetch_update<F>(
        &self,
        fetch_order: Ordering,
        set_order: Ordering,
        f: F,
    ) -> Result<Self::Type, Self::Type>
    where
        F: FnMut(Self::Type) -> Option<Self::Type>,
    {
        Self::fetch_update(&self, fetch_order, set_order, f)
    }
}

//impl Xor for AtomicF32 {
//    type Type = f32;
//
//    fn fetch_xor(&self, val: Self::Type, order: Ordering) -> Self::Type {
//        Self::fetch_xor(&self, val, order)
//    }
//}

//impl Bitwise for AtomicF32 {}

impl NumOps for AtomicF32 {}
