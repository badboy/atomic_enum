// Purpose: This integration test checks that atomic_enum can be used in
// a no_std environment.

#![no_std]

use core::mem;
use core::sync::atomic::Ordering;

use atomic_enum::atomic_enum;

#[atomic_enum]
#[derive(PartialEq, Eq)]
enum FooBar {
    Foo,
    Bar,
}

#[test]
fn test_no_std_use() {
    assert_eq!(mem::size_of::<usize>(), mem::size_of::<AtomicFooBar>());

    let fb = AtomicFooBar::new(FooBar::Foo);
    let prev = fb
        .compare_exchange(
            FooBar::Foo,
            FooBar::Bar,
            Ordering::SeqCst,
            Ordering::Relaxed,
        )
        .unwrap();
    assert_eq!(prev, FooBar::Foo);

    let prev_fail = fb.compare_exchange(
        FooBar::Foo,
        FooBar::Bar,
        Ordering::SeqCst,
        Ordering::Relaxed,
    );
    assert!(prev_fail.is_err());
}

#[atomic_enum]
#[derive(PartialEq, Eq)]
#[repr(u8)]
enum CatState {
    Dead = 0,
    BothDeadAndAlive,
    Alive,
}

#[test]
fn test_cat_state() {
    assert_eq!(mem::size_of::<u8>(), mem::size_of::<AtomicCatState>());

    let cat = AtomicCatState::new(CatState::BothDeadAndAlive);
    assert_eq!(CatState::BothDeadAndAlive, cat.load(Ordering::SeqCst));

    cat.store(CatState::Alive, Ordering::SeqCst);
    assert_eq!(CatState::Alive, cat.load(Ordering::SeqCst));
}
