// Inferno's Dare:
// https://discord.com/channels/273534239310479360/832043898456113182/867946092686372894
// > I dare you to prove sqrt(2) is not in Q with Rust.

//! # Proving `sqrt(2)` is not inside the set of rational numbers with Rust.
//!
//! Rust's type system can be used as a verifier for constructive logic.

// ## Axioms.
use ::core::marker::PhantomData;

/// Convenience macro for proof verification.
macro_rules! proof {
    (type $name:ident = $t:ty) => {
        #[allow(dead_code)]
        type $name = $t;
        proof!($name);
    };
    ($t:ty) => {
        // To verify a proof, we just need to force rustc to check that it's a valid type.
        const _: Option<$t> = None;
    }
}
/// An even more convenient macro for proof verification.
macro_rules! proofs {
    (type $name:ident = $t:ty
     $(; $($rest:tt)*)?
    ) => {
        proof!(type $name = $t);
        $(
            proofs!($($rest)*);
        )?
    };
    ($t:ty
     $(; $($rest:tt)*)?
    ) => {
        proof!($t);
        $(
            proofs!($($rest)*);
        )?
    };
    ($($t:ty);* $(;)?) => {
        $(
            proof!($t);
        )*
    }
}


// A Peano-ish definition for natural numbers.
trait Nat {}
struct Zero;
impl Nat for Zero {}
struct Successor<N: Nat> { _n: PhantomData<N> }
impl<N: Nat> Nat for Successor<N> {}
trait Reify {
    const OUTPUT: u64;
    fn val(&self) -> u64 { Self::OUTPUT }
}
impl Reify for Zero {
    const OUTPUT: u64 = 0;
}
impl<N: Nat + Reify> Reify for Successor<N> {
    const OUTPUT: u64 = 1 + N::OUTPUT;
}

/// Reflexive equality.
trait Congruent<A> {}
impl<A> Congruent<A> for A {}
// Being able to write this type is proof that the two argument types are equal.
struct Equal<A, B: Congruent<A>> { _a: PhantomData<A>, _b: PhantomData<B> }

/// Addition!
trait Sum<Addend: Nat> {
    type Output;
}
impl<A: Nat> Sum<Zero> for A {
    type Output = A;
}
impl<A: Nat, B: Nat> Sum<Successor<B>> for A where Successor<A>: Sum<B> {
    type Output = <Successor<A> as Sum<B>>::Output;
}

/// Subtraction!
trait Difference<Subtrahend: Nat> {
    type Output;
}
impl<A: Nat> Difference<Zero> for A {
    type Output = A;
}
impl<A: Nat, B: Nat> Difference<Successor<B>> for Successor<A> where A: Difference<B> {
    type Output = <A as Difference<B>>::Output;
}

trait Product<Multiplicand> {
    type Output;
}
impl<A> Product<Zero> for A {
    type Output = Zero;
}
impl<A: Nat, B: Nat> Product<Successor<B>> for A where A: Product<B>, <A as Product<B>>::Output: Sum<A> {
    type Output = <<A as Product<B>>::Output as Sum<A>>::Output;
}

// LessThan<N> is essentially an alias for `N: Difference<Successor<Self>>`
/// Less than comparison.
trait LessThan<N> {
    // This has no result, but I'd like it to be easily usable with
    // the `proof!` macro, which works by asserting a type is valid.
    type Output;
}
impl<A: Nat, B: Nat> LessThan<B> for A where
    B: Difference<Successor<A>>,
{
    type Output = ();
}

trait LessThanOrEqual<N> {
    type Output;
}
impl<A: Nat, B: Nat> LessThanOrEqual<B> for A where
    B: Difference<A>,
{
    type Output = ();
}

trait GreaterThan<N> {
    type Output;
}
impl<A: Nat, B: Nat> GreaterThan<B> for A where
    A: Difference<Successor<B>>,
{
    type Output = ();
}

trait GreaterThanOrEqual<N> {
    type Output;
}
impl<A: Nat, B: Nat> GreaterThanOrEqual<B> for A where
    A: Difference<B>,
{
    type Output = ();
}

// These fail to compile, as you'd expect:
// proof! { <Zero as Difference<One>>::Output }
// proof! { <Zero as LessThan<Zero>>::Output }

// Here are some proofs I expect to work.
// If they don't, my axioms are wrong.
proofs! {
    // Addition tests:
    Equal<Two, <One as Sum<One>>::Output>;
    Equal<Three, <One as Sum<Two>>::Output>;
    
    // Subtraction tests:
    Equal<Two, <Three as Difference<One>>::Output>;
    Equal<Zero, <Four as Difference<Four>>::Output>;
    Equal<Zero, <Zero as Difference<Zero>>::Output>;
    
    // Multiplication tests:
    Equal<One, <One as Product<One>>::Output>;
    Equal<Four, <Two as Product<Two>>::Output>;
    Equal<Six, <Two as Product<Three>>::Output>;
}


// Oh boy, let's try and do rationals now.
struct Ratio<Numerator: Nat, Denominator: Nat> { _a: PhantomData<Numerator>, _b: Denominator }

// ## Lemmas

// Let's start by just labeling some numbers. That's easy.
proofs! {
    type One = Successor<Zero>;
    type Two = Successor<One>;
    type Three = Successor<Two>;
    type Four = Successor<Three>;
    // Mostly writing this here just to ensure my macro works for
    // interleaving named and anonymous proofs.
    Equal<<Two as Sum<Two>>::Output, Four>;
    type Five = Successor<Four>;
    Equal<<Two as Sum<Three>>::Output, Five>;
    type Six = Successor<Five>;
}

type ThreeFourths = Ratio<Three, Four>;

// ## Proof

fn main() {}
