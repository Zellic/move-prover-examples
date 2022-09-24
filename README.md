# Move Prover Examples

An example-based guide to getting started with the Move prover.

- [Introduction](#introduction)
- [Step 0: Installation](#step-0)
- [Step 1: First specification](#step-1)
- [Step 2: Aborts](#step-2)
- [Step 3: Preconditions](#step-3)
- [Step 4: Helper functions](#step-4)
- [Step 5: State](#step-5)
- [Step 6: Operators and Quantifiers](#step-6)
- [Step 7: Invariants](#step-7)
- [Step 8: Invariants, part two](#step-8)

## Introduction <span id="introduction"></span>

The Move Prover is a tool for formally verifying the correctness of smart
contracts written in Move. It is designed to be fast and practical—something
that can really be used in the code development process. This is something it
achieves: the prover nearly always runs in minutes or less, and has been used
to verify all the Move in the Diem framework.

The Move smart contract language was designed with formal verification in mind.
For instance, its use of Rust-like borrow semantics, lack of dynamic dispatch,
and limited state interaction APIs all make program analysis more
straightforward. Further, the Move language is developed alongside the Move
specification language (MSL), which is more expressive than the language
itself.

Despite the power of the Move Prover and its huge influence on the language
design, many existing Move contracts we have seen do not utilize it to the
fullest. Among other reasons may be difficulty in getting started with the
specification language: though it is [reasonably documented][1], there aren't
many examples provided.

This resource aims to provide a gentle introduction to writing specifications
and using the prover to make Move contracts more secure.

[1]: https://github.com/move-language/move/blob/main/language/move-prover/doc/user/spec-lang.md

## Step 0: Installation <span id="step-0"></span>

The prover comes with the Move cli. Install it using [cargo][2].

```sh
cargo install --git https://github.com/move-language/move move-cli
```

The prover also depends on the Boogie verifier and a backend SMT solver.
Either install Boogie and [z3][3] with your preferred package manager or use
the [dev setup script][4] provided by Move.

Finally, the prover looks for the Boogie and z3 environment variables in the
`Z3_EXE` and `BOOGIE_EXE` environment variables. Make sure these are set.

[2]: https://github.com/rust-lang/cargo/
[3]: https://github.com/Z3Prover/z3
[4]: https://github.com/move-language/move/blob/main/scripts/dev_setup.sh

## Step 1: First specification <span id="step-1"></span>

Let's begin by considering a very simple example function:

```move
fun sum(first: u64, second: u64): u64 {
    first + second
}
```

How do we prove that this function works properly? Well, we need to tell the
Move prover what it is supposed to do. In this case, we want to check that
at the end of the function, the result of `sum` is indeed the sum of the two
arguments.

```move
spec sum {
    ensures result == first + second;
}
```

These specification blocks (or spec blocks) can sit in lots of places. For now,
let's keep it side by side with our function:

```move
module address::step_1 {
    fun sum(first: u64, second: u64): u64 {
        first + second
    }

    spec sum {
        ensures result == first + second;
    }
}
```

Cool. With our new postcondition, we can run `move prove --path step-1`...

```
[INFO] preparing module 0x2::step_1
[INFO] transforming bytecode
[INFO] generating verification conditions
[INFO] 1 verification conditions
[INFO] running solver
[INFO] 0.029s build, 0.001s trafo, 0.008s gen, 2.350s verify, total 2.387s
```

Awesome, no issues.

## Step 2: Aborts <span id="step-2"></span>

Suppose that we want to know when a function can abort. This might be important
because aborts will revert the entire transaction.

Working off the previous code, why don't we add a module spec and make the
prover always check aborts:

```move
spec module {
    pragma aborts_if_is_strict;
}
```

Alternatively, we could add `aborts_if false` to the `sum` spec. This common
pattern would tell the prover to check that `sum` never aborts.

Either way, when we run the prover with `move prove --path step-2`, we get an
error!
```
error: abort not covered by any of the `aborts_if` clauses
   ┌─ ./sources/step-2.move:10:5
   │
 7 │           first + second
   │                 - abort happened here with execution failure
   ·
10 │ ╭     spec sum {
11 │ │         ensures result == first + second;
12 │ │     }
   │ ╰─────^
   │
   =     at ./sources/step-2.move:6: sum
   =         first = 1
   =         second = 18446744073709551615
   =     at ./sources/step-2.move:7: sum
   =         ABORTED

Error: exiting with verification errors
```

The prover finds a case where our function _can_ abort: when `second` is
`18446744073709551615`. This makes sense, because on Move, all "bad arithmetic"
like overflow and division by zero will cause a revert. Let's fix this by
asserting when it will abort:

```move
spec module {
    pragma aborts_if_is_strict;
}

spec sum {
    aborts_if first + second > MAX_U64;
    ensures result == first + second;
}
```

Now when we run the verifier, we see no errors. When writing `aborts_if`
clauses, it is good to know that once you have at least one written—or the
`aborts_if_is_strict` pragma is set—then the abort conditions must exactly
cover when the function will abort. To disable this behavior, set the
`aborts_if_is_partial` pragma to true.

## Step 3: Preconditions <span id="step-3"></span>

In the specification language, preconditions are used to constrain how a
function can be called. If a function is called in a way that violates
its preconditions, the prover will give a verification error.

Why don't we modify our spec for `sum` to see how preconditions work:

```move
module address::step_3 {
    spec module {
        pragma aborts_if_is_strict;
    }

    public fun sum(first: u64, second: u64): u64 {
        first + second
    }

    spec sum {
        // redundant, because of the `aborts_if_is_strict` pragma
        aborts_if false;

        requires first + second <= MAX_U64;
        ensures result == first + second;
    }
}
```

Running the prover, we see that this verifies. Because we provide the
precondition that `first + second` will not overflow, our assertion that
`sum` will not abort (`aborts_if false`) gets verified.

Now, what if we call `sum` in a way that violates its preconditions?

```move
module address::step_3 {
    fun double(number: u64): u64 {
        sum(number, number)
    }

    fun sum(first: u64, second: u64): u64 {
        first + second
    }

    spec sum {
        requires first + second <= MAX_U64;
        aborts_if false;
        ensures result == first + second;
    }
}
```

It aborts with the following error:

```
error: precondition does not hold at this call
   ┌─ ./sources/step-3.move:12:9
   │
12 │         requires first + second <= MAX_U64;
   │         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   │
   =     at ./sources/step-3.move:3: double
   =         number = 9223372036854775808
   =     at ./sources/step-3.move:12: sum (spec)
```

Nice, so it properly checks that functions which call `sum` can't violate its
preconditions. Let's add guards in `double` to make this work:

```move
const MAX_U32: u64 = 1 << 32 - 1;

fun double(number: u64): u64 {
    assert!(number <= MAX_U32, 0);
    sum(number, number)
}

spec double {
    aborts_if number > MAX_U32;
}
```

Now, everything verifies properly! However, what happens if `sum` is called
from some other contract? Let's make it public...

```move
module address::step_3 {
    public fun sum(first: u64, second: u64): u64 {
        first + second
    }

    spec sum {
        requires first + second <= MAX_U64;
        aborts_if false;
        ensures result == first + second;
    }
}
```

Again running the prover, we see that this verifies. However, because `sum` is
public, it can _still_ be called in a way that aborts, despite the prover's
verification!

Recall that Move prover specifications have no runtime effects. For example,
adding an `aborts_if` condition can give meaningful insight about a contract
but won't itself provide runtime guards. Thus, in most contexts, preconditions
do not make much sense in public APIs.

## Step 4: Helper functions <span id="step-4"></span>

Let's write a contract with a bit more functionality:

```move
module address::account {
    use std::signer;

    spec module {
        pragma aborts_if_is_strict;
    }

    struct Account has key {
        balance: u64;
    }

    public fun create_account(s: signer) {
        let address = signer::address_of(&s);
        assert!(!exists<Account>(address), 0);
        move_to<Account>(&s, Account {
            balance: 1
        })
    }
}
```

Now, let's write a spec for `create_account`.

```move
spec create_account {
    aborts_if exists<Account>(signer::address_of(s));
    ensures exists<Account>(signer::address_of(s));
    ensures global<Account>(signer::address_of(s)).balance == 1;
}
```

Notice that we use a number of builtin functions from the specification
language, like `exists` and `borrow_global`. The specification language also
includes many builtin helper functions for working with `vector`s, like
`len`, `contains`, and `index_of`.

To clean up our code, let's write a few helper functions of our own:

```move
spec fun address_of(s: signer): address { signer::address_of(s) }
spec fun balance(a: address): u64 { global<Account>(a).balance }

spec create_account {
    let address = address_of(s);
    aborts_if exists<Account>(address);
    ensures exists<Account>(address);
    ensures balance(address) == 1;
}
```

Much better. Here is our final result:

```move
module address::coin {
    use std::signer;

    spec module {
        pragma aborts_if_is_strict;
    }

    struct Account has key {
        balance: u64
    }

    spec fun address_of(s: signer): address { signer::address_of(s) }
    spec fun balance(a: address): u64 { global<Account>(a).balance }

    public fun create_account(s: signer) {
        let address = signer::address_of(&s);
        assert!(!exists<Account>(address), 0);
        move_to<Account>(&s, Account {
            balance: 1
        })
    }

    spec create_account {
        let address = address_of(s);
        aborts_if exists<Account>(address);
        ensures exists<Account>(address);
        ensures balance(address) == 1;
    }
}
```

## Step 5: State <span id="step-5"></span>

While writing these specifications, we have been implicitly dealing with pre-
and post-state. In the `aborts_if` and `requires` conditions, our expressions
were evaluated against state at function _entry_. In the `ensures`
conditions, the expressions were evaluated against state at function
_exit_.

In contexts like `ensures`, we can also evaluate expressions against the state
at function entry. To do this, we use the `old` builtin. This is extremely
useful: we can verify the action of functions on state.

Suppose we allow users to transfer funds across accounts. Let's implement that:

```move
fun withdraw(target: address, amount: u64) acquires Account {
    let account = borrow_global_mut<Account>(target);
    account.balance = account.balance - amount;
}

spec withdraw {
    aborts_if !exists<Account>(target);
    aborts_if balance(target) < amount;
}

fun deposit(target: address, amount: u64) acquires Account {
    let account = borrow_global_mut<Account>(target);
    account.balance = account.balance + amount;
}

spec deposit {
    aborts_if !exists<Account>(target);
    aborts_if balance(target) + amount > MAX_U64;
}

public fun transfer(
    s: signer,
    to: address,
    amount: u64
) acquires Account {
    let from = signer::address_of(&s);
    assert!(from != to, 0);
    withdraw(from, amount);
    deposit(to, amount);
}

spec transfer {
    let from = address_of(s);
    aborts_if from == to;
    aborts_if !exists<Account>(from);
    aborts_if !exists<Account>(to);
    aborts_if balance(from) < amount;
    aborts_if balance(to) + amount > MAX_U64;
}
```

Now, let's prove that `transfer` works properly. Specifically, the balance of
`from` should decrease by `amount` and the balance of `to` should increase by
`amount`.

```move
ensures balance(from) == old(balance(from)) - amount;
ensures balance(to) == old(balance(to)) + amount;
```

After the prover with `move prove --path step-5`, we see it verifies!

As an aside, it's good to know that function specifications can only access
arguments (as opposed to intermediate variables) and do not respect
reassignment. For instance, consider the following two functions.
```move
fun inc_one(num: &mut u64) {
    *num = *num + 1;
}

fun inc_two(num: u64): u64 {
    num = num + 1;
    num
}
```
If `inc_one` were called on `10`, then in its spec, `num` would be `11` while
`old(num)` would be `10`. However, if `inc_two` were called on `10`, both
`num` and `old(num)` would have value `10`.

# Step 6: Operators and Quantifiers <span id="step-6"></span>

In the Move specification language, all relevant Move operators are supported.
However, the MSL provides a few additional ones as well. For instance, consider
the following function:

```move
fun first_or_second(condition: bool, a: u64, b: u64): u64 {
    if (condition) { a } else { b }
}
```

Now, to write a spec for this, we could just use our standard logical
operators.

```move
spec first_or_second {
    ensures condition && result == a || !condition && result == b;
}
```

However, this is a bit unnatural. We can use the MSL's implication operator
instead!

```move
spec first_or_second {
    ensures condition ==> result == a;
    ensures !condition ==> result == b;
}
```

Another very powerful aspect of the Move prover is that it supports
quantifiers. We can write assertions about the _existence_ of things using
`exists` and about _all_ members of a domain using `forall`. For instance, we
can claim that a vector is sorted.

```move
fun ordered_vector(): vector<u8> {
    vector[1, 2, 3, 4, 5]
}

spec ordered_vector {
    ensures forall i in 0..len(result), j in 0..len(result) where i < j:
        result[i] <= result[j];
}
```

Note that this also uses some more operators specific to the specification
language! For instance, we use the range constructor `0..len(result)` to
declare bounds on the indices `i` and `j`. Also, we can index the `result`
vector using square brackets.

# Step 7: Invariants <span id="step-7"></span>

Let's return to the `coin` module from earlier. Suppose we want to add a
maximum balance for each `Account`. We can do this by adding a check in
`deposit`.

```move
const MAX_BALANCE: u64 = 1000;

fun deposit(target: address, amount: u64) acquires Account {
    let account = borrow_global_mut<Account>(target);
    account.balance = account.balance + amount;
    assert!(account.balance <= MAX_BALANCE, 0);
}
```

Of course, we update our `deposit` and `transfer` specifications to reflect
this possible abort. Now, we can write a global invariant to guarantee that the
balance can never increase above the maximum anywhere in the program. Note that
this invariant is not inside a specification block; it sits directly in the
module.

```move
invariant forall a: address where exists<Account>(a):
    balance(a) <= MAX_BALANCE;
```

Unfortunately, this causes a verification error!

```
error: global memory invariant does not hold
   ┌─ ./sources/coin.move:76:5
   │
76 │ ╭     invariant forall a: address where exists<Account>(a):
77 │ │         balance(a) <= MAX_BALANCE;
   │ ╰──────────────────────────────────^
   │
   =     at ./sources/coin.move:42: deposit
   =         target = 0x0
   =         amount = 2
   =     at ./sources/coin.move:43: deposit
   =         account = &coin.Account{balance = 999}
   =     at ./sources/coin.move:44: deposit
   =     at ./sources/coin.move:45: deposit
   =     at ./sources/coin.move:76

Error: exiting with verification errors
```

This happens because the invariant is temporarily violated in the process of
executing `deposit`. However, the balance increase will always be aborted if it
does bring it over `MAX_BALANCE`. Let's just rewrite our `deposit` function to
maintain this invariant:

```move
fun deposit(target: address, amount: u64) acquires Account {
    let account = borrow_global_mut<Account>(target);
    let new_balance = account.balance + amount;
    assert!(new_balance <= MAX_BALANCE, 0);
    account.balance = new_balance;
}
```

Testing with `move prove --path step-7`, everything verifies properly.

# Step 8: Invariants, part two <span id="step-8"></span>

One of the trickest parts of using the prover is dealing with loops. In the
prover internals, an early step of the proving processes involves performing a
topological sort on the control flow graph. However, this is impossible if the
graph has cycles, so loops are handled in a special way.

Specifically, Move tries to prove loops by using induction. After you provide
loop invariants, the prover checks that

1. The loop invariants hold at the beginning of the loop
2. Loop invariants before an iteration implies them at the end

For instance, consider this simple case:

```move
module address::step_8 {
    fun looper(input: u64): u64 {
        input = if (input < 50) input else 50;
        while (input < 50) {
            input = input + 1;
        };
        input
    }

    spec looper {
        ensures result == 50;
    }
}
```

Although this is clearly true, the prover cannot verify it.

```
error: post-condition does not hold
   ┌─ ./sources/step-8.move:13:9
   │
13 │         ensures result == 50;
   │         ^^^^^^^^^^^^^^^^^^^^^
   │
   =     at ./sources/step-8.move:4: looper
   =         input = 91
   =     at ./sources/step-8.move:5: looper
   =         input = 50
   =     at ./sources/step-8.move:6: looper
   =     enter loop, variable(s) input havocked and reassigned
   =         input = 51
   =     at ./sources/step-8.move:9: looper
   =         result = 51
   =     at ./sources/step-8.move:13: looper (spec)
```

This is because we need to write a loop invariant. Here is one that works.

```move
module address::step_8 {
    fun looper(input: u64): u64 {
        input = if (input < 50) input else 50;
        while ({
            spec {
                invariant input <= 50;
            };

            (input < 50)
        }) {
            input = input + 1;
        };
        input
    }

    spec looper {
        ensures result == 50;
    }
}
```

Now, this verifies properly. Let's take a look at why.

1. Because `input` is constrained to 50 or less, the invariant is clearly true
at the beginning of the loop.
2. If our invariant and loop condition are both true, then `input < 50`. Since
`input` can increase by only one every time, `input <= 50` at the end of the
iteration. Thus, the invariant remains true during an iteration.
3. If we exit the loop, then the invariant is true and the loop condition is
false. If `input <= 50` is true but `input < 50` is false, then `input = 50`.
This proves our assertion.

Loop invariants are hard to write because loops are very powerful. To
illustrate why this is true, let's consider the following function:

```move
fun collatz(input: u64): u64 {
    let steps = 10000;
    let min = input;
    while (steps > 0) {
        if (input % 2 == 0) {
            input = input / 2
        } else {
            input = 3 * input + 1
        };

        min = if (input < min) input else min;

        steps = steps - 1;
    };
    min
}
```

By exhaustive search in existing research, we know that `collatz` on any 64-bit
integer will reach a minimum of 1 within a few thousand steps. However, putting
`ensures result == 1;` into the spec is not sufficient. To make the prover
work, we would have to write an inductive proof that the stopping time of every
64-bit input is less than 10,000, and add it as a loop invariant. No general
proof bounding stopping times exists at this time, though it may be possible to
find one for the restricted input size.

Though writing loop invariants can be hard, we can still use them to do some
pretty cool stuff. Let's say we write a utility function `max` that finds the
maximum value of a `vector<u64>`.

```move
fun max(values: &vector<u64>): u64 {
    let max = *vector::borrow(values, 0);
    let index = 0;
    while (index < vector::length(values)) {
        let current = *vector::borrow(values, index);
        max = if (current > max) current else max;
        index = index + 1;
    };
    max
}
```

Now, let's add the specification we want. Colloquially, given
`values: vector<u64>`, we want `max` to return a result such that every other
`result >= value[i]`. We can write this with a `forall` quantifier:

```move
ensures forall i in 0..len(values): result >= values[i];
```

We also need to make sure that our result is actually in the vector.

```move
spec max {
    ensures forall i in 0..len(values): result >= values[i];
    ensures contains(values, result);
}
```

Of course, this doesn't verify quite yet. We have to write a loop invariant!
I would encourage readers to work through this one on their own, but here is
one solution:

```move
fun max(values: &vector<u64>): u64 {
    let max = *vector::borrow(values, 0);
    let index = 0;
    while ({
        spec {
            invariant forall i in 0..index: max >= values[i];
            invariant contains(values, max);
        };

        (index < vector::length(values))
    }) {
        let current = *vector::borrow(values, index);
        max = if (current > max) current else max;
        index = index + 1;
    };
    max
}
```

Essentially, we hold the invariant that `max` holds the maximum of the sublist
seen so far. As in the specification, we also assert that `max` is actually in
the vector. Now with this invariant, our function gets verified properly.
