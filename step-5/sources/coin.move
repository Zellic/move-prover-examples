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

        ensures balance(from) == old(balance(from)) - amount;
        ensures balance(to) == old(balance(to)) + amount;
    }
}
