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
