module address::step_3 {
    spec module {
        pragma aborts_if_is_strict;
    }

    const MAX_U32: u64 = 1 << 32 - 1;

    fun double(number: u64): u64 {
        assert!(number <= MAX_U32, 0);
        sum(number, number)
    }

    spec double {
        aborts_if number > MAX_U32;
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
