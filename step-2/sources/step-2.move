module address::step_2 {
    spec module {
        pragma aborts_if_is_strict;
    }

    fun sum(first: u64, second: u64): u64 {
        first + second
    }

    spec sum {
        aborts_if first + second > MAX_U64;
        ensures result == first + second;
    }
}
