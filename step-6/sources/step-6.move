module address::step_6 {
    fun first_or_second(condition: bool, a: u64, b: u64): u64 {
        if (condition) { a } else { b }
    }

    spec first_or_second {
        ensures condition ==> result == a;
        ensures !condition ==> result == b;
    }

    fun ordered_vector(): vector<u8> {
        vector[1, 2, 3, 4, 5]
    }

    spec ordered_vector {
        ensures forall i in 0..len(result), j in 0..len(result) where i < j:
            result[i] <= result[j];
    }
}
